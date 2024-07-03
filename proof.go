package main

import (
	"fmt"
	"slices"
)

type Scope struct {
	lemmas map[string]Lemma
	stack  []*LocalScope
	defs   map[string]SequencedProofSteps
}

func (scope *Scope) cloneRoot() Scope {
	v := Scope{
		lemmas: map[string]Lemma{},
		stack:  []*LocalScope{},
		defs:   map[string]SequencedProofSteps{},
	}
	for k, lemma := range scope.lemmas {
		v.lemmas[k] = lemma
	}
	return v
}

func (scope *Scope) push(local *LocalScope) {
	scope.stack = append(scope.stack, local)
}

func (scope *Scope) pop() *LocalScope {
	last := scope.stack[len(scope.stack)-1]
	scope.stack = scope.stack[:len(scope.stack)-1]
	return last
}

func (scope *Scope) getState(name string) string {
	for i := range len(scope.stack) {
		state, ok := scope.stack[len(scope.stack)-1-i].states[name]
		if ok {
			return state
		}
	}

	panic(fmt.Errorf("could not find state %s", name))
}

type Provable interface {
	prefix(string)
	condition(string)
	copy() Provable
	flatten(*FlatProofSequence, int) int
}

type FlatProofSequence struct {
	props [][]*Property
}

func (seq *FlatProofSequence) addTo(n int, prop *Property) {
	for n >= len(seq.props) {
		seq.props = append(seq.props, make([]*Property, 0))
	}
	seq.props[n] = append(seq.props[n], prop)
}

type Property struct {
	name            string
	revImplications []string
}

func NewPropertyFrom(name string, statement string) Property {
	return Property{
		name:            name,
		revImplications: []string{statement},
	}
}

func (prop *Property) prefix(prefix string) {
	if prop.name == "" {
		prop.name = prefix
	} else {
		prop.name = prefix + "_" + prop.name
	}
}

func (prop *Property) condition(cond string) {
	prop.revImplications = append(prop.revImplications, cond)
}

func (prop *Property) copy() Provable {
	return &Property{
		name:            prop.name,
		revImplications: slices.Clone(prop.revImplications),
	}
}

func (prop *Property) flatten(seq *FlatProofSequence, n int) int {
	seq.addTo(n, prop)
	return n
}

// An unordered set of properties
type ProvableGroup struct {
	props []Provable
}

func NewProvableGroup() ProvableGroup {
	return ProvableGroup{
		props: make([]Provable, 0),
	}
}

func (group *ProvableGroup) appendProp(prop Property) {
	group.props = append(group.props, &prop)
}

func (group *ProvableGroup) prefix(prefix string) {
	for _, step := range group.props {
		step.prefix(prefix)
	}
}

func (group *ProvableGroup) append(prop Provable) {
	if other, ok := prop.(*ProvableGroup); ok {
		group.props = append(group.props, other.props...)
	} else {
		group.props = append(group.props, prop)
	}
}

func (group *ProvableGroup) condition(cond string) {
	for _, step := range group.props {
		step.condition(cond)
	}
}

func (group *ProvableGroup) flatten(seq *FlatProofSequence, prev int) int {
	max := prev
	for _, prop := range group.props {
		if n := prop.flatten(seq, prev); n > max {
			max = n
		}
	}
	return max
}

func (group *ProvableGroup) copy() Provable {
	new := ProvableGroup{
		props: make([]Provable, len(group.props)),
	}
	for i, prop := range group.props {
		new.props[i] = prop.copy()
	}
	return &new
}

// An ordered sequence of properties
type ProvableSeq struct {
	seq []Provable
}

func (seq *ProvableSeq) prefix(prefix string) {
	for _, step := range seq.seq {
		step.prefix(prefix)
	}
}

func (seq *ProvableSeq) append(prop Provable) {
	if other, ok := prop.(*ProvableSeq); ok {
		seq.seq = append(seq.seq, other.seq...)
	} else {
		seq.seq = append(seq.seq, prop)
	}
}

func (seq *ProvableSeq) condition(cond string) {
	for _, step := range seq.seq {
		step.condition(cond)
	}
}

func (seq *ProvableSeq) copy() Provable {
	new := ProvableSeq{
		seq: make([]Provable, len(seq.seq)),
	}
	for i, prop := range seq.seq {
		new.seq[i] = prop.copy()
	}
	return &new
}

func (seq *ProvableSeq) flatten(fseq *FlatProofSequence, prev int) int {
	max := prev
	for _, prop := range seq.seq {
		max = prop.flatten(fseq, max) + 1
	}
	return max - 1
}

type GenProperty interface {
	genProperty(scope *Scope) Provable
}

type HelpProperty interface {
	helpProperty(scope *Scope, prop Provable) Provable
}

func (cmd *NullProofHelpher) helpProperty(scope *Scope, prop Provable) Provable {
	return prop
}

func (cmd *GraphInductionProofHelper) helpProperty(scope *Scope, prop Provable) Provable {
	group := cmd.genCommonProperty(scope)
	return &ProvableSeq{
		seq: []Provable{
			group,
			prop,
		},
	}
}

func (cmd *SplitProofHelper) helpProperty(scope *Scope, prop Provable) Provable {
	group := ProvableGroup{
		props: make([]Provable, 0),
	}

	for _, cas := range cmd.cases {
		new := prop.copy()
		new.condition(cas.condition.getString(scope))
		group.append(cas.helper.helpProperty(scope, new))
	}

	return &ProvableSeq{
		seq: []Provable{&group, prop},
	}
}

func (cmd *SplitBoolProofHelper) helpProperty(scope *Scope, prop Provable) Provable {
	group := ProvableGroup{
		props: make([]Provable, 0),
	}

	if len(cmd.pivots) > 16 {
		panic("to many pivots")
	}

	i := 0
	for i < 1<<len(cmd.pivots) {
		new := prop.copy()

		for j, pivot := range cmd.pivots {
			if i&(1<<j) != 0 {
				new.condition(pivot.getString(scope))
			} else {
				new.condition("~(" + pivot.getString(scope) + ")")
			}
		}

		group.append(new)

		i += 1
	}

	return &group
}

func (cmd *LemmaProofCommand) genProperty(scope *Scope) Provable {
	lemma, ok := scope.lemmas[cmd.name]
	if !ok {
		panic(fmt.Errorf("lemma does not exist: %s", cmd.name))
	}
	fresh := scope.cloneRoot()
	return lemma.genProperty(&fresh)
}

func (cmd *BlockProofCommand) genProperty(scope *Scope) Provable {
	prop := cmd.seq.genProperty(scope)
	if cmd.label != "" {
		prop.prefix(cmd.label)
	}
	return prop
}

func (cmd *HaveProofCommand) genProperty(scope *Scope) Provable {
	prop := NewPropertyFrom(cmd.label, cmd.condition)
	return cmd.helper.helpProperty(scope, &prop)
}

func (cmd *InStatesSubProofCommand) genProperty(scope *Scope) Provable {
	group := NewProvableGroup()
	prop := cmd.seq.genProperty(scope)
	for _, cond := range cmd.states {
		copy := prop.copy()
		copy.condition(cond.getString(scope))
		group.append(copy)
	}
	if cmd.label != "" {
		group.prefix(cmd.label)
	}
	return &group
}

func (cmd *UseProofCommand) genProperty(scope *Scope) Provable {
	prop_seq, ok := scope.defs[cmd.name]
	if !ok {
		panic(fmt.Errorf("undefined def %s", cmd.name))
	}

	return cmd.helper.helpProperty(scope, prop_seq.genProperty(scope))
}

func (cmd *GraphInductionProofHelper) genCommonProperty(scope *Scope) Provable {
	scope.push(&cmd.scope)
	group := NewProvableGroup()

	unionNodeConds := func(nodes []string) string {
		statesActive := ""
		for _, node := range nodes {
			statesActive += " | (" + cmd.findNode(node).condition.getString(scope) + ")"
		}
		return statesActive[3:]
	}

	if len(cmd.entryNodes) > 0 {
		// Base cases:
		// Check that the entry condition implies one of the entry nodes are active
		group.appendProp(NewPropertyFrom("initial", "("+cmd.entryCondition+") |-> ("+unionNodeConds(cmd.entryNodes)+")"))

		// Check that whichever entry node we are in, that node's invariant is satisfied
		for _, node := range cmd.entryNodes {
			group.appendProp(NewPropertyFrom("initial_"+node, "("+cmd.entryCondition+") & ("+cmd.findNode(node).condition.getString(scope)+") |-> ("+cmd.invariants[cmd.findNode(node).invariant]+")"))
		}
	}

	// Inductive steps:
	for _, node := range cmd.nodes {
		// If there are no next nodes we are allowed to leave the graph
		if len(node.nextNodes) == 0 {
			continue
		}

		sub_group := NewProvableGroup()
		// The condition for one of my outgoing nodes is met in the next cycle
		sub_group.appendProp(NewPropertyFrom(node.name+"_step", "("+node.condition.getString(scope)+") |=> ("+unionNodeConds(node.nextNodes)+")"))

		for _, dst := range node.nextNodes {
			// If last cycle I was active and this cycle you are active, then my invariant being true last cycle implies your invariant is true this cycle
			sub_group.appendProp(NewPropertyFrom(node.name+"_"+dst+"_inv", "$past("+node.condition.getString(scope)+") && ("+cmd.findNode(dst).condition.getString(scope)+") && $past("+cmd.invariants[node.invariant]+") |-> ("+cmd.invariants[cmd.findNode(dst).invariant]+")"))
		}

		if cmd.backward {
			// Reverse inductive step path
			reverseNodes := []string{}
			for _, other := range cmd.nodes {
				if !slices.Contains(other.nextNodes, node.name) {
					reverseNodes = append(reverseNodes, other.name)
				}
			}
			backwardStr := unionNodeConds(reverseNodes)

			entryCarvout := ""
			if slices.Contains(cmd.entryNodes, node.name) {
				entryCarvout += " | (" + cmd.entryCondition + ")"
			}

			sub_group.appendProp(NewPropertyFrom(node.name+"_rev", "("+node.condition.getString(scope)+") |-> $past("+backwardStr+")"+entryCarvout))
		}

		group.append(node.helper.helpProperty(scope, &sub_group))
	}

	scope.pop()
	cmd.scope.applyScopeConds(&group)
	if cmd.label != "" {
		group.prefix(cmd.label)
	}
	return &group
}

func (cmd *GraphInductionProofCommand) genProperty(scope *Scope) Provable {
	return cmd.proof.genCommonProperty(scope)
}

func (seq *SequencedProofSteps) genProperty(scope *Scope) Provable {
	scope.push(&seq.scope)
	prop := ProvableSeq{
		seq: make([]Provable, 0),
	}

	for _, step := range seq.sequence {
		if len(step) == 0 {
			continue
		}

		if len(step) == 1 {
			prop.append(step[0].genProperty(scope))
			continue
		}

		group := ProvableGroup{
			props: make([]Provable, 0),
		}
		for _, cmd := range step {
			group.append(cmd.genProperty(scope))
		}
		prop.append(&group)
	}

	scope.pop()
	seq.scope.applyScopeConds(&prop)
	return &prop
}

func (scope *LocalScope) applyScopeConds(prop Provable) {
	for _, cond := range scope.conditions {
		prop.condition(cond)
	}
}

func (lemma *Lemma) genProperty(scope *Scope) Provable {
	return lemma.seq.genProperty(scope)
}
