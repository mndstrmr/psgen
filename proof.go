package main

import (
	"fmt"
	"os"
	"slices"
	"strconv"
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

func (scope *Scope) getState(name string) TokenStream {
	for i := range len(scope.stack) {
		state, ok := scope.stack[len(scope.stack)-1-i].states[name]
		if ok {
			return state
		}
	}

	panic(fmt.Errorf("could not find state %s", name))
}

func (scope *Scope) getPreConditions() []TokenStream {
	pres := []TokenStream{}
	for _, scope := range scope.stack {
		pres = append(pres, scope.conditions...)
	}
	return pres
}

type Provable interface {
	walkProps(func(*Property))
	copy() Provable
	flatten(*FlatProofSequence, int) int
}

func prefix(prop Provable, prefix string) {
	prop.walkProps(func(prop *Property) {
		prop.prefix(prefix)
	})
}

func suffix(prop Provable, suffix string) {
	prop.walkProps(func(prop *Property) {
		prop.suffix(suffix)
	})
}

func condition(prop Provable, cond TokenStream) {
	prop.walkProps(func(prop *Property) {
		prop.condition(cond)
	})
}

type FlatProofSequence struct {
	props [][]*Property
}

func (seq *FlatProofSequence) checkNames() {
	names := []string{}
	unnamed := 0
	for _, group := range seq.props {
		for _, prop := range group {
			if prop.name == "" {
				unnamed += 1
				fmt.Fprintln(os.Stderr, fmt.Errorf("warning: unnamed property with post condition %s. Giving it name Unnamed_%d", prop.postCondition, unnamed))
				prop.name = "Unnamed_" + strconv.Itoa(unnamed)
			} else if slices.Contains(names, prop.name) {
				unnamed += 1
				fmt.Fprintln(os.Stderr, fmt.Errorf("warning: multiple properties with name %s, renaming to %s_%d", prop.name, prop.name, unnamed))
				prop.name += "_" + strconv.Itoa(unnamed)
			} else {
				names = append(names, prop.name)
			}
		}
	}
}

func (seq *FlatProofSequence) addTo(n int, prop *Property) {
	for n >= len(seq.props) {
		seq.props = append(seq.props, make([]*Property, 0))
	}
	seq.props[n] = append(seq.props[n], prop)
}

type Property struct {
	name          string
	preConditions []TokenStream
	postCondition TokenStream
	step          string
	wait          int
}

func NewPropertyFrom(name string, statement TokenStream, scope *Scope) Property {
	return Property{
		name:          name,
		postCondition: statement,
		preConditions: scope.getPreConditions(),
		step:          "|->",
		wait:          0,
	}
}

func (prop *Property) walkProps(f func(*Property)) {
	f(prop)
}

func (prop *Property) prefix(prefix string) {
	if prop.name == "" {
		prop.name = prefix
	} else {
		prop.name = prefix + "_" + prop.name
	}
}

func (prop *Property) suffix(suffix string) {
	if prop.name == "" {
		prop.name = suffix
	} else {
		prop.name = prop.name + "_" + suffix
	}
}

func (prop *Property) condition(cond TokenStream) {
	for _, pre := range prop.preConditions {
		if slices.Equal(pre, cond) {
			return
		}
	}
	prop.preConditions = append(prop.preConditions, cond)
}

func (prop *Property) copy() Provable {
	return &Property{
		name:          prop.name,
		preConditions: slices.Clone(prop.preConditions),
		postCondition: prop.postCondition,
		step:          prop.step,
		wait:          prop.wait,
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

func (group *ProvableGroup) walkProps(f func(*Property)) {
	for _, prop := range group.props {
		prop.walkProps(f)
	}
}

func (group *ProvableGroup) appendProp(prop Property) {
	group.props = append(group.props, &prop)
}

func (group *ProvableGroup) append(prop Provable) {
	if other, ok := prop.(*ProvableGroup); ok {
		group.props = append(group.props, other.props...)
	} else {
		group.props = append(group.props, prop)
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

func (seq *ProvableSeq) walkProps(f func(*Property)) {
	for _, prop := range seq.seq {
		prop.walkProps(f)
	}
}

func (seq *ProvableSeq) append(prop Provable) {
	if other, ok := prop.(*ProvableSeq); ok {
		seq.seq = append(seq.seq, other.seq...)
	} else {
		seq.seq = append(seq.seq, prop)
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

func (cmd *SequenceProofHelper) helpProperty(scope *Scope, prop Provable) Provable {
	for _, helper := range cmd.helpers {
		prop = helper.helpProperty(scope, prop)
	}
	return prop
}

func (cmd *KInductionProofHelper) helpProperty(scope *Scope, prop Provable) Provable {
	group := NewProvableGroup()
	for k := 1; k <= cmd.k; k++ {
		copy := prop.copy()
		copy.walkProps(func(prop *Property) {
			prop.prefix(strconv.Itoa(k) + "Ind")

			// FIXME: Technically the below would be k-induction, but it seems less useful for our purposes I guess
			// if prop.step != "|->" {
			// 	panic("blocking arrow in k induction property")
			// }
			// step := "(" + conjoin(prop.preConditions) + ") -> (" + prop.postCondition + ")"
			// prop.preConditions = []string{}
			// prop.postCondition = step
			// for i := 1; i <= k; i++ {
			// 	prop.preConditions = append(prop.preConditions, past(step, i))
			// }
			prop.wait = k
		})
		group.append(copy)
	}
	group.append(prop)
	return &group
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
	group := NewProvableGroup()

	for i, cas := range cmd.cases {
		new := prop.copy()
		new = cas.helper.helpProperty(scope, new)
		condition(new, cas.condition.getStream(scope))
		if cas.label != "" {
			suffix(new, cas.label)
		} else {
			suffix(new, "Case"+strconv.Itoa(i))
		}
		group.append(new)
	}

	return &ProvableSeq{
		seq: []Provable{&group, prop},
	}
}

func (cmd *SplitBoolProofHelper) helpProperty(scope *Scope, prop Provable) Provable {
	group := NewProvableGroup()

	if len(cmd.pivots) > 16 {
		panic("too many pivots")
	}

	i := 0
	for i < 1<<len(cmd.pivots) {
		new := prop.copy()

		for j, pivot := range cmd.pivots {
			if i&(1<<j) != 0 {
				condition(new, pivot.getStream(scope))

				if pivot.label != "" {
					suffix(new, pivot.label)
				} else {
					suffix(new, "1")
				}
			} else {
				condition(new, negate(pivot.getStream(scope)))
				if pivot.label != "" {
					suffix(new, "Not"+pivot.label)
				} else {
					suffix(new, "0")
				}
			}
		}

		group.append(new)

		i += 1
	}

	return cmd.helper.helpProperty(scope, &group)
}

func (cmd *LemmaProofCommand) genProperty(scope *Scope) Provable {
	lemma, ok := scope.lemmas[cmd.name]
	if !ok {
		panic(fmt.Errorf("lemma does not exist: %s", cmd.name))
	}
	fresh := scope.cloneRoot()
	prop := lemma.genProperty(&fresh)
	if cmd.label != "" {
		prefix(prop, cmd.label)
	}
	return prop
}

func (cmd *BlockProofCommand) genProperty(scope *Scope) Provable {
	prop := cmd.seq.genProperty(scope)
	if cmd.label != "" {
		prefix(prop, cmd.label)
	}
	return prop
}

func (cmd *HaveProofCommand) genProperty(scope *Scope) Provable {
	prop := NewPropertyFrom(cmd.label, cmd.condition, scope)
	return cmd.helper.helpProperty(scope, &prop)
}

func (cmd *InStatesSubProofCommand) genProperty(scope *Scope) Provable {
	group := NewProvableGroup()
	for _, cond := range cmd.states {
		scope.push(&LocalScope{
			states:     map[string]TokenStream{},
			conditions: []TokenStream{cond.getStream(scope)},
		})
		prop := cmd.seq.genProperty(scope)
		if cond.label != "" {
			prefix(prop, cond.label)
		}
		group.append(prop)
		scope.pop()
	}
	if cmd.label != "" {
		prefix(&group, cmd.label)
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

	unionNodeConds := func(nodes []string) TokenStream {
		conds := []TokenStream{}
		for _, node := range nodes {
			conds = append(conds, cmd.findNode(node).condition.getStream(scope))
		}
		return disjoin(conds)
	}

	if len(cmd.entryNodes) > 0 {
		entryGroup := NewProvableGroup()
		// Base cases:
		// Check that the entry condition implies one of the entry nodes are active
		prop := NewPropertyFrom("Initial", unionNodeConds(cmd.entryNodes), scope)
		prop.condition(cmd.entryCondition)
		entryGroup.appendProp(prop)

		// Check that whichever entry node we are in, that node's invariant is satisfied
		for _, node := range cmd.entryNodes {
			prop := NewPropertyFrom("Initial_"+camelCase(node), cmd.invariants[cmd.findNode(node).invariant], scope)
			prop.condition(cmd.findNode(node).condition.getStream(scope))
			prop.condition(cmd.entryCondition)
			entryGroup.appendProp(prop)
		}

		group.append(cmd.entryHelper.helpProperty(scope, &entryGroup))
	}

	// Inductive steps:
	for _, node := range cmd.nodes {
		subGroup := NewProvableGroup()

		if len(node.nextNodes) != 0 {
			// The condition for one of my outgoing nodes is met in the next cycle, unless we leave the domain of the graph altogether
			nexts := unionNodeConds(node.nextNodes)
			negPre := []TokenStream{nexts}
			for _, pre := range scope.getPreConditions() {
				negPre = append(negPre, negate(pre))
			}
			nexts = disjoin(negPre)

			prop := NewPropertyFrom(camelCase(node.name)+"_Step", nexts, scope)
			prop.step = "|=>"
			prop.condition(node.condition.getStream(scope))
			subGroup.appendProp(prop)

			for _, dst := range node.nextNodes {
				// If last cycle I was active and this cycle you are active, then my invariant being true last cycle implies your invariant is true this cycle
				prop := NewPropertyFrom(camelCase(node.name)+"_"+camelCase(dst)+"_Inv", cmd.invariants[cmd.findNode(dst).invariant], scope)
				condition(&prop, past(node.condition.getStream(scope), 1))
				condition(&prop, cmd.findNode(dst).condition.getStream(scope))
				condition(&prop, past(cmd.invariants[node.invariant], 1))
				subGroup.appendProp(prop)
			}
		}

		if cmd.backward {
			// Reverse inductive step path
			incomingNodes := []string{}
			for _, other := range cmd.nodes {
				if slices.Contains(other.nextNodes, node.name) {
					incomingNodes = append(incomingNodes, other.name)
				}
			}
			backwardStr := past(unionNodeConds(incomingNodes), 1)

			if slices.Contains(cmd.entryNodes, node.name) {
				backwardStr = disjoin([]TokenStream{backwardStr, cmd.entryCondition})
			}

			// If my condition is true now, then in the previous cycle one of the conditions of one of the incoming nodes is true
			prop := NewPropertyFrom(camelCase(node.name)+"_Rev", backwardStr, scope)
			prop.condition(node.condition.getStream(scope))
			subGroup.appendProp(prop)
		}

		group.append(node.helper.helpProperty(scope, &subGroup))
	}

	scope.pop()
	if cmd.label != "" {
		prefix(&group, cmd.label)
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
	return &prop
}

func (lemma *Lemma) genProperty(scope *Scope) Provable {
	prop := lemma.seq.genProperty(scope)
	if lemma.label != "" {
		prefix(prop, lemma.label)
	}
	return prop
}
