package main

import (
	"fmt"
	"strconv"
)

type LocalScope struct {
	states     map[string]TokenStream
	conditions []TokenStream
}

type VerbatimOrState struct {
	label    string
	state    string
	stream   TokenStream
	verbatim bool
}

func (vos *VerbatimOrState) getStream(scope *Scope) TokenStream {
	if vos.verbatim {
		return vos.stream
	} else {
		return scope.getState(vos.state)
	}
}

type ProofCommand interface {
	GenProperty
}

type EachProofCommand struct {
	label string
	ident string
	subs  []VerbatimOrState
	seq   SequencedProofSteps
}

type InStatesSubProofCommand struct {
	label  string
	states []VerbatimOrState
	seq    SequencedProofSteps
}

type LemmaProofCommand struct {
	label string
	name  string
}

type BlockProofCommand struct {
	label string
	seq   SequencedProofSteps
}

type HaveProofCommand struct {
	label     string
	condition TokenStream
	helper    ProofHelper
}

type UseProofCommand struct {
	name   string
	helper ProofHelper
}

type ProofHelper interface {
	HelpProperty
}

type NullProofHelpher struct{}

type SplitProofCase struct {
	label     string
	condition VerbatimOrState
	helper    ProofHelper
}

type SplitProofHelper struct {
	check bool
	cases []SplitProofCase
}

type SplitBoolProofHelper struct {
	pivots []VerbatimOrState
	helper ProofHelper
}

type KInductionProofHelper struct {
	label    string
	k        int
	wireSets []string
}

type SequenceProofHelper struct {
	helpers []ProofHelper
}

func NopProofHelper() ProofHelper {
	return &SequenceProofHelper{helpers: []ProofHelper{}}
}

type GraphInductionNodeDefinition struct {
	exit            bool
	invariant       VerbatimOrState
	condition       VerbatimOrState
	stepTransitions []string
	epsTransitions  []string
	helper          ProofHelper
}

type GraphInductionProofHelper struct {
	label          string
	backward       bool
	complete       bool
	onehot         bool
	invariants     map[string]TokenStream
	entryCondition TokenStream
	entryNodes     []string
	entryHelper    HelpProperty
	nodes          map[string]GraphInductionNodeDefinition
	scope          LocalScope
}

type GraphInductionProofCommand struct {
	proof GraphInductionProofHelper
}

type SequencedProofSteps struct {
	scope    LocalScope
	sequence [][]ProofCommand
}

type Lemma struct {
	label string
	name  string
	seq   SequencedProofSteps
}

type ProofDocument struct {
	defs   map[string]SequencedProofSteps
	lemmas map[string]Lemma
}

func blocksToProofHelper(blocks []Block) ProofHelper {
	helpers := []ProofHelper{}

	for _, block := range blocks {
		switch block.first.operator {
		case "split_bool":
			pivots := make([]VerbatimOrState, 0)
			for _, arg := range block.first.inlineArgs {
				pivots = append(pivots, arg.toVerbatimOrState())
			}
			helpers = append(helpers, &SplitBoolProofHelper{
				pivots: pivots,
				helper: blocksToProofHelper(block.body),
			})
		case "split":
			cases := make([]SplitProofCase, 0)

			for _, arg := range block.first.inlineArgs {
				cases = append(cases, SplitProofCase{
					label:     "",
					condition: arg.toVerbatimOrState(),
					helper:    NopProofHelper(),
				})
			}

			for _, block := range block.body {
				if block.first.operator != "case" {
					panic("non case command in split")
				}
				block.first.fixArgs(1)
				cases = append(cases, SplitProofCase{
					label:     block.first.label,
					condition: block.first.verbatimOrStateArg(0),
					helper:    blocksToProofHelper(block.body),
				})
			}

			helpers = append(helpers, &SplitProofHelper{
				check: !block.first.hasFlag("nocheck"),
				cases: cases,
			})
		case "k_induction":
			block.first.fixArgs(1)
			k, err := strconv.Atoi(block.first.wordArg(0))
			if err != nil {
				panic(fmt.Errorf("expected an integer for k"))
			}
			helpers = append(helpers, &KInductionProofHelper{
				label:    block.first.label,
				k:        k,
				wireSets: []string{},
			})
		case "graph_induction":
			block.first.fixArgs(0)
			x := blocksToGraphInduction(block)
			helpers = append(helpers, &x)
		default:
			panic("unknown proof helper " + block.first.operator)
		}
	}

	if len(helpers) == 1 {
		return helpers[0]
	} else {
		return &SequenceProofHelper{helpers}
	}
}

func blocksToGraphInduction(root Block) GraphInductionProofHelper {
	cmd := GraphInductionProofHelper{
		label:          root.first.label,
		backward:       root.first.hasFlag("rev"),
		complete:       root.first.hasFlag("complete"),
		onehot:         root.first.hasFlag("onehot"),
		invariants:     make(map[string]TokenStream, 0),
		entryCondition: nil,
		entryNodes:     make([]string, 0),
		entryHelper:    NopProofHelper(),
		nodes:          map[string]GraphInductionNodeDefinition{},
		scope: LocalScope{
			states:     make(map[string]TokenStream, 0),
			conditions: make([]TokenStream, 0),
		},
	}
	for _, block := range root.body {
		switch block.first.operator {
		case "inv":
			block.first.fixArgs(2)
			cmd.invariants[block.first.wordArg(0)] = block.first.verbatimArg(1)
		case "entry":
			block.first.fixArgs(1)
			cmd.entryCondition = block.first.verbatimArg(0)
			cmd.entryNodes = append(cmd.entryNodes, block.first.nowWordArray()...)
			cmd.entryHelper = blocksToProofHelper(block.body)
		case "node":
			block.first.fixArgs(3)
			node := GraphInductionNodeDefinition{
				exit:            block.first.hasFlag("exit"),
				invariant:       block.first.verbatimOrStateArg(1),
				condition:       block.first.verbatimOrStateArg(2),
				stepTransitions: []string{},
				helper:          blocksToProofHelper(block.body),
			}
			if block.first.trailingMode == TRAILING_NOW {
				node.epsTransitions = append(node.epsTransitions, block.first.nowWordArray()...)
			} else if block.first.trailingMode == TRAILING_STEP {
				node.stepTransitions = append(node.stepTransitions, block.first.stepWordArray()...)
			}
			cmd.nodes[block.first.wordArg(0)] = node
		case "edge":
			block.first.fixArgs(1)
			name := block.first.wordArg(0)
			node := cmd.nodes[name]
			if block.first.trailingMode == TRAILING_NOW {
				node.epsTransitions = append(node.epsTransitions, block.first.nowWordArray()...)
			} else if block.first.trailingMode == TRAILING_STEP {
				node.stepTransitions = append(node.stepTransitions, block.first.stepWordArray()...)
			}
			cmd.nodes[name] = node
		case "cond":
			block.first.fixArgs(1)
			cmd.scope.conditions = append(cmd.scope.conditions, block.first.verbatimArg(0))
		}
	}
	return cmd
}

func blocksToSequenceProof(blocks []Block) SequencedProofSteps {
	seq := SequencedProofSteps{
		scope: LocalScope{
			states:     make(map[string]TokenStream, 0),
			conditions: make([]TokenStream, 0),
		},
		sequence: make([][]ProofCommand, 1),
	}
	seq.sequence[0] = make([]ProofCommand, 0)

	for _, block := range blocks {
		if block.first.operator == "/" {
			if len(seq.sequence[len(seq.sequence)-1]) != 0 {
				seq.sequence = append(seq.sequence, make([]ProofCommand, 0))
			}
			continue
		}

		cmd := blockToProofCommand(block, &seq.scope)
		if cmd != nil {
			seq.sequence[len(seq.sequence)-1] = append(seq.sequence[len(seq.sequence)-1], cmd)
		}
	}
	return seq
}

func blockToProofCommand(block Block, scope *LocalScope) ProofCommand {
	switch block.first.operator {
	case "block":
		return &BlockProofCommand{
			label: block.first.label,
			seq:   blocksToSequenceProof(block.body),
		}
	case "each":
		subs := []VerbatimOrState{}
		for _, arg := range block.first.inlineArgs[1:] {
			subs = append(subs, arg.toVerbatimOrState())
		}
		return &EachProofCommand{
			label: block.first.label,
			ident: block.first.wordArg(0),
			subs:  subs,
			seq:   blocksToSequenceProof(block.body),
		}
	case "in":
		states := []VerbatimOrState{}
		for _, arg := range block.first.inlineArgs {
			states = append(states, arg.toVerbatimOrState())
		}
		return &InStatesSubProofCommand{
			label:  block.first.label,
			states: states,
			seq:    blocksToSequenceProof(block.body),
		}
	case "lemma":
		block.first.fixArgs(1)
		return &LemmaProofCommand{
			label: block.first.label,
			name:  block.first.wordArg(0),
		}
	case "have":
		block.first.fixArgs(1)
		return &HaveProofCommand{
			label:     block.first.label,
			condition: block.first.verbatimArg(0),
			helper:    blocksToProofHelper(block.body),
		}
	case "cond":
		block.first.fixArgs(1)
		scope.conditions = append(scope.conditions, block.first.verbatimArg(0))
		return nil
	case "state":
		block.first.fixArgs(2)
		scope.states[block.first.wordArg(0)] = block.first.verbatimArg(1)
		return nil
	case "use":
		block.first.fixArgs(1)
		return &UseProofCommand{
			name:   block.first.wordArg(0),
			helper: blocksToProofHelper(block.body),
		}
	case "graph_induction":
		block.first.fixArgs(0)
		return &GraphInductionProofCommand{
			proof: blocksToGraphInduction(block),
		}
	default:
		panic("unknown operator " + block.first.operator)
	}
}

func blocksToProofDocument(blocks []Block) ProofDocument {
	lemmas := make(map[string]Lemma, 0)
	defs := make(map[string]SequencedProofSteps, 0)

	for _, block := range blocks {
		switch block.first.operator {
		case "lemma":
			block.first.fixArgs(1)
			name := block.first.wordArg(0)
			lemmas[name] = Lemma{
				label: block.first.label,
				name:  name,
				seq:   blocksToSequenceProof(block.body),
			}
		case "def":
			block.first.fixArgs(1)
			defs[block.first.wordArg(0)] = blocksToSequenceProof(block.body)
		default:
			panic(fmt.Errorf("bad first operator: %s", block.first.operator))
		}
	}

	return ProofDocument{lemmas: lemmas, defs: defs}
}
