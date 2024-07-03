package main

import (
	"flag"
	"fmt"
	"os"
	"strings"
)

type CommandArg interface {
	toString() string
	toVerbatimOrState() VerbatimOrState
}

type WordArg struct {
	word string
}

func (self *WordArg) toString() string {
	return self.word
}

func (self *WordArg) toVerbatimOrState() VerbatimOrState {
	return VerbatimOrState{
		str:      self.word,
		verbatim: false,
	}
}

type VerbatimCommandArg struct {
	content string
}

func (self *VerbatimCommandArg) toString() string {
	return "[[" + self.content + "]]"
}

func (self *VerbatimCommandArg) toVerbatimOrState() VerbatimOrState {
	return VerbatimOrState{
		str:      self.content,
		verbatim: true,
	}
}

type Command struct {
	operator    string
	inline_args []CommandArg
}

func parseCommand(str string) Command {
	operator_rest := strings.SplitN(str, " ", 2)

	inline_args := make([]CommandArg, 0)
	i := 0
	for len(operator_rest) > 1 && i < len(operator_rest[1]) {
		if operator_rest[1][i] == ' ' {
			i += 1
			continue
		}

		if operator_rest[1][i] == '(' {
			i += 1
			start := i
			depth := 1
			for i < len(operator_rest[1]) && (operator_rest[1][i] != ')' || depth > 1) {
				if operator_rest[1][i] == '(' {
					depth += 1
				} else if operator_rest[1][i] == ')' {
					depth -= 1
				}
				i += 1
			}
			if depth != 1 || operator_rest[1][i] != ')' {
				panic(fmt.Errorf("unclosed verbatim"))
			}
			inline_args = append(inline_args, &VerbatimCommandArg{
				content: operator_rest[1][start:i],
			})

			i += 1 // Closing ')'
		} else {
			start := i
			for i < len(operator_rest[1]) && operator_rest[1][i] != ' ' {
				i += 1
			}
			inline_args = append(inline_args, &WordArg{
				word: operator_rest[1][start:i],
			})
		}
	}

	return Command{
		operator:    operator_rest[0],
		inline_args: inline_args,
	}
}

type Block struct {
	first Command
	body  []Block
}

func lineDepth(line string) int {
	for c, chr := range line {
		if chr != ' ' {
			return c / 4
		}
	}
	return -1
}

func parseBlocks(lines []string, depth int) (int, []Block) {
	blocks := make([]Block, 0)
	l := 0
	for l < len(lines) {
		line := lines[l]

		if len(strings.Trim(line, " \t")) == 0 {
			l += 1
			continue
		}

		lineDepth := lineDepth(line)
		if lineDepth < depth {
			return l, blocks
		}

		if lineDepth > depth {
			panic(fmt.Errorf("unexpected indent"))
		}

		incL, body := parseBlocks(lines[l+1:], depth+1)

		blocks = append(blocks, Block{
			first: parseCommand(strings.Trim(line, " \t")),
			body:  body,
		})

		l += 1 + incL
	}
	return l, blocks
}

type Scope struct {
	states     map[string]string
	conditions []string
}

type VerbatimOrState struct {
	str      string
	verbatim bool
}

type ProofCommand interface{}

type InStateSubProofCommand struct {
	state string
	seq   SequencedProofSteps
}

type HaveProofCommand struct {
	condition string
	helper    ProofHelper
}

type UseProofCommand struct {
	name string
}

type ProofHelper interface{}

type SplitProofCase struct {
	condition string
	helper    ProofHelper
}

type SplitProofHelper struct {
	cases []SplitProofCase
}

type GraphInductionNodeDefinition struct {
	name        string
	invariant   string
	condition   VerbatimOrState
	next_states []string
	helper      ProofHelper
}

type GraphInductionProofHelper struct {
	backward        bool
	invariants      map[string]string
	entry_condition string
	entry_states    []string
	nodes           []GraphInductionNodeDefinition
	scope           Scope
}

type GraphInductionProofCommand struct {
	proof GraphInductionProofHelper
}

type SequencedProofSteps struct {
	scope    Scope
	sequence [][]ProofCommand
}

type Lemma struct {
	name string
	seq  SequencedProofSteps
}

type ProofDocument struct {
	lemmas []Lemma
}

func hasFlag(args []CommandArg, flag string) bool {
	for _, arg := range args {
		word, ok := arg.(*WordArg)
		if !ok {
			continue
		}
		if word.word == "+"+flag {
			return true
		}
		if word.word == "->" || word.word == "=>" {
			return false
		}
	}
	return false
}

func checkInlineArgs(s string, args []CommandArg) int {
	i := 0

	for _, c := range s {
		for i < len(args) {
			arg, ok := args[i].(*WordArg)
			if ok && strings.HasPrefix(arg.word, "+") {
				i += 1
			} else {
				break
			}
		}

		switch c {
		case 'i':
			if i >= len(args) {
				panic(fmt.Errorf("too few arguments for i (%s)", s))
			}
			_, ok := args[i].(*WordArg)
			if !ok {
				panic(fmt.Errorf("incorrect argument type, expecting word"))
			}
			i += 1
		case 'v':
			if i >= len(args) {
				panic(fmt.Errorf("too few arguments for v (%s)", s))
			}
			_, ok := args[i].(*VerbatimCommandArg)
			if !ok {
				panic(fmt.Errorf("incorrect argument type, expecting verbatim (%s)", s))
			}
			i += 1
		case '|':
			if i >= len(args) {
				panic(fmt.Errorf("too few arguments for verbatim or state (%s)", s))
			}
			i += 1
		case '=':
			if i >= len(args) {
				return 0
			}
			w, ok := args[i].(*WordArg)
			if !ok || w.word != "=>" {
				panic(fmt.Errorf("incorrect argument, expecting =>"))
			}
			return len(args) - i - 1
		case '-':
			if i >= len(args) {
				return 0
			}
			w, ok := args[i].(*WordArg)
			if !ok || w.word != "->" {
				panic(fmt.Errorf("incorrect argument, expecting ->"))
			}
			return len(args) - i - 1
		}
	}

	for i < len(args) {
		arg, ok := args[i].(*WordArg)
		if ok && strings.HasPrefix(arg.word, "+") {
			i += 1
		} else {
			break
		}
	}

	if i != len(args) {
		panic(fmt.Errorf("too many arguments"))
	}
	return 0
}

func blocksToProofHelper(blocks []Block) ProofHelper {
	if len(blocks) == 0 {
		return nil
	}

	if len(blocks) > 1 {
		panic("multi step proof helper")
	}

	switch blocks[0].first.operator {
	case "split":
		checkInlineArgs("", blocks[0].first.inline_args)

		cases := make([]SplitProofCase, len(blocks[0].body))
		for b, block := range blocks[0].body {
			if block.first.operator != "case" {
				panic("non case command in split")
			}
			checkInlineArgs("v", block.first.inline_args)
			cases[b] = SplitProofCase{
				condition: block.first.inline_args[0].(*VerbatimCommandArg).content,
				helper:    blocksToProofHelper(block.body),
			}
		}

		return SplitProofHelper{
			cases: cases,
		}
	case "graph_induction":
		checkInlineArgs("", blocks[0].first.inline_args)
		return blocksToGraphInduction(blocks[0])
	default:
		panic("unknown proof helper " + blocks[0].first.operator)
	}
}

func blocksToGraphInduction(root Block) GraphInductionProofHelper {
	cmd := GraphInductionProofHelper{
		backward:        hasFlag(root.first.inline_args, "rev"),
		invariants:      make(map[string]string, 0),
		entry_condition: "",
		entry_states:    make([]string, 0),
		nodes:           make([]GraphInductionNodeDefinition, 0),
		scope: Scope{
			states:     make(map[string]string, 0),
			conditions: make([]string, 0),
		},
	}
	for _, block := range root.body {
		switch block.first.operator {
		case "inv":
			checkInlineArgs("iv", block.first.inline_args)
			cmd.invariants[block.first.inline_args[0].(*WordArg).word] = block.first.inline_args[1].(*VerbatimCommandArg).content
		case "entry":
			n := checkInlineArgs("v-", block.first.inline_args)
			cmd.entry_condition = block.first.inline_args[0].(*VerbatimCommandArg).content
			for i := range n {
				cmd.entry_states = append(cmd.entry_states, block.first.inline_args[len(block.first.inline_args)-n+i].(*WordArg).word)
			}
		case "node":
			n := checkInlineArgs("ii|=", block.first.inline_args)
			node := GraphInductionNodeDefinition{
				name:        block.first.inline_args[0].(*WordArg).word,
				invariant:   block.first.inline_args[1].(*WordArg).word,
				condition:   block.first.inline_args[2].toVerbatimOrState(),
				next_states: make([]string, n),
				helper:      blocksToProofHelper(block.body),
			}
			for i := range n {
				node.next_states[i] = block.first.inline_args[len(block.first.inline_args)-n+i].(*WordArg).word
			}

			cmd.nodes = append(cmd.nodes, node)
		case "cond":
			checkInlineArgs("v", block.first.inline_args)
			cmd.scope.conditions = append(cmd.scope.conditions, block.first.inline_args[0].(*VerbatimCommandArg).content)
		}
	}
	return cmd
}

func blocksToSequenceProof(blocks []Block) SequencedProofSteps {
	seq := SequencedProofSteps{
		scope: Scope{
			states:     make(map[string]string, 0),
			conditions: make([]string, 0),
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
			seq.sequence[len(seq.sequence)-1] = append(seq.sequence[len(seq.sequence)-1], &cmd)
		}
	}
	return seq
}

func blockToProofCommand(block Block, scope *Scope) ProofCommand {
	switch block.first.operator {
	case "in":
		checkInlineArgs("i", block.first.inline_args)
		return InStateSubProofCommand{
			state: block.first.inline_args[0].(*WordArg).word,
			seq:   blocksToSequenceProof(block.body),
		}
	case "have":
		checkInlineArgs("v", block.first.inline_args)
		return HaveProofCommand{
			condition: block.first.inline_args[0].(*VerbatimCommandArg).content,
			helper:    blocksToProofHelper(block.body),
		}
	case "cond":
		checkInlineArgs("v", block.first.inline_args)
		scope.conditions = append(scope.conditions, block.first.inline_args[0].(*VerbatimCommandArg).content)
		return nil
	case "state":
		checkInlineArgs("iv", block.first.inline_args)
		scope.states[block.first.inline_args[0].(*WordArg).word] = block.first.inline_args[1].(*VerbatimCommandArg).content
		return nil
	case "use":
		checkInlineArgs("i", block.first.inline_args)
		return UseProofCommand{
			name: block.first.inline_args[0].(*WordArg).word,
		}
	case "graph_induction":
		checkInlineArgs("", block.first.inline_args)
		return GraphInductionProofCommand{
			proof: blocksToGraphInduction(block),
		}
	default:
		panic("unknown operator " + block.first.operator)
	}
}

func blocksToProofDocument(blocks []Block) ProofDocument {
	lemmas := make([]Lemma, 0)

	for _, block := range blocks {
		if block.first.operator == "lemma" {
			checkInlineArgs("i", block.first.inline_args)
			lemmas = append(lemmas, Lemma{
				name: block.first.inline_args[0].(*WordArg).word,
				seq:  blocksToSequenceProof(block.body),
			})
		} else {
			panic(fmt.Errorf("bad first operator: %s", block.first.operator))
		}
	}

	return ProofDocument{lemmas: lemmas}
}

var path string

func main() {
	flag.StringVar(&path, "path", "", "path to root proof structure")
	flag.Parse()

	if path == "" {
		fmt.Println(fmt.Errorf("error: must specify a path"))
		return
	}

	data, err := os.ReadFile(path)
	if err != nil {
		fmt.Println(err)
		return
	}

	str := strings.Split(string(data), "\n")
	_, blocks := parseBlocks(str, 0)
	dumpBlock(blocks, 0)
	structure := blocksToProofDocument(blocks)
	println(len(structure.lemmas))
	x := structure.lemmas[0].seq.sequence[0][0]
	y, _ := x.(*ProofCommand)
	fmt.Printf("%+v\n", (*y).(GraphInductionProofCommand))
}

func dumpBlock(blocks []Block, indent int) {
	for _, block := range blocks {
		fmt.Print(strings.Repeat(">", indent) + block.first.operator)
		for _, arg := range block.first.inline_args {
			fmt.Print(" " + arg.toString())
		}
		fmt.Println()
		dumpBlock(block.body, indent+1)
	}
}
