package main

import (
	"fmt"
	"strings"
)

type CommandArg interface {
	toString() string
	toVerbatimOrState() VerbatimOrState
}

type WordArg struct {
	label string
	word  string
}

func (word *WordArg) toString() string {
	return word.word
}

func (word *WordArg) toVerbatimOrState() VerbatimOrState {
	return VerbatimOrState{
		label:    word.label,
		state:    word.word,
		verbatim: false,
	}
}

type VerbatimCommandArg struct {
	label  string
	stream TokenStream
}

func (verbatim *VerbatimCommandArg) toString() string {
	return "[[" + "]]"
}

func (verbatim *VerbatimCommandArg) toVerbatimOrState() VerbatimOrState {
	return VerbatimOrState{
		label:    verbatim.label,
		stream:   verbatim.stream,
		verbatim: true,
	}
}

type TrailingMode = int

const (
	TRAILING_NONE = iota
	TRAILING_NOW
	TRAILING_STEP
)

type Command struct {
	label        string
	operator     string
	flags        []string
	inlineArgs   []CommandArg
	trailingMode TrailingMode
	trailing     string
}

func (cmd *Command) hasFlag(flag string) bool {
	for _, name := range cmd.flags {
		if name == flag {
			return true
		}
	}
	return false
}

func (cmd *Command) arg(i int) CommandArg {
	if i >= len(cmd.inlineArgs) {
		panic(fmt.Errorf("too few arguments, expecting at least %d arguments to %s", i+1, cmd.operator))
	}
	return cmd.inlineArgs[i]
}

func (cmd *Command) wordArg(i int) string {
	word, ok := cmd.arg(i).(*WordArg)
	if !ok {
		panic(fmt.Errorf("malformed argument, expecting word at index %d to %s", i, cmd.operator))
	}

	return word.word
}

func (cmd *Command) verbatimArg(i int) TokenStream {
	verbatim, ok := cmd.arg(i).(*VerbatimCommandArg)
	if !ok {
		panic(fmt.Errorf("malformed argument, expecting verbatim at index %d to %s", i, cmd.operator))
	}

	return verbatim.stream
}

func (cmd *Command) verbatimOrStateArg(i int) VerbatimOrState {
	return cmd.arg(i).toVerbatimOrState()
}

func (cmd *Command) nowWordArray() []string {
	if cmd.trailingMode == TRAILING_NONE {
		return make([]string, 0)
	}
	if cmd.trailingMode != TRAILING_NOW {
		panic(fmt.Errorf("malformed arguments, expected trailing now array to %s", cmd.operator))
	}
	return strings.Split(cmd.trailing, " ")
}

func (cmd *Command) stepWordArray() []string {
	if cmd.trailingMode == TRAILING_NONE {
		return make([]string, 0)
	}
	if cmd.trailingMode != TRAILING_STEP {
		panic(fmt.Errorf("malformed arguments, expected trailing step array to %s", cmd.operator))
	}
	return strings.Split(cmd.trailing, " ")
}

func (cmd *Command) fixArgs(n int) {
	if len(cmd.inlineArgs) != n {
		panic(fmt.Errorf("expecting %d arguments to %s, found %d", n, cmd.operator, len(cmd.inlineArgs)))
	}
}

func parseLabel(str string) (string, string) {
	labelRest := strings.SplitN(str, ":", 2)
	if len(labelRest) > 1 && !strings.Contains(labelRest[0], " ") {
		return labelRest[0], strings.Trim(labelRest[1], " \t")
	} else {
		return "", str
	}
}

func parseArg(str string) (string, CommandArg) {
	label, rest := parseLabel(str)
	str = rest

	if len(str) > 0 && str[0] == '(' {
		i := 1
		start := i
		depth := 1
		for i < len(str) && (str[i] != ')' || depth > 1) {
			if str[i] == '(' {
				depth += 1
			} else if str[i] == ')' {
				depth -= 1
			}
			i += 1
		}
		if depth != 1 || i >= len(str) || str[i] != ')' {
			panic(fmt.Errorf("unclosed verbatim"))
		}
		s, toks := tokenize(str[start:i])
		if s != "" {
			panic(fmt.Errorf("failed to parse systemverilog"))
		}
		return str[i+1:], &VerbatimCommandArg{
			label:  label,
			stream: toks,
		}
	}

	i := 0
	for i < len(str) && str[i] != ' ' {
		i += 1
	}
	return str[i:], &WordArg{
		label: label,
		word:  str[:i],
	}
}

func parseCommand(str string) Command {
	label, rest := parseLabel(str)
	operatorRest := strings.SplitN(rest, " ", 2)

	if len(operatorRest) > 1 {
		str = operatorRest[1]
	} else {
		str = ""
	}

	inlineArgs := make([]CommandArg, 0)
	flags := make([]string, 0)
	trailing := ""
	trailingMode := TRAILING_NONE
	i := 0
	for i < len(str) {
		if str[i] == ' ' {
			i += 1
			continue
		}

		if strings.HasPrefix(str[i:], "=>") {
			trailing = strings.Trim(str[i+2:], " \t")
			trailingMode = TRAILING_STEP
			break
		} else if strings.HasPrefix(str[i:], "->") {
			trailing = strings.Trim(str[i+2:], " \t")
			trailingMode = TRAILING_NOW
			break
		} else if strings.HasPrefix(str[i:], "+") {
			i += 1
			start := i
			for i < len(str) && str[i] != ' ' {
				i += 1
			}
			flags = append(flags, str[start:i])
		} else {
			newStr, arg := parseArg(str[i:])
			str = newStr
			inlineArgs = append(inlineArgs, arg)
			i = 0
		}
	}

	return Command{
		label:        label,
		operator:     operatorRest[0],
		inlineArgs:   inlineArgs,
		flags:        flags,
		trailing:     trailing,
		trailingMode: trailingMode,
	}
}

type Block struct {
	first Command
	body  []Block
}

func lineDepth(line string) int {
	for c, chr := range line {
		if chr != ' ' {
			return c
		}
	}
	return -1
}

func parseBlocks(lines []string, parentDepth int) (int, []Block) {
	blocks := make([]Block, 0)
	l := 0
	nestedDepth := -1
	for l < len(lines) {
		line := lines[l]

		preComment := strings.SplitN(line, "# ", 2)
		if len(preComment) > 1 {
			line = preComment[0]
		}

		lineDepth := lineDepth(line)
		line = strings.Trim(line, " \t")

		if len(line) == 0 || line == "#" {
			l += 1
			continue
		}

		if lineDepth > parentDepth && nestedDepth == -1 {
			nestedDepth = lineDepth
		}

		if lineDepth <= parentDepth {
			return l, blocks
		}

		if lineDepth > nestedDepth {
			panic(fmt.Errorf("unexpected indent"))
		}

		for l < len(lines) {
			if strings.HasSuffix(line, "\\") {
				l += 1
				line = line[:len(line)-1] + strings.Trim(lines[l], " \t")
			} else if strings.HasSuffix(line, ":") {
				l += 1
				line = line + strings.Trim(lines[l], " \t")
			} else {
				break
			}
		}

		incL, body := parseBlocks(lines[l+1:], nestedDepth)

		blocks = append(blocks, Block{
			first: parseCommand(line),
			body:  body,
		})

		l += 1 + incL
	}
	return l, blocks
}

// func dumpBlock(blocks []Block, indent int) {
// 	for _, block := range blocks {
// 		fmt.Print(strings.Repeat(">", indent) + block.first.operator)
// 		for _, arg := range block.first.inlineArgs {
// 			fmt.Print(" " + arg.toString())
// 		}
// 		fmt.Println()
// 		dumpBlock(block.body, indent+1)
// 	}
// }
