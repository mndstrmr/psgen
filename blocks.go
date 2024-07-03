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

type TrailingMode = int

const (
	TRAILING_NONE = iota
	TRAILING_NOW
	TRAILING_STEP
)

type Command struct {
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

func (cmd *Command) verbatimArg(i int) string {
	verbatim, ok := cmd.arg(i).(*VerbatimCommandArg)
	if !ok {
		panic(fmt.Errorf("malformed argument, expecting verbatim at index %d to %s", i, cmd.operator))
	}

	return verbatim.content
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

func parseCommand(str string) Command {
	operatorRest := strings.SplitN(str, " ", 2)

	inlineArgs := make([]CommandArg, 0)
	flags := make([]string, 0)
	trailing := ""
	trailingMode := TRAILING_NONE
	i := 0
	for len(operatorRest) > 1 && i < len(operatorRest[1]) {
		if operatorRest[1][i] == ' ' {
			i += 1
			continue
		}

		if operatorRest[1][i] == '(' {
			i += 1
			start := i
			depth := 1
			for i < len(operatorRest[1]) && (operatorRest[1][i] != ')' || depth > 1) {
				if operatorRest[1][i] == '(' {
					depth += 1
				} else if operatorRest[1][i] == ')' {
					depth -= 1
				}
				i += 1
			}
			if depth != 1 || operatorRest[1][i] != ')' {
				panic(fmt.Errorf("unclosed verbatim"))
			}
			inlineArgs = append(inlineArgs, &VerbatimCommandArg{
				content: operatorRest[1][start:i],
			})

			i += 1 // Closing ')'
		} else if strings.HasPrefix(operatorRest[1][i:], "=>") {
			trailing = strings.Trim(operatorRest[1][i+2:], " \t")
			trailingMode = TRAILING_STEP
			break
		} else if strings.HasPrefix(operatorRest[1][i:], "->") {
			trailing = strings.Trim(operatorRest[1][i+2:], " \t")
			trailingMode = TRAILING_NOW
			break
		} else {
			start := i
			for i < len(operatorRest[1]) && operatorRest[1][i] != ' ' {
				i += 1
			}
			word := operatorRest[1][start:i]
			if strings.HasPrefix(word, "+") {
				flags = append(flags, word[1:])
			} else {
				inlineArgs = append(inlineArgs, &WordArg{
					word: word,
				})
			}
		}
	}

	return Command{
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

func dumpBlock(blocks []Block, indent int) {
	for _, block := range blocks {
		fmt.Print(strings.Repeat(">", indent) + block.first.operator)
		for _, arg := range block.first.inlineArgs {
			fmt.Print(" " + arg.toString())
		}
		fmt.Println()
		dumpBlock(block.body, indent+1)
	}
}
