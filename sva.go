package main

import (
	"fmt"
	"slices"
	"strconv"
	"strings"
)

func camelCase(str string) string {
	out := ""
	for _, word := range strings.Split(str, "_") {
		out += strings.ToUpper(string(word[0])) + word[1:]
	}
	return out
}

type BreakLoc = int

const (
	BREAK_REPLACE = iota
	BREAK_BEFORE
	BREAK_AFTER
	BREAK_AROUND
)

type BreakMode struct {
	loc  BreakLoc
	prio int
}

type TokenStream = []Token

type Token interface {
	breakMode() BreakMode
	toString() string
	subs(ident string, new []Token) []Token
}

type NameToken struct {
	content string
}

func (name *NameToken) breakMode() BreakMode {
	return BreakMode{prio: -1}
}

func (name *NameToken) toString() string {
	return name.content
}

func (name *NameToken) subs(ident string, new []Token) []Token {
	if ident == name.content {
		return new
	} else {
		return []Token{name}
	}
}

type NumToken struct {
	num string
}

func (num *NumToken) breakMode() BreakMode {
	return BreakMode{prio: -1}
}

func (num *NumToken) toString() string {
	return num.num
}

func (num *NumToken) subs(ident string, new []Token) []Token {
	return []Token{num}
}

type OperatorToken struct {
	operator string
}

func (op *OperatorToken) breakMode() BreakMode {
	switch op.operator {
	case "|->", "|=>", "->":
		return BreakMode{loc: BREAK_AROUND, prio: 5}
	case "&&", "&", "|", "||":
		return BreakMode{loc: BREAK_AFTER, prio: 4}
	case "(", ")", ";", "``", "`":
		return BreakMode{prio: -1}
	default:
		return BreakMode{loc: BREAK_AFTER, prio: 1}
	}
}

func (op *OperatorToken) toString() string {
	return op.operator
}

func (op *OperatorToken) subs(ident string, new []Token) []Token {
	return []Token{op}
}

type BracketedToken struct {
	openBracket  byte
	closeBracket byte
	content      TokenStream
}

func (brack *BracketedToken) breakMode() BreakMode {
	return BreakMode{prio: -1}
}

func (brack *BracketedToken) toString() string {
	return string(brack.openBracket) + streamToString(brack.content) + string(brack.closeBracket)
}

func (brack *BracketedToken) subs(ident string, new []Token) []Token {
	return []Token{&BracketedToken{
		openBracket:  brack.openBracket,
		closeBracket: brack.closeBracket,
		content:      subsStream(brack.content, ident, new),
	}}
}

type WhiteSpaceToken struct{}

func (ws *WhiteSpaceToken) breakMode() BreakMode {
	return BreakMode{loc: BREAK_REPLACE, prio: 2}
}

func (ws *WhiteSpaceToken) toString() string {
	return " "
}

func (ws *WhiteSpaceToken) subs(ident string, new []Token) []Token {
	return []Token{ws}
}

func streamToString(stream TokenStream) string {
	str := ""
	for _, tok := range stream {
		str += tok.toString()
	}
	return str
}

func paren(stream TokenStream) Token {
	return &BracketedToken{
		openBracket:  '(',
		closeBracket: ')',
		content:      stream,
	}
}

func isIdentStart(c byte) bool {
	return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '_' || c == '$'
}

func isNum(c byte) bool {
	return '0' <= c && c <= '9'
}

func isDecStep(c byte) bool {
	return isNum(c) || c == '_'
}

func isBinStep(c byte) bool {
	return c == '0' || c == '1' || c == '_'
}

func isOctStep(c byte) bool {
	return ('0' <= c && c <= '7') || c == '_'
}

func isHexStep(c byte) bool {
	return ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F') || c == '_'
}

func isIdentStep(c byte) bool {
	return isIdentStart(c) || isNum(c) || (c == '.')
}

func isWhitespace(c byte) bool {
	return c == ' ' || c == '\n' || c == '\t' || c == '\r'
}

func tokenizeNum(str string) (string, NumToken) {
	i := 1
	for i < len(str) && isDecStep(str[i]) {
		i++
	}

	if i+2 < len(str) && str[i] == '\'' {
		i += 2
		switch str[i-1] {
		case 'b':
			for i < len(str) && isBinStep(str[i]) {
				i++
			}
		case 'o':
			for i < len(str) && isOctStep(str[i]) {
				i++
			}
		case 'd':
			for i < len(str) && isDecStep(str[i]) {
				i++
			}
		case 'h':
			for i < len(str) && isHexStep(str[i]) {
				i++
			}
		default:
			panic(fmt.Errorf("unknown base"))
		}
	}
	return str[i:], NumToken{
		num: str[:i],
	}
}

func tokenize(str string) (string, TokenStream) {
	stream := TokenStream{}

	for len(str) > 0 {
		if isWhitespace(str[0]) {
			for len(str) > 0 && isWhitespace(str[0]) {
				str = str[1:]
			}
			stream = append(stream, &WhiteSpaceToken{})
			continue
		}

		if strings.Contains(")]}", string(str[0])) {
			break
		}

		if idx := strings.IndexAny("([{", string(str[0])); idx >= 0 {
			newStr, content := tokenize(str[1:])
			str = newStr
			if str[0] != ")]}"[idx] {
				panic(fmt.Errorf("malformed SystemVerilog, expected %c found %c", ")]}"[idx], str[0]))
			}
			str = str[1:]
			stream = append(stream, &BracketedToken{
				openBracket:  "([{"[idx],
				closeBracket: ")]}"[idx],
				content:      content,
			})
			continue
		}

		if isIdentStart(str[0]) {
			i := 1
			for i < len(str) && isIdentStep(str[i]) {
				i++
			}
			stream = append(stream, &NameToken{
				content: str[:i],
			})
			str = str[i:]
			continue
		}

		if isNum(str[0]) {
			newStr, tok := tokenizeNum(str)
			str = newStr
			stream = append(stream, &tok)
			continue
		}

		end := 1
		for _, operator := range []string{
			"|->", "|=>", "&&", "&", "||", "|", "->", "~", "``", "`",
		} {
			if strings.HasPrefix(str, operator) {
				end = len(operator)
				break
			}
		}

		stream = append(stream, &OperatorToken{
			operator: str[:end],
		})
		str = str[end:]
	}

	return str, stream
}

func past(str TokenStream, n int) TokenStream {
	end := ""
	if n != 1 {
		end = ", " + strconv.Itoa(n)
	}

	newStream := TokenStream{}
	for _, tok := range str {
		if id, ok := tok.(*NameToken); ok {
			newStream = append(newStream, &NameToken{
				content: "$past(" + id.content + end + ")",
			})
		} else if bracket, ok := tok.(*BracketedToken); ok {
			newStream = append(newStream, &BracketedToken{
				openBracket:  bracket.openBracket,
				closeBracket: bracket.closeBracket,
				content:      past(bracket.content, n),
			})
		} else {
			newStream = append(newStream, tok)
		}
	}
	return newStream
}

func isConjunctionOperator(op string) bool {
	return op == "&" || op == "&&"
}

func isDisjunctionOperator(op string) bool {
	return op == "|" || op == "||"
}

func isUnaryOperator(op string) bool {
	return op == "~" || op == "-" || op == "`"
}

func isUnary(stream TokenStream) bool {
	for _, token := range stream {
		if op, ok := token.(*OperatorToken); ok {
			if !isUnaryOperator(op.operator) {
				return false
			}
		}
	}
	return true
}

func isConjunction(stream TokenStream) bool {
	for _, token := range stream {
		if op, ok := token.(*OperatorToken); ok {
			if !isUnaryOperator(op.operator) && !isConjunctionOperator(op.operator) {
				return false
			}
		}
	}
	return true
}

func isDisjunction(stream TokenStream) bool {
	for _, token := range stream {
		if op, ok := token.(*OperatorToken); ok {
			if !isUnaryOperator(op.operator) && !isDisjunctionOperator(op.operator) {
				return false
			}
		}
	}
	return true
}

func isWhitespaceTerm(stream TokenStream) bool {
	for _, token := range stream {
		if _, ok := token.(*WhiteSpaceToken); !ok {
			return false
		}
	}
	return true
}

func comma(terms []TokenStream) TokenStream {
	newStream := TokenStream{}
	for i, term := range terms {
		if i != 0 {
			newStream = append(newStream, &OperatorToken{operator: ","}, &WhiteSpaceToken{})
		}
		newStream = append(newStream, term...)
	}
	return newStream
}

func vector(bits []TokenStream) TokenStream {
	return TokenStream{
		&BracketedToken{
			openBracket:  '{',
			closeBracket: '}',
			content:      comma(bits),
		},
	}
}

func onehot(terms []TokenStream) TokenStream {
	return TokenStream{
		&NameToken{"$onehot"},
		paren(vector(terms)),
	}
}

func onehot0(terms []TokenStream) TokenStream {
	return TokenStream{
		&NameToken{"$onehot0"},
		paren(vector(terms)),
	}
}

func conjoin(terms []TokenStream) TokenStream {
	newStream := TokenStream{}

	for _, term := range terms {
		if isWhitespaceTerm(term) {
			continue
		}

		if len(newStream) != 0 {
			newStream = append(newStream, &WhiteSpaceToken{})
			newStream = append(newStream, &OperatorToken{
				operator: "&&",
			})
			newStream = append(newStream, &WhiteSpaceToken{})
		}
		if !isConjunction(term) {
			newStream = append(newStream, paren(term))
		} else {
			newStream = append(newStream, term...)
		}
	}

	if len(newStream) == 0 {
		newStream = append(newStream, &NumToken{num: "1"})
	}

	return newStream
}

func disjoin(terms []TokenStream) TokenStream {
	newStream := TokenStream{}

	for _, term := range terms {
		if isWhitespaceTerm(term) {
			continue
		}

		if len(newStream) != 0 {
			newStream = append(newStream, &WhiteSpaceToken{})
			newStream = append(newStream, &OperatorToken{
				operator: "||",
			})
			newStream = append(newStream, &WhiteSpaceToken{})
		}
		if !isDisjunction(term) {
			newStream = append(newStream, paren(term))
		} else {
			newStream = append(newStream, term...)
		}
	}

	if len(newStream) == 0 {
		newStream = append(newStream, &NumToken{num: "0"})
	}

	return newStream
}

func termsOf(stream TokenStream) []TokenStream {
	blocks := []TokenStream{{}}
	for _, tok := range stream {
		if op, ok := tok.(*OperatorToken); ok && !isUnaryOperator(op.operator) {
			blocks = append(blocks, TokenStream{})
		} else {
			blocks[len(blocks)-1] = append(blocks[len(blocks)-1], tok)
		}
	}
	return blocks
}

func reJoinNegate(stream TokenStream, newOp string) TokenStream {
	terms := termsOf(stream)
	newStream := TokenStream{}
	for i, term := range terms {
		if i != 0 {
			newStream = append(newStream, &OperatorToken{operator: newOp})
		}
		newStream = append(newStream, negate(term)...)
	}
	return newStream
}

func negate(term TokenStream) TokenStream {
	if isUnary(term) {
		i := 0
		for i < len(term) {
			if _, ok := term[i].(*WhiteSpaceToken); !ok {
				break
			}
			i += 1
		}
		if i < len(term) {
			if op, ok := term[i].(*OperatorToken); ok && op.operator == "~" {
				return slices.Delete(slices.Clone(term), i, i+1)
			}
		}
		var op Token
		op = &OperatorToken{operator: "~"}
		return slices.Insert(slices.Clone(term), i, op)
	} else if isConjunction(term) {
		return reJoinNegate(term, "||")
	} else if isDisjunction(term) {
		return reJoinNegate(term, "&&")
	} else {
		return TokenStream{&OperatorToken{operator: "~"}, paren(term)}
	}
}

func subsStream(stream TokenStream, ident string, new TokenStream) TokenStream {
	tokens := TokenStream{}
	for _, tok := range stream {
		tokens = append(tokens, tok.subs(ident, new)...)
	}
	return tokens
}

// Every parens is either broken or not
// Every whitespace is either broken or not
// Every whitespace has a priority
// A whitespace inside a parens cannot be broken unless the parens is broken
// A parens inside a parens cannot be broken unless the parens is broken
//
// Repeatedly consider the longest line:
//  2. If the highest priority (not nested) break is a parens break it
//  3. Break along the highest priority whitespace if it exists (not nested).
//  4. Otherwise find the longest parens and break it
//  5. Otherwise ignore this line

type Line struct {
	tokens          TokenStream
	breakRangeStart int
	breakRangeEnd   int
	indent          int
}

func (line *Line) breakParens(i int, newLines *[]Line) {
	paren := line.tokens[i].(*BracketedToken)

	line1 := Line{tokens: slices.Clone(line.tokens[:i]), indent: line.indent, breakRangeStart: line.breakRangeStart, breakRangeEnd: i + 1}
	line1.tokens = append(line1.tokens, &OperatorToken{operator: string(paren.openBracket)})
	line2 := Line{tokens: paren.content, indent: line.indent + 1, breakRangeStart: 0, breakRangeEnd: len(paren.content)}
	line3 := Line{tokens: slices.Clone(line.tokens[i+1:]), indent: line.indent, breakRangeStart: 0, breakRangeEnd: line.breakRangeEnd - i}
	line3.tokens = slices.Insert[[]Token, Token](line3.tokens, 0, &OperatorToken{operator: string(paren.closeBracket)})

	*newLines = append(*newLines, line1, line2, line3)
}

// If any parens on the line contains more than lineWidth chars, break the parens and continue
func (line *Line) checkParens(newLines *[]Line, lineWidth int) bool {
	for i, tok := range line.tokens {
		paren, ok := tok.(*BracketedToken)
		if !ok || len(streamToString(paren.content)) <= lineWidth {
			continue
		}
		line.breakParens(i, newLines)
		return true
	}
	return false
}

func (line *Line) highestPrio() int {
	highestPrio := -1
	for _, tok := range line.tokens[line.breakRangeStart:line.breakRangeEnd] {
		mode := tok.breakMode()
		if mode.prio > highestPrio {
			highestPrio = mode.prio
		}
	}
	return highestPrio
}

// Break along the highest priority token if it exists (not nested).
func (line *Line) chooseBreak(lineLen int) int {
	highestPrio := line.highestPrio()
	if highestPrio == -1 {
		return -1
	}

	col := 0
	highPrioCenterI := -1
	highPrioCenter := 999999
	for i, tok := range line.tokens {
		mode := tok.breakMode()
		add := len(tok.toString()) // FIXME: Leading whitespace
		if i < line.breakRangeStart || i >= line.breakRangeEnd || mode.prio != highestPrio {
			col += add
			continue
		}

		abs := func(a int) int {
			if a < 0 {
				return -a
			}
			return a
		}

		var d int
		switch mode.loc {
		case BREAK_BEFORE, BREAK_AROUND, BREAK_REPLACE:
			d = abs(lineLen/2 - col)
		case BREAK_AFTER:
			d = abs(lineLen/2 - (col + add))
		default:
			panic("bad loc")
		}

		if d < highPrioCenter {
			highPrioCenter = d
			highPrioCenterI = i
		}
		col += add
	}

	return highPrioCenterI
}

func (line *Line) breakAt(idx int, newLines *[]Line) {
	tok := line.tokens[idx]
	loc := tok.breakMode().loc
	line1 := Line{tokens: slices.Clone(line.tokens[:idx]), indent: line.indent, breakRangeStart: line.breakRangeStart, breakRangeEnd: idx}
	line2 := Line{tokens: slices.Clone(line.tokens[idx+1:]), indent: line.indent, breakRangeStart: 0, breakRangeEnd: len(line.tokens) - idx - 1}

	switch loc {
	case BREAK_AFTER:
		line1.tokens = append(line1.tokens, tok)
		// Don't update breakRangeEnd
		*newLines = append(*newLines, line1, line2)
	case BREAK_BEFORE:
		line2.tokens = slices.Insert(line2.tokens, 0, tok)
		line1.breakRangeStart += 1
		line1.breakRangeEnd += 1
		*newLines = append(*newLines, line1, line2)
	case BREAK_AROUND:
		line3 := Line{tokens: []Token{tok}, indent: line.indent, breakRangeStart: 0, breakRangeEnd: 0}
		*newLines = append(*newLines, line1, line3, line2)
	case BREAK_REPLACE:
		*newLines = append(*newLines, line1, line2)
	default:
		panic("bad break")
	}
}

func (line *Line) longestParens() int {
	longestI := -1
	longestW := 0
	for i, tok := range line.tokens {
		if parens, ok := tok.(*BracketedToken); ok {
			w := len(parens.toString())
			if w >= longestW {
				longestW = w
				longestI = i
			}
		}
	}
	return longestI
}

func concatTokens(stream TokenStream) TokenStream {
	newStream := TokenStream{}
	for _, tok := range stream {
		if brack, ok := tok.(*BracketedToken); ok {
			newStream = append(newStream, &BracketedToken{
				openBracket:  brack.openBracket,
				closeBracket: brack.closeBracket,
				content:      concatTokens(brack.content),
			})
			continue
		}

		if len(newStream) < 2 {
			newStream = append(newStream, tok)
			continue
		}

		name1, ok1 := newStream[len(newStream)-2].(*NameToken)
		op, ok2 := newStream[len(newStream)-1].(*OperatorToken)
		name2, ok3 := tok.(*NameToken)
		if !ok1 || !ok2 || !ok3 || op.operator != "``" {
			newStream = append(newStream, tok)
			continue
		}

		newStream = slices.Delete(newStream, len(newStream)-2, len(newStream))
		newStream = append(newStream, &NameToken{content: name1.content + name2.content})
	}
	return newStream
}

func formatStream(stream TokenStream, lineWidth int) string {
	lines := []Line{{tokens: concatTokens(stream), indent: 0, breakRangeStart: 0, breakRangeEnd: len(stream)}}

	allFit := false
	changed := true
	for !allFit && changed {
		newLines := []Line{}
		allFit = true
		changed = false
		for _, line := range lines {
			// FIXME: Wasteful and slow to keep generating strings
			lineLen := line.indent*4 + len(streamToString(line.tokens))
			if lineLen <= lineWidth {
				newLines = append(newLines, line)
				continue
			}
			allFit = false

			if line.checkParens(&newLines, lineWidth) {
				changed = true
				continue
			}

			if brkI := line.chooseBreak(lineLen); brkI != -1 {
				line.breakAt(brkI, &newLines)
				changed = true
				continue
			}

			// Find the longest parens to break
			if longestI := line.longestParens(); longestI != -1 {
				line.breakParens(longestI, &newLines)
				changed = true
				continue
			}

			newLines = append(newLines, line)

		}

		lines = newLines
	}

	str := ""
	for _, line := range lines {
		str += strings.Repeat(" ", line.indent*4) + strings.Trim(streamToString(line.tokens), " ") + "\n"
	}
	return str
}

func (prop *Property) toSva(assume bool, clocking bool, lineWidth int) string {
	unsplittableStart := prop.name + ": "
	if assume {
		unsplittableStart += "assume"
	} else {
		unsplittableStart += "assert"
	}
	unsplittableStart += " property "

	inner := TokenStream{}
	if clocking {
		inner = append(inner, &NameToken{content: "@(posedge clk_i) disable iff (~rst_ni) "})
	}

	if prop.wait != 0 {
		inner = append(inner, &OperatorToken{
			operator: "##" + strconv.Itoa(prop.wait),
		})
		inner = append(inner, &WhiteSpaceToken{})
	}
	if len(prop.preConditions) > 0 {
		inner = append(inner, conjoin(prop.preConditions)...)
		inner = append(inner, &WhiteSpaceToken{})
		inner = append(inner, &OperatorToken{
			operator: prop.step,
		})
		inner = append(inner, &WhiteSpaceToken{})
	}
	inner = append(inner, prop.postCondition...)

	return formatStream(TokenStream{
		&NameToken{content: unsplittableStart},
		paren(inner),
		&OperatorToken{operator: ";"},
	}, lineWidth)
}

func (wire *Wiring) toSva(lineWidth int) string {
	unsplittableStart := "assign " + wire.name + " = "
	stream := TokenStream{}
	stream = append(stream, &NameToken{content: unsplittableStart})
	stream = append(stream, wire.value...)
	stream = append(stream, &OperatorToken{operator: ";"})
	return formatStream(stream, lineWidth)
}

func (seq *FlatProofSequence) toSva(slice int, clocking bool, lineWidth int) string {
	sva := ""

	for _, wire := range seq.wires {
		sva += wire.toSva(lineWidth) + "\n"
	}

	for i, step := range seq.props {
		if slice != -1 && i > slice {
			break
		}
		sva += "`ifndef REMOVE_SLICE_" + strconv.Itoa(i) + "\n"
		for _, prop := range step {
			sva += prop.toSva(slice != -1 && i != slice, clocking, lineWidth) + "\n"
		}
		sva += "`endif\n\n"
	}

	return sva
}

func (seq *FlatProofSequence) toTasks() string {
	cmds := ""

	for i := range seq.props {
		not_own_props := ""
		for j := i - 1; j >= 0; j-- {
			for _, prop := range seq.props[j] {
				not_own_props += " Step" + strconv.Itoa(i) + "::*." + prop.name
			}
		}

		prop_names := ""
		for j := i; j >= 0; j-- {
			for _, prop := range seq.props[j] {
				prop_names += " *." + prop.name
			}
		}

		cmds += "task -create Step" + strconv.Itoa(i) + " -copy_assumes -copy {" + prop_names[1:] + "}\n"
		if not_own_props != "" {
			cmds += "assume -from_assert {" + not_own_props[1:] + "}\n"
		}
	}

	return cmds
}

func (seq *FlatProofSequence) toProofStructure() string {
	patterns := ""

	for _, step := range seq.props {
		prop_names := ""
		for _, prop := range step {
			prop_names += " *." + prop.name
		}
		patterns += " {" + strings.Trim(prop_names, " ") + "}"
	}

	return "proof_structure -init root -copy_asserts -copy_assumes\n" +
		"proof_structure -create assume_guarantee" +
		" -from root" +
		" -property [list" + patterns + "]\n"
}
