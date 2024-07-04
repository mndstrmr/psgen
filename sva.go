package main

import (
	"regexp"
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

func isParenthesised(str string) bool {
	if len(str) == 0 {
		return false
	}

	openParen := str[0]
	if openParen != '(' && openParen != '[' && openParen != '{' {
		return false
	}
	closeParen := str[len(str)-1]
	if (openParen == '(' && closeParen != ')') || (openParen == '[' && closeParen != ']') || (openParen == '{' && closeParen != '}') {
		return false
	}

	depth := 1
	for _, c := range str[1 : len(str)-1] {
		if c == '(' || c == '[' || c == '{' {
			depth += 1
		} else if c == ')' || c == ']' || c == '}' {
			depth -= 1
			if depth == 0 {
				return false
			}
		}
	}
	return true
}

func isUnary(str string) bool {
	str = strings.Trim(str, " ")
	re := regexp.MustCompile("^[$a-z`A-Z0-9_~.]+([([{]?)")
	groups := re.FindStringSubmatchIndex(str)
	if groups[1] == len(str) {
		return true
	}
	openParen := str[groups[1]-1]
	if openParen == '(' || openParen == '[' || openParen == '{' {
		return isParenthesised(str[groups[1]-1:])
	}
	return false
}

func conjoin(terms []string) string {
	re := regexp.MustCompile("^[a-z`A-Z0-9_& ~.]*$")
	new := ""
	for i, term := range terms {
		if i != 0 {
			new += " & "
		}
		if re.MatchString(term) || isUnary(term) {
			new += term
			continue
		}

		subterms := strings.Split(term, "&")
		allSubtermsUnary := true
		for _, term := range subterms {
			if !isUnary(term) {
				allSubtermsUnary = false
				break
			}
		}

		if allSubtermsUnary {
			new += term
		} else {
			new += "(" + term + ")"
		}
	}
	return new
}

func disjoin(terms []string) string {
	re := regexp.MustCompile("^[a-z`A-Z0-9_| ~.]*$")
	new := []string{}
	for _, term := range terms {
		if re.MatchString(term) {
			new = append(new, term)
		} else {
			new = append(new, "("+term+")")
		}
	}
	return strings.Join(new, " || ")
}

func negate(term string) string {
	re := regexp.MustCompile("^[a-z`A-Z0-9_.~]*$")
	if !re.MatchString(term) {
		return "~(" + term + ")"
	}
	if strings.HasPrefix(term, "~") {
		return term[1:]
	} else {
		return "~" + term
	}
}

func wrap(str string, lineWidth int) []string {
	lines := []string{}
	for len(str) > lineWidth {
		done := false
		for i := lineWidth; i >= 0; i-- {
			if str[i] == ' ' {
				lines = append(lines, str[:i])
				str = str[i+1:]
				done = true
				break
			}
		}

		if !done {
			for i := lineWidth + 1; i < len(str); i++ {
				if str[i] == ' ' {
					lines = append(lines, str[:i])
					str = str[i+1:]
					break
				}
			}
		}
	}
	if len(str) > 0 {
		lines = append(lines, str)
	}
	return lines
}

func (prop *Property) toSva(assume bool, lineWidth int) string {
	pre := ""
	arrow := ""
	post := prop.postCondition
	if len(prop.preConditions) > 0 {
		slices.Reverse(prop.preConditions)
		pre = conjoin(prop.preConditions)
		arrow = " " + prop.step + " "
	}

	assume_assert := "assert"
	if assume {
		assume_assert = "assume"
	}
	start := prop.name + ": " + assume_assert + " property ("
	end := ");"

	var str string
	if len(arrow) > 0 && len(pre)+len(arrow)+len(post) > lineWidth {
		str = start + "\n" + "    " + strings.Join(wrap(pre, lineWidth), "\n    ") + "\n    " + strings.Trim(arrow, " ") + "\n    " + strings.Join(wrap(post, lineWidth), "\n    ") + "\n" + end
	} else if len(str) > lineWidth {
		str = start + "\n" + "    " + strings.Join(wrap(pre+arrow+post, lineWidth), "\n    ") + "\n" + end
	} else {
		str = start + pre + arrow + post + end
	}

	return str
}

func (seq *FlatProofSequence) toTclSva(slice int, lineWidth int) (string, string) {
	sva := ""
	patterns := ""

	id := 0
	for i, step := range seq.props {
		if slice != -1 && i > slice {
			break
		}
		prop_names := ""
		sva += "`ifndef REMOVE_SLICE_" + strconv.Itoa(i) + "\n"
		for _, prop := range step {
			prop_sva := prop.toSva(slice != -1 && i != slice, lineWidth)
			id += 1
			prop_names += " *." + prop.name
			sva += prop_sva + "\n"
		}
		patterns += " {" + strings.Trim(prop_names, " ") + "}"
		sva += "`endif\n\n"
	}

	tcl := ""
	if slice != -1 {
		tcl =
			"proof_structure -create assume_guarantee" +
				" -from root" +
				" -property [list" + patterns + "]\n"
	}

	return tcl, sva
}
