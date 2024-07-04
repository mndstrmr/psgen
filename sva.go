package main

import (
	"regexp"
	"slices"
	"strconv"
	"strings"
)

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
	new := []string{}
	for _, term := range terms {
		if re.MatchString(term) || isUnary(term) {
			new = append(new, term)
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
			new = append(new, term)
		} else {
			new = append(new, "("+term+")")
		}
	}
	return strings.Join(new, " && ")
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

func (prop *Property) toSva(id int, sliceid int, assume bool) (string, string) {
	sva := ""
	if len(prop.preConditions) > 0 {
		slices.Reverse(prop.preConditions)
		sva = conjoin(prop.preConditions) + " |-> " + prop.postCondition
	} else {
		sva = prop.postCondition
	}

	prefix := "GenProp"
	if prop.name != "" {
		prefix = prop.name
	}
	gen_name := prefix + "_" + strconv.Itoa(sliceid) + "_" + strconv.Itoa(id)

	assume_assert := "assert"
	if assume {
		assume_assert = "assume"
	}
	return gen_name, gen_name + ": " + assume_assert + " property (" + sva + ");"
}

func (seq *FlatProofSequence) toTclSva(slice int) (string, string) {
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
			prop_name, prop_sva := prop.toSva(id, i, slice != -1 && i != slice)
			id += 1
			prop_names += " *." + prop_name
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
