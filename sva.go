package main

import (
	"strconv"
	"strings"
)

func (prop *Property) toSva(id int, sliceid int, assume bool) (string, string) {
	sva := "(" + prop.revImplications[0] + ")"
	for _, s := range prop.revImplications[1:] {
		sva = "(" + s + ")" + " |-> " + sva
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
