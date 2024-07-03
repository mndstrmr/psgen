package main

import (
	"strconv"
	"strings"
)

func (prop *Property) toSva(id int) (string, string) {
	sva := prop.revImplications[0]
	for _, s := range prop.revImplications[1:] {
		sva = s + " |-> (" + sva + ")"
	}
	gen_name := "GenProp_" + strconv.Itoa(id)
	return gen_name, gen_name + ": assert property (" + sva + ");"
}

func (seq *FlatProofSequence) toTclSva() (string, string) {
	sva := ""
	patterns := ""

	id := 0
	for _, step := range seq.props {
		prop_names := ""
		for _, prop := range step {
			prop_name, prop_sva := prop.toSva(id)
			id += 1
			prop_names += " *." + prop_name
			sva += prop_sva + "\n"
		}
		patterns += " {" + strings.Trim(prop_names, " ") + "}"
		sva += "\n"
	}

	tcl :=
		"proof_structure -create assume_guarantee" +
			" -from root" +
			" -property [list" + patterns + "]\n"

	return tcl, sva
}
