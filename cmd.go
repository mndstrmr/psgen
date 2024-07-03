package main

import (
	"flag"
	"fmt"
	"os"
	"strings"
)

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
	structure := blocksToProofDocument(blocks)

	tcl := "proof_structure -init root -copy_asserts -copy_assumes\n"
	sva := ""

	scope := Scope{
		stack: make([]*LocalScope, 0),
		defs:  structure.defs,
	}

	for _, lemma := range structure.lemmas {
		prop := lemma.genProperty(&scope)
		seq := FlatProofSequence{
			props: make([][]*Property, 0),
		}
		prop.flatten(&seq, 0)
		new_tcl, new_sva := seq.toTclSva()
		tcl += new_tcl
		sva += new_sva
	}

	os.WriteFile("out.tcl", []byte(tcl), 0664)
	os.WriteFile("out.sv", []byte(sva), 0664)
}
