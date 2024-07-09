package main

import (
	"flag"
	"fmt"
	"os"
	"strings"
)

var paths []string
var rootLemma string
var svOut string
var tclOut string
var slice int
var task bool

func main() {
	paths = []string{}
	flag.Func("path", "paths to source files", func(s string) error {
		paths = append(paths, s)
		return nil
	})
	flag.StringVar(&rootLemma, "root", "", "name of root lemma")
	flag.IntVar(&slice, "slice", -1, "select a slice to assert, those leading up to it will be assumed and those after ignored")
	flag.StringVar(&svOut, "sv-out", "out.sv", "path to write generated SystemVerilog to")
	flag.StringVar(&tclOut, "tcl-out", "", "path to write generated TCL to, or empty to ignore")
	flag.BoolVar(&task, "task", false, "instead of using proof_structure, generate a set of TCL tasks of assumptions and assertions")
	flag.Parse()

	if len(paths) == 0 {
		fmt.Println(fmt.Errorf("error: must specify at least one path"))
		return
	}

	if rootLemma == "" {
		fmt.Println(fmt.Errorf("error: must specify a root lemma"))
		return
	}

	scope := Scope{
		lemmas: map[string]Lemma{},
		stack:  make([]*LocalScope, 0),
		defs:   map[string]SequencedProofSteps{},
	}

	for _, path := range paths {
		data, err := os.ReadFile(path)
		if err != nil {
			fmt.Println(err)
			return
		}

		str := strings.Split(string(data), "\n")
		_, blocks := parseBlocks(str, -1)
		structure := blocksToProofDocument(blocks)

		for k, v := range structure.lemmas {
			scope.lemmas[k] = v
		}
		for k, v := range structure.defs {
			scope.defs[k] = v
		}
	}

	lemma, ok := scope.lemmas[rootLemma]
	if !ok {
		panic(fmt.Errorf("root lemma %s does not exist", rootLemma))
	}
	prop := lemma.genProperty(&scope)
	seq := FlatProofSequence{
		wires: []Wiring{},
		props: make([][]*Property, 0),
	}
	prop.flatten(&seq, 0)
	seq.checkNames()

	sva := seq.toSva(slice, 100)
	os.WriteFile(svOut, []byte(sva), 0664)

	if tclOut != "" {
		var tcl string
		if task {
			tcl = seq.toTasks()
		} else {
			tcl = seq.toProofStructure()
		}
		os.WriteFile(tclOut, []byte(tcl), 0664)
	}
}
