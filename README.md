This code contains Coq proofs supplementing the _Mechanizing the semantics of shared memory
in Intel CPU/FPGA systems_ bachelor thesis by Nikit Mittcev.
<!-- More on the artifact constructed from the code (including a VM image and installation guidelines) are stated in [ARTIFACT.md](ARTIFACT.md). -->

### Project dependencies
* [Coq 8.15.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`). This library provides useful definitions and proofs of various relations and sets properties, as well as a general trace definition used throughout the development.

## List of paper claims and definitions supported by the artifact
	
The overall structure of Coq development in `src` folder is as follows:	

- `basic` folder contains general definitions.
- `equivalence` folder contains definitions a proof of operational definitions being a subset of the declarative as well as a counterexample for the opposite direction.
- `lib` folder contains auxiliary proofs and definitions not directly related to memory models. 
### (§2) X+F Operational Semantics
- To formalize the LTS, the `HahnTrace.LTS` definition from the `hahn` library is used. 
- Both traces and runs of LTS are formalized as `HahnTrace.trace` which is a finite or infinite enumeration of labels of arbitrary type. Note that we often refer both to traces and runs as to "traces" in Coq development because of the implementation type. 
- As mentioned in the paper, we don't specify a program under consideration explicitly but rather assume that its behaviors are expressed using a set of possible traces of LTS. 
- We define operational behavior as sets of events corresponding to a run: see `src/equivalence/Equivalence.v`, variable `trace_events`.
 
### (§3) X+F Declarative Semantics	
- The definition of graph events is given in `src/basic/Events.v` (`Event` type). 
- The definition of a well-formed set of events is included in the graph well-formedness predicate (`Wf` in `src/basic/Execution.v`):	
  The `Wf` predicate also specifies well-formedness conditions for graph relations. 
- The execution graph definition is given in `src/basic/Execution.v` (`execution` type). Note that there are some differences in notation:
    - The set `E` of graph events is formalized as `acts` field of `execution`.
    - The program order (`G.po` in the paper) is formalized as `sb` ("sequenced-before") relation.
    - The modification order (`G.mo` in the paper) is formalized as `co` ("coherence order") field of `execution`.
	
### (§4) Declarative semantics to operational: a counterexample
The file `src/equivalence/Counterexample.v` contains a counterexample for the inclusion of declarative semantics into operational. 
It defines an execution and proves that it is X+F consistent.
There is currently no mechanization of the fact that it doesn't correspond to any operational behavior.

### Used axioms

Our development relies on non-constructive axioms. Namely, we use excluded middle, functional extensionality and functional/relational choice which [can be safely added to Coq logic](https://github.com/coq/coq/wiki/The-Logic-of-Coq#what-axioms-can-be-safely-added-to-coq). 

To list axioms used to prove a theorem `Thm` execute the file with `Thm` in any proof editor, then execute `Print Assumptions Thm`. 

During the proof compilation assumptions used to prove main statements are recorded in `axioms_*.out` files. Run `print_axioms.sh` script to view their content. This script filters out irrelevant output and only prints axioms.  


