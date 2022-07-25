# MUNTA -- Fully Verified Model Checker for Timed Automata

## Introduction
MUNTA is
- a model checker for the popular realtime systems modeling formalism of Timed Automata
- formally verified with Isabelle/HOL: there is a machine-checked proof that it only computes correct results!

MUNTA is at an early stage of development. Nevertheless, you can:
- run the model checker on a number of benchmarks
- browse the Isabelle/HOL proof
- try its graphical user interface [here](https://wimmers.github.io/munta-frontend/)

## Graphical User Interface
MUNTA now features a graphical user interface:
- [try it](https://wimmers.github.io/munta-frontend/)
- [source code](https://github.com/wimmers/munta-frontend)
- [instructions on how to run the verification server](#verification-server)

## Building

The following instructions should work on all Unix systems.

#### To build the checker:
Install the [MLton compiler](http://mlton.org/). Then run:
```
cd ML
make
```

#### To browse the sources interactively in Isabelle:
Install [Isabelle](https://isabelle.in.tum.de/) and the [AFP](https://www.isa-afp.org/using.shtml). Then run:
```
isabelle jedit -l Refine_Imperative_HOL
```
and open one of the `.thy` files.
A good starting point is the file where the model checker is exported to executable code:
`Simple_Networks/Simple_Network_Language_Export_Code.thy`.


#### To build the Isabelle sources and extract the checker source code:
Install [Isabelle](https://isabelle.in.tum.de/) and the [AFP](https://www.isa-afp.org/using.shtml). Then run:
```
isabelle build -d . TA_Code
```
and build the checker as described above.

## Verification Server
After building, you can run the verification server via:
```
cd ML
python2 server.py
```
The server will run under port 3069 and communicates with the GUI.

## Running
Pick one of the `.muntax` files from `benchmarks` and run:
```
ML/munta -m benchmarks/<the_benchmark>.muntax
```
To list MUNTA's command line options, run:
```
ML/munta -h
```

## OCaml

The [JANI](https://jani-spec.org/) interface is exposed as an OCaml module.
The corresponding [dune](https://dune.build/) and [opam](https://opam.ocaml.org/) setup is located in subfolder `OCaml`.

To install this package for use from your OCaml projects, make sure you have opam installed, and run:

```sh
cd OCaml
opam install .
```

If the exported OCaml code changes, you can run `opam upgrade munta` from anywhere to recompile and update.

It is recommended to interact with the module `Munta.MC`.

## Documentation

### Input Format
MUNTA accepts a simple modeling language, which is formally described in the file
`Simple_Networks/Simple_Network_Language.thy`.
Input models and formulas are specified in the JSON format (MUNTA's file ending: `.muntax`).
Examples can be found in the folder `benchmarks`.

## Benchmarks
The benchmarks are derived from the [UPPAAL](https://www.it.uu.se/research/group/darts/uppaal/benchmarks/) and
[TChecker](http://www.labri.fr/perso/herbrete/tchecker/) benchmarks.



## Outdated
The following instructions are outdated and in the progress of being updated:

### Input Format
MUNTA is aimed at understanding bytecode produced by [UPPAAL](http://uppaal.org/).
However, for the time being, this bytecode needs to be pre-processed slightly.
You can find some pre-processed benchmarks in `benchmarks`.
The input format is documented in `UPPAAL_Asm.thy` and `ML/Checker.sml`.

#### To build the checker with OCaml:
Replace `Big_int` with `Big_int_Z` in `UPPAAL_Model_Checker.ml` and `to_int` with `int_of_big_int`.
Then run
```
cd ML
ocamlfind ocamlopt -package zarith -package angstrom -linkpkg nums.cmxa -linkpkg UPPAAL_Model_Checker.ml -linkpkg Checker.ml
```

### Isabelle Formalizations
Human readable `.pdf` documents (with textual annotations) of the formalizations can be produced by Isabelle.
Run
```
isabelle build -d . TA
isabelle build -d . TA_All
```
and you will get the following:
- `output/abstract_reachability.pdf`: the abstract formalization of reachability checking for Timed Automata
- `output/model_checking.pdf`: the formalization of MUNTA and the route from the abstract formalization to the correctness proof for MUNTA
- `output/abstract_reachability_proofs.pdf`, `output/model_checking_proofs.pdf`: variants of the above documents with proofs