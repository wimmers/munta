# MUNTA -- Fully Verified Model Checker for Timed Automata

## Introduction
MUNTA is
- a model checker for the popular realtime systems modeling formalism of Timed Automata
- formally verified with Isabelle/HOL -- there is a machine-checked proof that it only computes correct results!

MUNTA is at an early development state. Nevertheless, you can:
- run the model checker on a number of benchmarks
- browse the Isabelle/HOL proof


## Building

The following instructions should work on all Unix systems.

#### To build the checker:
Install the [MLton compiler](http://mlton.org/) . Then run:
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

#### To build the Isabelle sources and extract the checker source code:
Install [Isabelle](https://isabelle.in.tum.de/) and the [AFP](https://www.isa-afp.org/using.shtml). Then run:
```
isabelle build -d . TA_Code
```
and build the checker as described above.

## Running
Pick one of the files from `benchmarks` and run:
```
ML/munta < benchmarks/<the_benchmark>.munta
```

## Input Format
MUNTA is aimed at understanding bytecode produced by [UPPAAL](http://http://uppaal.org/).
However, for the time being, this bytecode needs to be pre-processed slightly.
You can find some pre-processed benchmarks in `benchmarks`.
The input format is documented in `UPPAAL_Asm.thy` and `ML/Checker.sml`.

## Benchmarks
The benchmarks are derived from the [UPPAAL](https://www.it.uu.se/research/group/darts/uppaal/benchmarks/) and
[TChecker](http://www.labri.fr/perso/herbrete/tchecker/) benchmarks.