# Crowbar 

**Crowbar** is a symbolic execution engine for [**ABS**](https://abs-models.org), based on [**BPL**](https://doi.org/10.1007/978-3-030-29026-9_22).
Crowbar aims to provide a possibility to prototype novel deductive verification techniques for 
functional correctness of Active Objects. Contrary to [**KeY**](https://www.key-project.org/), which it aims to complement for ABS, and full interactive provers, **Crowbar** does not include a reasoning system.
Instead, symbolic execution generates a set of first-order formulas that are passed to a backend solver in the [**SMT-LIB**](http://smtlib.cs.uiowa.edu) format
(Test are checking with [**Z3**](https://github.com/Z3Prover/z3) and [**CVC4**](https://cvc4.github.io/)).

## What's here?

This fork of crowbar contains the first implementation of the _crowbar investigator_, crowbar's counterexample generation component, initially developed for my bachelor's thesis on _counterexample generation for formal verification of ABS_.  
Development of both crowbar and the crowbar investigator has since continued in the main repo at [Edkamb/crowbar-tool](https://github.com/Edkamb/crowbar-tool).
