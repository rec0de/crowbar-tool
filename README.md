# Crowbar 

**Crowbar** is a symbolic execution engine for [**ABS**](https://abs-models.org), based on [**BPL**](https://doi.org/10.1007/978-3-030-29026-9_22).
Crowbar aims to provide a possibility to prototype novel deductive verification techniques for 
functional correctness of Active Objects. Contrary to [**KeY**](https://www.key-project.org/) and [**KeY-ABS**](https://abs-models.org/tutorial_pdfs/KeY-ABS.pdf), **Crowbar** is not interactive 
and does not include a reasoning system.
Instead, symbolic execution generates a set of first-order formulas that are passed to a backend solver, right now [**Z3**](https://github.com/Z3Prover/z3). 

### Example

Install crowbar and generate an executable jar with `./gradlew shadowJar`, save the following ABS code and call `java -jar crowbar-0.1-pre-SNAPSHOT-all.jar <file> "Test.C.m"`
```
module Test;

data Spec = ObjInv(Bool) | Ensures(Bool);

[Spec : ObjInv(this.f >= 0)]
class C {
    Int f = 0;

    [Spec : Ensures(result >= 0)]
    Int m(Int v){
        Int w = v;
        if(w >= 0) this.f = w;
        else       this.f = -w;
        return v*w;
    }
}

{}
```

### For v0.1
For v0.1, we aim for a variant that can deal with programs containing only `ABS.StdLib.Int` 
and `ABS.StdLib.Fut<ABS.StdLib.Int>`-types, uses expressions as invariants and post-conditions, and has the following features

* Move global part (classReqs and allowedTypes) to a specification repository update
* Fixing the small todos in the code, catching up with the tests 
* Options to deal with type-checking and flattening of the model in main before executing symbolic execution
 
### Beyond v0.1
The following features are planned as further steps (unordered)
* ADT support
* ProgramElements (and PIT rules etc.) for `assert` and calls
* Taclet DSL
* Counter-model feedback from Z3
* First-order specification
* BPL leading composition
* Other SMT-solvers as backends: CVC4, Vampire, SMT-RAT(for HABS), AProVe...
* KeY-ABS as another backend
* All the other BPL org.abs_models.crowbar.types
* Connection to the dynamic analyses
* Frames
* Basic inference for effect org.abs_models.crowbar.types etc.
* Encoding the [**KeYmaera**](https://github.com/LS-Lab/KeYmaeraX-release) X bridge in a BPL type

### Misc.
Note that Z3 is written in C++ with Java-bindings that do not have a gradle dependency, so instead one must use the cli for that
