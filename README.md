# Crowbar 

**Crowbar** is a symbolic execution engine for [**ABS**](https://abs-models.org), based on [**BPL**](https://doi.org/10.1007/978-3-030-29026-9_22).
Crowbar aims to provide a possibility to prototype novel deductive verification techniques for 
functional correctness of Active Objects. Contrary to [**KeY**](https://www.key-project.org/), which it aims to complement for ABS, and full interactive provers, **Crowbar** does not include a reasoning system.
Instead, symbolic execution generates a set of first-order formulas that are passed to a backend solver in the [**SMT-LIB**](http://smtlib.cs.uiowa.edu) format
(Test are checking with [**Z3**](https://github.com/Z3Prover/z3) and [**CVC4**](https://cvc4.github.io/)).


### Example

Install crowbar and generate an executable jar with `./gradlew shadowJar`, save the following ABS code and call `java -jar crowbar-0.1-pre-SNAPSHOT-all.jar <file> --class=Test.C`
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

### Plans
**Crowbar** is a very early stage of development.

The following features are planned as further steps (unordered)
* ADT support
* ProgramElements (and PIT rules etc.) for `assert` and calls
* Taclet DSL
* Counter-model feedback from the backends
* First-order specification
* BPL leading composition
* Other solvers as backends: KeY, Vampire, SMT-RAT(for HABS), AProVe...
* All the other BPL-types
* Connection to the dynamic analyses
* Frames
* Verification and specification of SPLs without flattening
* Basic inference for effect-types etc.
* Encoding the [**KeYmaera X**](https://github.com/LS-Lab/KeYmaeraX-release) bridge in a BPL type

### Misc.
Please make sure that some SMT solver is installed and callable via command line. 
Right now, Crowbar does not support to pass a product to the ABS compiler.