# Crowbar 

**Crowbar** is a symbolic execution engine for [**ABS**](https://abs-models.org), based on [**BPL**](https://doi.org/10.1007/978-3-030-29026-9_22).
Crowbar aims to provide a possibility to prototype novel deductive verification techniques for 
functional correctness of Active Objects. Contrary to [**KeY**](https://www.key-project.org/), which it aims to complement for ABS, and full interactive provers, **Crowbar** does not include a reasoning system.
Instead, symbolic execution generates a set of first-order formulas that are passed to a backend solver in the [**SMT-LIB**](http://smtlib.cs.uiowa.edu) format
(Test are checking with [**Z3**](https://github.com/Z3Prover/z3) and [**CVC4**](https://cvc4.github.io/)).


**Crowbar** is at a very early development stage.

## Example

Clone the code, generate an executable jar with `./gradlew shadowJar`, save the following ABS code and call `java -jar crowbar-0.1-all.jar <file> --class=Test.C`
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

## Misc.
* Method preconditions are split into parameter preconditions in the interface and heap preconditions in the class.

  If you call a method asynchronously on this and you want to use parameter preconditions, it must be exposed.
  The [heap precondition propagation](https://doi.org/10.1007/978-3-030-30446-1_3) is not implemented, you have to ensure that yourself.
  
  Right now, the restrictions on pre- and postconditions in general are not checked
* Please make sure that some SMT solver is installed and callable via command line. The tests use the `z3` and `cvc` commands.
* Crowbar does not yet support any SPL option.
* Name clashes with internal expressions are not checked yet