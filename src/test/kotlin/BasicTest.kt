
import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.rule.*
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.PostInvariantPair
import org.abs_models.crowbar.types.nextPITStrategy

class BasicTest : StringSpec() {

    private val conc = org.abs_models.crowbar.data.AddExpr(org.abs_models.crowbar.data.ProgVar("v"), org.abs_models.crowbar.data.AddExpr(org.abs_models.crowbar.data.Const("1"), org.abs_models.crowbar.data.ProgVar("v")))
    private val pattern = org.abs_models.crowbar.data.AddExpr(org.abs_models.crowbar.data.ExprAbstractVar("A"), org.abs_models.crowbar.data.AddExpr(org.abs_models.crowbar.data.Const("1"), org.abs_models.crowbar.data.ExprAbstractVar("A")))
    private val pattern2 = org.abs_models.crowbar.data.AddExpr(org.abs_models.crowbar.data.ExprAbstractVar("A"), org.abs_models.crowbar.data.AddExpr(org.abs_models.crowbar.data.ExprAbstractVar("A"), org.abs_models.crowbar.data.Const("1")))
    private val pattern3 = org.abs_models.crowbar.data.AddExpr(org.abs_models.crowbar.data.ExprAbstractVar("A"), org.abs_models.crowbar.data.Const("1"))

    init {
        /*"matchAndApply" {
            val cond = MatchCondition()
            match(conc, pattern, cond)
            assert(!cond.failure)
            val res = org.abs_models.crowbar.data.apply(pattern3,cond) as Anything
            res shouldBe AddExpr(ProgVar("v"), Const("1"))
            assert(!containsAbstractVar(res))
        }*/
        "Z3Test"{
            val prog = org.abs_models.crowbar.data.SeqStmt(
                    org.abs_models.crowbar.data.IfStmt(org.abs_models.crowbar.data.SExpr(">=", listOf(org.abs_models.crowbar.data.ProgVar("v"), org.abs_models.crowbar.data.Const("0"))),
                            org.abs_models.crowbar.data.AssignStmt(org.abs_models.crowbar.data.Field("f"), org.abs_models.crowbar.data.ProgVar("v")),
                            org.abs_models.crowbar.data.AssignStmt(org.abs_models.crowbar.data.Field("f"), org.abs_models.crowbar.data.SExpr("-", listOf(org.abs_models.crowbar.data.ProgVar("v"))))
                    ),
                    org.abs_models.crowbar.data.ReturnStmt(org.abs_models.crowbar.data.Field("f"))
            )

            val input3 = org.abs_models.crowbar.data.SymbolicState(
                    org.abs_models.crowbar.data.True,
                    org.abs_models.crowbar.data.EmptyUpdate,
                    org.abs_models.crowbar.data.Modality(prog, PostInvariantPair(org.abs_models.crowbar.data.Predicate(">=", listOf(org.abs_models.crowbar.data.select(org.abs_models.crowbar.data.Field("f")), Function("0"))),
                            org.abs_models.crowbar.data.True))
            )

            val strategy = nextPITStrategy()
            val node = SymbolicNode(input3, emptyList())
            strategy.execute(node)
            println(node.debugString(0))
            println(node.finishedExecution())
            for(l in node.collectLeaves()){
                println(l.evaluate())
            }
        }
        "deupdatify" {/* { v := 0 }{ v := v+1 } ((v == { v := v+1 }(v+w)) /\ { v := v+1 }!(v == w))
                          ->
                         (0+1 == (0+1+1+w)) /\ !(0+1+1 == w) */
            val s = org.abs_models.crowbar.data.UpdateOnFormula(org.abs_models.crowbar.data.ChainUpdate(org.abs_models.crowbar.data.ElementaryUpdate(org.abs_models.crowbar.data.ProgVar("v"), Function("0")), org.abs_models.crowbar.data.ElementaryUpdate(org.abs_models.crowbar.data.ProgVar("v"), Function("+", listOf(org.abs_models.crowbar.data.ProgVar("v"), Function("1"))))),
                    org.abs_models.crowbar.data.And(org.abs_models.crowbar.data.Predicate("=", listOf(
                            org.abs_models.crowbar.data.ProgVar("v"),
                            org.abs_models.crowbar.data.UpdateOnTerm(org.abs_models.crowbar.data.ElementaryUpdate(org.abs_models.crowbar.data.ProgVar("v"), Function("+", listOf(org.abs_models.crowbar.data.ProgVar("v"), Function("1")))),
                                    Function("+", listOf(org.abs_models.crowbar.data.ProgVar("v"), org.abs_models.crowbar.data.ProgVar("w"))))
                    )), org.abs_models.crowbar.data.UpdateOnFormula(org.abs_models.crowbar.data.ElementaryUpdate(org.abs_models.crowbar.data.ProgVar("v"), Function("+", listOf(org.abs_models.crowbar.data.ProgVar("v"), Function("1")))),
                            org.abs_models.crowbar.data.Not(org.abs_models.crowbar.data.Predicate("=", listOf(org.abs_models.crowbar.data.ProgVar("v"), org.abs_models.crowbar.data.ProgVar("w")))))))

            deupdatify(s).prettyPrint() shouldBe "(0+1=0+1+1+w) /\\ (!0+1+1=w)"
        }
        "apply" {
            apply(ElementaryUpdate(ProgVar("v"), Function("0")),
                    Predicate("=", listOf(Function("+", listOf(ProgVar("v"), ProgVar("v"))), Function("0")))) shouldBe
                    org.abs_models.crowbar.data.Predicate("=", listOf(Function("+", listOf(Function("0"), Function("0"))), Function("0")))
        }
        "subst" {
            subst(ProgVar("v"), ProgVar("v"), Function("0")) shouldBe Function("0")
            subst(ProgVar("w"), ProgVar("v"), Function("0")) shouldBe org.abs_models.crowbar.data.ProgVar("w")
            subst(Predicate("=",
                    listOf(Function("+", listOf(ProgVar("v"), ProgVar("v"))),
                            Function("0"))), ProgVar("v"), Function("0")) shouldBe
                    org.abs_models.crowbar.data.Predicate("=",
                            listOf(Function("+", listOf(Function("0"), Function("0"))),
                                    Function("0")))

            subst(Predicate("=",
                    listOf(Function("+", listOf(UpdateOnTerm(ElementaryUpdate(ProgVar("v"), Function("1")), ProgVar("v")),
                            UpdateOnTerm(ElementaryUpdate(ProgVar("w"), Function("1")), ProgVar("v")))),
                            Function("0"))), ProgVar("v"), Function("0")) shouldBe
                    org.abs_models.crowbar.data.Predicate("=",
                            listOf(Function("+", listOf(org.abs_models.crowbar.data.UpdateOnTerm(org.abs_models.crowbar.data.ElementaryUpdate(org.abs_models.crowbar.data.ProgVar("v"), Function("1")), org.abs_models.crowbar.data.ProgVar("v")),
                                    org.abs_models.crowbar.data.UpdateOnTerm(org.abs_models.crowbar.data.ElementaryUpdate(org.abs_models.crowbar.data.ProgVar("w"), Function("1")), Function("0")))),
                                    Function("0")))

            subst(ElementaryUpdate(ProgVar("v"), Function("+", listOf(ProgVar("v"), Function("1")))),
                    ProgVar("v"),
                    Function("0")) shouldBe
                    org.abs_models.crowbar.data.ElementaryUpdate(org.abs_models.crowbar.data.ProgVar("v"), Function("+", listOf(Function("0"), Function("1"))))

        }
        "matchAndFail1" {
            val cond = MatchCondition()
            match(conc, pattern2, cond)
            assert(cond.failure)
            cond.failReason shouldBe "AbstractVar A failed unification with two terms: v and 1"
        }
        "matchAndFail2"{
            val cond = MatchCondition()
            match(pattern, conc, cond)
            assert(cond.failure)
            cond.failReason shouldBe "Concrete statement contains abstract variables: ${pattern.prettyPrint()}"
        }
        "matchAndFail3"{
            val cond = MatchCondition()
            match(org.abs_models.crowbar.data.Const("v"), org.abs_models.crowbar.data.StmtAbstractVar("A"), cond)
            assert(cond.failure)
            cond.failReason shouldBe "AbstractVar A failed unification because of a type error: v"
        }
        "containsAbstractVar"{
            assert(!containsAbstractVar(conc))
            assert(containsAbstractVar(pattern))
            assert(containsAbstractVar(pattern2))
            assert(containsAbstractVar(pattern3))
        }
    }

}