package org.abs_models.crowbar.data


interface ProgramElement: Anything
data class ProgramElementAbstractVar(val name : String) : ProgramElement, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
}


interface PP: ProgramElement
data class PPId(val id: Int): PP, ProgramElement {
    override fun prettyPrint(): String {
        return "pp:$id"
    }
}

data class PPAbstractVar(val name : String) : PP, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
}

interface Stmt: ProgramElement {
    fun hasReturn(): Boolean = false
}

data class StmtAbstractVar(val name : String) : Stmt, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
}

data class AssignStmt(val lhs : Location, val rhs : Expr) : Stmt {
    override fun prettyPrint(): String {
        return lhs.prettyPrint()+" = "+rhs.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}

data class AllocateStmt(val lhs : Location, val rhs : Expr) : Stmt {
    override fun prettyPrint(): String {
        return lhs.prettyPrint()+" = new "+rhs.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}

data class SyncStmt(val lhs : Location, val rhs : Expr) : Stmt {
    override fun prettyPrint(): String {
        return lhs.prettyPrint()+" =  "+rhs.prettyPrint()+".get"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}

object SkipStmt : Stmt {
    override fun prettyPrint(): String {
        return "skip"
    }
}

object ScopeMarker : Stmt {
    override fun prettyPrint() = ""
}

data class SeqStmt(val first : Stmt, val second : Stmt) : Stmt {
    override fun prettyPrint(): String {
        return first.prettyPrint()+";"+second.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + first.iterate(f) + second.iterate(f)
    override fun hasReturn(): Boolean = first.hasReturn() || second.hasReturn()
}

data class ReturnStmt(val resExpr : Expr) : Stmt {
    override fun prettyPrint(): String {
        return "return "+resExpr.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + resExpr.iterate(f)
    override fun hasReturn(): Boolean = true
}

data class IfStmt(val guard : Expr, val thenStmt : Stmt, val elseStmt : Stmt) : Stmt {
    override fun prettyPrint(): String {
        return "if( ${guard.prettyPrint()} ){ ${thenStmt.prettyPrint()} } else { ${elseStmt.prettyPrint()} }"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =
        super.iterate(f) + guard.iterate(f) + thenStmt.iterate(f) + elseStmt.iterate(f)
    override fun hasReturn(): Boolean = thenStmt.hasReturn() || elseStmt.hasReturn()
}

data class WhileStmt(val guard : Expr, val bodyStmt : Stmt, val id : PP, val invar : Formula = True) : Stmt {
    override fun prettyPrint(): String {
        return "while{${id.prettyPrint()}}( ${guard.prettyPrint()} ){ ${bodyStmt.prettyPrint()} }"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =
        super.iterate(f) + guard.iterate(f) + bodyStmt.iterate(f) + id.iterate(f) + invar.iterate(f)
    override fun hasReturn(): Boolean = bodyStmt.hasReturn()
}

data class AwaitStmt(val resExpr : Expr, val id : PP) : Stmt {
    override fun prettyPrint(): String {
        return "await{${id.prettyPrint()}} "+resExpr.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + resExpr.iterate(f) + id.iterate(f)
}

data class CallStmt(val lhs : Location, val target : Expr, val resExpr : CallingExpr) : Stmt {
    override fun prettyPrint(): String {
        return "${lhs.prettyPrint()} = ${target.prettyPrint()}!${resExpr.prettyPrint()}"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + target.iterate(f) + resExpr.iterate(f)
}


interface Expr : ProgramElement {
    var absExp: org.abs_models.frontend.ast.Exp?
}


data class ExprAbstractVar(val name : String) : Expr, AbstractVar {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}

interface CallingExpr : Expr
data class CallExprAbstractVar(val name : String) : CallingExpr, AbstractVar {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}

data class CallExpr(val met : String, val e : List<Expr>) : CallingExpr{
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return met+"("+e.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = e.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})
}

data class PollExpr(val e1 : Expr) : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return e1.prettyPrint()+"?"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + e1.iterate(f)
}

data class SExpr(val op : String, val e : List<Expr>) : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        if(e.isEmpty()) return op
        return op+"("+e.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
    }    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = e.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})

}

data class Const(val name : String)  : Expr {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}

interface Location : Expr
data class LocationAbstractVar(val name : String) : Location, AbstractVar{
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return name
    }
}
//name must end with _f when using automatic translation
open class Field(val name : String, val dType : String = "Int") : Location, Term {
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return "this.$name : $dType"
    }
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as Field

        if (name != other.name) return false

        return true
    }

    override fun hashCode(): Int {
        return name.hashCode()
    }
    override fun toSMT(isInForm : Boolean) : String = name
}

open class ProgVar(val name : String, val dType : String = "Int") : Location, Term { //todo: change simpleName to qualifiedName and do something clever in the SMT-translation
    override var absExp: org.abs_models.frontend.ast.Exp? = null
    override fun prettyPrint(): String {
        return "$name:$dType"
    }

    //this ignores the type and that is ok for now
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as ProgVar

        if (name != other.name) return false

        return true
    }

    override fun hashCode(): Int {
        return name.hashCode()
    }
    override fun toSMT(isInForm : Boolean) : String = name
}
data class ReturnVar(val vParam : String) : ProgVar("result", vParam)

data class ProgAbstractVar(val vName : String) : ProgVar(vName, "AVAR"), AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
}
data class ProgFieldAbstractVar(val vName : String) : Field(vName, "AVAR"), AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
    override fun toSMT(isInForm : Boolean) : String = name
}

fun appendStmt(stmt : Stmt, add : Stmt) : Stmt {
    return when(stmt){
        is SeqStmt -> {
            val (first, next) = stmt
            SeqStmt(first,appendStmt(next,add))
        }
        else -> SeqStmt(stmt, add)
    }
}

fun unitExpr() : Expr = SExpr("Unit", emptyList())
