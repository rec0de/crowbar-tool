package org.abs_models.crowbar.data

//General Elements
interface Anything /*: Cloneable*/ {
   /* public override fun clone(): Any {
        println("arrived at anything")
        return super.clone()
    }*/
    fun prettyPrint() : String { return toString() }
}
interface AbstractVar
data class AnyAbstractVar(val name : String) : Anything, AbstractVar

data class Modality(val remainder: Stmt, val target: DeductType) : Anything {
    override fun prettyPrint() : String{ return "["+remainder.prettyPrint()+" || "+target.prettyPrint()+"]"}
}
data class SymbolicState(val condition: Formula, val update: UpdateElement, val modality: Modality) : Anything {
    override fun prettyPrint() : String{ return condition.prettyPrint()+" ==> {"+update.prettyPrint()+"}"+modality.prettyPrint()}
}
