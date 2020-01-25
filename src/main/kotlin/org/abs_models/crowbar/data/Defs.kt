package org.abs_models.crowbar.data

import kotlin.reflect.KClass

//General Elements
interface Anything /*: Cloneable*/ {
   /* public override fun clone(): Any {
        return super.clone()
    }*/
    fun prettyPrint() : String { return toString() }
    fun iterate(f: (Anything) -> Boolean) : Set<Anything> = if(f(this)) setOf(this) else emptySet() // this is not implemented for DeductType
    fun<T : Any> collectAll(clazz : KClass<T>) : Set<Anything> = iterate { clazz.isInstance(it) }
}
interface AbstractVar
data class AnyAbstractVar(val name : String) : Anything, AbstractVar

data class Modality(var remainder: Stmt, val target: DeductType) : Anything {
    override fun prettyPrint() : String{ return "["+remainder.prettyPrint()+" || "+target.prettyPrint()+"]"}
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + remainder.iterate(f) + target.iterate(f)
}
data class SymbolicState(val condition: Formula, val update: UpdateElement, val modality: Modality) : Anything {
    override fun prettyPrint() : String{ return condition.prettyPrint()+" ==> {"+update.prettyPrint()+"}"+modality.prettyPrint()}
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + condition.iterate(f) + update.iterate(f) + modality.iterate(f)
}

