package org.abs_models.crowbar.rule

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.tree.SymbolicTree

//do not use variables starting with pv_ etc.
//todo: make some less intrusive restrictions
object FreshGenerator {
    private var count = 0
    fun getFreshProgVar() : ProgVar {
        return ProgVar("pv_" + (count++))
    }
    fun getFreshPP() : PP {
        return PPId(count++)
    }
    //todo: move this out
	fun getFreshObjectId(className: String, map: List<Expr>): Expr {
        if(map.isEmpty())
            return SExpr("NEW"+(count++), listOf(SExpr(className, emptyList()))+ listOf(Const("0")))
        return SExpr("NEW"+(count++), listOf(SExpr(className, emptyList()))+map)
	}
}

abstract class Rule(
        private val conclusion : Modality
){
    private var lastState : SymbolicState? = null
    private var cache : MatchCondition? = null

    fun isApplicable(input : SymbolicState) : Boolean {
        return !this.generateMatchCondition(input).failure
    }

    private fun generateMatchCondition(input : SymbolicState) : MatchCondition{
        if(lastState == input) return cache as MatchCondition
        val cond = MatchCondition()
        match(input.modality.remainder, conclusion.remainder, cond)
        match(input.modality.target, conclusion.target, cond)
        lastState = input
        cache = cond
        return cond
    }
    fun apply(input : SymbolicState) : List<SymbolicTree>?{
        val cond = generateMatchCondition(input)
        if(cond.failure) return null

        //todo: check here that the result contains no abstract variables anymore
        return transform(cond, input)
    }

    abstract fun transform(cond : MatchCondition, input: SymbolicState) : List<SymbolicTree>?
}

