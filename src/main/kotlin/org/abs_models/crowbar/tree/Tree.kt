package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Not
import org.abs_models.crowbar.data.SymbolicState
import org.abs_models.crowbar.interfaces.evaluateSMT

interface SymbolicTree{
    fun finishedExecution() : Boolean
    fun debugString(steps : Int) : String
    fun collectLeaves() : List<SymbolicLeaf>
}

interface SymbolicLeaf : SymbolicTree{
    fun evaluate() : Boolean
}

data class StaticNode(val str : String) : SymbolicLeaf{
    override fun finishedExecution() : Boolean = true
    override fun debugString(steps : Int) : String = "NOT IMPLEMENTED"
    override fun collectLeaves() : List<SymbolicLeaf> = listOf(this)
    override fun evaluate() : Boolean = false
}

data class LogicNode(val formula: Formula) : SymbolicLeaf{
    private var isEvaluated = false
    private var isValid = false
    override fun evaluate() : Boolean{
        if(isEvaluated) return isValid
        isValid = evaluateSMT(Not(formula))//\phi valid <-> !\phi unsat
        isEvaluated = true
        return isValid
    }

    override fun finishedExecution() : Boolean = true
    override fun debugString(steps : Int) : String = "\t".repeat(steps)+formula.prettyPrint()+"\n"
    override fun collectLeaves() : List<SymbolicLeaf> = listOf(this)
}
data class SymbolicNode(val content : SymbolicState, var children : List<SymbolicTree> = emptyList()) : SymbolicTree{
    override fun finishedExecution() : Boolean {
        return children.isNotEmpty() && children.fold(true, { acc, nx -> acc && nx.finishedExecution()})
    }

    override fun debugString(steps : Int) : String {
        var res = "\t".repeat(steps)+content.prettyPrint()+"\n"
        for(child in children){
            res += child.debugString(steps+1)
        }
        return res
    }

    override fun collectLeaves() : List<SymbolicLeaf> = children.fold(emptyList(), { acc, nx -> acc + nx.collectLeaves()})
}