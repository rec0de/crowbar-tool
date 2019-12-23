package org.abs_models.crowbar.tree

import org.abs_models.crowbar.rule.Rule

interface Strategy{
    fun execute(symbolicNode: SymbolicNode)
}


class DefaultStrategy(private val rules : List<Rule>) : Strategy{

    override fun execute(symbolicNode: SymbolicNode){
        symbolicNode.children = emptyList()
        for(rule in rules){
            if(rule.isApplicable(symbolicNode.content)){
                val next = rule.apply(symbolicNode.content)
                if(next != null) {
                    symbolicNode.children = next
                    for (node in next) {
                        if(node is SymbolicNode)
                             this.execute(node)
                    }
                }
                break
            }
        }
    }
}