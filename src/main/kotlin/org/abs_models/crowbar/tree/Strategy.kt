package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.DeductType
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.types.*
import kotlin.reflect.KClass

interface Strategy{
    fun execute(symbolicNode: SymbolicNode)
}


class DefaultStrategy(private val rules : List<Rule>, private val repos : Repository) : Strategy{

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

fun getStrategy(clazz: KClass<out DeductType>, repos: Repository) : Strategy{
    return when(clazz){
        PostInvType::class -> nextPITStrategy(repos)
        RegAccType::class  -> nextRAStrategy(repos)
        else               -> throw Exception("unsupported type $clazz")
    }
}


fun nextRAStrategy(repos: Repository) : Strategy = DefaultStrategy(listOf(RAReturn, RAFieldAssign, RAVarAssign, RASkip, RASkipSkip),repos)
fun nextPITStrategy(repos: Repository) : Strategy = DefaultStrategy(listOf(PITSyncAssign(repos),PITVarAssign(repos), PITFieldAssign(repos), PITAllocAssign(repos), PITCallAssign(repos), PITReturn, PITSkip, PITIf, PITAwait, PITSkipSkip, PITWhile), repos)