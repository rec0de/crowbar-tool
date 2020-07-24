package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.PollExpr
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.SExpr
import org.abs_models.crowbar.data.Term

fun collectUsedDefinitions(elem: Term): Set<String> {
    return when (elem) {
        is Function -> collectFromFunction(elem)
        is ProgVar -> setOf(elem.name)
        is Field -> setOf(elem.name)
        else -> throw Exception("Cannot collect used definitions from term: ${elem.prettyPrint()}")
    }
}

fun collectFromFunction(func: Function): Set<String> {
    val paramDefs = func.params.map { collectUsedDefinitions(it) }.flatten().toSet()
    return if (func.name.startsWith("f_")) paramDefs + func.name else paramDefs
}

fun collectBaseExpressions(exp: Expr): Set<Expr> {
    return when (exp) {
        is ProgVar -> setOf(exp)
        is Field -> setOf(exp)
        is PollExpr -> collectBaseExpressions(exp.e1)
        is Const -> setOf()
        is SExpr -> exp.e.map { collectBaseExpressions(it) }.flatten().toSet()
        else -> throw Exception("Cannot collect base expressions from unknown expression: ${exp.prettyPrint()}")
    }
}
