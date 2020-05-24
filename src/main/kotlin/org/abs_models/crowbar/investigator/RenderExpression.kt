package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Expr
import org.abs_models.frontend.ast.AddAddExp
import org.abs_models.frontend.ast.AndBoolExp
import org.abs_models.frontend.ast.AsyncCall
import org.abs_models.frontend.ast.DataConstructorExp
import org.abs_models.frontend.ast.DivMultExp
import org.abs_models.frontend.ast.EqExp
import org.abs_models.frontend.ast.Exp
import org.abs_models.frontend.ast.FieldUse
import org.abs_models.frontend.ast.FnApp
import org.abs_models.frontend.ast.GetExp
import org.abs_models.frontend.ast.GTEQExp
import org.abs_models.frontend.ast.GTExp
import org.abs_models.frontend.ast.IfExp
import org.abs_models.frontend.ast.IntLiteral
import org.abs_models.frontend.ast.LTEQExp
import org.abs_models.frontend.ast.LTExp
import org.abs_models.frontend.ast.MinusExp
import org.abs_models.frontend.ast.MultMultExp
import org.abs_models.frontend.ast.NegExp
import org.abs_models.frontend.ast.NewExp
import org.abs_models.frontend.ast.NotEqExp
import org.abs_models.frontend.ast.NullExp
import org.abs_models.frontend.ast.OrBoolExp
import org.abs_models.frontend.ast.SubAddExp
import org.abs_models.frontend.ast.ThisExp
import org.abs_models.frontend.ast.VarUse

fun renderExpression(expression: Expr): String {
    if(expression.absExp == null)
        return expression.prettyPrint()
    else
        return renderAbsExpression(expression.absExp!!)
}

fun renderAbsExpression(e: Exp): String {
     return when(e){
        is ThisExp         -> "this"
        is NullExp         -> "null"
        is IntLiteral      -> e.content
        is FieldUse        -> "this.${e.name}"
        is VarUse          -> e.name
        is GTEQExp         -> "(${renderAbsExpression(e.left)} >= ${renderAbsExpression(e.right)})"
        is LTEQExp         -> "(${renderAbsExpression(e.left)} <= ${renderAbsExpression(e.right)})"
        is GTExp           -> "(${renderAbsExpression(e.left)} > ${renderAbsExpression(e.right)})"
        is LTExp           -> "(${renderAbsExpression(e.left)} < ${renderAbsExpression(e.right)})"
        is EqExp           -> "(${renderAbsExpression(e.left)} == ${renderAbsExpression(e.right)})"
        is NotEqExp        -> "(${renderAbsExpression(e.left)} != ${renderAbsExpression(e.right)})"
        is AddAddExp       -> "(${renderAbsExpression(e.left)} + ${renderAbsExpression(e.right)})"
        is SubAddExp       -> "(${renderAbsExpression(e.left)} - ${renderAbsExpression(e.right)})"
        is MultMultExp     -> "(${renderAbsExpression(e.left)} * ${renderAbsExpression(e.right)})"
        is DivMultExp      -> "(${renderAbsExpression(e.left)} / ${renderAbsExpression(e.right)})"
        is MinusExp        -> "-${renderAbsExpression(e.operand)}"
        is AndBoolExp      -> "(${renderAbsExpression(e.left)} && ${renderAbsExpression(e.right)})"
        is OrBoolExp       -> "(${renderAbsExpression(e.left)} || ${renderAbsExpression(e.right)})"
        is GetExp          -> "(${renderAbsExpression(e.pureExp)}).get"
        is NegExp          -> "!${renderAbsExpression(e.operand)}"
        is NewExp          -> "new ${e.className}(${e.paramList.map{ renderAbsExpression(it) }.joinToString(", ")})"
        is AsyncCall       -> "${e.methodSig.name}(${e.params.map{ renderAbsExpression(it) }.joinToString(", ")})"
        is IfExp           -> "(if ${renderAbsExpression(e.condExp)} then ${renderAbsExpression(e.thenExp)} else ${renderAbsExpression(e.elseExp)})"
        is FnApp           -> "${e.name}(${e.params.map{ renderAbsExpression(it) }.joinToString(", ")})"
        is DataConstructorExp -> e.dataConstructor!!.name
        else               -> throw Exception("Cannot render ABS Expression: $e")
    }
}