package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.crowbar.data.exprToForm
import org.abs_models.frontend.ast.ASTNode
import org.abs_models.frontend.ast.DataConstructorExp
import org.abs_models.frontend.ast.Exp

fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String) : Formula {
    val annotation = decl.nodeAnnotations.firstOrNull { it.type.toString().endsWith(".Spec") }
    if(annotation == null) {
        throw Exception("Could not extract any specification from $decl")
    }
    if(annotation.value !is DataConstructorExp) {
        throw Exception("Could not extract any specification from $decl because of the expected value")
    }
    val annotated = annotation.value as DataConstructorExp
    if(annotated.constructor != expectedSpec) throw Exception("Could not extract $expectedSpec specification from ${annotated.constructor}")
    return exprToForm(translateABSExpToSymExpr(annotated.getParam(0) as Exp))
}