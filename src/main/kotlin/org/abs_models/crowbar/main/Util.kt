package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.True
import org.abs_models.crowbar.data.exprToForm
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.frontend.ast.ASTNode
import org.abs_models.frontend.ast.DataConstructorExp
import org.abs_models.frontend.ast.Exp

fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String, default:Formula = True) : Formula {
    for(annotation in decl.nodeAnnotations){
        if(!annotation.type.toString().endsWith(".Spec")) continue
        if(annotation.value !is DataConstructorExp) {
            throw Exception("Could not extract any specification from $decl because of the expected value")
        }
        val annotated = annotation.value as DataConstructorExp
        if(annotated.constructor != expectedSpec) continue
        return exprToForm(translateABSExpToSymExpr(annotated.getParam(0) as Exp))
    }
    if(verbosity >= Verbosity.V)
        println("Crowbar-v: Could not extract $expectedSpec specification, using $default")
    return default
    //throw Exception("Could not extract any specification from $decl")
}