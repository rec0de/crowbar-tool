package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.SExpr
import org.abs_models.crowbar.data.readFut
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.main.isAllowedType
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.ast.IfStmt

fun translateABSExpToSymExpr(input : Exp) : Expr {
    when(input){
        is FieldUse        -> return org.abs_models.crowbar.data.Field(input.name)
        is VarUse          ->  {
            if (input.name == "result")
                return org.abs_models.crowbar.data.ReturnVar
            return org.abs_models.crowbar.data.ProgVar(input.name)
        }
        is IntLiteral      -> return org.abs_models.crowbar.data.Const(input.content)
        is GTEQExp         -> return SExpr(">=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is LTEQExp         -> return SExpr("<=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is GTExp           -> return SExpr(">", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is LTExp           -> return SExpr("<", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is EqExp           -> return SExpr("=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is NotEqExp        -> return SExpr("!=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is AddAddExp       -> return SExpr("+", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is SubAddExp       -> return SExpr("-", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is MultMultExp     -> return SExpr("*", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is DivMultExp      -> return SExpr("/", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is MinusExp        -> return SExpr("-", listOf(translateABSExpToSymExpr(input.operand)))
        is AndBoolExp      -> return SExpr("&&",listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is GetExp          -> return readFut(translateABSExpToSymExpr(input.pureExp))
        else -> throw Exception("Translation of ${input::class} not supported" )
    }
}

fun translateABSStmtToSymStmt(input: Stmt) : org.abs_models.crowbar.data.Stmt {
    when(input){
        is ExpressionStmt ->{
            if (input.exp is GetExp){
                return org.abs_models.crowbar.data.AssignStmt(FreshGenerator.getFreshProgVar(), translateABSExpToSymExpr(input.exp))
            }else throw Exception("Translation of ${input.exp::class} in an expression statement is not supported" )
        }
        is Block -> {
            val subs = input.stmts.map {translateABSStmtToSymStmt(it)  }
            val last = subs.last()
            val tail = subs.dropLast(1)
            return tail.foldRight( last , {nx, acc -> org.abs_models.crowbar.data.SeqStmt(nx, acc) })
        }
        is VarDeclStmt -> {
            if(!isAllowedType(input.varDecl.type.toString())) throw Exception("Translation of ${input.varDecl.type} not supported" )
            return org.abs_models.crowbar.data.AssignStmt(org.abs_models.crowbar.data.ProgVar(input.varDecl.name), translateABSExpToSymExpr(input.varDecl.initExp))
        }
        is AssignStmt -> {
            if(input.varNoTransform is FieldUse)
                return org.abs_models.crowbar.data.AssignStmt(org.abs_models.crowbar.data.Field(input.varNoTransform.name), translateABSExpToSymExpr(input.valueNoTransform))
            return org.abs_models.crowbar.data.AssignStmt(org.abs_models.crowbar.data.ProgVar(input.varNoTransform.name), translateABSExpToSymExpr(input.valueNoTransform))
        }
        is WhileStmt -> {
            return org.abs_models.crowbar.data.WhileStmt(translateABSExpToSymExpr(input.conditionNoTransform),
                                                         translateABSStmtToSymStmt(input.bodyNoTransform),
                                                         FreshGenerator.getFreshPP(),
                                                         extractSpec(input,"WhileInv"))
        }
        //is Get
        is AwaitStmt -> return org.abs_models.crowbar.data.AwaitStmt(translateABSGuardToSymExpr(input.guard),FreshGenerator.getFreshPP())
        is ReturnStmt -> return org.abs_models.crowbar.data.ReturnStmt(translateABSExpToSymExpr(input.retExp))
        is IfStmt -> return org.abs_models.crowbar.data.IfStmt(translateABSExpToSymExpr(input.conditionNoTransform), translateABSStmtToSymStmt(input.then), translateABSStmtToSymStmt(input.`else`))
        else -> throw Exception("Translation of ${input::class} not supported" )
    }
}

fun translateABSGuardToSymExpr(input : Guard) : Expr{
    when(input){
        is ExpGuard -> return translateABSExpToSymExpr(input.pureExp)
        else -> throw Exception("Translation of ${input::class} not supported" )
    }
}