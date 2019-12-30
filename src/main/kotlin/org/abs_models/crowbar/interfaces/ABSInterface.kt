package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.ast.AssignStmt
import org.abs_models.frontend.ast.AwaitStmt
import org.abs_models.frontend.ast.IfStmt
import org.abs_models.frontend.ast.ReturnStmt
import org.abs_models.frontend.ast.Stmt
import org.abs_models.frontend.ast.WhileStmt

fun translateABSExpToSymExpr(input : Exp) : Expr {
    when(input){
        is FieldUse        -> return Field(input.name)
        is VarUse          ->  {
            if (input.name == "result")
                return ReturnVar
            return ProgVar(input.name)
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
        is NewExp          -> return FreshGenerator.getFreshObjectId(input.className, input.paramList.map { translateABSExpToSymExpr(it) })
        is NullExp         -> return org.abs_models.crowbar.data.Const("0")
        else -> throw Exception("Translation of ${input::class} not supported" )
    }
}

fun translateABSStmtToSymStmt(input: Stmt) : org.abs_models.crowbar.data.Stmt {
    when(input){
        is ExpressionStmt ->{
            if (input.exp is GetExp){
                return org.abs_models.crowbar.data.AssignStmt(FreshGenerator.getFreshProgVar(), translateABSExpToSymExpr(input.exp))
            }
            if (input.exp is NewExp){
                return AllocateStmt(FreshGenerator.getFreshProgVar(), translateABSExpToSymExpr(input.exp))
            }
            throw Exception("Translation of ${input.exp::class} in an expression statement is not supported" )
        }
        is Block -> {
            val subs = input.stmts.map {translateABSStmtToSymStmt(it)  }
            val last = subs.last()
            val tail = subs.dropLast(1)
            return tail.foldRight( last , {nx, acc -> SeqStmt(nx, acc) })
        }
        is VarDeclStmt -> {
            if(input.varDecl.initExp is NewExp) return AllocateStmt(ProgVar(input.varDecl.name),translateABSExpToSymExpr(input.varDecl.initExp))
            return org.abs_models.crowbar.data.AssignStmt(ProgVar(input.varDecl.name), translateABSExpToSymExpr(input.varDecl.initExp))
        }
        is AssignStmt -> {
            val loc:Location = if(input.varNoTransform is FieldUse) Field(input.varNoTransform.name) else ProgVar(input.varNoTransform.name)
            if(input.varNoTransform is NewExp) return AllocateStmt(loc,translateABSExpToSymExpr(input.valueNoTransform))
            return org.abs_models.crowbar.data.AssignStmt(loc, translateABSExpToSymExpr(input.valueNoTransform))
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