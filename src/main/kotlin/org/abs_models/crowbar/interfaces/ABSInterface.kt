package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.SkipStmt
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
        is FieldUse        -> return Field(input.name,input.type.simpleName)
        is VarUse          ->  {
            if (input.name == "result")
                return ReturnVar(input.type.simpleName)
            return ProgVar(input.name, input.type.simpleName)
        }
        is IntLiteral           -> return org.abs_models.crowbar.data.Const(input.content)
        is GTEQExp              -> return SExpr(">=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is LTEQExp              -> return SExpr("<=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is GTExp                -> return SExpr(">", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is LTExp                -> return SExpr("<", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is EqExp                -> return SExpr("=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is NotEqExp             -> return SExpr("!=", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is AddAddExp            -> return SExpr("+", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is SubAddExp            -> return SExpr("-", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is MultMultExp          -> return SExpr("*", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is DivMultExp           -> return SExpr("/", listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is MinusExp             -> return SExpr("-", listOf(translateABSExpToSymExpr(input.operand)))
        is AndBoolExp           -> return SExpr("&&",listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is OrBoolExp            -> return SExpr("||",listOf(translateABSExpToSymExpr(input.left), translateABSExpToSymExpr(input.right)))
        is GetExp               -> return readFut(translateABSExpToSymExpr(input.pureExp))
        is NegExp               -> return SExpr("!", listOf(translateABSExpToSymExpr(input.operand)))
        is NewExp               -> return FreshGenerator.getFreshObjectId(input.className, input.paramList.map { translateABSExpToSymExpr(it) })
        is NullExp              -> return org.abs_models.crowbar.data.Const("0")
        is ThisExp              -> return org.abs_models.crowbar.data.Const("1")
        is DataConstructorExp   ->
            return when(input.dataConstructor!!.name){
                "Unit"          -> unitExpr()
                "True"          -> org.abs_models.crowbar.data.Const("1")
                "False"         -> org.abs_models.crowbar.data.Const("0")
                else            -> throw Exception("Translation of data ${input::class} not supported, term is $input" )
            }
        is AsyncCall            -> return CallExpr(input.methodSig.contextDecl.qualifiedName+"."+input.methodSig.name,
                                              input.params.map {  translateABSExpToSymExpr(it) })
        else                    -> throw Exception("Translation of ${input::class} not supported, term is $input" )
    }
}

fun translateABSStmtToSymStmt(input: Stmt?) : org.abs_models.crowbar.data.Stmt {
    if(input == null) return SkipStmt
    when(input){
        is org.abs_models.frontend.ast.SkipStmt -> return SkipStmt
        is ExpressionStmt ->{
            when(input.exp) {
                is GetExp       -> return org.abs_models.crowbar.data.AssignStmt(FreshGenerator.getFreshProgVar(input.type.simpleName), translateABSExpToSymExpr(input.exp))
                is NewExp       -> return AllocateStmt(FreshGenerator.getFreshProgVar(input.type.simpleName), translateABSExpToSymExpr(input.exp))
                is AsyncCall    -> { 
                    val v = input.exp as AsyncCall
                    return CallStmt(FreshGenerator.getFreshProgVar(input.type.simpleName), translateABSExpToSymExpr(v.callee), translateABSExpToSymExpr(v) as CallExpr)
                }
            }
            throw Exception("Translation of ${input.exp::class} in an expression statement is not supported" )
        }
        is Block -> {
            val subs = input.stmts.map {translateABSStmtToSymStmt(it)  }
            if(subs.isEmpty())  return SkipStmt
            val last = subs.last()
            val tail = subs.dropLast(1)
            return tail.foldRight( last , {nx, acc -> SeqStmt(nx, acc) })
        }
        is VarDeclStmt -> {
            if(input.varDecl.initExp is NewExp) return AllocateStmt(ProgVar(input.varDecl.name, input.varDecl.initExp.type.simpleName),translateABSExpToSymExpr(input.varDecl.initExp))
            if(input.varDecl.initExp is AsyncCall) {
                val v = input.varDecl.initExp as AsyncCall
                return CallStmt(ProgVar(input.varDecl.name, input.varDecl.initExp.type.simpleName), translateABSExpToSymExpr(v.callee), translateABSExpToSymExpr(v) as CallExpr)
            }
            return org.abs_models.crowbar.data.AssignStmt(ProgVar(input.varDecl.name,input.varDecl.type.simpleName), translateABSExpToSymExpr(input.varDecl.initExp))
        }
        is AssignStmt -> {
            val loc:Location = if(input.varNoTransform is FieldUse) Field(input.varNoTransform.name, input.type.simpleName)
                               else ProgVar(input.varNoTransform.name, input.varNoTransform.type.simpleName)
            if(input.valueNoTransform is NewExp) return AllocateStmt(loc,translateABSExpToSymExpr(input.valueNoTransform))
            if(input.valueNoTransform is AsyncCall) {
                val v = input.valueNoTransform as AsyncCall
                return CallStmt(loc, translateABSExpToSymExpr(v.callee), translateABSExpToSymExpr(v) as CallExpr)
            }
            return org.abs_models.crowbar.data.AssignStmt(loc, translateABSExpToSymExpr(input.valueNoTransform))
        }
        is WhileStmt -> {
            return org.abs_models.crowbar.data.WhileStmt(translateABSExpToSymExpr(input.conditionNoTransform),
                                                         translateABSStmtToSymStmt(input.bodyNoTransform),
                                                         FreshGenerator.getFreshPP(),
                                                         extractSpec(input,"WhileInv"))
        }
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