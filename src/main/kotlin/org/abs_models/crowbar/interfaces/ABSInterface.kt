package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.main.FunctionRepos
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.ast.AssignStmt
import org.abs_models.frontend.ast.AwaitStmt
import org.abs_models.frontend.ast.IfStmt
import org.abs_models.frontend.ast.ReturnStmt
import org.abs_models.frontend.ast.Stmt
import org.abs_models.frontend.ast.WhileStmt
import org.abs_models.frontend.typechecker.Type
import kotlin.system.exitProcess

fun translateABSExpToSymExpr(input : Exp) : Expr {
    when(input){
        is FieldUse        -> return Field(input.name+"_f",input.type.simpleName)
        is VarUse          ->  {
            if (input.name == "result")
                return ReturnVar(input.type.simpleName)
            return ProgVar(input.name, input.type.simpleName)
        }
        is IntLiteral           -> return Const(input.content)
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
        is NullExp              -> return Const("0")
        is ThisExp              -> return Const("1")
        is DataConstructorExp   ->
            return when(input.dataConstructor!!.name){
                "Unit"          -> unitExpr()
                "True"          -> Const("1")
                "False"         -> Const("0")
                else            -> throw Exception("Translation of data ${input::class} not supported, term is $input" )
            }
        is AsyncCall            -> return CallExpr(input.methodSig.contextDecl.qualifiedName+"."+input.methodSig.name,
                                              input.params.map {  translateABSExpToSymExpr(it) })
        is SyncCall             ->
            {
                if(input.callee  is ThisExp)
                    throw Exception("\"this\" not supported")
                return CallExpr(input.methodSig.contextDecl.qualifiedName+"."+input.methodSig.name,
                        input.params.map {  translateABSExpToSymExpr(it) })
                                              }
        is FnApp                -> if(input.name == "valueOf") return readFut(translateABSExpToSymExpr(input.params.getChild(0)))
                                   else if(FunctionRepos.isKnown(input.decl.qualifiedName)) {
                                        return SExpr(input.decl.qualifiedName.replace(".","-"),input.params.map { translateABSExpToSymExpr(it) })
                                    } else throw Exception("Translation of FnApp is not fully supported, term is $input with function ${input.name}" )
        is IfExp                -> return SExpr("iite", listOf(translateABSExpToSymExpr(input.condExp),translateABSExpToSymExpr(input.thenExp),translateABSExpToSymExpr(input.elseExp)))
        else                    -> throw Exception("Translation of ${input::class} not supported, term is $input" )
    }
}

fun translateABSStmtToSymStmt(input: Stmt?) : org.abs_models.crowbar.data.Stmt {
    if(input == null) return SkipStmt
    when(input){
        is org.abs_models.frontend.ast.SkipStmt -> return SkipStmt
        is ExpressionStmt ->{
            when(input.exp) {
                is GetExp       -> return SyncStmt(FreshGenerator.getFreshProgVar(input.type.simpleName), translateABSExpToSymExpr(input.exp))
                is NewExp       -> return AllocateStmt(FreshGenerator.getFreshProgVar(input.type.simpleName), translateABSExpToSymExpr(input.exp))
                is AsyncCall    -> { 
                    val v = input.exp as AsyncCall
                    return CallStmt(FreshGenerator.getFreshProgVar(input.type.simpleName), translateABSExpToSymExpr(v.callee), translateABSExpToSymExpr(v) as CallExpr)
                }
                is SyncCall     -> {
                    val syncCall = input.exp as SyncCall
                    val loc = FreshGenerator.getFreshProgVar(input.type.simpleName)
                    return desugaring(loc, input.type, syncCall)
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
            if(input.varDecl.initExp is GetExp) return SyncStmt(ProgVar(input.varDecl.name, input.varDecl.initExp.type.simpleName),translateABSExpToSymExpr(input.varDecl.initExp))
            if(input.varDecl.initExp is AsyncCall) {
                val v = input.varDecl.initExp as AsyncCall
                return CallStmt(ProgVar(input.varDecl.name, input.varDecl.initExp.type.simpleName), translateABSExpToSymExpr(v.callee), translateABSExpToSymExpr(v) as CallExpr)
            }
            if(input.varDecl.initExp is SyncCall) {
                val syncCall = input.varDecl.initExp as SyncCall
                val loc = ProgVar(input.varDecl.name, input.varDecl.type.simpleName)
                return desugaring(loc, input.type, syncCall)
            }
            return org.abs_models.crowbar.data.AssignStmt(ProgVar(input.varDecl.name,input.varDecl.type.simpleName), translateABSExpToSymExpr(input.varDecl.initExp))
        }
        is AssignStmt -> {
            val loc:Location = if(input.varNoTransform is FieldUse) Field(input.varNoTransform.name+"_f", input.varNoTransform.type.simpleName)
                               else ProgVar(input.varNoTransform.name, input.varNoTransform.type.simpleName)
            if(input.valueNoTransform is NewExp) return AllocateStmt(loc,translateABSExpToSymExpr(input.valueNoTransform))
            if(input.valueNoTransform is GetExp) return SyncStmt(loc,translateABSExpToSymExpr(input.valueNoTransform))
            if(input.valueNoTransform is AsyncCall) {
                val v = input.valueNoTransform as AsyncCall
                return CallStmt(loc, translateABSExpToSymExpr(v.callee), translateABSExpToSymExpr(v) as CallExpr)
            }
            if(input.valueNoTransform is SyncCall) {
                val syncCall = input.valueNoTransform as SyncCall
                return desugaring(loc, input.type, syncCall)
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

fun desugaring(loc: Location, type: Type, syncCall: SyncCall) : org.abs_models.crowbar.data.Stmt{
    val calleeExpr = translateABSExpToSymExpr(syncCall.callee)
    val syncCallExpr = translateABSExpToSymExpr(syncCall)

    if(syncCall.callee is ThisExp)
        return SyncCallStmt(loc, calleeExpr, syncCallExpr as SyncCallExpr)

    val fut = FreshGenerator.getFreshProgVar("Fut<"+type+">")
    val callStmt = CallStmt(fut, calleeExpr, syncCallExpr as CallExpr)
    val syncStmt = SyncStmt(loc, fut)
    return SeqStmt(callStmt, syncStmt)
}

fun translateABSGuardToSymExpr(input : Guard) : Expr{
    return when(input){
        is ExpGuard -> translateABSExpToSymExpr(input.pureExp)
        is ClaimGuard -> SExpr("=",listOf(Const("1"), Const("1")))//todo: proper translation
        is AndGuard -> SExpr("&&",listOf(translateABSGuardToSymExpr(input.left),translateABSGuardToSymExpr(input.right)))
        else -> throw Exception("Translation of ${input::class} not supported" )
    }
}


fun filterAtomic(input: Stmt?, app : (Stmt) -> Boolean) : Set<Stmt> {
    if(input == null) return emptySet()
    return when(input){
        is Block ->     input.stmts.fold(emptySet() , { acc, nx -> acc + filterAtomic(nx, app) })
        is WhileStmt -> filterAtomic(input.body, app)
        is IfStmt ->    filterAtomic(input.then, app) +filterAtomic(input.`else`, app)
        else -> if(app(input)) setOf(input) else emptySet()
    }
}


fun directSafe(exp: Exp, safeCalls: List<MethodSig>, safeSyncs: MutableList<VarOrFieldDecl>) : Boolean {
    when(exp) {
        is GetExp       -> return exp.pureExp is VarOrFieldUse && safeSyncs.contains((exp.pureExp as VarOrFieldUse).decl)
        is NewExp       -> return true
        is AsyncCall    -> {
            return safeCalls.contains(exp.methodSig)
        }
        else -> return true
    }
}

fun directSafeGuard(guard: Guard, safeSyncs: MutableList<VarOrFieldDecl>) : Boolean {

    when(guard) {
        is ClaimGuard -> {
            if(guard.`var` is VarOrFieldUse) return safeSyncs.contains((guard.`var` as VarOrFieldUse).decl)
            else return false
        }
        is AndGuard -> return directSafeGuard(guard.left,safeSyncs) && directSafeGuard(guard.right,safeSyncs)
        is DurationGuard -> return true
        else -> return false
    }
}

fun directlySafe(input: Stmt?, safeCalls: List<MethodSig>, safeSyncs: MutableList<VarOrFieldDecl>) : Boolean {
    if(input == null) return true
    when(input){
        is org.abs_models.frontend.ast.SkipStmt -> return true
        is ExpressionStmt -> return directSafe(input.exp, safeCalls, safeSyncs)
        is VarDeclStmt -> {
            val res = directSafe(input.varDecl.initExp, safeCalls, safeSyncs)
            if(res) safeSyncs.add(input.varDecl)
            return res
        }
        is AssignStmt -> {
            val res = directSafe(input.valueNoTransform, safeCalls, safeSyncs)
            safeSyncs.remove(input.varNoTransform.decl)
            if(res) safeSyncs.add(input.varNoTransform.decl)
            return res
        }
        is Block -> {
            for(stmt in input.stmts){
                val res = directlySafe(stmt, safeCalls, safeSyncs)
                if(!res) return false
            }
            return true
        }

        is WhileStmt -> {
            return directlySafe(input.body, safeCalls, safeSyncs)
        }
        is AwaitStmt -> {
            return directSafeGuard(input.guard, safeSyncs)
        }
        is ReturnStmt -> return directSafe(input.retExp, safeCalls, safeSyncs)
        is IfStmt -> {
            val left = mutableListOf<VarOrFieldDecl>()
            val right = mutableListOf<VarOrFieldDecl>()
            left.addAll(safeSyncs)
            right.addAll(safeSyncs)
            val res = directlySafe(input.then, safeCalls, left) && directlySafe(input.`else`, safeCalls, right)
            safeSyncs.removeAll { true }
            safeSyncs.addAll(left.intersect(right))
            return res
        }
        else -> throw Exception("Analysis of ${input::class} not supported" )
    }
}