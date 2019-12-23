package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.rule.*
import org.abs_models.crowbar.tree.*

//todo: right now this does *NOT* distinguish between a get and a normal assignment

//Declaration
interface PostInvType : DeductType
data class PostInvAbstractVar(val name : String) : PostInvType, AbstractVar{
    override fun prettyPrint(): String {
        return name
    }
}
data class PostInvariantPair(val post : Formula, val objInvariant : Formula) : PostInvType {
    override fun prettyPrint(): String {
        return post.prettyPrint()+", "+objInvariant.prettyPrint()
    }
}

//Type system
object PITVarAssign : Rule(Modality(
        SeqStmt(AssignStmt(ProgAbstractVar("LHS"), ExprAbstractVar("EXPR")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {
        val lhs = cond.map[ProgAbstractVar("LHS")] as ProgVar
        val rhs = exprToTerm(cond.map[ExprAbstractVar("EXPR")] as Expr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val next = SymbolicState(
                input.condition,
                ChainUpdate(input.update, ElementaryUpdate(lhs, rhs)),
                Modality(remainder, target)
        )
        if(containsAbstractVar(next)) return null
        return listOf(SymbolicNode(next))
    }
}

object PITFieldAssign : Rule(Modality(
        SeqStmt(AssignStmt(ProgFieldAbstractVar("LHS"), ExprAbstractVar("EXPR")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {
        val lhs = cond.map[ProgFieldAbstractVar("LHS")] as Field
        val rhs = exprToTerm(cond.map[ExprAbstractVar("EXPR")] as Expr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val next = SymbolicState(
                input.condition,
                ChainUpdate(input.update, ElementaryUpdate(Heap, store(lhs, rhs))),
                Modality(remainder, target)
        )
        if(containsAbstractVar(next)) return null
        return listOf(SymbolicNode(next))
    }
}

object PITSkip : Rule(Modality(
        SkipStmt,
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {
        val target = cond.map[FormulaAbstractVar("POST")] as Formula
        val res = LogicNode(
                Impl(
                        input.condition,
                        UpdateOnFormula(input.update, target)
                )
        )
        return listOf(res)
    }
}

object PITSkipSkip : Rule(Modality(
        SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype)))
        return listOf(res)
    }
}

object PITReturn : Rule(Modality(
        ReturnStmt(ExprAbstractVar("RET")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula
        val retExpr = exprToTerm(cond.map[ExprAbstractVar("RET")] as Expr)
        val res = LogicNode(
                Impl(
                        input.condition,
                        And(
                                UpdateOnFormula(ChainUpdate(input.update, ElementaryUpdate(ReturnVar, retExpr)), targetPost),
                                UpdateOnFormula(input.update, target)
                        )
                )
        )
        return listOf(res)
    }
}

object PITIf : Rule(Modality(
        SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {

        //then
        val guardYes = exprToForm(cond.map[ExprAbstractVar("LHS")] as Expr)
        val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, cond.map[StmtAbstractVar("CONT")] as Stmt)
        val updateYes = input.update
        val typeYes = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes))

        //else
        val guardNo = Not(exprToForm(cond.map[ExprAbstractVar("LHS")] as Expr))
        val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, cond.map[StmtAbstractVar("CONT")] as Stmt)
        val updateNo = input.update
        val typeNo = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo))
        return listOf(SymbolicNode(resThen),SymbolicNode(resElse))
    }
}


object PITAwait : Rule(Modality(
        SeqStmt(AwaitStmt(ExprAbstractVar("GUARD"),PPAbstractVar("PP")), StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {
        val guard = exprToForm(cond.map[ExprAbstractVar("GUARD")] as Expr)
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        val lNode = LogicNode(Impl(input.condition, UpdateOnFormula(input.update, target)))
        val sStat = SymbolicState(And(input.condition,UpdateOnFormula(ChainUpdate(input.update, ElementaryUpdate(Heap,anon(Heap))), And(target,guard))),
                                 ChainUpdate(input.update, ElementaryUpdate(Heap,anon(Heap))),
                                 Modality(cont, PostInvariantPair(targetPost,target)))
        return listOf(lNode,SymbolicNode(sStat))

    }
}

//todo: warning: this is the throwaway variant of loop invariants
object PITWhile : Rule(Modality(
        SeqStmt(WhileStmt(ExprAbstractVar("GUARD"),
                          StmtAbstractVar("BODY"),
                          PPAbstractVar("PP"),
                          FormulaAbstractVar("INV")),
                StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"),
                          FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree>? {
        val guard = exprToForm(cond.map[ExprAbstractVar("GUARD")] as Expr)
        val body = cond.map[StmtAbstractVar("BODY")] as Stmt
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val targetInv = cond.map[FormulaAbstractVar("INV")] as Formula
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        //Initial Case
        val initial = LogicNode(Impl(input.condition, UpdateOnFormula(input.update, targetInv)))

        //Preserves Case
        val preserves = SymbolicState(And(targetInv,guard),
                                      EmptyUpdate,
                                      Modality(appendStmt(body,SkipStmt), PostInvariantPair(targetInv,target)))

        //Use Case
        val use = SymbolicState(And(targetInv,Not(guard)),
                                  EmptyUpdate,
                                  Modality(cont, PostInvariantPair(targetPost,target)))
        return listOf(initial,SymbolicNode(preserves),SymbolicNode(use))

    }
}

val PITCalc = listOf(PITVarAssign,PITFieldAssign,PITReturn,PITSkip,PITIf,PITAwait,PITSkipSkip,PITWhile)
fun nextPITStrategy() : Strategy = DefaultStrategy(PITCalc)