package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.InferenceLeaf
import org.abs_models.crowbar.tree.SymbolicLeaf
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.Model


interface RegAcc
data class ReadAcc(val field : Field) : RegAcc
data class WriteAcc(val field : Field) : RegAcc

data class AccInferenceLeaf(val left : RegAccType, val right : RegAccType) : InferenceLeaf{
	override fun finishedExecution() : Boolean = true
	override fun debugString(steps : Int) : String = "${left.prettyPrint()} = ${right.prettyPrint()}"
	override fun collectLeaves() : List<SymbolicLeaf> = listOf(this)
	override fun evaluate() : Boolean = false
	override fun hasAbstractVar() : Boolean = left.hasAbstractVar() || right.hasAbstractVar()
	override fun normalize() = Unit
}




//Declaration
interface RegAccType : DeductType{
	companion object : PostInvType
	override fun extractMethodNode(classDecl: ClassDecl, name : String, repos: Repository) : SymbolicNode = throw Exception("This type is not executable")
	override fun extractInitialNode(classDecl: ClassDecl) : SymbolicNode = throw Exception("This type is not executable")
	override fun exctractMainNode(model: Model) : SymbolicNode = throw Exception("This type cannot be applied to the main block")
	fun hasAbstractVar() : Boolean // in the sense of BPL unification, not AccVar
}
data class RegAccAbstractVar(val name : String) : RegAccType, AbstractVar {
	override fun prettyPrint(): String {
		return name
	}
	override fun hasAbstractVar() : Boolean = true
}

data class AccVar(val name : String) : RegAccType{
	override fun hasAbstractVar() : Boolean = false
}
data class AccAtom(val fields : Set<RegAcc>) : RegAccType{
	override fun hasAbstractVar() : Boolean = false
}
data class AccSeq(val first : RegAccType, val second : RegAccType) : RegAccType {
	override fun hasAbstractVar(): Boolean = first.hasAbstractVar() || second.hasAbstractVar()
}
data class AccBranch(val left : RegAccType, val right : RegAccType) : RegAccType {
	override fun hasAbstractVar(): Boolean = left.hasAbstractVar() || right.hasAbstractVar()
}
data class AccRep(val inner : RegAccType) : RegAccType {
	override fun hasAbstractVar(): Boolean = inner.hasAbstractVar()
}

abstract class RAAssign(protected val repos: Repository,
                         conclusion : Modality) : Rule(conclusion){

	protected fun assignFor(loc : Location, rhs : Term) : ElementaryUpdate{
		return if(loc is Field)   ElementaryUpdate(Heap, store(loc, rhs)) else ElementaryUpdate(loc as ProgVar, rhs)
	}
	protected fun symbolicNext(loc : Location,
	                           rhs : Term,
	                           remainder : Stmt,
	                           target : DeductType,
	                           iForm : Formula,
	                           iUp : UpdateElement) : SymbolicNode {
		return SymbolicNode(SymbolicState(
			iForm,
			ChainUpdate(iUp, assignFor(loc,rhs)),
			Modality(remainder, target)
		))
	}
}
class RAVarAssign(repos: Repository) : RAAssign(repos, Modality(
	SeqStmt(AssignStmt(ProgAbstractVar("LHS"), ExprAbstractVar("EXPR")),
		StmtAbstractVar("CONT")),
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val lhs = cond.map[ProgAbstractVar("LHS")] as ProgVar
		val rhs = cond.map[ExprAbstractVar("EXPR")] as Expr
		val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
		val target = cond.map[PostInvAbstractVar("TYPE")] as RegAccType
		val myVar = FreshGenerator.getFreshRAVar()
		val infLeaf = AccInferenceLeaf(
			myVar,
			AccSeq(target, AccAtom(generateAccs(rhs)))
		)
		return listOf(infLeaf, symbolicNext(lhs, exprToTerm(rhs), remainder, target, input.condition, input.update))
	}
}


class RAFieldAssign(repos: Repository) : RAAssign(repos, Modality(
	SeqStmt(AssignStmt(ProgFieldAbstractVar("LHS"), ExprAbstractVar("EXPR")),
		StmtAbstractVar("CONT")),
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val lhs = cond.map[ProgFieldAbstractVar("LHS")] as Field
		val rhs = cond.map[ExprAbstractVar("EXPR")] as Expr
		val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
		val target = cond.map[PostInvAbstractVar("TYPE")] as RegAccType
		val myVar = FreshGenerator.getFreshRAVar()
		val infLeaf = AccInferenceLeaf(
			myVar,
			AccSeq(target, AccAtom(generateAccs(rhs) + WriteAcc(lhs)))
		)
		return listOf(infLeaf, symbolicNext(lhs, exprToTerm(rhs), remainder, target, input.condition, input.update))
	}
}


object RAReturn : Rule(Modality(
	ReturnStmt(ExprAbstractVar("RET")),
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val target = cond.map[PostInvAbstractVar("TYPE")] as RegAccType
		val myVar = FreshGenerator.getFreshRAVar()
		val retExpr = cond.map[ExprAbstractVar("RET")] as Expr
		val res = AccInferenceLeaf(
			myVar,
			AccSeq(target, AccAtom(generateAccs(retExpr)))
		)
		return listOf(res)
	}
}

fun generateAccs(input: Expr): Set<RegAcc> {
	return input.collectAll(Field::class).map { ReadAcc(it as Field) }.toSet()
}
