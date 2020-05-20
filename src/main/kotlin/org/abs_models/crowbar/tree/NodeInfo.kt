package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.CallExpr
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Term
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Location

// Abstract classes & interfaces

abstract class NodeInfo(val isAnon: Boolean, val isHeapAnon: Boolean) {
	open val isSignificantBranch = false
	abstract fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>): ReturnType
}

abstract class SigBranch(isAnon: Boolean, isHeapAnon: Boolean): NodeInfo(isAnon, isHeapAnon) {
	override val isSignificantBranch = true
}

interface LeafInfo {
	val obligations: List<Pair<String,Formula>>
}

// Significant branches

class InfoInvariant(invariant: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Object invariant", invariant))
}

class InfoLoopInitial(val guard: Expr, loopInv: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Loop invariant", loopInv))
}

class InfoLoopPreserves(val guard: Expr, val loopInv: Formula) : SigBranch(isAnon = true, isHeapAnon = true) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoClassPrecondition(precondition: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Class precondition", precondition))
}

class InfoNullCheck(condition: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Null-check", condition))
}

// Other rule applications

class NoInfo() : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoScopeClose() : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoAwaitUse(val guard: Expr) : NodeInfo(isAnon = false, isHeapAnon = true) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoLoopUse(val guard: Expr, val invariant: Formula) : NodeInfo(isAnon = true, isHeapAnon = true) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoIfThen(val guard: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoIfElse(val guard: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoLocAssign(val lhs: Location, val expression: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoGetAssign(val lhs: Location, val expression: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoCallAssign(val lhs: Location, val callee: Expr, val call: CallExpr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoObjAlloc(val lhs: Location, val classInit: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoReturn(val expression: Expr, postcondition: Formula, invariant: Formula) : LeafInfo, NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Method postcondition", postcondition), Pair("Object invariant", invariant))
}

class InfoSkip() : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoSkipEnd(postcondition: Formula) : LeafInfo, NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Method postcondition", postcondition))
}