package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Term
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Location

abstract class NodeInfo(val isAnon: Boolean, val isHeapAnon: Boolean) {
	open val isSignificantBranch = false
	abstract fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>): ReturnType
}

abstract class SigBranch(isAnon: Boolean, isHeapAnon: Boolean): NodeInfo(isAnon, isHeapAnon) {
	override val isSignificantBranch = true
}

class NoInfo() : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoScopeClose() : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoLoopInitial(val guard: Expr) : SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoLoopPreserves(val guard: Expr, val loopInv: Formula) : SigBranch(isAnon = true, isHeapAnon = true) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoInvariant() : SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoClassPrecondition() : SigBranch(isAnon = false, isHeapAnon = false) {
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

class InfoObjAlloc(val lhs: Location, val classInit: Function) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoReturn(val expression: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoSkip() : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}