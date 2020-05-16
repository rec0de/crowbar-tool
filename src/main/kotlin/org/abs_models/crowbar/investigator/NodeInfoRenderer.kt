package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.tree.NodeInfo
import org.abs_models.crowbar.tree.NodeInfoVisitor
import org.abs_models.crowbar.tree.NoInfo
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoClassPrecondition
import org.abs_models.crowbar.tree.InfoIfElse
import org.abs_models.crowbar.tree.InfoIfThen
import org.abs_models.crowbar.tree.InfoInvariant
import org.abs_models.crowbar.tree.InfoLocAssign
import org.abs_models.crowbar.tree.InfoLoopInitial
import org.abs_models.crowbar.tree.InfoLoopPreserves
import org.abs_models.crowbar.tree.InfoLoopUse
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.InfoReturn
import org.abs_models.crowbar.tree.InfoScopeClose
import org.abs_models.crowbar.tree.InfoSkip

object NodeInfoRenderer: NodeInfoVisitor<String> {

    override fun visit(info: InfoAwaitUse) = "await ${info.guard.prettyPrint()};"

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoIfElse) = "if(${info.guard.prettyPrint()}){}\nelse{"

    override fun visit(info: InfoIfThen) = "if(${info.guard.prettyPrint()}){"

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: InfoLocAssign) = "${info.lhs.prettyPrint()} = ${info.expression.prettyPrint()};"

    override fun visit(info: InfoLoopInitial) = "while(${info.guard.prettyPrint()}) { }"

    override fun visit(info: InfoLoopPreserves): String {
        return "// Known true:\n" +
               "// Loop guard: ${info.guard.prettyPrint()}\n" +
               "// Loop invariant: ${info.loopInv.prettyPrint()}\n" +
               "while(${info.guard.prettyPrint()}) {"
    }

    override fun visit(info: InfoLoopUse): String {
        return "while(${info.guard.prettyPrint()}){ ... } \n" +
               "// Known true:\n" + 
               "// Negated loop guard: !(${info.guard.prettyPrint()})\n" +
               "// Loop invariant: ${info.invariant.prettyPrint()}"
    }

    override fun visit(info: InfoObjAlloc) = "${info.lhs.prettyPrint()} = new ${info.classInit.prettyPrint()};"

    override fun visit(info: InfoReturn) = "return ${info.expression.prettyPrint()};"

    override fun visit(info: InfoScopeClose) = "}"

    override fun visit(info: InfoSkip) = ""

    override fun visit(info: NoInfo) = "[unknown rule application]"
}