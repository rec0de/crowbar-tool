package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.tree.NodeInfo
import org.abs_models.crowbar.tree.NodeInfoVisitor
import org.abs_models.crowbar.tree.NoInfo
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoClassPrecondition
import org.abs_models.crowbar.tree.InfoIfElse
import org.abs_models.crowbar.tree.InfoIfThen
import org.abs_models.crowbar.tree.InfoInvariant
import org.abs_models.crowbar.tree.InfoLocAssign
import org.abs_models.crowbar.tree.InfoGetAssign
import org.abs_models.crowbar.tree.InfoCallAssign
import org.abs_models.crowbar.tree.InfoLoopInitial
import org.abs_models.crowbar.tree.InfoLoopPreserves
import org.abs_models.crowbar.tree.InfoLoopUse
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.InfoReturn
import org.abs_models.crowbar.tree.InfoScopeClose
import org.abs_models.crowbar.tree.InfoSkip
import org.abs_models.crowbar.tree.InfoNullCheck

object NodeInfoRenderer: NodeInfoVisitor<String> {

    private var indentLevel = 0
    private var indentString = "\t"

    fun reset() {
        indentLevel = 0
    }

    override fun visit(info: InfoAwaitUse) = indent("await ${info.guard.prettyPrint()};")

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoNullCheck) = ""

    override fun visit(info: InfoIfElse): String {
        val res =  indent("if(${info.guard.prettyPrint()}){}\nelse{")
        indentLevel += 1

        return res
    }

    override fun visit(info: InfoIfThen): String {
        val res = indent("if(${info.guard.prettyPrint()}){")
        indentLevel += 1
        return res
    }

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: InfoLocAssign): String {
        val location = renderLocation(info.lhs)
        return indent("$location = ${info.expression.prettyPrint()};")
    }

    override fun visit(info: InfoGetAssign): String {
        val location = renderLocation(info.lhs)
        return indent("$location = ${info.expression.prettyPrint()}.get;")
    }

    override fun visit(info: InfoCallAssign): String {
        val location = renderLocation(info.lhs)
        return indent("$location = ${info.callee.prettyPrint()}!${info.call.prettyPrint()};")
    }

    override fun visit(info: InfoLoopInitial) = indent("while(${info.guard.prettyPrint()}) { }")

    override fun visit(info: InfoLoopPreserves): String {
        val text = "// Known true:\n" +
                   "// Loop guard: ${info.guard.prettyPrint()}\n" +
                   "// Loop invariant: ${info.loopInv.prettyPrint()}\n" +
                   "while(${info.guard.prettyPrint()}) {"
        val res = indent(text)

        indentLevel += 1

        return res
    }

    override fun visit(info: InfoLoopUse): String {
        val text = "while(${info.guard.prettyPrint()}){ ... } \n" +
                   "// Known true:\n" + 
                   "// Negated loop guard: !(${info.guard.prettyPrint()})\n" +
                   "// Loop invariant: ${info.invariant.prettyPrint()}"

        return indent(text)
    }

    override fun visit(info: InfoObjAlloc) = indent("${renderLocation(info.lhs)} = new ${info.classInit.prettyPrint()};")

    override fun visit(info: InfoReturn) = indent("return ${info.expression.prettyPrint()};")

    override fun visit(info: InfoScopeClose): String {
        indentLevel -= 1
        return indent("}")
    }

    override fun visit(info: InfoSkip) = ""

    override fun visit(info: NoInfo) = indent("[unknown rule application]")

    private fun renderLocation(loc: Location): String {
        return when(loc) {
            is ProgVar -> loc.name
            is Field -> "this.${loc.name}"
            else -> loc.prettyPrint()
        }
    }

    private fun indent(text: String): String {
        val lines = text.split("\n")
        val spacer = indentString.repeat(indentLevel)

        return lines.map{ "$spacer$it" }.joinToString("\n")
    }
}