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
import org.abs_models.crowbar.tree.InfoSkipEnd
import org.abs_models.crowbar.tree.InfoNullCheck

object NodeInfoRenderer: NodeInfoVisitor<String> {

    private var indentLevel = 0
    private var indentString = "\t"

    private val varDefs = mutableSetOf<String>()

    fun reset() {
        indentLevel = 0
        varDefs.clear()
    }

    override fun visit(info: InfoAwaitUse) = indent("await ${renderExpression(info.guard)};")

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoNullCheck) = ""

    override fun visit(info: InfoIfElse): String {
        val res =  indent("if(${renderExpression(info.guard)}){}\nelse{")
        indentLevel += 1

        return res
    }

    override fun visit(info: InfoIfThen): String {
        val res = indent("if(${renderExpression(info.guard)}){")
        indentLevel += 1
        return res
    }

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: InfoLocAssign): String {
        val location = renderDeclLocation(info.lhs)

        return indent("$location = ${renderExpression(info.expression)};")
    }

    override fun visit(info: InfoGetAssign): String {
        val location = renderDeclLocation(info.lhs)

        return indent("$location = ${renderExpression(info.expression)}.get;")
    }

    override fun visit(info: InfoCallAssign): String {
        val location = renderDeclLocation(info.lhs)

        return indent("$location = ${renderExpression(info.callee)}!${renderExpression(info.call)};")
    }

    override fun visit(info: InfoLoopInitial) = indent("while(${renderExpression(info.guard)}) { }")

    override fun visit(info: InfoLoopPreserves): String {
        val text = "// Known true:\n" +
                   "// Loop guard: ${renderExpression(info.guard)}\n" +
                   "// Loop invariant: ${info.loopInv.prettyPrint()}\n" +
                   "while(${renderExpression(info.guard)}) {"
        val res = indent(text)

        indentLevel += 1

        return res
    }

    override fun visit(info: InfoLoopUse): String {
        val text = "while(${renderExpression(info.guard)}){} \n" +
                   "// Known true:\n" + 
                   "// Negated loop guard: !(${renderExpression(info.guard)})\n" +
                   "// Loop invariant: ${info.invariant.prettyPrint()}"

        return indent(text)
    }

    override fun visit(info: InfoObjAlloc) = indent("${renderLocation(info.lhs)} = ${renderExpression(info.classInit)};")

    override fun visit(info: InfoReturn) = indent("return ${renderExpression(info.expression)};")

    override fun visit(info: InfoScopeClose): String {
        indentLevel -= 1
        return indent("}")
    }

    override fun visit(info: InfoSkip) = ""

    override fun visit(info: InfoSkipEnd) = ""

    override fun visit(info: NoInfo) = indent("[unknown rule application]")

    private fun renderDeclLocation(loc: Location): String {
        val location = renderLocation(loc)

        // Variables have to be declared on first use
        if(loc is ProgVar && !varDefs.contains(location)) {
            varDefs.add(location)
            return "${loc.dType} $location"
        }

        return location
    }

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