package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoCallAssign
import org.abs_models.crowbar.tree.InfoClassPrecondition
import org.abs_models.crowbar.tree.InfoGetAssign
import org.abs_models.crowbar.tree.InfoIfElse
import org.abs_models.crowbar.tree.InfoIfThen
import org.abs_models.crowbar.tree.InfoInvariant
import org.abs_models.crowbar.tree.InfoLocAssign
import org.abs_models.crowbar.tree.InfoLoopInitial
import org.abs_models.crowbar.tree.InfoLoopPreserves
import org.abs_models.crowbar.tree.InfoLoopUse
import org.abs_models.crowbar.tree.InfoNullCheck
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.InfoReturn
import org.abs_models.crowbar.tree.InfoScopeClose
import org.abs_models.crowbar.tree.InfoSkip
import org.abs_models.crowbar.tree.InfoSkipEnd
import org.abs_models.crowbar.tree.NoInfo
import org.abs_models.crowbar.tree.NodeInfoVisitor
import org.abs_models.frontend.ast.FieldUse

object NodeInfoRenderer : NodeInfoVisitor<String> {

    private var scopeLevel = 0
    private var objectCounter = 0
    private val objMap = mutableMapOf<String, String>()
    private val varDefs = mutableSetOf<Pair<String, Int>>()
    private var model = EmptyModel

    fun reset(newModel: Model) {
        model = newModel
        scopeLevel = 0
        objectCounter = 0
        objMap.clear()
        varDefs.clear()
    }

    fun initAssignments(): String {
        val initAssign = model.initState.map { renderModelAssignment(it.first, it.second) }.joinToString("\n")
        return indent("// Assume the following pre-state:\n$initAssign\n// End of setup\n")
    }

    override fun visit(info: InfoAwaitUse): String {
        val postHeap = model.heapMap[info.heapExpr]

        val assignmentBlock: String
        if (postHeap == null)
            assignmentBlock = "// No heap modification info available for this call"
        else {
            val assignments = postHeap.map { renderModelAssignment(it.first, it.second) }.joinToString("\n")
            assignmentBlock = "// Assume the following assignments during the async call:\n$assignments\n// End assignments"
        }

        val renderedGuard = if (info.guard.absExp is FieldUse) "${renderExpression(info.guard)}?" else renderExpression(info.guard)

        return indent("\n// await $renderedGuard;\n$assignmentBlock\n")
    }

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoNullCheck) = ""

    override fun visit(info: InfoIfElse): String {
        val res =  indent("if(${renderExpression(info.guard)}){}\nelse{")
        scopeLevel += 1

        return res
    }

    override fun visit(info: InfoIfThen): String {
        val res = indent("if(${renderExpression(info.guard)}){")
        scopeLevel += 1
        return res
    }

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: InfoLocAssign): String {
        val location = renderDeclLocation(info.lhs, type2str = true)

        return indent("$location = ${renderExpression(info.expression)};")
    }

    override fun visit(info: InfoGetAssign): String {
        // Get location with possible type declaration both in original form and executable form
        val strLocation = renderDeclLocation(info.lhs, type2str = true, declare = false)
        val location = renderDeclLocation(info.lhs, type2str = false)

        val origGet = "// $location = ${renderExpression(info.expression)};"

        val futureValue = model.futMap[info.futureExpr]
        val getReplacement = if (futureValue != null) "$strLocation = $futureValue;" else "// No future evaluation info available"

        return indent("$origGet\n$getReplacement")
    }

    override fun visit(info: InfoCallAssign): String {
        // Get location with possible type declaration both in original form and executable form
        val strLocation = renderDeclLocation(info.lhs, type2str = true, declare = false)
        val location = renderDeclLocation(info.lhs, type2str = false)

        val origCall = "// $location = ${renderExpression(info.callee)}!${renderExpression(info.call)};"
        val callReplacement = "$strLocation = \"${info.futureName}\";"

        return indent("$origCall\n$callReplacement")
    }

    override fun visit(info: InfoLoopInitial) = indent("while(${renderExpression(info.guard)}) { }")

    override fun visit(info: InfoLoopPreserves): String {
        val text = "// Known true:\n" +
            "// Loop guard: ${renderExpression(info.guard)}\n" +
            "// Loop invariant: ${renderFormula(info.loopInv)}\n" +
            "while(${renderExpression(info.guard)}) {"
        val res = indent(text)

        scopeLevel += 1

        return res
    }

    override fun visit(info: InfoLoopUse): String {
        val text = "while(${renderExpression(info.guard)}){} \n" +
            "// Known true:\n" +
            "// Negated loop guard: !(${renderExpression(info.guard)})\n" +
            "// Loop invariant: ${renderFormula(info.invariant)}"

        return indent(text)
    }

    override fun visit(info: InfoObjAlloc): String {
        // Get location with possible type declaration both in original form and executable form
        val strLocation = renderDeclLocation(info.lhs, type2str = true, declare = false)
        val location = renderDeclLocation(info.lhs, type2str = false)

        val original = "// $location = ${renderExpression(info.classInit)};"
        val replacement = "$strLocation = \"${getObjectBySMT(info.newSMTExpr)}\";"
        return indent("$original\n$replacement")
    }

    override fun visit(info: InfoReturn): String {
        return indent("// return ${renderExpression(info.expression)};\nprintln ${renderExpression(info.expression)};")
    }

    override fun visit(info: InfoScopeClose): String {
        // Invalidate declarations made in the current scope
        val validDefs = varDefs.filter { it.second < scopeLevel }
        varDefs.clear()
        varDefs.addAll(validDefs)

        scopeLevel -= 1
        return indent("}")
    }

    override fun visit(info: InfoSkip) = ""

    override fun visit(info: InfoSkipEnd) = ""

    override fun visit(info: NoInfo) = ""

    private fun renderModelAssignment(loc: Location, value: Int): String {
        val location = renderDeclLocation(loc, type2str = true)

        val type = when (loc) {
            is Field -> loc.dType
            is ProgVar -> loc.dType
            else -> throw Exception("Cannot render unknown location: ${loc.prettyPrint()}")
        }

        val renderedValue = when (type) {
            "Int" -> value.toString()
            "Fut" -> "\"${model.futNameById(value)}\""
            "Bool" -> if (value == 0) "False" else "True"
            else -> "\"${getObjectById(value)}\""
        }
        return "$location = $renderedValue;"
    }

    private fun renderDeclLocation(loc: Location, type2str: Boolean, declare: Boolean = true): String {
        var location = renderLocation(loc)

        // Variables have to be declared on first use
        if (loc is ProgVar && varDefs.none { it.first == location }) {
            if (declare)
                varDefs.add(Pair(location, scopeLevel))
            // Futures and object types are replaced by placeholder strings
            // in executable code but kept in comments for context
            val type = if (type2str) complexTypeToString(loc.dType) else loc.dType
            location = "$type $location"
        }

        return location
    }

    private fun getObjectBySMT(smtRep: String): String {
        if (!objMap.containsKey(smtRep)) {
            objectCounter++
            objMap[smtRep] = "object_$objectCounter"
        }

        return objMap[smtRep]!!
    }

    private fun getObjectById(id: Int): String {
        if (!model.objLookup.containsKey(id))
            return "object_?($id)"

        val smtRep = model.objLookup[id]!!
        return getObjectBySMT(smtRep)
    }

    private fun indent(text: String) = indent(text, scopeLevel)
}

fun complexTypeToString(type: String) = if (type == "Int" || type == "Bool") type else "String"

fun renderLocation(loc: Location): String {
    return when (loc) {
        is ProgVar -> loc.name
        is Field -> "this.${loc.name.substring(0, loc.name.length - 2)}" // Remove _f suffix
        else -> loc.prettyPrint()
    }
}

fun indent(text: String, level: Int, indentString: String = "\t"): String {
    val lines = text.split("\n")
    val spacer = indentString.repeat(level)

    return lines.map { "$spacer$it" }.joinToString("\n")
}
