package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
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
import org.abs_models.crowbar.tree.InfoMethodPrecondition
import org.abs_models.crowbar.tree.InfoNullCheck
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.InfoReturn
import org.abs_models.crowbar.tree.InfoScopeClose
import org.abs_models.crowbar.tree.InfoSkip
import org.abs_models.crowbar.tree.InfoSkipEnd
import org.abs_models.crowbar.tree.InfoSyncCallAssign
import org.abs_models.crowbar.tree.NoInfo
import org.abs_models.crowbar.tree.NodeInfoVisitor
import org.abs_models.frontend.ast.FieldUse

object NodeInfoRenderer : NodeInfoVisitor<String> {

    private var scopeLevel = 0
    private var objectCounter = 0
    private val objMap = mutableMapOf<String, String>()
    private val varDefs = mutableSetOf<Pair<String, Int>>()
    private val varTypes = mutableMapOf<String, String>()
    private val varRemaps = mutableMapOf<String, String>()
    private var model = EmptyModel

    fun reset(newModel: Model) {
        model = newModel
        scopeLevel = 0
        objectCounter = 0
        objMap.clear()
        varDefs.clear()
        varTypes.clear()
        varRemaps.clear()
    }

    fun initAssignments(): String {
        val initAssign = model.initState.map { renderModelAssignment(it.first, it.second) }.joinToString("\n")
        return indent("// Assume the following pre-state:\n$initAssign\n// End of setup\n")
    }

    override fun visit(info: InfoAwaitUse): String {
        val postHeap = model.heapMap[info.heapExpr]
        val assignmentBlock = renderHeapAssignmentBlock(postHeap)

        val renderedGuard = if (info.guard.absExp is FieldUse) "${renderExp(info.guard)}?" else renderExp(info.guard)

        return indent("\n// await $renderedGuard;\n$assignmentBlock\n")
    }

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoMethodPrecondition) = ""

    override fun visit(info: InfoNullCheck) = ""

    override fun visit(info: InfoIfElse): String {
        val res =  indent("if(${renderExp(info.guard)}){}\nelse{")
        scopeLevel += 1

        return res
    }

    override fun visit(info: InfoIfThen): String {
        val res = indent("if(${renderExp(info.guard)}){")
        scopeLevel += 1
        return res
    }

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: InfoLocAssign): String {
        val location = renderDeclLocation(info.lhs, type2str = true)

        return indent("$location = ${renderExp(info.expression)};")
    }

    override fun visit(info: InfoGetAssign): String {
        // Get location with possible type declaration both in original form and executable form
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val strLocation = renderDeclLocation(info.lhs, type2str = true)

        val origGet = "// $location = ${renderExp(info.expression)};"

        val futureValue = model.smtExprs[info.futureExpr]
        val getReplacement = if (futureValue != null) "$strLocation = $futureValue;" else "// No future evaluation info available"

        return indent("$origGet\n$getReplacement")
    }

    override fun visit(info: InfoCallAssign): String {
        // Get location with possible type declaration both in original form and executable form
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val strLocation = renderDeclLocation(info.lhs, type2str = true)

        val origCall = "// $location = ${renderExp(info.callee)}!${renderExp(info.call)};"
        val callReplacement = "$strLocation = \"${info.futureName}\";"

        return indent("$origCall\n$callReplacement")
    }

    override fun visit(info: InfoSyncCallAssign): String {
        // Get location with possible type declaration both in original form
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val origCall = "// $location = ${renderExp(info.callee)}.${renderExp(info.call)};"

        // Get heap anonymization assignments
        val postHeap = model.heapMap[info.heapExpr]
        val assignmentBlock = renderHeapAssignmentBlock(postHeap)

        val methodReturnVal = model.smtExprs[info.returnValSMT]
        val callReplacement = if (methodReturnVal != null) renderModelAssignment(info.lhs, methodReturnVal) else "// No return value available"

        return indent("$origCall\n$assignmentBlock\n$callReplacement")
    }

    override fun visit(info: InfoLoopInitial) = indent("while(${renderExp(info.guard)}) { }")

    override fun visit(info: InfoLoopPreserves): String {
        val text = "// Known true:\n" +
            "// Loop guard: ${renderExp(info.guard)}\n" +
            "// Loop invariant: ${renderFormula(info.loopInv)}\n" +
            "while(${renderExp(info.guard)}) {"
        val res = indent(text)

        scopeLevel += 1

        return res
    }

    override fun visit(info: InfoLoopUse): String {
        val text = "while(${renderExp(info.guard)}){} \n" +
            "// Known true:\n" +
            "// Negated loop guard: !(${renderExp(info.guard)})\n" +
            "// Loop invariant: ${renderFormula(info.invariant)}"

        return indent(text)
    }

    override fun visit(info: InfoObjAlloc): String {
        // Get location with possible type declaration both in original form and executable form
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val strLocation = renderDeclLocation(info.lhs, type2str = true)

        val original = "// $location = ${renderExp(info.classInit)};"
        val replacement = "$strLocation = \"${getObjectBySMT(info.newSMTExpr)}\";"
        return indent("$original\n$replacement")
    }

    override fun visit(info: InfoReturn): String {
        return indent("// return ${renderExp(info.expression)};\nprintln ${renderExp(info.expression)};")
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

    private fun renderHeapAssignmentBlock(postHeap: List<Pair<Field, Int>>?): String {
        return if (postHeap == null)
            "// No heap modification info available at this point"
        else if (postHeap.size == 0)
            "// Heap remains unchanged here"
        else {
            val assignments = postHeap.map { renderModelAssignment(it.first, it.second) }.joinToString("\n")
            "// Assume the following assignments while blocked:\n$assignments\n// End assignments"
        }
    }

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
            else -> if (value == 0) "null" else "\"${getObjectById(value)}\""
        }
        return "$location = $renderedValue;"
    }

    private fun renderDeclLocation(loc: Location, type2str: Boolean, declare: Boolean = true): String {
        var location = renderLocation(loc)

        // Fields do not need to be declared
        if (loc !is ProgVar)
            return location

        // Futures and object types are replaced by placeholder strings
        // in executable code but kept in comments for context
        val tpe = if (type2str) complexTypeToString(loc.dType) else loc.dType

        // Variables have to be declared on first use
        if (varDefs.none { it.first == location }) {
            // Remember that we declared this variable and type
            if (declare) {
                varDefs.add(Pair(location, scopeLevel))
                varTypes[location] = tpe
            }
            location = "$tpe $location"
        }
        // Edge case: Because we lose block information during translation, a variable from a closed scope
        // may be redeclared with a different type. In this case, we'll declare a renamed variable to avoid compiler issues
        else if (tpe != varTypes[location] && declare) {
            val disambName = loc.name + "_redec" + tpe

            // Remap all future occurences of the original name to the new name
            varRemaps[loc.name] = disambName
            location = disambName

            if (varDefs.none { it.first == disambName }) {
                // Remember declaration of the renamed variable
                varDefs.add(Pair(disambName, scopeLevel))
                varTypes[disambName] = tpe

                val warning = "// Warning: Due to lost scoping, variable ${loc.name} is redeclared with new type $tpe. Renaming all future occurences to $disambName"
                location = "$warning\n$tpe $disambName"
            }
        }

        return location
    }

    private fun renderLocation(loc: Location): String {
        return when (loc) {
            is ProgVar -> if (varRemaps.containsKey(loc.name)) varRemaps[loc.name]!! else loc.name
            is Field -> "this.${loc.name.substring(0, loc.name.length - 2)}" // Remove _f suffix
            else -> throw Exception("rip")
        }
    }

    private fun renderExp(e: Expr) = renderExpression(e, varRemaps)

    private fun renderFormula(formula: Formula) = renderFormula(formula, varRemaps)

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

fun indent(text: String, level: Int, indentString: String = "\t"): String {
    val lines = text.split("\n")
    val spacer = indentString.repeat(level)

    return lines.map { "$spacer$it" }.joinToString("\n")
}
