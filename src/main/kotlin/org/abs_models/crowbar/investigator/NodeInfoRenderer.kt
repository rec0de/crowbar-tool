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

    fun fieldDefs(): List<String> {
        val fields = model.initState.filter { it.first is Field }.map { it.first as Field }
        val defs = fields.map {
            val name = it.name.substring(0, it.name.length - 2)
            val value = renderModelValue(0, it.dType)
            "${complexTypeToString(it.dType)} $name = $value;"
        }
        return defs
    }

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoMethodPrecondition) = ""

    override fun visit(info: InfoNullCheck) = ""

    override fun visit(info: InfoSkip) = ""

    override fun visit(info: InfoSkipEnd) = ""

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: NoInfo) = ""

    override fun visit(info: InfoAwaitUse): String {
        val postHeap = model.heapMap[info.heapExpr]
        val assignmentBlock = renderHeapAssignmentBlock(postHeap)

        val renderedGuard = if (info.guard.absExp is FieldUse) "${renderExp(info.guard)}?" else renderExp(info.guard)

        return indent("\n// await $renderedGuard;\n$assignmentBlock\n")
    }

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

    override fun visit(info: InfoLocAssign): String {
        val location = renderDeclLocation(info.lhs, type2str = true)

        return indent("$location = ${renderExp(info.expression)};")
    }

    override fun visit(info: InfoGetAssign): String {
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val origGet = "// $location = ${renderExp(info.expression)};"

        var futureValue = model.smtExprs[info.futureExpr.toSMT(false)]
        var getReplacement = ""
        if (futureValue == null) {
            getReplacement = "// Future value irrelevant or unavailable, using default:\n"
            futureValue = 0
        }

        getReplacement += renderModelAssignment(info.lhs, futureValue)

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
        // Detect a stand-alone method call with no lhs
        val unitCall = if (info.lhs is ProgVar) info.lhs.dType == "Unit" else (info.lhs as Field).dType == "Unit"

        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val origCallExp = "${renderExp(info.callee)}.${renderExp(info.call)}"

        // Get heap anonymization assignments
        val postHeap = model.heapMap[info.heapExpr]
        val assignmentBlock = renderHeapAssignmentBlock(postHeap)

        var methodReturnVal = model.smtExprs[info.returnValExpr.toSMT(false)]
        var callReplacement = ""
        if (methodReturnVal == null) {
            callReplacement = "// Return value irrelevant or unavailable, using default:\n"
            methodReturnVal = 0
        }
        callReplacement += renderModelAssignment(info.lhs, methodReturnVal)

        return if (unitCall)
                indent("// $origCallExp;\n$assignmentBlock")
            else
                indent("// $location = $origCallExp;\n$assignmentBlock\n$callReplacement")
    }

    override fun visit(info: InfoLoopInitial) = indent("while(${renderExp(info.guard)}) { }")

    override fun visit(info: InfoLoopPreserves): String {
        val text = "// Known true:\n" +
            "// Loop guard: ${renderExp(info.guard)}\n" +
            "// Loop invariant: ${renderFormula(info.loopInv)}\n" +
            "// while(${renderExp(info.guard)}) {\n" +
            "{"
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
        val original = "// return ${renderExp(info.expression)};"
        val replacement = "println ${renderExp(info.expression)};"

        val evalValue = model.smtExprs[info.retExpr.toSMT(false)]
        val eval = if (evalValue == null) "Irrelevant or unavailable value" else renderModelValue(evalValue, info.expression.absExp!!.type.simpleName)
        val evalMsg = "// Evaluates to: $eval"

        return indent("$original\n$replacement\n$evalMsg")
    }

    override fun visit(info: InfoScopeClose): String {
        // Invalidate declarations made in the current scope
        val validDefs = varDefs.filter { it.second < scopeLevel }
        varDefs.clear()
        varDefs.addAll(validDefs)

        scopeLevel -= 1
        return indent("}")
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

        return "$location = ${renderModelValue(value, type)};"
    }

    private fun renderModelValue(value: Int, dType: String): String {
        return when (dType) {
            "Int" -> value.toString()
            "Fut" -> "\"${model.futNameById(value)}\""
            "Bool" -> if (value == 0) "False" else "True"
            "<UNKNOWN>" -> "\"unknownType($value)\""
            else -> if (value == 0) "null" else "\"${getObjectById(value)}\""
        }
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

    private fun renderExp(e: Expr) = renderExpression(e, varRemaps)

    // Public to allow rendering of formulas with correct replacements from elsewhere
    fun renderFormula(formula: Formula) = renderFormula(formula, varRemaps)

    private fun indent(text: String) = indent(text, scopeLevel)
}

fun complexTypeToString(type: String) = if (type == "Int" || type == "Bool") type else "String"

fun indent(text: String, level: Int, indentString: String = "\t"): String {
    val lines = text.split("\n")
    val spacer = indentString.repeat(level)

    return lines.map { "$spacer$it" }.joinToString("\n")
}
