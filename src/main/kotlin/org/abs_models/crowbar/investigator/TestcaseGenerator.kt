package org.abs_models.crowbar.investigator

import java.io.File
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.interfaces.generateSMT
import org.abs_models.crowbar.interfaces.plainSMTCommand
import org.abs_models.crowbar.main.Verbosity
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.main.tmpPath
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoGetAssign
import org.abs_models.crowbar.tree.InfoNode
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.LeafInfo
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree

object TestcaseGenerator {

    fun investigateAll(node: SymbolicNode) {
        val uncloseable = node.collectLeaves().filter { it is LogicNode && !it.evaluate() }.map { it as LogicNode }
        var fileIndex = 1

        uncloseable.forEach {
            val counterexample = investigateSingle(node, it)
            writeTestcase(counterexample, fileIndex)
        }
    }

    fun investigateFirst(node: SymbolicNode) {
        val uncloseable = node.collectLeaves().first { it is LogicNode && !it.evaluate() } as LogicNode
        investigateSingle(node, uncloseable)
    }

    private fun investigateSingle(node: SymbolicNode, uncloseable: LogicNode): String {
        if (uncloseable.info !is LeafInfo)
            throw Exception("Unclosed branch does not have proof obligation information")

        val obligations = (uncloseable.info as LeafInfo).obligations

        output("Investigator: found unclosed branch", Verbosity.V)

        output("Investigator: collecting branch nodes....", Verbosity.V)
        val branchNodes = collectBranchNodes(node, uncloseable)
        val infoNodes = branchNodes.map { (it as InfoNode).info }

        output("Investigator: collecting anonymized heap expressions....", Verbosity.V)
        val heapExpressions = infoNodes.filter { it is InfoAwaitUse }.map { (it as InfoAwaitUse).heapExpr }

        output("Investigator: collecting future expressions....", Verbosity.V)
        val futureExpressions = infoNodes.filter { it is InfoGetAssign }.map { (it as InfoGetAssign).futureExpr }

        output("Investigator: collecting object allocation expressions....", Verbosity.V)
        val newExpressions = infoNodes.filter { it is InfoObjAlloc }.map { (it as InfoObjAlloc).newSMTExpr }

        output("Investigator: parsing model....", Verbosity.V)
        val model = getModel(uncloseable, heapExpressions, futureExpressions, newExpressions, listOf())
        val fields = model.initState.filter { it.first is Field }.map { it.first as Field }

        output("Investigator: rendering counterexample....", Verbosity.V)
        NodeInfoRenderer.reset(model)
        val statements = mutableListOf<String>(NodeInfoRenderer.initAssignments())

        for (it in branchNodes.asReversed()) {
            statements.add((it as InfoNode).info.accept(NodeInfoRenderer))
        }

        return buildTestcase(statements, obligations, fields)
    }

    private fun collectBranchNodes(root: SymbolicNode, leaf: SymbolicTree): List<SymbolicTree> {
        val parents = parentMapping(root)
        val nodes = mutableListOf<SymbolicTree>()
        var n: SymbolicTree? = leaf

        while (n != null) {
            nodes.add(n)

            if (n is InfoNode && n.info.isAnon)
                break

            n = parents[n]
        }

        return nodes
    }

    private fun parentMapping(root: SymbolicNode): Map<SymbolicTree, SymbolicTree?> {
        // Create child-parent mapping for symbolic tree
        val parents = mutableMapOf<SymbolicTree, SymbolicTree?>()
        val worklist = mutableListOf<SymbolicTree>(root)

        while (worklist.isNotEmpty()) {
            val elem = worklist.removeAt(0)

            if (elem is SymbolicNode) {
                elem.children.forEach {
                    parents[it] = elem
                }
                worklist.addAll(elem.children)
            }
        }

        return parents
    }

    private fun getModel(
        leaf: LogicNode,
        heapExpressions: List<String>,
        futureExpressions: List<String>,
        newExpressions: List<String>,
        debugExpressions: List<String>
    ): Model {

        // Collect types of fields and variables from leaf node
        val fieldTypes = ((leaf.ante.iterate { it is Field } + leaf.succ.iterate { it is Field }) as Set<Field>).associate { Pair(it.name, it.dType) }
        val varTypes = ((leaf.ante.iterate { it is ProgVar } + leaf.succ.iterate { it is ProgVar }) as Set<ProgVar>).filter { it.name != "heap" }.associate { Pair(it.name, it.dType) }

        // Build model command
        var baseModel = "(get-model)"
        if (heapExpressions.size > 0)
            baseModel += "(get-value (${heapExpressions.joinToString(" ")}))"
        if (futureExpressions.size > 0)
            baseModel += "(get-value (${futureExpressions.map{ "(valueOf $it)" }.joinToString(" ")}))"
        if (newExpressions.size > 0)
            baseModel += "(get-value (${newExpressions.joinToString(" ")}))"
        if (debugExpressions.size > 0)
            baseModel += "(get-value (${debugExpressions.joinToString(" ")}))"

        // Get state at full anonymization point
        val smtRep = generateSMT(leaf.ante, leaf.succ, modelCmd = baseModel)
        val solverResponse = plainSMTCommand(smtRep)!!

        // Can't parse model if solver timed out
        if (solverResponse.substring(0, 7) == "unknown") {
            output("Investigator: solver did not return definite sat/unsat result")
            return EmptyModel
        }

        ModelParser.loadSMT(solverResponse)

        val parsed = ModelParser.parseModel()
        val constants = parsed.filter { it is Constant }
        val initHeap = constants.find { it.name == "heap" }
        val vars = constants.filter { !(it.name matches Regex("(.*_f|fut_.*|NEW\\d.*|Unit|heap)")) }
        val fields = constants.filter { it.name matches Regex(".*_f") }
        val futLookup = constants.filter { it.name.startsWith("fut_") }.associate { Pair((it.value as Integer).value, it.name) }

        if (initHeap == null)
            throw Exception("Model contained no heap definition")

        val heapState = initHeap.value as Array
        val initialAssignments = mutableListOf<Pair<Location, Int>>()

        fields.forEach {
            val initValue = heapState.getValue((it.value as Integer).value)
            val field = Field(it.name, fieldTypes[it.name]!!)
            initialAssignments.add(Pair(field, initValue))
        }

        vars.forEach {
            val initValue = (it.value as Integer).value
            val variable = ProgVar(it.name, varTypes[it.name]!!)
            initialAssignments.add(Pair(variable, initValue))
        }

        // Get heap-states at heap anonymization points
        val heapAssignments = getHeapMap(heapExpressions, fields, fieldTypes)

        // Get values of futures
        val futureAssignments = getExpressionMap(futureExpressions)

        // Get mapping of object ids to names
        val objLookup = getObjectMap(newExpressions)

        // Get evaluations of misc expressions (e.g. return value expressions)
        val miscLookup = getExpressionMap(debugExpressions)

        return Model(initialAssignments, heapAssignments, futureAssignments, futLookup, objLookup)
    }

    private fun getHeapMap(heapExpressions: List<String>, fields: List<Function>, fieldTypes: Map<String, String>): Map<String, List<Pair<Field, Int>>> {
        if (heapExpressions.size == 0)
            return mapOf()

        val parsedHeaps = ModelParser.parseArrayValues()
        val rawMap = heapExpressions.zip(parsedHeaps).associate { it }
        val heapMap = rawMap.mapValues { (_, heap) ->
            fields.map {
                val initValue = heap.getValue((it.value as Integer).value)
                val field = Field(it.name, fieldTypes[it.name]!!)
                Pair(field, initValue)
            }
        }

        return heapMap
    }

    private fun getExpressionMap(expressions: List<String>): Map<String, Int> {
        if (expressions.size == 0)
            return mapOf()

        val parsed = ModelParser.parseIntegerValues()
        val expMap = expressions.zip(parsed).associate { it }

        return expMap
    }

    private fun getObjectMap(newExpressions: List<String>): Map<Int, String> {
        if (newExpressions.size == 0)
            return mapOf()

        val parsed = ModelParser.parseIntegerValues()
        val objMap = parsed.zip(newExpressions).associate { it }

        return objMap
    }

    private fun buildTestcase(statements: List<String>, obligations: List<Pair<String, Formula>>, fields: List<Field>): String {

        val classFrameHeader = "module Counterexample;\n\nclass CeFrame {\n"
        val classFrameFooter = "\n}\n"

        val fieldDefs = fields.map { "${complexTypeToString(it.dType)} ${it.name.substring(0, it.name.length - 2)};" }.joinToString("\n")

        val methodFrameHeader = "Unit ce() {\n"
        val methodFrameFooter = "\n}"

        val stmtString = statements.joinToString("\n")
        val explainer = "\n// Proof failed here. Trying to show:\n"
        val oblString = obligations.map { "// ${it.first}: ${renderFormula(it.second)}" }.joinToString("\n")

        val methodContent = stmtString + explainer + oblString
        val methodFrame = methodFrameHeader + indent(methodContent, 1) + methodFrameFooter

        val classFrame = classFrameHeader + indent(fieldDefs, 1) + "\n\n" + indent(methodFrame, 1) + classFrameFooter

        return classFrame
    }

    private fun writeTestcase(content: String, index: Int) {
        val filename = "${tmpPath}crowbar-ce-$index.abs"
        val file = File(filename)
        file.createNewFile()
        file.writeText(content)
        output("Investigator: wrote counterexample to $filename")
    }
}

class Model(
    val initState: List<Pair<Location, Int>>,
    val heapMap: Map<String, List<Pair<Field, Int>>>,
    val futMap: Map<String, Int>,
    val futLookup: Map<Int, String>,
    val objLookup: Map<Int, String>
) {
    // The SMT solver may reference futures that were not defined in the program
    // we'll mark these with a questionmark and give the underlying integer id from the solver
    fun futNameById(id: Int) = if (futLookup.containsKey(id)) futLookup[id]!! else "fut_?($id)"
}

val EmptyModel = Model(listOf(), mapOf(), mapOf(), mapOf(), mapOf())
