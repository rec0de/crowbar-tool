package org.abs_models.crowbar.investigator

import java.io.File
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.Term
import org.abs_models.crowbar.data.deupdatify
import org.abs_models.crowbar.data.specialHeapKeywords
import org.abs_models.crowbar.interfaces.generateSMT
import org.abs_models.crowbar.interfaces.plainSMTCommand
import org.abs_models.crowbar.main.Verbosity
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.main.tmpPath
import org.abs_models.crowbar.tree.InfoNode
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.LeafInfo
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.NodeInfo
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree

object TestcaseGenerator {

    var fileIndex = 1

    fun investigateAll(node: SymbolicNode) {
        val uncloseable = node.collectLeaves().filter { it is LogicNode && !it.evaluate() }.map { it as LogicNode }

        uncloseable.forEach {
            val counterexample = investigateSingle(node, it)
            writeTestcase(counterexample, fileIndex)
            fileIndex++
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
        val heapExpressions = infoNodes.map { it.heapExpressions }.flatten()

        output("Investigator: collecting object allocation expressions....", Verbosity.V)
        val newExpressions = infoNodes.filter { it is InfoObjAlloc }.map { (it as InfoObjAlloc).newSMTExpr }

        output("Investigator: collecting other smt expressions....", Verbosity.V)
        val miscExpressionTerms = infoNodes.map { it.smtExpressions }.flatten()

        // Remove expressions that contain definitions missing from the SMT model
        // This will cause the solver to error out, and any expression depending on a definition
        // not present in the SMT model is irrelevant to the correctness of the method anyway
        // Collect types of fields and variables from leaf node
        val pre = deupdatify(uncloseable.ante)
        val post = deupdatify(uncloseable.succ)
        val availableDefs = ((pre.iterate { it is Term } + post.iterate { it is Term }) as Set<Term>).map { collectUsedDefinitions(it) }.flatten().toSet()
        val miscExpressions = miscExpressionTerms.filter { collectUsedDefinitions(it).minus(availableDefs).isEmpty() }.map { it.toSMT(false) }

        output("Investigator: parsing model....", Verbosity.V)
        val model = getModel(uncloseable, heapExpressions, newExpressions, miscExpressions)

        output("Investigator: rendering counterexample....", Verbosity.V)

        return buildTestcase(infoNodes.asReversed(), model, obligations)
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
        newExpressions: List<String>,
        miscExpressions: List<String>
    ): Model {

        // "heap", "old", "last", etc do not reference program vars
        val reservedVarNames = listOf("heap", "Unit") + specialHeapKeywords.values.map{ it.name }

        // Collect types of fields and variables from leaf node
        val fieldTypes = ((leaf.ante.iterate { it is Field } + leaf.succ.iterate { it is Field }) as Set<Field>).associate { Pair(it.name, it.dType) }
        val varTypes = ((leaf.ante.iterate { it is ProgVar } + leaf.succ.iterate { it is ProgVar }) as Set<ProgVar>).filter { !reservedVarNames.contains(it.name) }.associate { Pair(it.name, it.dType) }

        // Collect conjunctively joined sub-obligation parts
        val subObligationMap = collectSubObligations(deupdatify(leaf.succ) as Formula).associate { Pair(it.toSMT(false), it) }
        val subObligations = subObligationMap.keys.toList()

        // Build model command
        var baseModel = "(get-model)"
        if (heapExpressions.size > 0)
            baseModel += "(get-value (${heapExpressions.joinToString(" ")}))"
        if (newExpressions.size > 0)
            baseModel += "(get-value (${newExpressions.joinToString(" ")}))"
        if (miscExpressions.size > 0)
            baseModel += "(get-value (${miscExpressions.joinToString(" ")}))"
        if (subObligationMap.keys.size > 0)
            baseModel += "(get-value (${subObligations.joinToString(" ")}))"

        // Get evaluations of all collected expressions (heap states after anon, new objects, future values, etc)
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
        val vars = constants.filter { !(it.name matches Regex("(.*_f|fut_.*|NEW\\d.*|f_(\\d)+)") || reservedVarNames.contains(it.name)) }
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

        // Get mapping of object ids to names
        val objLookup = getObjectMap(newExpressions)

        // Get evaluations of misc expressions (return value expressions, values of futures, method return values)
        val smtExprs = getExpressionMap(miscExpressions)

        // Get evaluations of sub-obligations and create usable mapping by formula
        val subObligationValues = getExpressionMap(subObligations).mapKeys { subObligationMap[it.key]!! }.mapValues { it.value == 1 }

        return Model(initialAssignments, heapAssignments, futLookup, objLookup, smtExprs, subObligationValues)
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

    private fun buildTestcase(infoNodes: List<NodeInfo>, model: Model, obligations: List<Pair<String, Formula>>): String {
        val classFrameHeader = "module Counterexample;\n\nclass CeFrame {\n"
        val classFrameFooter = "\n}\n"

        val methodFrameHeader = "Unit ce() {\n"
        val methodFrameFooter = "\n}"

        NodeInfoRenderer.reset(model)
        val fieldDefs = NodeInfoRenderer.fieldDefs().joinToString("\n")
        val statements = mutableListOf<String>(NodeInfoRenderer.initAssignments())

        for (it in infoNodes) {
            statements.add(it.accept(NodeInfoRenderer))
        }

        val stmtString = statements.joinToString("\n")
        val explainer = "\n// Proof failed here. Trying to show:\n"
        val oblString = obligations.map { "// ${it.first}: ${NodeInfoRenderer.renderFormula(it.second)}" }.joinToString("\n")

        var subOblString = "\n// Failed to show the following sub-obligations:\n"
        subOblString += model.subObligations.filter { !it.value }.map { "// ${NodeInfoRenderer.renderFormula(it.key)}" }.joinToString("\n")

        val methodContent = stmtString + explainer + oblString + subOblString
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
    val futLookup: Map<Int, String>,
    val objLookup: Map<Int, String>,
    val smtExprs: Map<String, Int>,
    val subObligations: Map<Formula, Boolean>
) {
    // The SMT solver may reference futures that were not defined in the program
    // we'll mark these with a questionmark and give the underlying integer id from the solver
    fun futNameById(id: Int) = if (futLookup.containsKey(id)) futLookup[id]!! else "fut_?($id)"
}

val EmptyModel = Model(listOf(), mapOf(), mapOf(), mapOf(), mapOf(), mapOf())
