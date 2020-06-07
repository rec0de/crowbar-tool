package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.interfaces.generateSMT
import org.abs_models.crowbar.interfaces.plainSMTCommand
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoGetAssign
import org.abs_models.crowbar.tree.InfoNode
import org.abs_models.crowbar.tree.LeafInfo
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree

object TestcaseGenerator {
    fun investigate(node: SymbolicNode) {

        val uncloseable = node.collectLeaves().first { it is LogicNode && !it.evaluate() }

        if (uncloseable !is InfoNode || uncloseable.info !is LeafInfo)
            throw Exception("Unclosed branch does not have proof obligation information")

        val obligations = (uncloseable.info as LeafInfo).obligations

        output("Investigator: found unclosed branch")

        output("Investigator: collecting branch nodes....")
        val branchNodes = collectBranchNodes(node, uncloseable)

        output("Investigator: collecting anonymized heap expressions....")
        val heapExpressions = branchNodes.map { (it as InfoNode).info }.filter { it is InfoAwaitUse }.map { (it as InfoAwaitUse).heapExpr }

        output("Investigator: collecting future expressions....")
        val futureExpressions = branchNodes.map { (it as InfoNode).info }.filter { it is InfoGetAssign }.map { (it as InfoGetAssign).futureExpr }

        output("Investigator: parsing model....")
        val model = getModel(uncloseable as LogicNode, heapExpressions, futureExpressions)

        output("Investigator: rendering counterexample....")
        NodeInfoRenderer.reset(model)
        val statements = mutableListOf<String>()

        for (it in branchNodes.asReversed()) {
            statements.add((it as InfoNode).info.accept(NodeInfoRenderer))
        }

        output(buildTestcase(statements, obligations, model))
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

    private fun getModel(leaf: LogicNode, heapExpressions: List<String>, futureExpressions: List<String>): Model {

        // Build model command
        var baseModel = "(get-model)"
        if (heapExpressions.size > 0)
            baseModel += "(get-value (${heapExpressions.joinToString(" ")}))"
        if (futureExpressions.size > 0)
            baseModel += "(get-value (${futureExpressions.map{ "(valueOf $it)" }.joinToString(" ")}))"

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
        val initHeap = parsed.find { it is Constant && it.name == "heap" }
        val vars = parsed.filter { it is Constant && !(it.name matches Regex("(.*_f|fut_.*|Unit|heap)")) }
        val fields = parsed.filter { it is Constant && it.name matches Regex(".*_f") }

        if (initHeap == null)
            throw Exception("Model contained no heap definition")

        val heapState = initHeap.value as Array
        val initialAssignments = mutableListOf<Pair<String, Int>>()

        fields.forEach {
            val initValue = heapState.getValue((it.value as Integer).value)
            val fieldName = it.name.substring(0, it.name.length - 2) // Strip _f suffix
            initialAssignments.add(Pair("this.$fieldName", initValue))
        }

        vars.forEach {
            val initValue = (it.value as Integer).value
            initialAssignments.add(Pair(it.name, initValue))
        }

        // Get heap-states at heap anonymization points
        val heapAssignments = getHeapMap(heapExpressions, fields)

        // Get values of futures
        val futureAssignments = getFutureMap(futureExpressions)

        return Model(initialAssignments, heapAssignments, futureAssignments)
    }

    private fun getHeapMap(heapExpressions: List<String>, fields: List<Function>): Map<String, List<Pair<String, Int>>> {
        if (heapExpressions.size == 0)
            return mapOf()

        val parsedHeaps = ModelParser.parseArrayValues()
        val rawMap = heapExpressions.zip(parsedHeaps).associate { it }
        val heapMap = rawMap.mapValues { (_, heap) ->
            fields.map {
                val initValue = heap.getValue((it.value as Integer).value)
                val fieldName = it.name.substring(0, it.name.length - 2)
                Pair("this.$fieldName", initValue)
            }
        }

        return heapMap
    }

    private fun getFutureMap(futureExpressions: List<String>): Map<String, Int> {
        if (futureExpressions.size == 0)
            return mapOf()

        val parsed = ModelParser.parseIntegerValues()
        val futMap = futureExpressions.zip(parsed).associate { it }

        return futMap
    }

    private fun buildTestcase(statements: List<String>, obligations: List<Pair<String, Formula>>, model: Model): String {

        val initAssign = model.initState.map { "${it.first} = ${it.second};" }.joinToString("\n")
        val initString = "// Assume the following pre-state:\n$initAssign\n// End of setup\n\n"

        val stmtString = statements.joinToString("\n")
        val explainer = "\n// Proof failed here. Trying to show:\n"
        val oblString = obligations.map { "// ${it.first}: ${it.second.prettyPrint()}" }.joinToString("\n")

        return initString + stmtString + explainer + oblString
    }
}

class Model(val initState: List<Pair<String, Int>>, val heapMap: Map<String, List<Pair<String, Int>>>, val futMap: Map<String, Int>)

val EmptyModel = Model(listOf(), mapOf(), mapOf())
