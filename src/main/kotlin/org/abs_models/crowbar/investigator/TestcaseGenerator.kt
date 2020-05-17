package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree
import org.abs_models.crowbar.tree.InfoNode
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.main.tmpPath
import org.abs_models.crowbar.interfaces.plainSMTCommand
import org.abs_models.crowbar.interfaces.generateSMT
import java.io.File

object TestcaseGenerator {
	fun investigate(node: SymbolicNode) {

		// Create child-parent mapping for symbolic tree
		val parents = mutableMapOf<SymbolicTree,SymbolicTree?>()
		val worklist = mutableListOf<SymbolicTree>(node)

		while(worklist.isNotEmpty()) {
			val elem = worklist.removeAt(0)

			if(elem is SymbolicNode) {
				elem.children.forEach {
					parents[it] = elem
				}
				worklist.addAll(elem.children)
			}	
		}

		val uncloseable = node.collectLeaves().first{ it is LogicNode && !it.evaluate() }

		output("Investigator: found unclosed branch")
		output("Investigator: traversing upwards....")

		val branchNodes = mutableListOf<SymbolicTree>()
		var n: SymbolicTree = uncloseable

		while(parents[n] != null) {
			branchNodes.add(n)

			if(n is InfoNode && n.info.isAnon)
				break

			n = parents[n]!!
		}

		output("Investigator: reached full anonymization point or root of tree")

		NodeInfoRenderer.reset()
		val statements = mutableListOf<String>()

		for(it in branchNodes.asReversed()) {
			if(it is InfoNode) {
				statements.add(it.info.accept(NodeInfoRenderer))
			}
		}

		output(statements.joinToString("\n"))

		output("Investigator: parsing model....")
		getModel(uncloseable as LogicNode)
	}	

	fun getModel(leaf: LogicNode) {
		val smtRep = generateSMT(leaf.ante, leaf.succ, model = true)
		val model = plainSMTCommand(smtRep)!!

		if(model.substring(0, 7) == "unknown")
			output("Investigator: solver did not return definite sat/unsat result")
		else {
			val parsed = ModelParser.parse(model)
			output(parsed.joinToString("\n"))
		}	
	}
}