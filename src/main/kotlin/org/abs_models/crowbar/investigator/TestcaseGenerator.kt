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

class TestcaseGenerator {
	companion object {
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

			output("Found issue branch: ${uncloseable.debugString(0)}")
			output("Traversing upwards...")

			val statements = mutableListOf<String>()
			var n: SymbolicTree = uncloseable

			while(parents[n] != null) {
				
				if(n is InfoNode) {
					statements.add(n.info.accept(NodeInfoRenderer))

					if(n.info.isAnon)
						break
				}

				n = parents[n]!!
			}

			output("Reached full anonymization point or root of tree")

			getModel(uncloseable as LogicNode)

			output(statements.asReversed().joinToString("\n"))

		}

		fun getModel(leaf: LogicNode) {
			val smtRep = generateSMT(leaf.ante, leaf.succ, model = true)
			val res = plainSMTCommand(smtRep)

			output(res!!)
		}
	}
}