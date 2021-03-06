package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.DeductType
import org.abs_models.crowbar.data.exprToTerm
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.frontend.ast.DataTypeDecl
import org.abs_models.frontend.ast.ExpFunctionDef
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model
import kotlin.reflect.KClass
import kotlin.system.exitProcess


object ADTRepos {
	private val known: MutableMap<String, DataTypeDecl> = mutableMapOf()

}

object FunctionRepos{
    private val known : MutableMap<String, FunctionDecl> = mutableMapOf()
    fun isKnown(str: String) = known.containsKey(str)
    fun get(str: String) = known.getValue(str)
	fun hasContracts() = known.filter { hasContract(it.value) }.any()
    override fun toString() : String {
	    val contracts = known.filter { hasContract(it.value) }
	    val direct = known.filter { !hasContract(it.value) }
	    var ret = ""
	    if(contracts.isNotEmpty()) {
		    var sigs = ""
		    var defs = ""
		    for (pair in contracts) {
			    val name = pair.key.replace(".", "-")
			    val params = pair.value.params
			    val zParams = "Int ".repeat(params.count())
			    val nextsig =  "\n(declare-fun $name ($zParams) Int)"
			    sigs += nextsig

			    val callParams = params.joinToString(" ") { it.name }

			    val funpre = extractSpec(pair.value, "Requires")
			    val funpost = extractSpec(pair.value, "Ensures")
			    val transpost = funpost.toSMT(true).replace("result","($name $callParams)")
			    val paramsTyped = params.joinToString(" ") { "(${it.name} Int)" }
			    val nextDef = "\n(assert (forall ($paramsTyped) (=> ${funpre.toSMT(true)} $transpost)))"
			    defs += nextDef
		    }
		    ret += (sigs+defs)
	    }
		    if(direct.isNotEmpty()) {
			    var sigs = ""
			    var defs = ""
			    for (pair in direct) {
				    val params = pair.value.params
				    val eDef: ExpFunctionDef = pair.value.functionDef as ExpFunctionDef
				    val def = eDef.rhs
				    sigs += "\t(${pair.key.replace(".", "-")} (${params.fold("", { acc, nx -> "$acc (${nx.name} Int)" })}) Int)\n"
				    defs += "\t${exprToTerm(translateABSExpToSymExpr(def)).toSMT(false)}\n"
			    }
			    ret += "\n(define-funs-rec(\n$sigs)(\n$defs))"
		    }
	    return ret
    }

	private fun hasContract(fDecl: FunctionDecl) : Boolean {
		return fDecl.annotationList.filter { it.type.toString().endsWith(".Spec") }.any()
	}


	fun init(model: Model, repos: Repository) {
		known.clear()
		for (mDecl in model.moduleDecls){
			if(mDecl.name.startsWith("ABS.")) continue
			for (decl in mDecl.decls){
				if(decl is FunctionDecl){
					initFunctionDef(decl, repos)
				}
			}
		}
	}

	private fun initFunctionDef(fDecl: FunctionDecl, repos: Repository) {
		val fName = fDecl.qualifiedName
		val params = fDecl.params
		if(params.find { !repos.isAllowedType(it.type.qualifiedName) } != null){
			System.err.println("functions with non-Int type not supported")
			exitProcess(-1)
		}
		val fType = fDecl.type
		if(!repos.isAllowedType(fType.qualifiedName)) {
			System.err.println("parameters with non-Int type not supported")
			exitProcess(-1)
		}
		if(fDecl.functionDef is ExpFunctionDef){
			known[fName] = fDecl
		} else {
			System.err.println("builtin types not supported")
			exitProcess(-1)
		}
	}
	fun extractAll(usedType: KClass<out DeductType>) : List<Pair<String,SymbolicNode>> {
		return known.filter { hasContract(it.value) }.map { Pair(it.key,it.value.exctractFunctionNode(usedType)) }
	}
}