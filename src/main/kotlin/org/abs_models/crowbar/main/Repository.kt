package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.exprToTerm
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.frontend.ast.ExpFunctionDef
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model
import kotlin.system.exitProcess

//todo: this is for development purposes only and will be removed once the translation is automatic
object FunctionRepos{
    private val known : MutableMap<String, FunctionDecl> = mutableMapOf()//Pair("fib","(define-fun-rec fib ((n Int)) Int\n" +
   // "    (ite (<= n 2) 1\n" +
   // "           (+ (fib (- n 1)) (fib (- n 2)))))"))
    fun isKnown(str: String) = known.containsKey(str)
    fun get(str: String) = known.getValue(str)
    override fun toString() : String {
	    if(known.isEmpty()) return ""
	    var sigs = ""
	    var defs = ""
	    for(pair in known){
		    val params = pair.value.params
			val eDef : ExpFunctionDef = pair.value.functionDef as ExpFunctionDef
			val def = eDef.rhs
		    sigs += "\t(${pair.key.replace(".","-")} (${params.fold("",{acc, nx -> "$acc (${nx.name} Int)"})}) Int)\n"
		    defs += "\t${exprToTerm(translateABSExpToSymExpr(def)).toSMT(false)}\n"
	    }
	    return "\n(define-funs-rec(\n$sigs)(\n$defs))"
    }



	fun init(model: Model, repos: Repository) {
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
			known.put(fName,fDecl)
		} else {
			System.err.println("builtin types not supported")
			exitProcess(-1)
		}
	}
}