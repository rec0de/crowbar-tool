package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.exprToTerm
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.frontend.ast.ExpFunctionDef
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model

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
	    return "\n(define-funs-rec\n(\n$sigs)\n(\n$defs))"
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
		if(params.find { !repos.isAllowedType(it.type.qualifiedName) } != null) return //todo: should be an error
		val fType = fDecl.type
		if(!repos.isAllowedType(fType.qualifiedName)) return //todo: should be an error
		if(fDecl.functionDef is ExpFunctionDef){
			known.put(fName,fDecl)
		} else {
			return //todo: should be an error
		}
	}
}