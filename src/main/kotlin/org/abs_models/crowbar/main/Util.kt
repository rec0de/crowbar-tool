package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.ReturnStmt
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.crowbar.interfaces.translateABSStmtToSymStmt
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.PostInvariantPair
import org.abs_models.crowbar.types.nextPITStrategy
import org.abs_models.frontend.ast.*
import java.io.File
import java.nio.file.Path
import kotlin.system.exitProcess

fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String, default:Formula = True) : Formula {
    for(annotation in decl.nodeAnnotations){
        if(!annotation.type.toString().endsWith(".Spec")) continue
        if(annotation.value !is DataConstructorExp) {
            throw Exception("Could not extract any specification from $decl because of the expected value")
        }
        val annotated = annotation.value as DataConstructorExp
        if(annotated.constructor != expectedSpec) continue
        return exprToForm(translateABSExpToSymExpr(annotated.getParam(0) as Exp))
    }
    if(verbosity >= Verbosity.V)
        println("Crowbar-v: Could not extract $expectedSpec specification, using $default")
    return default
}


fun load(path : Path) : Model {

    println("Crowbar  : loading files....")
    val input = File(path.toString())
    if(!input.exists()) {
        System.err.println("file not found: $path")
        exitProcess(-1)
    }

    println("Crowbar  : loading ABS model....")
    val model = try {
        org.abs_models.frontend.parser.Main().parse(listOf(input))
    } catch (e : Exception) {
        e.printStackTrace()
        System.err.println("error during parsing, aborting")
        exitProcess(-1)
    }
    return model
}

fun extractClassDecl(moduleName : String, className : String, model : Model) : ClassDecl {
    val moduleDecl = model.moduleDecls.firstOrNull { it.name == moduleName }
    if(moduleDecl == null){
        System.err.println("module not found: $moduleName")
        exitProcess(-1)
    }
    val classDecl : ClassDecl? = moduleDecl.decls.firstOrNull { it is ClassDecl && it.name == className } as ClassDecl?
    if(classDecl == null){
        System.err.println("class not found: ${moduleName}.${className}")
        exitProcess(-1)
    }

    if(    classDecl.params.any { !isAllowedType(it.type.toString()) }
        || classDecl.fields.any { !isAllowedType(it.type.toString()) } ){
        System.err.println("fields with non-Int type not supported")
        exitProcess(-1)
    }
    return classDecl
}


fun extractInitialNode( classDecl: ClassDecl) : SymbolicNode {

    val initBlock = classDecl.initBlock
    var body = if(initBlock!= null) appendStmt(translateABSStmtToSymStmt(initBlock), ReturnStmt(unitExpr())) else ReturnStmt(unitExpr())
    for (fieldDecl in classDecl.fields){
        if(fieldDecl.hasInitExp()){
            val nextBody = AssignStmt(Field(fieldDecl.name), translateABSExpToSymExpr(fieldDecl.initExp))
            body = SeqStmt(nextBody,body)
        }
    }

    println("Crowbar  : loading specification....")
    val objInv: Formula?
    val objPre: Formula?
    try {
        objInv = extractSpec(classDecl, "ObjInv")
        objPre = extractSpec(classDecl, "Requires")
    } catch (e: Exception) {
        e.printStackTrace()
        System.err.println("error during translation, aborting")
        exitProcess(-1)
    }
    if (verbosity >= Verbosity.V) {
        println("Crowbar-v: object precondition: ${objPre.prettyPrint()}")
        println("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
    }
    val symb = SymbolicState(objPre, EmptyUpdate, Modality(body, PostInvariantPair(True, objInv)))
    return SymbolicNode(symb, emptyList())
}
fun extractMethodNode(name : String, classDecl: ClassDecl) : SymbolicNode {

    if(name == "<init>")
        return extractInitialNode(classDecl)
    val mDecl = classDecl.methods.firstOrNull { it.methodSig.name == name }
    if (mDecl == null) {
        System.err.println("method not found: ${classDecl.qualifiedName}.${name}")
        exitProcess(-1)
    }
    if (mDecl.methodSig.params.any { !isAllowedType(it.type.toString()) }) {
        System.err.println("parameters with non-Int type not supported")
        exitProcess(-1)
    }

    println("Crowbar  : loading specification....")
    val symb: SymbolicState?
    val objInv: Formula?
    val metpost: Formula?
    val body: Stmt?
    try {
        objInv = extractSpec(classDecl, "ObjInv")
        metpost = extractSpec(mDecl, "Ensures")
        val st = mDecl.block
        body = translateABSStmtToSymStmt(st)
    } catch (e: Exception) {
        e.printStackTrace()
        System.err.println("error during translation, aborting")
        exitProcess(-1)
    }
    if (verbosity >= Verbosity.V) {
        println("Crowbar-v: method post-condition: ${metpost.prettyPrint()}")
        println("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
    }

    symb = SymbolicState(objInv, EmptyUpdate, Modality(body, PostInvariantPair(metpost, objInv)))
    return SymbolicNode(symb, emptyList())

}

fun executeNode(node : SymbolicNode) : Boolean{

    println("Crowbar  : starting symbolic execution....")
    val pit = nextPITStrategy()
    pit.execute(node)

    if(verbosity >= Verbosity.V) {
        println("Crowbar-v: symbolic execution tree:")
        println(node.debugString(0))
    }

    if(!node.finishedExecution()){
        System.err.println("could not finish symbolic execution")
        println(node.debugString(0))
        exitProcess(-1)
    }

    println("Crowbar  : closing open branches....")
    var closed = true
    for(l in node.collectLeaves()){
        if(l is LogicNode){
            if(verbosity >= Verbosity.V) println("Crowbar-v: "+ deupdatify(l.formula).prettyPrint())
            closed = closed && l.evaluate()
            if(verbosity >= Verbosity.V) println("Crowbar-v: verified? ${l.evaluate()}")
        } else {
            System.err.println("Crowbar-v: static analysis nodes not supported")
            exitProcess(-1)
        }
    }

    return closed
}