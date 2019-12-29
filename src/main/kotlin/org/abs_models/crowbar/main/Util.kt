package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.ReturnStmt
import org.abs_models.crowbar.data.SkipStmt
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

fun output(text : String, level : Verbosity = Verbosity.NORMAL){
    if(verbosity >= level)
        println(text)
}

fun load(path : Path) : Pair<Model,Repository> {

    output("Crowbar  : loading files....")
    val input = File(path.toString())
    if(!input.exists()) {
        System.err.println("file not found: $path")
        exitProcess(-1)
    }

    output("Crowbar  : loading ABS model....")
    val model = try {
        org.abs_models.frontend.parser.Main().parse(listOf(input))
    } catch (e : Exception) {
        e.printStackTrace()
        System.err.println("error during parsing, aborting")
        exitProcess(-1)
    }
    val repos = Repository()
    repos.populateAllowedTypes(model)
    repos.populateClassReqs(model)
    return Pair(model, repos)
}



fun Model.extractClassDecl(moduleName : String, className : String, repos : Repository) : ClassDecl {
    val moduleDecl = moduleDecls.firstOrNull { it.name == moduleName }
    if(moduleDecl == null){
        System.err.println("module not found: $moduleName")
        exitProcess(-1)
    }
    val classDecl : ClassDecl? = moduleDecl.decls.firstOrNull { it is ClassDecl && it.name == className } as ClassDecl?
    if(classDecl == null){
        System.err.println("class not found: ${moduleName}.${className}")
        exitProcess(-1)
    }

    if(    classDecl.params.any { !repos.isAllowedType(it.type.toString()) }
        || classDecl.fields.any { !repos.isAllowedType(it.type.toString()) } ){
        System.err.println("fields with non-Int type not supported")
        exitProcess(-1)
    }
    return classDecl
}

fun Model.exctractMainNode() : SymbolicNode{
    if(!model.hasMainBlock()){
        System.err.println("model has no main block!")
        exitProcess(-1)
    }

    val v = appendStmt(translateABSStmtToSymStmt(this.mainBlock), SkipStmt)
    return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(v, PostInvariantPair(True, True))), emptyList())
}

fun ClassDecl.extractInitialNode() : SymbolicNode {

    val initBlock = this.initBlock
    var body = if(initBlock!= null) appendStmt(translateABSStmtToSymStmt(initBlock), ReturnStmt(unitExpr())) else ReturnStmt(unitExpr())
    for (fieldDecl in this.fields){
        if(fieldDecl.hasInitExp()){
            val nextBody = AssignStmt(Field(fieldDecl.name), translateABSExpToSymExpr(fieldDecl.initExp))
            body = SeqStmt(nextBody,body)
        }
    }

    output("Crowbar  : loading specification....")
    val objInv: Formula?
    val objPre: Formula?
    try {
        objInv = extractSpec(this, "ObjInv")
        objPre = extractSpec(this, "Requires")
    } catch (e: Exception) {
        e.printStackTrace()
        System.err.println("error during translation, aborting")
        exitProcess(-1)
    }
    if (verbosity >= Verbosity.V) {
        output("Crowbar-v: object precondition: ${objPre.prettyPrint()}")
        output("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
    }
    val symb = SymbolicState(objPre, EmptyUpdate, Modality(body, PostInvariantPair(True, objInv)))
    return SymbolicNode(symb, emptyList())
}
fun ClassDecl.extractMethodNode(name : String, repos: Repository) : SymbolicNode {

    if(name == "<init>")
        return this.extractInitialNode()
    val mDecl = this.methods.firstOrNull { it.methodSig.name == name }
    if (mDecl == null) {
        System.err.println("method not found: ${this.qualifiedName}.${name}")
        exitProcess(-1)
    }
    if (mDecl.methodSig.params.any { !repos.isAllowedType(it.type.toString()) }) {
        System.err.println("parameters with non-Int type not supported")
        exitProcess(-1)
    }

    output("Crowbar  : loading specification....")
    val symb: SymbolicState?
    val objInv: Formula?
    val metpost: Formula?
    val body: Stmt?
    try {
        objInv = extractSpec(this, "ObjInv")
        metpost = extractSpec(mDecl, "Ensures")
        val st = mDecl.block
        body = translateABSStmtToSymStmt(st)
    } catch (e: Exception) {
        e.printStackTrace()
        System.err.println("error during translation, aborting")
        exitProcess(-1)
    }
    output("Crowbar-v: method post-condition: ${metpost.prettyPrint()}", Verbosity.V)
    output("Crowbar-v: object invariant: ${objInv.prettyPrint()}",Verbosity.V)

    symb = SymbolicState(objInv, EmptyUpdate, Modality(body, PostInvariantPair(metpost, objInv)))
    return SymbolicNode(symb, emptyList())

}

fun executeNode(node : SymbolicNode, repos: Repository) : Boolean{

    output("Crowbar  : starting symbolic execution....")
    val pit = nextPITStrategy(repos)
    pit.execute(node)

    output("Crowbar-v: symbolic execution tree:",Verbosity.V)
    output(node.debugString(0),Verbosity.V)

    if(!node.finishedExecution()){
        System.err.println("could not finish symbolic execution")
        println(node.debugString(0))
        exitProcess(-1)
    }

    output("Crowbar  : closing open branches....")
    var closed = true
    for(l in node.collectLeaves()){
        if(l is LogicNode){
            output("Crowbar-v: "+ deupdatify(l.formula).prettyPrint(), Verbosity.V)
            closed = closed && l.evaluate()
            output("Crowbar-v: verified? ${l.evaluate()}", Verbosity.V)
        } else {
            System.err.println("Crowbar-v: static analysis nodes not supported")
            exitProcess(-1)
        }
    }

    return closed
}

fun ClassDecl.executeAll(repos: Repository): Boolean{
    val iNode = extractInitialNode()
    var totalClosed = executeNode(iNode, repos)
    output("Crowbar  : Verification <init>: $totalClosed")

    for(m in methods){
        val node = extractMethodNode(m.methodSig.name, repos)
        val closed = executeNode(node, repos)
        output("Crowbar  : Verification ${m.methodSig.name}: $closed \n")
        totalClosed = totalClosed && closed
    }
    return totalClosed
}