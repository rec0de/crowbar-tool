package org.abs_models.crowbar.main

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.path
import com.github.ajalt.clikt.parameters.types.restrictTo
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.crowbar.interfaces.translateABSStmtToSymStmt
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.PostInvariantPair
import org.abs_models.crowbar.types.nextPITStrategy
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.Model
import java.io.File
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.system.exitProcess

enum class Verbosity { NORMAL, V, VV }

var tmpPath = "/tmp/"
var z3Path  = "z3"
var verbosity = Verbosity.NORMAL

val allowedTypes = listOf<String>("ABS.StdLib.Int","ABS.StdLib.Fut<ABS.StdLib.Int>")
fun isAllowedType(input : String) : Boolean = allowedTypes.contains(input)

class Main : CliktCommand() {
    private val filePath by argument(help="path to ABS file").path()
    private val target   by argument(help="method under verification in the format <module>.<class>.<method>")
    private val tmp      by   option("--tmp","-t",help="path to a directory used to store the .z3 files").path().default(Paths.get(tmpPath))
    private val z3Cmd    by   option("--z3","-z3",help="command to start z3").default(z3Path)
    private val verbose  by   option("--verbose", "-v",help="verbosity output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)

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
        var body = if(initBlock!= null) appendStmt(translateABSStmtToSymStmt(initBlock),ReturnStmt(unitExpr())) else ReturnStmt(unitExpr())
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

    override fun run() {

        tmpPath = "$tmp/"
        z3Path = z3Cmd
        verbosity = Verbosity.values()[verbose]

        val model = load(filePath)

        val targetPath = target.split(".")
        if(targetPath.size < 2 || targetPath.size > 3){
            System.err.println("$target is not a fully qualified method or class name!")
            exitProcess(-1)
        }

        val classDecl = extractClassDecl(targetPath[0],targetPath[1], model)
        if(targetPath.size == 3) {
            val node = extractMethodNode(targetPath[2], classDecl)
            val closed = executeNode(node)
            println("Crowbar  : Verification result: $closed")
        } else if (targetPath.size == 2){
            val iNode = extractInitialNode(classDecl)
            var totalClosed = executeNode(iNode)
            println("Crowbar  : Verification <init>: $totalClosed")

            for(m in classDecl.methods){
                val node = extractMethodNode(m.methodSig.name, classDecl)
                val closed = executeNode(node)
                println("Crowbar  : Verification ${m.methodSig.name}: $closed")
                totalClosed = totalClosed && closed
            }
            println("Crowbar  : final verification result: $totalClosed")
        }

    }

}

fun main(args:Array<String>) = Main().main(args)