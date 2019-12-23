package org.abs_models.crowbar.main

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.path
import com.github.ajalt.clikt.parameters.types.restrictTo
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.interfaces.translateABSStmtToSymStmt
import org.abs_models.crowbar.data.deupdatify
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.PostInvariantPair
import org.abs_models.crowbar.types.nextPITStrategy
import org.abs_models.frontend.ast.*
import java.io.File
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
    private val verbose  by   option("--verbose", "-v",help="verbose output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)

    override fun run() {

        println("Crowbar  : loading files....")
        tmpPath = "$tmp/"
        z3Path = z3Cmd
        verbosity = Verbosity.values()[verbose]
        val targetPath = target.split(".")
        if(targetPath.size != 3){
            System.err.println("$target is not a fully qualified method name!")
            exitProcess(-1)
        }
        val input = File(filePath.toString())
        if(!input.exists()) {
            System.err.println("file not found: $filePath")
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
        val moduleDecl = model.moduleDecls.firstOrNull { it.name == targetPath[0] }
        if(moduleDecl == null){
            System.err.println("module not found: ${targetPath[0]}")
            exitProcess(-1)
        }
        val classDecl : ClassDecl? = moduleDecl.decls.firstOrNull { it is ClassDecl && it.name == targetPath[1] } as ClassDecl?
        if(classDecl == null){
            System.err.println("class not found: ${targetPath[0]}.${targetPath[1]}")
            exitProcess(-1)
        }
        if(    classDecl.params.any { !isAllowedType(it.type.toString()) }
            || classDecl.fields.any { !isAllowedType(it.type.toString()) } ){
            System.err.println("fields with non-Int type not supported")
            exitProcess(-1)
        }
        val mDecl = classDecl.methods.firstOrNull { it.methodSig.name == targetPath[2] }
        if(mDecl == null){
            System.err.println("method not found: ${targetPath[0]}.${targetPath[1]}.${targetPath[2]}")
            exitProcess(-1)
        }
        if(mDecl.methodSig.params.any { !isAllowedType(it.type.toString()) }){
            System.err.println("parameters with non-Int type not supported")
            exitProcess(-1)
        }

        println("Crowbar  : loading specification....")
        var symb : SymbolicState? = null
        var objInv : Formula? = null
        var metpost : Formula?  = null
        var body : Stmt? = null
        try {
            objInv  = extractSpec(classDecl, "ObjInv")
            metpost = extractSpec(mDecl,"Ensures")
            val st = mDecl.block
            body = translateABSStmtToSymStmt(st)
        }catch (e : Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        if(verbosity >= Verbosity.V) {
            println("Crowbar-v: method post-condition: ${metpost.prettyPrint()}")
            println("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
        }

        println("Crowbar  : starting symbolic execution....")
        symb = SymbolicState(objInv, EmptyUpdate, Modality(body, PostInvariantPair(metpost, objInv)))
        val pit = nextPITStrategy()
        val node = SymbolicNode(symb, emptyList())
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

        println("Crowbar  : Verification result: $closed")
    }

}

fun main(args:Array<String>) = Main().main(args)