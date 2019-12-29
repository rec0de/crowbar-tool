package org.abs_models.crowbar.main

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.path
import com.github.ajalt.clikt.parameters.types.restrictTo
import org.abs_models.crowbar.data.Formula
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.InterfaceDecl
import org.abs_models.frontend.ast.Model
import java.nio.file.Paths
import kotlin.system.exitProcess

enum class Verbosity { SILENT, NORMAL, V, VV }

var tmpPath = "/tmp/"
var z3Path  = "z3"
var verbosity = Verbosity.NORMAL

//todo: once allowedTypes is not needed anymore, the repository needs to be passed to fewer places
data class Repository(val allowedTypes : MutableList<String> =  mutableListOf("ABS.StdLib.Int","ABS.StdLib.Fut<ABS.StdLib.Int>"),
                      val classReqs : MutableMap<String,Pair<Formula,ClassDecl>> = mutableMapOf()){
    fun populateClassReqs(model: Model) {
        for(moduleDecl in model.moduleDecls) {
            for (decl in moduleDecl.decls) {
                if (decl is ClassDecl) {
                    val spec = extractSpec(decl,"Requires")
                    classReqs[decl.name] = Pair(spec,decl)
                }
            }
        }
    }

    fun populateAllowedTypes(model: Model) {
        for(moduleDecl in model.moduleDecls){
            for(decl in moduleDecl.decls){
                if(decl is InterfaceDecl){
                    allowedTypes += decl.qualifiedName
                    allowedTypes += decl.name
                }
            }
        }
    }
    fun isAllowedType(input : String) : Boolean = allowedTypes.contains(input)
}

/*val allowedTypes =)
val classReqs = mutableMapOf<String,Pair<Formula,ClassDecl>>()*/

class Main : CliktCommand() {
    private val filePath by argument(help="path to ABS file").path()
    private val target   by argument(help="method under verification in the format <module>.<class>.<method> or class under verification in the format <module>.<class> or main block (just main)")
    private val tmp      by   option("--tmp","-t",help="path to a directory used to store the .z3 files").path().default(Paths.get(tmpPath))
    private val z3Cmd    by   option("--z3","-z3",help="command to start z3").default(z3Path)
    private val verbose  by   option("--verbose", "-v",help="verbosity output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)


    override fun run() {

        tmpPath = "$tmp/"
        z3Path = z3Cmd
        verbosity = Verbosity.values()[verbose]
        val (model, repos) = load(filePath)

        val targetPath = target.split(".")
        if(targetPath.isEmpty() || targetPath.size > 3){
            System.err.println("$target is not \"main\" or a fully qualified method or class name!")
            exitProcess(-1)
        }
        if(targetPath[0] == "main"){
            val node = model.exctractMainNode()
            val closed = executeNode(node, repos)
            output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
        }else {
            val classDecl = model.extractClassDecl(targetPath[0], targetPath[1], repos)

            if (targetPath.size == 2) {
                val totalClosed = classDecl.executeAll(repos)
                output("Crowbar  : Final verification result: $totalClosed", Verbosity.SILENT)
            } else if (targetPath.size == 3) {
                val node = classDecl.extractMethodNode(targetPath[2],repos)
                val closed = executeNode(node, repos)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
        }

    }


}

fun main(args:Array<String>) = Main().main(args)