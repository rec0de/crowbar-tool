package org.abs_models.crowbar.main

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.groups.mutuallyExclusiveOptions
import com.github.ajalt.clikt.parameters.groups.required
import com.github.ajalt.clikt.parameters.groups.single
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.path
import com.github.ajalt.clikt.parameters.types.restrictTo
import org.abs_models.crowbar.data.Formula
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.InterfaceDecl
import org.abs_models.frontend.ast.Model
import java.nio.file.Paths

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

sealed class CrowOption{
data class MethodOption(val path : String) : CrowOption()
data class InitOption(val path : String) : CrowOption()
data class AllClassOption(val path : String) : CrowOption()
object MainBlockOption : CrowOption()
}

class Main : CliktCommand() {
    private val filePath by argument(help="path to ABS file").path().multiple()

    //the casts is convert and validate are added to make the type checker happy
    private val target : CrowOption by mutuallyExclusiveOptions<CrowOption>(
        option("--method","-m",help="Verifies a single method <module>.<class.<method>")
                .convert { CrowOption.MethodOption(it) as CrowOption }
                .validate { require((it as CrowOption.MethodOption).path.split(".").size == 3,
                    lazyMessage = {"invalid fully qualified method name $it"}) },
        option("--init","-i",help="Verifies the initial block of <module>.<class>")
                .convert {  CrowOption.InitOption(it) as CrowOption  }
                .validate { require((it as CrowOption.InitOption).path.split(".").size == 2,
                    lazyMessage = {"invalid fully qualified class name $it"}) },
        option("--class","-c",help="Verifies the initial block and all methods of <module>.<class>")
                .convert {  CrowOption.AllClassOption(it) as CrowOption }
                .validate { require((it as CrowOption.AllClassOption).path.split(".").size == 2,
                                    lazyMessage = {"invalid fully qualified class name $it"}) },
        option(help="Verifies the main block of the model").switch("--main" to CrowOption.MainBlockOption)
    ).single().required()

    private val tmp      by   option("--tmp","-t",help="path to a directory used to store the .z3 files").path().default(Paths.get(tmpPath))
    private val z3Cmd    by   option("--z3","-z3",help="command to start z3").default(z3Path)
    private val verbose  by   option("--verbose", "-v",help="verbosity output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)

    override fun run() {

        tmpPath = "$tmp/"
        z3Path = z3Cmd
        verbosity = Verbosity.values()[verbose]
        val (model, repos) = load(filePath)

        when(target){
            is  CrowOption.MainBlockOption -> {
                val node = model.exctractMainNode()
                val closed = executeNode(node, repos)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
            is  CrowOption.AllClassOption -> {
                val tt = target as  CrowOption.AllClassOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1], repos)
                val totalClosed = classDecl.executeAll(repos)
                output("Crowbar  : Final verification result: $totalClosed", Verbosity.SILENT)
            }
            is  CrowOption.MethodOption -> {
                val tt = target as  CrowOption.MethodOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1], repos)
                val node = classDecl.extractMethodNode(targetPath[2],repos)
                val closed = executeNode(node, repos)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
            is  CrowOption.InitOption -> {
                val tt = target as  CrowOption.InitOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1], repos)
                val node = classDecl.extractInitialNode()
                val closed = executeNode(node, repos)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
        }
    }


}

fun main(args:Array<String>) = Main().main(args)