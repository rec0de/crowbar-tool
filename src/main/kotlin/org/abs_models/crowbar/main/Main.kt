package org.abs_models.crowbar.main

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.groups.mutuallyExclusiveOptions
import com.github.ajalt.clikt.parameters.groups.required
import com.github.ajalt.clikt.parameters.groups.single
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.choice
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.path
import com.github.ajalt.clikt.parameters.types.restrictTo
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.True
import org.abs_models.crowbar.types.PostInvType
import org.abs_models.crowbar.types.RegAccType
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.InterfaceDecl
import org.abs_models.frontend.ast.MethodSig
import org.abs_models.frontend.ast.Model
import java.nio.file.Paths

enum class Verbosity { SILENT, NORMAL, V, VV, VVV }

var tmpPath = "/tmp/"
var smtPath  = "z3"
var verbosity = Verbosity.NORMAL

//todo: this is for development purposes only and will be removed once the translation is automatic
object FunctionRepos{
    private val known : Map<String, String> = mapOf(Pair("fib","(define-fun-rec fib ((n Int)) Int\n" +
    "    (ite (<= n 2) 1\n" +
    "           (+ (fib (- n 1)) (fib (- n 2)))))"))
    fun isKnown(str: String) = known.containsKey(str)
    fun get(str: String) = known.getValue(str)
    override fun toString() = known.values.fold("",{acc, it -> "$acc \n $it"})
}

//todo: once allowedTypes is not needed anymore, the repository needs to be passed to fewer places
data class Repository(private val model : Model?,
                      val allowedTypes : MutableList<String> =  mutableListOf("ABS.StdLib.Int",
                                                                              "ABS.StdLib.Bool",
                                                                              "ABS.StdLib.Unit",
                                                                              "ABS.StdLib.Fut<ABS.StdLib.Int>",
                                                                              "ABS.StdLib.Fut<ABS.StdLib.Bool>",
                                                                              "ABS.StdLib.Fut<ABS.StdLib.Unit>"),
                      val classReqs : MutableMap<String,Pair<Formula,ClassDecl>> = mutableMapOf(),
                      val methodReqs : MutableMap<String,Pair<Formula,MethodSig>> = mutableMapOf(),
                      val methodEnss : MutableMap<String,Pair<Formula,MethodSig>> = mutableMapOf()){
    init{
        if(model != null) {
            populateClassReqs(model)
            populateMethodReqs(model)
            populateAllowedTypes(model)
        }
    }
    private fun populateClassReqs(model: Model) {
        for(moduleDecl in model.moduleDecls) {
            if(moduleDecl.name.startsWith("ABS.")) continue
            for (decl in moduleDecl.decls) {
                if (decl is ClassDecl) {
                    val spec = extractSpec(decl,"Requires")
                    classReqs[decl.name] = Pair(spec,decl) //todo: use fully qualified name here
                }
            }
        }
    }
    private fun populateMethodReqs(model: Model) {
        for(moduleDecl in model.moduleDecls) {
            if(moduleDecl.name.startsWith("ABS.")) continue
            for (decl in moduleDecl.decls) {
                if (decl is InterfaceDecl) {
                    for (mDecl in decl.allMethodSigs) {
                        val spec = extractSpec(mDecl, "Requires")
                        val spec2 = extractSpec(mDecl, "Ensures")
                        methodReqs[decl.qualifiedName+"."+mDecl.name] = Pair(spec, mDecl)
                        methodEnss[decl.qualifiedName+"."+mDecl.name] = Pair(spec2, mDecl)
                    }
                }
                if(decl is ClassDecl){
                    for(mImpl in decl.methods){
                        val iUse = getDeclaration(mImpl.methodSig,mImpl.contextDecl as ClassDecl)
                        if(iUse == null){
                            methodReqs[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(True, mImpl.methodSig)
                        } else {
                            val spec = extractSpec(iUse.allMethodSigs.first { it.matches(mImpl.methodSig) }, "Requires")
                            methodReqs[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(spec, mImpl.methodSig)

                            val spec2 = extractSpec(iUse.allMethodSigs.first { it.matches(mImpl.methodSig) }, "Ensures")
                            methodEnss[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(spec2, mImpl.methodSig)
                        }
                    }
                }
            }
        }
    }

    private fun populateAllowedTypes(model: Model) {
        for(moduleDecl in model.moduleDecls){
            if(moduleDecl.name.startsWith("ABS.")) continue
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
    object FullOption : CrowOption()
}

class Main : CliktCommand() {
    private val filePath by argument(help="path to ABS file").path().multiple()

    //the casts in convert and validate are added to make the type checker happy
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
        option(help="Verifies the main block of the model").switch("--main" to CrowOption.MainBlockOption),
        option(help="Verifies the full model").switch("--full" to CrowOption.FullOption)
    ).single().required()

    private val tmp        by   option("--tmp","-t",help="path to a directory used to store the .smt files").path().default(Paths.get(tmpPath))
    private val smtCmd     by   option("--smt","-s",help="command to start SMT solver").default(smtPath)
    private val verbose    by   option("--verbose", "-v",help="verbosity output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)
    private val deductType by   option("--deduct","-d",help="Used Deductive Type").choice("PostInv","RegAcc").convert { when(it){"PostInv" -> PostInvType::class; "RegAcc" -> RegAccType::class; else -> throw Exception(); } }.default(PostInvType::class)

    override fun run() {

        tmpPath = "$tmp/"
        smtPath = smtCmd
        verbosity = Verbosity.values()[verbose]
        val (model, repos) = load(filePath)

        //todo: check all VarDecls and Field Decls here
        //      no 'result', no 'heap', no '_f' suffix

        when(target){
            is  CrowOption.FullOption -> {
                var finalClose = true
                for( classDecl in model.extractAllClasses() ) {
                    val totalClosed = classDecl.executeAll(repos, deductType)
                    output("Crowbar  : Verification result ${classDecl.qualifiedName}: $totalClosed", Verbosity.SILENT)
                    finalClose = finalClose && totalClosed
                }
                val node = model.exctractMainNode(deductType)
                val closed = executeNode(node, repos, deductType)
                finalClose = finalClose && closed
                output("Crowbar  : Verification of main: $closed", Verbosity.SILENT)
                output("Crowbar  : Final verification result: $finalClose", Verbosity.SILENT)
            }
            is  CrowOption.MainBlockOption -> {
                val node = model.exctractMainNode(deductType)
                val closed = executeNode(node, repos, deductType)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
            is  CrowOption.AllClassOption -> {
                val tt = target as  CrowOption.AllClassOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1], repos)
                val totalClosed = classDecl.executeAll(repos, deductType)
                output("Crowbar  : Final verification result: $totalClosed", Verbosity.SILENT)
            }
            is  CrowOption.MethodOption -> {
                val tt = target as  CrowOption.MethodOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1], repos)
                val node = classDecl.extractMethodNode(deductType, targetPath[2],repos)
                val closed = executeNode(node, repos, deductType)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
            is  CrowOption.InitOption -> {
                val tt = target as  CrowOption.InitOption
                val targetPath = tt.path.split(".")
                val classDecl = model.extractClassDecl(targetPath[0], targetPath[1], repos)
                val node = classDecl.extractInitialNode(deductType)
                val closed = executeNode(node, repos, deductType)
                output("Crowbar  : Verification result: $closed", Verbosity.SILENT)
            }
        }
    }


}

fun main(args:Array<String>) = Main().main(args)