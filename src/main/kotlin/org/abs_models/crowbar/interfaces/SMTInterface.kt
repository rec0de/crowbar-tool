package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Not
import org.abs_models.crowbar.data.deupdatify
import org.abs_models.crowbar.main.Verbosity
import org.abs_models.crowbar.main.tmpPath
import org.abs_models.crowbar.main.verbosity
import java.io.File
import java.util.concurrent.TimeUnit

val smtHeader = """
    (set-logic ALL)
    (define-sort Field () Int)
    (define-sort MHeap () (Array Field Int))
    (declare-const heap MHeap)
    (declare-fun   anon (MHeap) MHeap)
    (declare-fun   read (Int) Int)
    (define-fun iOr((x Int) (y Int)) Int
        (ite (or (= x 1) (= y 1)) 1 0))
    (define-fun iAnd((x Int) (y Int)) Int
        (ite (and (= x 1) (= y 1)) 1 0))
    (define-fun iNot((x Int)) Int
        (ite (= x 1) 0 1))
    (define-fun iLt((x Int) (y Int)) Int
        (ite (< x y) 1 0))
    (define-fun iLeq((x Int) (y Int)) Int
        (ite (<= x y) 1 0))
    (define-fun iGt((x Int) (y Int)) Int
        (ite (> x y) 1 0))
    (define-fun iGeq((x Int) (y Int)) Int
        (ite (>= x y) 1 0))
    (define-fun iEq((x Int) (y Int)) Int
        (ite (= x y) 1 0))
    (define-fun iNeq((x Int) (y Int)) Int
        (ite (= x y) 0 1))
    (declare-const Unit Int)
    (assert (= Unit 0))
    """.trimIndent()

fun generateSMT(ante : Formula, succ: Formula) : String {
    val pre = deupdatify(ante)
    val post = deupdatify(Not(succ))
    val fields = pre.getFields() + post.getFields()
    val vars = pre.getProgVars() + post.getProgVars()
    val heaps = pre.getHeapNews() + post.getHeapNews()
    var header = smtHeader
    header = fields.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Field)"})
    header = vars.fold(header, {acc, nx-> acc+"\n(declare-const ${nx.name} Int)"}) //hack: dtype goes here
    header = heaps.fold(header, {acc, nx-> "$acc\n(declare-fun $nx (${"Int ".repeat(nx.split("_")[1].toInt())}) Int)" })
    fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> header += "\n (assert (not (= ${f1.name} ${f2.name})))" } }

    return """
    $header 
    (assert ${pre.toSMT(true)} ) 
    (assert ${post.toSMT(true)}) 
    (check-sat)
    (exit)
    """.trimIndent()
}

/* https://stackoverflow.com/questions/35421699 */
fun String.runCommand(
        workingDir: File = File("."),
        timeoutAmount: Long = 60,
        timeoutUnit: TimeUnit = TimeUnit.SECONDS
): String? = try {
    ProcessBuilder(split("\\s".toRegex()))
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start().apply { waitFor(timeoutAmount, timeoutUnit) }
            .inputStream.bufferedReader().readText()
} catch (e: java.io.IOException) {
    e.printStackTrace()
    null
}

fun evaluateSMT(smtRep : String) : Boolean {
    val path = "${tmpPath}out.smt2"
    File(path).writeText(smtRep)
    val res = "${org.abs_models.crowbar.main.smtPath} $path".runCommand()
    return res != null && res.trim() == "unsat"
}

fun evaluateSMT(ante: Formula, succ: Formula) : Boolean {
    val smtRep = generateSMT(ante, succ)
    if(verbosity >= Verbosity.VV) println("crowbar-v: \n$smtRep")
    return evaluateSMT(smtRep)
}