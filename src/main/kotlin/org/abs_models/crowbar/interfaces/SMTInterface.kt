package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Impl
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
    """.trimIndent()

fun generateSMT(formula: Formula) : String {
    val noUp = deupdatify(formula)
    val fields = noUp.getFields()
    val vars = noUp.getProgVars()
    val heaps = noUp.getHeapNews()
    var header = smtHeader
    header = fields.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Field)"})
    header = vars.fold(header, {acc, nx-> acc+"\n(declare-const ${nx.name} Int)"}) //hack: dtype goes here
    header = heaps.fold(header, {acc, nx-> "$acc\n(declare-fun $nx (Int) Int)" })
    fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> header += "\n (assert (not (= ${f1.name} ${f2.name})))" } }
    val pre = ((noUp as Not).left as Impl).left   //todo: hack
    val post = ((noUp as Not).left as Impl).right
    return """
    $header 
     (assert ${pre.toSMT(true)} ) 
    (assert ${Not(post).toSMT(true)}) 
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

fun evaluateSMT(formula: Formula) : Boolean {
    val smtRep = generateSMT(formula)
    if(verbosity >= Verbosity.VV) println("crowbar-v: \n$smtRep")
    return evaluateSMT(smtRep)
}