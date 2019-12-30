package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.Formula
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
    """.trimIndent()

fun generateSMT(formula: Formula) : String {
    val noUp = deupdatify(formula)
    val fields = noUp.getFields()
    val vars = noUp.getProgVars()
    var header = smtHeader
    header = fields.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Field)"})
    header = vars.fold(header, {acc, nx-> acc+"\n(declare-const ${nx.name} Int)"})
    fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> header += "\n (assert (not (= ${f1.name} ${f2.name})))" } }
    return """
    $header 
    (assert ${noUp.toSMT()}) 
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