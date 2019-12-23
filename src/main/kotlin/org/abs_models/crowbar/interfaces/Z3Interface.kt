package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.data.deupdatify
import java.io.File
import java.util.concurrent.TimeUnit

val z3Header = """
    (define-sort MHeap () (Array Field Int))
    (declare-const heap MHeap)
    (declare-fun   anon (MHeap) MHeap)
    (declare-fun   read (Int) Int)
    """.trimIndent()

fun generateZ3(formula: Formula) : String {
    val noUp = deupdatify(formula)
    val fields = noUp.getFields()
    val vars = noUp.getProgVars()
    var header = z3Header
    if(fields.isNotEmpty()) header = "(declare-datatypes () ((Field ${fields.fold("", { acc, nx-> acc +" " +nx.name})})))\n$header"
    header = vars.fold(header, {acc, nx-> acc+"\n(declare-const ${nx.name} Int)"})
    return """
    $header 
    (assert ${noUp.toZ3()}) 
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

fun evaluateZ3(z3Rep : String) : Boolean {
    val path = "${tmpPath}z3.out"
    File(path).writeText(z3Rep)
    val res = "$z3Path $path".runCommand()
    return res != null && res.trim() == "unsat"
}

fun evaluateZ3(formula: Formula) : Boolean {
    val z3Rep = generateZ3(formula)
    if(verbosity >= Verbosity.VV) println("crowbar-v: \n$z3Rep")
    return evaluateZ3(z3Rep)
}