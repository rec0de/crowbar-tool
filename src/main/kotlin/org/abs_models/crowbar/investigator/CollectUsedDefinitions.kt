package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.Term

fun collectUsedDefinitions(elem: Term): Set<String> {
    return when (elem) {
        is Function -> collectFromFunction(elem)
        is ProgVar -> setOf(elem.name)
        is Field -> setOf(elem.name)
        else -> throw Exception("Cannot collect used definitions from term: $elem")
    }
}

fun collectFromFunction(func: Function): Set<String> {
    val paramDefs = func.params.map { collectUsedDefinitions(it) }.flatten().toSet()
    return if (func.name.startsWith("f_")) paramDefs + func.name else paramDefs
}
