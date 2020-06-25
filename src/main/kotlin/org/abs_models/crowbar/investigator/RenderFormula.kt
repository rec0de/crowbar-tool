package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.And
import org.abs_models.crowbar.data.False
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.FormulaAbstractVar
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Heap
import org.abs_models.crowbar.data.Impl
import org.abs_models.crowbar.data.Not
import org.abs_models.crowbar.data.Or
import org.abs_models.crowbar.data.Predicate
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.Term
import org.abs_models.crowbar.data.True
import org.abs_models.crowbar.data.binaries

fun renderFormula(f: Formula, m: Map<String, String>): String {
    return when (f) {
        is True         -> "true"
        is False        -> "false"
        is Not          -> "!${renderFormula(f.left, m)}"
        is Or           -> "(${renderFormula(f.left, m)}) \\/ (${renderFormula(f.right, m)})"
        is And          -> "(${renderFormula(f.left, m)}) /\\ (${renderFormula(f.right, m)})"
        is Impl         -> "(${renderFormula(f.left, m)}) -> (${renderFormula(f.right, m)})"
        is Predicate    -> renderPredicate(f, m)
        is FormulaAbstractVar -> f.name
        else               -> throw Exception("Cannot render formula: ${f.prettyPrint()}")
    }
}

fun renderTerm(t: Term, m: Map<String, String>): String {
    return when (t) {
        is Function     -> renderFunction(t, m)
        is Field        -> "this.${t.name}"
        is ProgVar      -> if (m.containsKey(t.name)) m[t.name]!! else t.name
        is Heap         -> "heap"
        else            -> throw Exception("Cannot render term: ${t.prettyPrint()}")
    }
}

fun renderPredicate(p: Predicate, m: Map<String, String>): String {
    return when {
        p.params.isEmpty() -> p.name
        binaries.contains(p.name) && p.params.size == 2 -> renderTerm(p.params[0], m) + p.name + renderTerm(p.params[1], m)
        else -> p.name + "(" + p.params.map { t -> renderTerm(t, m) }.joinToString(", ") + ")"
    }
}

fun renderFunction(f: Function, m: Map<String, String>): String {
    return when {
        f.params.isEmpty() -> f.name
        binaries.contains(f.name) && f.params.size == 2 -> renderTerm(f.params[0], m) + f.name + renderTerm(f.params[1], m)
        else -> f.name + "(" + f.params.map { t -> renderTerm(t, m) }.joinToString(", ") + ")"
    }
}
