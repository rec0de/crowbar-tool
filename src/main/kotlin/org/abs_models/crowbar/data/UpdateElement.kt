package org.abs_models.crowbar.data

interface UpdateElement: LogicElement {
    fun assigns(v : ProgVar) : Boolean
    override fun toSMT(isInForm : Boolean) : String = throw Exception("Updates are not translatable to SMT-LIB")
}
object EmptyUpdate : UpdateElement {
    override fun prettyPrint(): String {
        return "empty"
    }
    override fun assigns(v : ProgVar) : Boolean = false
    override fun getFields() : Set<Field> = emptySet()
    override fun getProgVars() : Set<ProgVar> = emptySet()
    override fun getHeapNews() : Set<String> =  emptySet()
}
data class ChainUpdate(val left : UpdateElement, val right: UpdateElement) : UpdateElement {
    override fun prettyPrint(): String {
        return left.prettyPrint()+ "}{"+right.prettyPrint()
    }
    override fun assigns(v : ProgVar) : Boolean = left.assigns(v) || right.assigns(v)
    override fun getFields() : Set<Field> = left.getFields()+right.getFields()
    override fun getProgVars() : Set<ProgVar> = left.getProgVars()+right.getProgVars()
    override fun getHeapNews() : Set<String> = left.getHeapNews()+right.getHeapNews()
}
data class ElementaryUpdate(val lhs : ProgVar, val rhs : Term) : UpdateElement {
    override fun prettyPrint(): String {
        return lhs.prettyPrint() + " := "+rhs.prettyPrint()
    }
    override fun assigns(v : ProgVar) : Boolean = lhs == v
    override fun getFields() : Set<Field> = rhs.getFields()
    override fun getProgVars() : Set<ProgVar> = setOf(lhs)+rhs.getProgVars()
    override fun getHeapNews() : Set<String> = rhs.getHeapNews()
}