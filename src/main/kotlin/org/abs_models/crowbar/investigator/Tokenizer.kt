package org.abs_models.crowbar.investigator

object Tokenizer {
   
    private val whitespace = Regex("\\s")
    private val numeric = Regex("(\\-)?\\d+")
    private val allowedId = Regex("[a-zA-Z0-9\\-_!=]")

    fun tokenize(code: String): List<Token> {

        val tokens = mutableListOf<Token>()
        var i = 0

        // Extract single token until end of input reached
        while (i < code.length) {

            val char = code[i].toString()
            i += 1

            when {
                char == "(" -> tokens.add(LParen())
                char == ")" -> tokens.add(RParen())
                char matches whitespace -> {}
                char matches allowedId -> {
                    var identifier = char
                    while (i < code.length && allowedId matches code[i].toString()) {
                        identifier += code[i]
                        i += 1
                    }

                    if (numeric matches identifier)
                        tokens.add(ConcreteValue(identifier.toInt()))
                    else
                        tokens.add(Identifier(identifier))
                }
                else -> throw Exception("Unknown character at position $i: '$char'")
            }
        }

        return tokens
    }
}

abstract class Token(val spelling: String) {
    override fun toString() = spelling

    override fun equals(other: Any?): Boolean {
        return if (other != null && other is Token)
            toString() == other.toString()
        else
            false
    }

    override fun hashCode() = toString().hashCode()
}

class LParen() : Token("(")
class RParen() : Token(")")
class Identifier(spelling: String) : Token(spelling)
class ConcreteValue(val value: Int) : Token(value.toString())
