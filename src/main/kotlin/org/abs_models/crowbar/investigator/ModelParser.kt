package org.abs_models.crowbar.investigator

class ModelParser(val tokens: MutableList<Token>) {
    companion object {
        fun parse(modelString: String): List<Function> {
            val tokens = Tokenizer.tokenize(modelString).toMutableList()

            if(tokens[0].toString() == "sat")
                tokens.removeAt(0)

            return ModelParser(tokens).parseModel()
        }
    }

    fun parseModel(): List<Function> {
        consume(LParen())
        consume(Identifier("model"))

        val model = mutableListOf<Function>()

        while (tokens[0] is LParen)
            model.add(parseDefinition())

        consume(RParen())

        return model
    }

    fun parseDefinition(): Function {
        consume(LParen())
        consume(Identifier("define-fun")) // Is this always true?

        val name = tokens[0].toString()
        consume()

        val args = parseArguments()
        val type = parseType()

        val value = parseValue(type)

        consume(RParen())

        return if (args.size == 0)
            Constant(name, type, value)
        else
            Function(name, type, args, value)
    }

    fun parseArguments(): List<TypedVariable> {
        val args = mutableListOf<TypedVariable>()
        consume(LParen())

        while (tokens[0] is LParen)
            args.add(parseTypedVariable())

        consume(RParen())
        return args
    }

    fun parseTypedVariable(): TypedVariable {
        consume(LParen())
        val name = tokens[0].toString()
        consume()
        val type = parseType()
        consume(RParen())

        return TypedVariable(type, name)
    }

    fun parseType(): Type {
        if (tokens[0] is LParen) {
            consume()
            consume(Identifier("Array"))
            consume(Identifier("Int"))
            consume(Identifier("Int"))
            consume(RParen())
            return Type.ARRAY
        } else {
            consume(Identifier("Int"))
            return Type.INT
        }
    }

    fun parseValue(expectedType: Type): Value {
        if (expectedType == Type.INT) {
            return Integer(parseIntExp())
        } else
            return parseArrayExp()
    }

    fun parseIntExp(): Int {
        if (tokens[0] is ConcreteValue) {
            val value = (tokens[0] as ConcreteValue).value
            consume()
            return value
        } else if (tokens[0] is LParen) {
            consume()
            val value: Int

            when (tokens[0].toString()) {
                "-" -> {
                    consume()
                    value = - parseIntExp()
                }
                else -> throw Exception("Expected integer expression function but got '${tokens[0]}'' at ${tokens.joinToString(" ")}")
            }
            consume(RParen())
            return value
        } else
            throw Exception("Expected concrete integer value but got '${tokens[0]}'' at ${tokens.joinToString(" ")}")
    }

    fun parseArrayExp(): Array {
        consume(LParen())
        val array: Array

        if(tokens[0] is LParen)
        	array = parseConstArray()
        else {
        	consume(Identifier("store"))
        	array = parseArrayExp()
        	val index = parseIntExp()
        	val value = parseIntExp()
        	array.map.put(index, value)
        }

        consume(RParen())
        return array
    }

    fun parseConstArray(): Array {
    	consume(LParen())
    	consume(Identifier("as"))
    	consume(Identifier("const"))
    	consume(LParen())
    	consume(Identifier("Array"))
    	consume(Identifier("Int"))
    	consume(Identifier("Int"))
    	consume(RParen())
    	consume(RParen())
    	val value = parseIntExp()
    	return Array(value)
    }

    private fun consume(expected: Token? = null) {
        if (tokens.size == 0)
            throw Exception("Expected token but got end of input")

        val got = tokens.removeAt(0)

        if (expected != null && got != expected)
            throw Exception("Expected '$expected' but got '$got' at ${tokens.joinToString(" ")}")
    }
}

open class Function(val name: String, val type: Type, val args: List<TypedVariable>, val value: Value) {
    override fun toString() = "Function '$name(${args.joinToString(", ")})' of type '$type' set to '$value'"
}

class Constant(name: String, type: Type, value: Value) : Function(name, type, listOf(), value) {
    override fun toString() = "Constant '$name' of type '$type' set to '$value'"
}

data class TypedVariable(val type: Type, val name: String) {
    override fun toString() = "$name: $type"
}

abstract class Value

class Array(val defaultValue: Int, val map: MutableMap<Int,Int> = mutableMapOf()) : Value() {
	fun getValue(index: Int) = if(map.contains(index)) map[index] else defaultValue

	override fun toString(): String {
		val entries = mutableListOf("default: $defaultValue")
		map.forEach {
			entries.add("${it.key}: ${it.value}")
		}

		return "[${entries.joinToString(", ")}]"
	}
}

class Integer(val value: Int) : Value() {
	override fun toString() = value.toString()
}

enum class Type() {
    INT, ARRAY, UNKNOWN
}
