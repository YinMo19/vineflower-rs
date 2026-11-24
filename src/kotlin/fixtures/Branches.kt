// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.
package parity.kotlin

class Branches {
    fun lookup(key: Int): String = when (key) {
        -20 -> "left"
        7, 1024 -> "right"
        else -> "center"
    }

    fun table(key: Int) {
        when (key) {
            1 -> println("one")
            2, 3 -> println("two or three")
            else -> println("default")
        }
    }

    fun assigned(key: Int) {
        val text = when (key) {
            1 -> "one"
            2, 3, 5 -> "some prime"
            else -> "anything else"
        }
        println(text)
    }

    fun typed(value: Any?) {
        when (value) {
            7 -> println("seven")
            null -> println("nothing")
            is String -> println("string")
            !is Long -> println("not long")
            else -> println("long")
        }
    }
}
