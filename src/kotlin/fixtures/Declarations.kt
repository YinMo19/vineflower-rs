// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.
package parity.kotlin

const val answer: Int = 42
var visits: Int = 3
val note: String = "cost \$5"
fun greet(): String = "hi"

class Declaration(val id: Int, var active: Boolean) {
    val label: String = "ok"
    fun twice(x: Int): Int = x * 2
}

interface Contract<T : Any> {
    val getter: Int.(String) -> Unit
    fun project(value: T?): List<T?>
}

class Unsupported {
    fun loop(limit: Int): Int {
        var sum = 0
        var index = 0
        while (index < limit) {
            sum += index
            index++
        }
        return sum
    }
}
