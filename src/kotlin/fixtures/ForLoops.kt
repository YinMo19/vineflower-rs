// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.
package parity.kotlin

class ForLoops {
    fun list(words: List<String>) {
        for (word in words) println(word)
    }

    fun numbers(values: Iterable<Int>) {
        for (value in values) println(value + 1)
    }

    fun untilBound(end: Int) {
        for (index in 0 until end) println(index)
    }
}
