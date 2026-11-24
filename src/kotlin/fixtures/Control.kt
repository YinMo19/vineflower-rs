// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.
package parity.kotlin

class Control {
    fun branch(flag: Boolean): Int = if (flag) 1 else 2

    fun early(value: Int): Int {
        if (value == 0) return 5
        return value * 2
    }

    fun shortCircuit(flag: Boolean, value: Int): Boolean = flag && 120 / value > 1

    fun wide(a: Long, b: Long): Boolean = a < b

    fun charEqual(value: Char): Boolean = value == 'Z'

    fun bit(value: Long, count: Int): Long = value ushr count

    fun directBoolean(a: Boolean, b: Boolean): Boolean = a xor b
}
