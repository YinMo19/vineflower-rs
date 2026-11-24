// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.
package parity.kotlin

data class Defaults(val title: String = "hello", var count: Int = 7, val active: Boolean = true) {
    fun amount(base: Int = 3, scale: Int = 2): Int = base * scale
    fun indirect(base: Int, amount: Int = base * 2): Int = amount
}

fun withDefaults(required: Int, first: Long = 4L, second: Long = first): Long = first + second

class UnsupportedDefaults(val title: String = System.getProperty("user.name"))
