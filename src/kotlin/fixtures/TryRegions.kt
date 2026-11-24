// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.
package parity.kotlin

class TryRegions {
    fun divide(value: Int): Int = try {
        100 / value
    } catch (failure: ArithmeticException) {
        println(failure)
        -1
    }

    fun divideAndClean(value: Int): Int = try {
        100 / value
    } catch (failure: ArithmeticException) {
        println(failure)
        -1
    } finally {
        println("cleanup")
    }

    fun returnAndClean(value: Int): Int {
        try {
            return 100 / value
        } finally {
            println("cleanup")
        }
    }

    fun cleanupThenTail(value: Int) {
        try {
            println(value)
        } finally {
            println("cleanup")
        }
        println("tail")
    }
}
