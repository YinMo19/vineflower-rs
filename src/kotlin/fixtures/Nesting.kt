// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.
package parity.kotlin

class Nesting {
    class Payload(val value: Int) {
        fun doubled(value: Int): Int = value * 2
    }

    object Settings {
        val enabled: Boolean = true
        @JvmStatic fun valueOrDefault(value: Int = 3): Int = value
    }

    companion object Factory {
        @JvmStatic fun size(value: Long): Long = value + 1L
    }
}
