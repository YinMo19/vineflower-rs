package classlambda

class Target(private val base: Int) {
    fun plus(value: Int): Int = base + value
}

fun twice(value: Int): Int = 2 * value

class References {
    fun bound(target: Target): (Int) -> Int = target::plus
    fun unbound(): (Target, Int) -> Int = Target::plus
    fun constructor(): (Int) -> Target = ::Target
    fun topLevel(): (Int) -> Int = ::twice
}

class ClassSubject {
    fun singleton(): (Int) -> Int = { it + 1 }
    fun capture(seed: Long): (Int) -> Long = { value -> value + seed }
    fun suspended(): suspend (Int) -> Int = { it + 1 }
}

class Host {
    companion object Named {
        @JvmField
        val INSTANCE = Host()
    }
}

class CompanionRead {
    fun reference(): Host = Host.INSTANCE
}
