package indy

class IndySubject {
    fun simple(): (Int) -> Int = { it + 1 }

    fun capture(seed: Long, factor: Int): (Int) -> Long =
        { value -> (seed + value) * factor }

    fun multiple(seed: Int): (Int) -> Int = fun(value: Int): Int {
        if (value < 0) return seed
        if (value == 7) return -value
        println(value)
        return value + seed
    }

    fun empty(): () -> Unit = { println("text") }
}
