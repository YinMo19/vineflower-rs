package body

class BodySubject {
    fun equal(a: Any, b: Any): Boolean = a == b
    fun identical(a: Any, b: Any): Boolean = a === b
    fun elvis(a: String?, b: String): String = a ?: b
    fun template(a: String, b: Int): String = "value=$a + ${b + 1}"
    fun classOf(): kotlin.reflect.KClass<String> = String::class
    fun bits(a: Int, b: Int): Int = (a and b).inv() shl 2
    fun safeCast(a: Any): String? = a as? String
    fun branch(a: Int, b: Int): Int = if (a > b) a else b
    fun catching(a: String): Int = try { a.toInt() } catch (e: IllegalArgumentException) { -1 }
    fun select(a: Int): Int = when (a) { 1, 2 -> 3; 4 -> 5; else -> 6 }
    fun range(a: Int): Int {
        var result = 0
        for (i in 1..a) { result += i }
        return result
    }
    fun firstIndex(a: IntArray, value: Int): Int {
        var i = 0
        while (i < a.size) {
            if (a[i] == value) return i
            i++
        }
        return -1
    }
    fun iterate(a: IntArray): Int {
        var result = 0
        for (i in a) { result += i }
        return result
    }
    fun arrays(a: Int): IntArray = intArrayOf(a, 2)
    fun matrix(a: Int): Array<IntArray> = arrayOf(intArrayOf(a, 2))
}

class Receiver(var number: Int) {
    infix fun times(value: Int): Int = number * value
}

class Callers {
    fun call(receiver: Receiver, value: Int): Int {
        receiver.number = value
        return receiver.number + (receiver times value)
    }

    fun invoke(function: (Int, Int) -> Int, a: Int, b: Int): Int = function(a, b)
}
