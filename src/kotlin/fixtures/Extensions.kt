package parity.kotlin

class Extensions {
    class Point(val x: Int, val y: Int, val label: String)

    val x: Int get() = 12

    fun Point.dot(other: Point): Int = this.x * other.x + this.y * other.y

    fun Extensions.own(other: Extensions): Int = this.x + other.x

    fun Long.shift(bits: Int, delta: Long): Long = (this shl bits) + delta
}

fun Double.offset(delta: Double): Double = this - delta

fun Extensions.Point.describe(other: Extensions.Point): String = other.label

fun String.echo(other: String): String = this

fun String?.echoNullable(other: String?): String? = this
