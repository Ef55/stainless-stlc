import stainless.lang._
import stainless.collection._
import stainless.annotation._
import scala.collection.immutable.Range.BigInt.apply

object ListProperties {

  @opaque @pure
  def insertionIndexing[T](l1: List[T], l2: List[T], elem: T, k: BigInt): Unit = {
    require(k < l1.size + l2.size)
    require(k >= l1.size)
    l1 match{
      case Nil() => ()
      case Cons(x, ls1) =>
        insertionIndexing(ls1, l2, elem, k - 1)
    }
  }.ensuring((l1 ++ (elem :: l2))(k + 1) == (l1 ++ l2)(k))

  @opaque @pure
  def concatSecondIndexing[T](l1: List[T], l2: List[T], k: BigInt): Unit = {
    require(k >= l1.size)
    require(k < l1.size + l2.size)
    l1 match{
      case Nil() => ()
      case Cons(x, ls1) => 
        concatSecondIndexing(ls1, l2, k - 1)
    } 
  }.ensuring((l1 ++ l2)(k) == l2(k - l1.size))

  //Uses the previous thm
  @opaque @pure
  def concatFirstIndexing[T](l1: List[T], l2: List[T], k: BigInt): Unit = {
    require(k < l1.size)
    require(k >= 0)

    ListSpecs.reverseIndex((l1 ++ l2), l1.size + l2.size - k - 1)
    ListSpecs.reverseAppend(l1, l2)
    concatSecondIndexing(l2.reverse, l1.reverse, l1.size + l2.size - k - 1)
    ListSpecs.reverseIndex(l1, l1.size - k - 1)
    () //Unit required here for the return type
  }.ensuring((l1 ++ l2)(k) == l1(k))

  @opaque @pure
  def concatFilter[T](@induct l1: List[T], l2: List[T], p: T => Boolean): Unit = {
  }.ensuring(l1.filter(p) ++ l2.filter(p) == (l1 ++ l2).filter(p))

  @opaque @pure
  def mergeFilter[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
  }.ensuring(l.filter(p1).filter(p2) == l.filter(x => p1(x) && p2(x)))

  @opaque @pure
  def filterCommutative[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
  }.ensuring(l.filter(p1).filter(p2) == l.filter(p2).filter(p1))

}

object BigIntListProperties{

  @opaque @pure
  def filterLeGe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ <= a) == l.filter(a >= _))

  @opaque @pure
  def filterGeLe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ >= a) == l.filter(a <= _))

  @opaque @pure
  def filterLtGt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ < a) == l.filter(a > _))

  @opaque @pure
  def filterGtLt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ > a) == l.filter(a < _))

  @opaque @pure
  def filterLtLe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ < a) == l.filter(_ <= a - 1))

  @opaque @pure
  def filterGtGe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ > a) == l.filter(_ >= a + 1))

  @opaque @pure
  def filterLeLt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ <= a) == l.filter(_ < a + 1))

  @opaque @pure
  def filterGeGt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ >= a) == l.filter(_ > a - 1))

  @opaque @pure
  def filterGeTwice(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.filter(_ >= a).filter(_ >= b) == 
    (if a >= b then
      l.filter(_ >= a)
    else
      l.filter(_ >= b)))

  @opaque @pure
  def filterLeTwice(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.filter(_ <= a).filter(_ <= b) == 
    (if a <= b then
      l.filter(_ <= a)
    else
      l.filter(_ <= b)))

  @opaque @pure
  def mapAddSub(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.map(_ + -a) == l.map(_ - a))

  @opaque @pure
  def mapAddComm(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.map(_ + a) == l.map(a + _))

  @opaque @pure
  def filterMapAddLe(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ <= b) == l.filter(_ <= b - a).map(_ + a))

  @opaque @pure
  def filterMapAddLt(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ < b) == l.filter(_ < b - a).map(_ + a))

  @opaque @pure
  def filterMapAddGe(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ >= b) == l.filter(_ >= b - a).map(_ + a))

  @opaque @pure
  def filterMapAddGt(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ > b) == l.filter(_ > b - a).map(_ + a))

  def filterSplitGeLt(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.filter(x => a <= x && x < b) == l.filter(a <= _).filter(_ < b))

}

object OptionProperties {
  
  @opaque @pure
  def equalityImpliesDefined[T](defOpt: Option[T], otherOpt: Option[T]): Unit = {
    require(defOpt.isDefined)
    require(defOpt == otherOpt)
  }.ensuring(otherOpt.isDefined)
}