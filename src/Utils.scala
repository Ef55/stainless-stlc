import stainless.lang._
import stainless.collection._
import stainless.annotation._

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

  def mergeFilter[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
  }.ensuring(l.filter(p1).filter(p2) == l.filter(x => p1(x) && p2(x)))

  def filterCommutative[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
  }.ensuring(l.filter(p1).filter(p2) == l.filter(p2).filter(p1))

}

object BigIntListProperties{

  @opaque @pure
  def filterSubGe(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ - a).filter(_ >= b) == l.filter(_ >= b + a).map(_ - a))

}

object OptionProperties {
  
  @opaque @pure
  def equalityImpliesDefined[T](defOpt: Option[T], otherOpt: Option[T]): Unit = {
    require(defOpt.isDefined)
    require(defOpt == otherOpt)
  }.ensuring(otherOpt.isDefined)
}