import stainless.lang._
import stainless.collection._
import stainless.annotation._
import scala.collection.immutable.Range.BigInt.apply

object ListProperties {

  @inlineOnce @opaque @pure
  def insertionIndexing[T](l1: List[T], l2: List[T], elem: T, k: BigInt): Unit = {
    decreases(l1)
    require(k < l1.size + l2.size)
    require(k >= l1.size)
    l1 match{
      case Nil() => ()
      case Cons(x, ls1) =>
        insertionIndexing(ls1, l2, elem, k - 1)
    }
  }.ensuring((l1 ++ (elem :: l2))(k + 1) == (l1 ++ l2)(k))

  @inlineOnce @opaque @pure
  def concatSecondIndexing[T](l1: List[T], l2: List[T], k: BigInt): Unit = {
    decreases(l1)
    require(k >= l1.size)
    require(k < l1.size + l2.size)
    l1 match{
      case Nil() => ()
      case Cons(x, ls1) => 
        concatSecondIndexing(ls1, l2, k - 1)
    } 
  }.ensuring((l1 ++ l2)(k) == l2(k - l1.size))

  //Uses the previous thm
  @inlineOnce @opaque @pure
  def concatFirstIndexing[T](l1: List[T], l2: List[T], k: BigInt): Unit = {
    require(k < l1.size)
    require(k >= 0)

    ListSpecs.reverseIndex((l1 ++ l2), l1.size + l2.size - k - 1)
    ListSpecs.reverseAppend(l1, l2)
    concatSecondIndexing(l2.reverse, l1.reverse, l1.size + l2.size - k - 1)
    ListSpecs.reverseIndex(l1, l1.size - k - 1)
    () //Unit required here for the return type
  }.ensuring((l1 ++ l2)(k) == l1(k))

  @inlineOnce @opaque @pure
  def concatFilter[T](@induct l1: List[T], l2: List[T], p: T => Boolean): Unit = {
  }.ensuring(l1.filter(p) ++ l2.filter(p) == (l1 ++ l2).filter(p))

  @inlineOnce @opaque @pure
  def concatForall[T](@induct l1: List[T], l2: List[T], p: T => Boolean): Unit = {
    require(l1.forall(p))
    require(l2.forall(p))
  }.ensuring((l1 ++ l2).forall(p))

  @inlineOnce @opaque @pure
  def concatContains[T](@induct l1: List[T], l2: List[T], e: T): Unit = {
  }.ensuring(l1.contains(e) || l2.contains(e) == (l1 ++ l2).contains(e))

  @inlineOnce @opaque @pure
  def mapContains[S, T](l: List[S], f: S => T, e: S): Unit = {
    decreases(l)
    require(l.contains(e))
    l match
      case Nil() => ()
      case Cons(h, t) => 
        if h == e then
          ()
        else
          mapContains(t, f, e)
  }.ensuring(l.map(f).contains(f(e)))

  @inlineOnce @opaque @pure
  def mergeFilter[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
  }.ensuring(l.filter(p1).filter(p2) == l.filter(x => p1(x) && p2(x)))

  @inlineOnce @opaque @pure
  def filterCommutative[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
  }.ensuring(l.filter(p1).filter(p2) == l.filter(p2).filter(p1))

  @inlineOnce @opaque @inlineOnce @pure
  def consConcat[T](e: T, @induct l1: List[T], l2: List[T]): Unit = {
  }.ensuring(Cons(e, l1 ++ l2) == Cons(e, l1) ++ l2)

}

object BigIntListProperties{

  @inlineOnce @opaque @pure
  def filterLeGe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ <= a) == l.filter(a >= _))

  @inlineOnce @opaque @pure
  def filterGeLe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ >= a) == l.filter(a <= _))

  @inlineOnce @opaque @pure
  def filterLtGt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ < a) == l.filter(a > _))

  @inlineOnce @opaque @pure
  def filterGtLt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ > a) == l.filter(a < _))

  @inlineOnce @opaque @pure
  def filterLtLe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ < a) == l.filter(_ <= a - 1))

  @inlineOnce @opaque @pure
  def filterGtGe(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ > a) == l.filter(_ >= a + 1))

  @inlineOnce @opaque @pure
  def filterLeLt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ <= a) == l.filter(_ < a + 1))

  @inlineOnce @opaque @pure
  def filterGeGt(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.filter(_ >= a) == l.filter(_ > a - 1))

  @inlineOnce @opaque @pure
  def filterGeTwice(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.filter(_ >= a).filter(_ >= b) == 
    (if a >= b then
      l.filter(_ >= a)
    else
      l.filter(_ >= b)))

  @inlineOnce @opaque @pure
  def filterLeTwice(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.filter(_ <= a).filter(_ <= b) == 
    (if a <= b then
      l.filter(_ <= a)
    else
      l.filter(_ <= b)))

  @inlineOnce @opaque @pure
  def mapAddSub(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.map(_ + -a) == l.map(_ - a))

  @inlineOnce @opaque @pure
  def mapAddComm(@induct l: List[BigInt], a: BigInt): Unit = {
  }.ensuring(l.map(_ + a) == l.map(a + _))

  @inlineOnce @opaque @pure
  def filterMapAddLe(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ <= b) == l.filter(_ <= b - a).map(_ + a))

  @inlineOnce @opaque @pure
  def filterMapAddLt(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ < b) == l.filter(_ < b - a).map(_ + a))

  @inlineOnce @opaque @pure
  def filterMapAddGe(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ >= b) == l.filter(_ >= b - a).map(_ + a))

  @inlineOnce @opaque @pure
  def filterMapAddGt(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.map(_ + a).filter(_ > b) == l.filter(_ > b - a).map(_ + a))

  @inlineOnce @opaque @pure
  def filterSplitGeLt(@induct l: List[BigInt], a: BigInt, b: BigInt): Unit = {
  }.ensuring(l.filter(x => a <= x && x < b) == l.filter(a <= _).filter(_ < b))

}

def Unreachable: Nothing =
  require(false)
  ???

def max(a: BigInt, b: BigInt): BigInt = if a > b then a else b


object OptionProperties {
  
  @inlineOnce @opaque @pure
  def equalityImpliesDefined[T](defOpt: Option[T], otherOpt: Option[T]): Unit = {
    require(defOpt.isDefined)
    require(defOpt == otherOpt)
  }.ensuring(otherOpt.isDefined)

  @inlineOnce @opaque @pure
  def someIsDefined[T](inner: T): Unit = {
  }.ensuring(Some(inner).isDefined)
}