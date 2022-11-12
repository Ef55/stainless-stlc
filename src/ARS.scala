import stainless.lang._
import stainless.collection._
import stainless.annotation._

object ARS {

  type ARSStep[T, R] = (R, T, T, Boolean)

  extension [T, R](s: ARSStep[T, R]) {
    def type1: T = s._2
    def type2: T = s._3
    def isSound: Boolean = s._4
  }

  sealed trait ARSKFoldComposition[T, R]{
    def type1: T = this match
      case ARSIdentity(t) => t
      case ARSComposition(h, t) => h.type1

    def type2: T = this match
      case ARSIdentity(t) => t
      case ARSComposition(h, t) => t.type2

    def isSound: Boolean = this match
      case ARSIdentity(t) => true
      case ARSComposition(h, t) => h.isSound && t.isSound && h.type2 == t.type1

    def size: BigInt = {
      this match
        case ARSIdentity(t) => BigInt(0)
        case ARSComposition(h, t) => t.size + 1
    }.ensuring(_ >= BigInt(0))

    def concat(that: ARSKFoldComposition[T, R]): ARSKFoldComposition[T, R] = {
      this match
        case ARSIdentity(t) => that
        case ARSComposition(h, t) => ARSComposition(h, t.concat(that))
    }.ensuring(res => 
      (this.isSound && that.isSound && type2 == that.type1) ==> 
      (res.isSound && res.type1 == type1 && res.type2 == that.type2 && res.size == size + that.size)) 

    def toClosure: ARSTransReflClosure[T, R] = {
      this match
        case ARSIdentity(t) => ARSReflexivity[T, R](t)
        case ARSComposition(h, t) => ARSTransitivity[T, R](ARSBaseRelation(h), t.toClosure)
    }.ensuring(res => isSound ==> (res.isSound && type1 == res.type1 && type2 == res.type2))
  }

  case class ARSIdentity[T, R](t: T) extends ARSKFoldComposition[T, R]
  case class ARSComposition[T, R](h: ARSStep[T, R], t: ARSKFoldComposition[T, R]) extends ARSKFoldComposition[T, R]

  sealed trait ARSTransReflClosure[T, R]{
    def type1: T = this match
      case ARSReflexivity(t) => t
      case ARSBaseRelation(r) => r.type1
      case ARSTransitivity(r1, r2) => r1.type1

    def type2: T = this match
      case ARSReflexivity(t) => t
      case ARSBaseRelation(r) => r.type2
      case ARSTransitivity(r1, r2) => r2.type2

    def isSound: Boolean = this match
      case ARSReflexivity(t) => true
      case ARSBaseRelation(r) => r.isSound
      case ARSTransitivity(r1, r2) => r1.isSound && r2.isSound && r1.type2 == r2.type1

    def toKFold: ARSKFoldComposition[T, R] = {
      this match
        case ARSReflexivity(t) => ARSIdentity[T, R](t)
        case ARSBaseRelation(r) => ARSComposition[T, R](r, ARSIdentity[T, R](r.type2))
        case ARSTransitivity(r1, r2) => 
          r1.toKFold.concat(r2.toKFold)
    }.ensuring(res => isSound ==> (res.isSound && type1 == res.type1 && type2 == res.type2)) 
  }

  case class ARSReflexivity[T, R](t: T) extends ARSTransReflClosure[T, R]
  case class ARSBaseRelation[T, R](r: ARSStep[T, R]) extends ARSTransReflClosure[T, R]
  case class ARSTransitivity[T, R](r1: ARSTransReflClosure[T, R], r2: ARSTransReflClosure[T, R]) extends ARSTransReflClosure[T, R]

  

}