import stainless.lang._
import stainless.collection._
import stainless.annotation._
import scala.collection.immutable.Range.BigInt.apply

object ARS {

  type ARSStep[T, R] = (R, T, T, Boolean)

  extension [T, R](s: ARSStep[T, R]) {
    def unfold: R = s._1
    def type1: T = s._2
    def type2: T = s._3
    def isSound: Boolean = s._4
    def inverse: ARSStep[T, ARSInverseStep[T, R]] = {
      ARSInverseStepClass(s).toARSStep
    }.ensuring(res => s.isSound ==> (res.isSound && res.type1 == s.type2 && res.type2 == s.type1))
  }

  sealed trait ARSInverseStep[T, R]{
    def type1: T = this match
      case ARSInverseStepClass(s) => s.type2
    
    def type2: T = this match
      case ARSInverseStepClass(s) => s.type1
    
    def isSound: Boolean = this match
      case ARSInverseStepClass(s) => s.isSound
    
    def baseStep: ARSStep[T, R] = this match
      case ARSInverseStepClass(s) => s
    
    def toARSStep: ARSStep[T, ARSInverseStep[T, R]] = {
      (this, type1, type2, isSound)
    }.ensuring(res => baseStep.isSound ==> (res.isSound && res.type2 == baseStep.type1 && res.type1 == baseStep.type2))
  }

  case class ARSInverseStepClass[T, R](s: ARSStep[T, R]) extends ARSInverseStep[T, R]

  sealed trait ARSSymmStep[T, R]{
    def type1: T = this match
      case ARSBaseStepClass(s) => s.type1
      case ARSSymmStepClass(s) => s.inverse.type1
    
    def type2: T = this match
      case ARSBaseStepClass(s) => s.type2
      case ARSSymmStepClass(s) => s.inverse.type2
    
    def isSound: Boolean = this match
      case ARSBaseStepClass(s) => s.isSound
      case ARSSymmStepClass(s) => s.inverse.isSound

    def inverse: ARSSymmStep[T, R] = {
      this match
        case ARSBaseStepClass(s) => ARSSymmStepClass(s)
        case ARSSymmStepClass(s) => ARSBaseStepClass(s)
      
    }.ensuring(res => (isSound) ==> res.isSound && res.type1 == type2 && res.type2 == type1)
    
    def toARSStep: ARSStep[T, ARSSymmStep[T, R]] = {
      (this, type1, type2, isSound)
    }.ensuring(_.isWellFormed)
  }

  case class ARSBaseStepClass[T, R](s: ARSStep[T, R]) extends ARSSymmStep[T, R]
  case class ARSSymmStepClass[T, R](s: ARSStep[T, R]) extends ARSSymmStep[T, R]

  extension [T, R] (s: ARSStep[T, ARSSymmStep[T, R]]) {
    def isWellFormed: Boolean = s.type1 == s.unfold.type1 && s.type2 == s.unfold.type2 && s.isSound == s.unfold.isSound
    def isValid: Boolean = s.isSound && s.isWellFormed
  }

  extension [T, R] (ms: ARSKFoldComposition[T, ARSSymmStep[T, R]]) {
    def isWellFormed: Boolean =
      ms match
        case ARSIdentity(t) => true
        case ARSComposition(h, t) => h.isWellFormed && t.isWellFormed  
    def isValid: Boolean = ms.isSound && ms.isWellFormed
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

    def toReflTrans: ARSEquivalence[T, R] = {
      decreases(size)
      this match
        case ARSIdentity(t) => ARSReflexivity[T, R](t)
        case ARSComposition(h, t) => ARSTransitivity[T, R](ARSBaseRelation(h), t.toReflTrans)
    }.ensuring(res => isSound ==> (res.isSound && type1 == res.type1 && type2 == res.type2 && res.isReflTrans))

    def inverse: ARSKFoldComposition[T, ARSInverseStep[T, R]] = {
      this match
        case ARSIdentity(t) => ARSIdentity[T, ARSInverseStep[T, R]](t)
        case ARSComposition(h, t) => 
          t.inverse match
            case ARSIdentity(_) => ARS1Fold(h.inverse)
            case ARSComposition(h2, t2) => ARSComposition(h2, t2.concat(ARS1Fold(h.inverse))) 
    }.ensuring(res => isSound ==> (res.isSound && res.type1 == type2 && res.type2 == type1))
  }

  case class ARSIdentity[T, R](t: T) extends ARSKFoldComposition[T, R]
  case class ARSComposition[T, R](h: ARSStep[T, R], t: ARSKFoldComposition[T, R]) extends ARSKFoldComposition[T, R]

  def ARS1Fold[T, R](s: ARSStep[T, R]): ARSKFoldComposition[T, R] = {
    ARSComposition[T, R](s, ARSIdentity(s.type2))
  }.ensuring(res => s.isSound ==> (res.isSound && res.type1 == s.type1 && res.type2 == s.type2))

  sealed trait ARSEquivalence[T, R]{
    def size: BigInt = {
      this match
        case ARSReflexivity(t) => BigInt(1)
        case ARSTransitivity(r1, r2) => r1.size + r2.size
        case ARSSymmetry(r) => r.size + 1
        case ARSBaseRelation(r) => BigInt(1) 
    }.ensuring(_ > BigInt(0))
    
    def type1: T = 
      decreases(size)
      this match
        case ARSReflexivity(t) => t
        case ARSBaseRelation(r) => r.type1
        case ARSTransitivity(r1, r2) => r1.type1
        case ARSSymmetry(r) => r.type2 

    def type2: T = 
      decreases(size)
      this match
        case ARSReflexivity(t) => t
        case ARSBaseRelation(r) => r.type2
        case ARSTransitivity(r1, r2) => r2.type2
        case ARSSymmetry(r) => r.type1

    def isSound: Boolean = 
      decreases(size)
      this match
        case ARSReflexivity(t) => true
        case ARSBaseRelation(r) => r.isSound
        case ARSTransitivity(r1, r2) => r1.isSound && r2.isSound && r1.type2 == r2.type1
        case ARSSymmetry(r) => r.isSound

    def isReflTrans: Boolean = 
      this match
        case ARSReflexivity(t) => true
        case ARSBaseRelation(r) => true
        case ARSTransitivity(r1, r2) => r1.isReflTrans && r2.isReflTrans
        case ARSSymmetry(r) => false 

    def toKFold: ARSKFoldComposition[T, R] = {
      decreases(size)
      this match
        case ARSReflexivity(t) => ARSIdentity[T, R](t)
        case ARSBaseRelation(r) => ARS1Fold(r)
        case ARSTransitivity(r1, r2) => r1.toKFold.concat(r2.toKFold)
        case ARSSymmetry(r) => r.toKFold  
        
    }.ensuring(res => (isSound && isReflTrans) ==> (res.isSound && type1 == res.type1 && type2 == res.type2))
      
  }

  case class ARSReflexivity[T, R](t: T) extends ARSEquivalence[T, R]
  case class ARSBaseRelation[T, R](r: ARSStep[T, R]) extends ARSEquivalence[T, R]
  case class ARSTransitivity[T, R](r1: ARSEquivalence[T, R], r2: ARSEquivalence[T, R]) extends ARSEquivalence[T, R]
  case class ARSSymmetry[T, R](r: ARSEquivalence[T, R]) extends ARSEquivalence[T, R]

}

object ARSProperties{

  import ARS._

  def kFoldInverseToReflTrans[T, R](ms: ARSKFoldComposition[T, R]): ARSEquivalence[T, R] = {
    require(ms.isSound)
    ARSSymmetry(ms.toReflTrans)
  }.ensuring(res => res.isSound && res.type1 == ms.type2 && res.type2 == ms.type1)


  def reductionPreserveEquivalence[T, R](ms1: ARSKFoldComposition[T, R], ms2: ARSKFoldComposition[T, R], eq: ARSEquivalence[T, R]) = {
    require(ms1.isSound)
    require(ms2.isSound)
    require(eq.isSound)
    require(ms1.type1 == eq.type1)
    require(ms2.type1 == eq.type2)
    ARSTransitivity(kFoldInverseToReflTrans(ms1), ARSTransitivity(eq, ms2.toReflTrans))
  }.ensuring(res => res.type1 == ms1.type2 && res.type2 == ms2.type2 && res.isSound)

  def reductionImpliesEquivalence[T, R](ms1: ARSKFoldComposition[T, R], ms2: ARSKFoldComposition[T, R], eq: ARSEquivalence[T, R]) = {
    require(ms1.isSound)
    require(ms2.isSound)
    require(eq.isSound)
    require(ms1.type2 == eq.type1)
    require(ms2.type2 == eq.type2)
    ARSTransitivity(ms1.toReflTrans, ARSTransitivity(eq, kFoldInverseToReflTrans(ms2)))
  }.ensuring(res => res.type1 == ms1.type1 && res.type2 == ms2.type1 && res.isSound)

  def reduceSameFormEquivalent[T, R](ms1: ARSKFoldComposition[T, R], ms2: ARSKFoldComposition[T, R]): ARSEquivalence[T, R] = {
    require(ms1.isSound)
    require(ms2.isSound)
    require(ms1.type2 == ms2.type2)
    reductionImpliesEquivalence(ms1, ms2, ARSReflexivity(ms1.type2))
  }.ensuring(res => res.type1 == ms1.type1 && res.type2 == ms2.type1 && res.isSound)

  def symmClosureToEquivalence[T, R](ms: ARSKFoldComposition[T, ARSSymmStep[T, R]]): ARSEquivalence[T, R] = {
    require(ms.isWellFormed && ms.isSound)
    ms match
      case ARSIdentity(t) => ARSReflexivity(t)
      case ARSComposition(h, t) => 
        val eq: ARSEquivalence[T, R] = 
          h.unfold match
            case ARSBaseStepClass(s) => ARSBaseRelation[T, R](s)
            case ARSSymmStepClass(s) => ARSSymmetry[T, R](ARSBaseRelation[T, R](s))
        ARSTransitivity(eq, symmClosureToEquivalence(t))
  }.ensuring(res => res.isSound && res.type1 == ms.type1 && res.type2 == ms.type2)

  def concatWellFormed[T, R](@induct s1: ARSKFoldComposition[T, ARSSymmStep[T, R]], s2: ARSKFoldComposition[T, ARSSymmStep[T, R]]): Unit = {
    require(s1.isWellFormed)
    require(s2.isWellFormed)
  }.ensuring(_ => s1.concat(s2).isWellFormed)

  def symmClosureInverse[T, R](ms: ARSKFoldComposition[T, ARSSymmStep[T, R]]): ARSKFoldComposition[T, ARSSymmStep[T, R]] = {
    require(ms.isSound && ms.isWellFormed)
    val res = ms match
      case ARSIdentity(t) => ARSIdentity(t)
      case ARSComposition(h, t) => 
        concatWellFormed(symmClosureInverse(t), ARS1Fold(h.unfold.inverse.toARSStep))
        symmClosureInverse(t).concat(ARS1Fold(h.unfold.inverse.toARSStep))
    res
  }.ensuring(res => res.isSound && res.type1 == ms.type2 && res.type2 == ms.type1 && res.isWellFormed)


  def equivalenceToSymmClosure[T, R](eq: ARSEquivalence[T, R]): ARSKFoldComposition[T, ARSSymmStep[T, R]] = {
    decreases(eq.size)
    require(eq.isSound)
    eq match
      case ARSReflexivity(t) => ARSIdentity[T, ARSSymmStep[T, R]](t)
      case ARSSymmetry(r) => 
        r match
          case ARSSymmetry(r2) => equivalenceToSymmClosure(r2)
          case ARSTransitivity(r1, r2) => 
            concatWellFormed(symmClosureInverse(equivalenceToSymmClosure(r2)), symmClosureInverse(equivalenceToSymmClosure(r1)))
            symmClosureInverse(equivalenceToSymmClosure(r2)).concat(symmClosureInverse(equivalenceToSymmClosure(r1)))
          case ARSReflexivity(t) => ARSIdentity[T, ARSSymmStep[T, R]](t)
          case ARSBaseRelation(r2) => ARS1Fold[T, ARSSymmStep[T, R]](ARSSymmStepClass[T, R](r2).toARSStep)
      case ARSTransitivity(r1, r2) => 
        concatWellFormed(equivalenceToSymmClosure(r1), equivalenceToSymmClosure(r2))
        equivalenceToSymmClosure(r1).concat(equivalenceToSymmClosure(r2))
      case ARSBaseRelation(r) => ARS1Fold[T, ARSSymmStep[T, R]](ARSBaseStepClass[T, R](r).toARSStep)
  }.ensuring(res => res.isWellFormed && res.type1 == eq.type1 && res.type2 == eq.type2 && res.isSound == eq.isSound)

}