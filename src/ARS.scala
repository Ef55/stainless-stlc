/**
  *  References: 
  *    - [TRAT] Term Rewriting and All That, Franz Baader and Tobias Nipkow, 1998, Cambridge University Press
  * 
  *  Framework to reason about Abstract Rewriting Systems (also called Abstract Reduction Systems or ARS) (TRAT Chapter 2)
  *  ARS is formally defined as a pair (T, ->) where T is the set of terms and -> is a binary relation on T x T called reduction.
  *  Throughout the file the set of terms will be denoted by the generic type T and the reduction by the generic type R.
  * 
  *  Moreover the file gives a constructive proof that r* = ⋃ rⁱ
  */

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import scala.annotation._

object ARS {

  /**
   * ARSStep[T, R] represents the reduction of an ARS.
   * It is meant to be a trait with 3 abstract methods, if t1 -> t2: ARSStep[T, R] then
   *  - t1 returns t1 (second element of the tuple)
   *  - t2 returns t2 (third element of the tuple)
   *  - isSound returns whether (t1, t2) ∈ -> (fourth element of the tuple)
   * 
   * ! In practice though, bounded type operators and not yet supported in Stainless.
   * ! Therefore, ARSStep[T, R] cannot be a trait. Instead it is defined as a wrapper (a tuple) that adds 3 methods
   * ! around R, the type that really represent the reduction relation.
   * ! The drawback of this approach is that when instantiating the generic types, one has always to check
   * ! that the methods in the tuple are the same as the one of R. This check will often appear throughtout
   * ! the project and will be called well formedness. If a step is well formed and sound then it is called valid.
   * ! This shaky solution should be replaced as soon as more advanced features will be added to Stainless. 
   */ 
  type ARSStep[T, R] = (R, T, T, Boolean)

  extension [T, R](s: ARSStep[T, R]) {
    @pure
    def t1: T = s._2
    @pure
    def t2: T = s._3
    @pure
    def isSound: Boolean = s._4

    /**
      * Extracts the original object inside the wrapper
      */
    @pure
    def unfold: R = s._1

    /**
      * If t1 -> t2, this functions returns t2 <- t1
      */
    @pure
    def inverse: ARSStep[T, ARSInverseStep[T, R]] = {
      ARSInverseStepClass(s).toARSStep
    }.ensuring(res => res.isSound == s.isSound && res.t1 == s.t2 && res.t2 == s.t1 && res.isWellFormed)
  }

  /**
    * Inverse reduction of an ARS (TRAR Definition 2.1.1)
    * It has only one case class constructor that builds t1 <- t2 if it is given t2 -> t1
    * 
    * ! Good software practices would suggest that ARSInverseStep extends ARSStep, but this is not possible
    * ! due to the way ARSStep was defined.
    */
  sealed trait ARSInverseStep[T, R]{
    @pure
    def t1: T = this match
      case ARSInverseStepClass(s) => s.t2
    
    @pure
    def t2: T = this match
      case ARSInverseStepClass(s) => s.t1
    
    @pure
    def isSound: Boolean = this match
      case ARSInverseStepClass(s) => s.isSound
    
    /**
     * Returns t2 -> t1
     */
    @pure
    def baseStep: ARSStep[T, R] = this match
      case ARSInverseStepClass(s) => s
    
    /**
      * Returns the reduction associated to <-
      * 
      * ! This method is needed as ARSInverseStep does not extend ARSStep.
      * 
      * * Basic property: the result is well formed
      */
    @pure //shoould not be opaque
    def toARSStep: ARSStep[T, ARSInverseStep[T, R]] = {
      (this, t1, t2, isSound)
    }.ensuring(_.isWellFormed)
  }

  case class ARSInverseStepClass[T, R](s: ARSStep[T, R]) extends ARSInverseStep[T, R]

  extension [T, R] (s: ARSStep[T, ARSInverseStep[T, R]]) {
    @targetName("inverseStepWellFormedness") @pure
    def isWellFormed: Boolean = s.t1 == s.unfold.t1 && s.t2 == s.unfold.t2 && s.isSound == s.unfold.isSound
    @targetName("inverseStepValidity") @pure
    def isValid: Boolean = s.isSound && s.isWellFormed
  }

  /**
    * Symmetric closure of a reduction (TRAR Definition 2.1.1)
    * The trait has two case class constructors as t1 <-> t2 if either t1 -> t2 or t2 -> t1
    * 
    * ! Good software practices would suggest that ARSSymmStep extends ARSStep, but this is not possible
    * ! due to the way ARSStep was defined.
    */
  sealed trait ARSSymmStep[T, R]{
    @pure
    def t1: T = this match
      case ARSBaseStepClass(s) => s.t1
      case ARSSymmStepClass(s) => s.t2
    
    @pure
    def t2: T = this match
      case ARSBaseStepClass(s) => s.t2
      case ARSSymmStepClass(s) => s.t1
    
    @pure
    def isSound: Boolean = this match
      case ARSBaseStepClass(s) => s.isSound
      case ARSSymmStepClass(s) => s.isSound

    /**
     * Returns t2 <-> t1
     * 
     * * Basic property: If t1 <-> t2 then t2 <-> t1
     */
    @pure
    def inverse: ARSSymmStep[T, R] = {
      this match
        case ARSBaseStepClass(s) => ARSSymmStepClass(s)
        case ARSSymmStepClass(s) => ARSBaseStepClass(s)
      
    }.ensuring(res => isSound == res.isSound && res.t1 == t2 && res.t2 == t1)
    
    /**
     * Returns the reduction associated to <->
     * 
     * ! This method is needed as ARSSymmStep does not extend ARSStep.
     * 
     * * Basic property: the result is well formed
     */
    @pure //should not be opaque
    def toARSStep: ARSStep[T, ARSSymmStep[T, R]] = {
      (this, t1, t2, isSound)
    }.ensuring(_.isWellFormed)
  }

  case class ARSBaseStepClass[T, R](s: ARSStep[T, R]) extends ARSSymmStep[T, R]
  case class ARSSymmStepClass[T, R](s: ARSStep[T, R]) extends ARSSymmStep[T, R]

  extension [T, R] (s: ARSStep[T, ARSSymmStep[T, R]]) {
    @pure
    def isWellFormed: Boolean = s.t1 == s.unfold.t1 && s.t2 == s.unfold.t2 && s.isSound == s.unfold.isSound
    @pure
    def isValid: Boolean = s.isSound && s.isWellFormed
  }

  /**
    * Trait representing the multistep reduction relation of an ARS (TRAR Chapter 2.1)
    * 
    * Formally we define the k-fold composition of a reduction, noted -k-> as
    * the composition of the reduction done k times. By convention -0-> is the
    * identity (also called diagonal) relation.
    * Therefore we represent it with two cases classes:
    *  - ARSIdentity which represents -0->
    *  - ARSComposition which represents the composition between -> and -k->
    * 
    * A way to represent multistep reduction to define it as the union over all k of
    * k-fold compositions. We prove further that this definition is equivalent to the
    * reflexive and transitive closure of the reduction noted ->* (cf ARSEquivalence).
    */
  sealed trait ARSKFoldComposition[T, R]{
    @pure
    def t1: T = this match
      case ARSIdentity(t) => t
      case ARSComposition(h, t) => h.t1

    @pure
    def t2: T = 
      decreases(size)
      this match
        case ARSIdentity(t) => t
        case ARSComposition(h, t) => t.t2

    /**
      * A sequence of step is sound if each of the step is sound and if for all i < k the end type of the i-th step is the same as
      * the start type of i+1-th step
      */
    @pure
    def isSound: Boolean = 
      decreases(size)
      this match
        case ARSIdentity(t) => true
        case ARSComposition(h, t) => h.isSound && t.isSound && h.t2 == t.t1
    
    /**
      * Returns the length of the step sequence. Alternatively, if a sequence witnesses t1 -k-> t2, returns k
      */
    @pure
    def size: BigInt = {
      this match
        case ARSIdentity(t) => BigInt(0)
        case ARSComposition(h, t) => t.size + 1
    }.ensuring(_ >= BigInt(0))

    /**
      * Composition of reduction sequences
      * 
      * * Formally, if t1 -m-> t2 and t2 -n-> t3 then t1 -m+n-> t3
      * 
      * * This proof is constructive and returns the witness of t1 -m+n-> t3
      * 
      * ! Should not be opaque in order to prove well formedness  
      */
    @pure
    def concat(that: ARSKFoldComposition[T, R]): ARSKFoldComposition[T, R] = {
      decreases(size)
      this match
        case ARSIdentity(t) => that
        case ARSComposition(h, t) => ARSComposition(h, t.concat(that))
    }.ensuring(res => 
      ((this.isSound && that.isSound && t2 == that.t1) ==> (res.isSound && res.t1 == t1)) && 
      res.t2 == that.t2 && res.size == size + that.size) 

    /**
      * * If there exists a k such that t1 -k-> t2 then t1 ->* t2
      * 
      * * This proof is constructive and returns a witness of t1 ->* t2
      * 
      * ! Should not be opaque in order to prove well formedness
      */
    @pure
    def toReflTrans: ARSEquivalence[T, R] = {
      decreases(size)
      this match
        case ARSIdentity(t) => ARSReflexivity[T, R](t)
        case ARSComposition(h, t) => ARSTransitivity[T, R](ARSBaseRelation(h), t.toReflTrans)
    }.ensuring(res => isSound == res.isSound && t1 == res.t1 && t2 == res.t2 && res.isReflTrans)

    /**
     * Inverse step sequence
     * 
     * * If t1 -k-> t2 then t2 <-k- t1
     * 
     * * This proof is constructive and returns the witness of t2 <-k- t1
     */
    @pure
    def inverse: ARSKFoldComposition[T, ARSInverseStep[T, R]] = {
      decreases(size)
      this match
        case ARSIdentity(t) => ARSIdentity[T, ARSInverseStep[T, R]](t)
        case ARSComposition(h, t) => 
          t.inverse match
            case ARSIdentity(_) => ARS1Fold(h.inverse)
            case ARSComposition(h2, t2) => ARSComposition(h2, t2.concat(ARS1Fold(h.inverse))) 
    }.ensuring(res => isSound ==> (res.isSound && res.t1 == t2 && res.t2 == t1) && res.size == size)
  }

  case class ARSIdentity[T, R](t: T) extends ARSKFoldComposition[T, R]
  case class ARSComposition[T, R](h: ARSStep[T, R], t: ARSKFoldComposition[T, R]) extends ARSKFoldComposition[T, R]


  /**
    * A step sequence is said to be well formed if all of its steps are well formed.
    * A step sequence is valid if it is sound and well formed.
    */
  extension [T, R] (ms: ARSKFoldComposition[T, ARSSymmStep[T, R]]) {
    @pure
    def isWellFormed: Boolean =
      ms match
        case ARSIdentity(t) => true
        case ARSComposition(h, t) => h.isWellFormed && t.isWellFormed  
    @pure
    def isValid: Boolean = ms.isSound && ms.isWellFormed
  }

  /**
    * Aternative, inductive definition of the validity of a step sequence
    */
  @pure
  def isValidInd[T, R](ms: ARSKFoldComposition[T, ARSSymmStep[T, R]]) = {
    ms match
      case ARSIdentity(t) => true
      case ARSComposition(h, t) => h.isValid && t.isValid && h.t2 == t.t1
  }.ensuring(_ == ms.isValid)

  /**
   * * t1 -1-> t2 if and only if t1 -> t2
   * 
   * * This proof is constructive and returns a witness of t1 -1-> t2
   */
  @pure
  def ARS1Fold[T, R](s: ARSStep[T, R]): ARSKFoldComposition[T, R] = {
    ARSComposition[T, R](s, ARSIdentity(s.t2))
  }.ensuring(res => res.size == BigInt(1) && res.t1 == s.t1 && res.t2 == s.t2 && s.isSound == res.isSound)


  /**
    * Equivalence witnesses between two terms
    * 
    * In an ARS, two terms t1 and t2 are said to be equivalent if t1 <->* t2, where <->*
    * denotes the symmetric, reflexive and transitive closure of the reduction relation
    * i.e. the smallest symmetric, reflexive and transitive relation containing ->.
    * 
    * An element of ARSEquivalence is therefore a proof or witness that t1 <->* t2. 
    */
  sealed trait ARSEquivalence[T, R]{

    /**
     * Measure for equivalence witnesses
     * 
     * ! This is not a formal definition, its only purpose is to ensure measure decreaseness
     */
    def size: BigInt = {
      this match
        case ARSReflexivity(t) => BigInt(1)
        case ARSTransitivity(r1, r2) => r1.size + r2.size + BigInt(1)
        case ARSSymmetry(r) => r.size + BigInt(1)
        case ARSBaseRelation(r) => BigInt(1) 
    }.ensuring(_ > BigInt(0))
    
    def t1: T = 
      decreases(size)
      this match
        case ARSReflexivity(t) => t
        case ARSBaseRelation(r) => r.t1
        case ARSTransitivity(r1, r2) => r1.t1
        case ARSSymmetry(r) => r.t2 

    def t2: T = 
      decreases(size)
      this match
        case ARSReflexivity(t) => t
        case ARSBaseRelation(r) => r.t2
        case ARSTransitivity(r1, r2) => r2.t2
        case ARSSymmetry(r) => r.t1

    /**
      * Verifier for the witness
      * 
      * Basically just checks if the transitivity rule is applied correctly
      */
    def isSound: Boolean = 
      decreases(size)
      this match
        case ARSReflexivity(t) => true
        case ARSBaseRelation(r) => r.isSound
        case ARSTransitivity(r1, r2) => r1.isSound && r2.isSound && r1.t2 == r2.t1
        case ARSSymmetry(r) => r.isSound

    /**
      * Verifier for ->*, the transitive and reflexive closure of reduction
      * 
      * Since it is a subset of equivalence, this function checks whether the witness
      * does also prove t1 ->* t2, by checking that symmetry is never used
      */
    def isReflTrans: Boolean = 
      decreases(size)
      this match
        case ARSReflexivity(t) => true
        case ARSBaseRelation(r) => true
        case ARSTransitivity(r1, r2) => r1.isReflTrans && r2.isReflTrans
        case ARSSymmetry(r) => false 

    /**
      * * If t1 ->* t2 then there exists a k such that t1 -k> t2 
      *
      * With ARSKFoldComposition.toReflTrans, this proves that ->* = ⋃ -k->
      * 
      * * This proof is constructive and returns a witness that t1 -k-> t2
      */
    def toKFold: ARSKFoldComposition[T, R] = {
      decreases(size)
      this match
        case ARSReflexivity(t) => ARSIdentity[T, R](t)
        case ARSBaseRelation(r) => ARS1Fold(r)
        case ARSTransitivity(r1, r2) => r1.toKFold.concat(r2.toKFold)
        case ARSSymmetry(r) => r.toKFold  
        
    }.ensuring(res => isReflTrans ==> (isSound ==> (res.isSound && t1 == res.t1) && t2 == res.t2))
      
  }

  case class ARSReflexivity[T, R](t: T) extends ARSEquivalence[T, R]
  case class ARSBaseRelation[T, R](r: ARSStep[T, R]) extends ARSEquivalence[T, R]
  case class ARSTransitivity[T, R](r1: ARSEquivalence[T, R], r2: ARSEquivalence[T, R]) extends ARSEquivalence[T, R]
  case class ARSSymmetry[T, R](r: ARSEquivalence[T, R]) extends ARSEquivalence[T, R]

}

object ARSProperties{

  import ARS._

  /**
    * * Short version: If t1 -k-> t2 then t2 <->* t1 
    *
    * Long version: 
    *
    * Preconditions:
    *   - ms the step sequence witnessing t1 -k-> t2 is sound
    * 
    * Postcondition:
    *   There exist a sound proof that witnesses t2 <-> t1*
    * 
    * * This proof is constructive and returns such a witness 
    */
  def kFoldInverseToReflTrans[T, R](ms: ARSKFoldComposition[T, R]): ARSEquivalence[T, R] = {
    require(ms.isSound)
    ARSSymmetry(ms.toReflTrans)
  }.ensuring(res => res.isSound && res.t1 == ms.t2 && res.t2 == ms.t1)

  /**
    * * Short version: If t1 -n-> t1', t2 -m-> t2' and t1 <->* t2 then t1' <->* t2' 
    *
    * Long version: 
    *
    * Preconditions:
    *   - ms1, the step sequence witnessing t1 -m-> t1' is sound
    *   - ms2, the step sequence witnessing t2 -n-> t2' is sound
    *   - eq, the witness of t3 <->* t4 is sound
    *   - t3 = t1 and t4 = t2
    * 
    * Postcondition:
    *   There exist a sound proof that witnesses t1' <->* t2'
    * 
    * * This proof is constructive and returns such a witness 
    */
  def reductionPreserveEquivalence[T, R](ms1: ARSKFoldComposition[T, R], ms2: ARSKFoldComposition[T, R], eq: ARSEquivalence[T, R]) = {
    require(ms1.isSound)
    require(ms2.isSound)
    require(eq.isSound)
    require(ms1.t1 == eq.t1)
    require(ms2.t1 == eq.t2)
    ARSTransitivity(kFoldInverseToReflTrans(ms1), ARSTransitivity(eq, ms2.toReflTrans))
  }.ensuring(res => res.t1 == ms1.t2 && res.t2 == ms2.t2 && res.isSound)

  /**
    * * Short version: If t1 -n-> t1', t2 -m-> t2' and t1' <->* t2' then t1 <->* t2 
    *
    * Long version: 
    *
    * Preconditions:
    *   - ms1, the step sequence witnessing t1 -m-> t1' is sound
    *   - ms2, the step sequence witnessing t2 -n-> t2' is sound
    *   - eq, the witness of t3 <->* t4 is sound
    *   - t3 = t1' and t4 = t2'
    * 
    * Postcondition:
    *   There exist a sound proof that witnesses t1 <->* t2
    * 
    * * This proof is constructive and returns such a witness 
    */
  def reductionImpliesEquivalence[T, R](ms1: ARSKFoldComposition[T, R], ms2: ARSKFoldComposition[T, R], eq: ARSEquivalence[T, R]) = {
    require(ms1.isSound)
    require(ms2.isSound)
    require(eq.isSound)
    require(ms1.t2 == eq.t1)
    require(ms2.t2 == eq.t2)
    ARSTransitivity(ms1.toReflTrans, ARSTransitivity(eq, kFoldInverseToReflTrans(ms2)))
  }.ensuring(res => res.t1 == ms1.t1 && res.t2 == ms2.t1 && res.isSound)

  /**
    * * Short version: If t1 -n-> t, t2 -m-> t then t1 <->* t2 
    *
    * Long version: 
    *
    * Preconditions:
    *   - ms1, the step sequence witnessing t1 -m-> t1' is sound
    *   - ms2, the step sequence witnessing t2 -n-> t2' is sound
    *   - t1' = t2' (= t in the above statement)
    * 
    * Postcondition:
    *   There exist a sound proof that witnesses t1 <->* t2
    * 
    * * This proof is constructive and returns such a witness 
    */ 
  def reduceSameFormEquivalent[T, R](ms1: ARSKFoldComposition[T, R], ms2: ARSKFoldComposition[T, R]): ARSEquivalence[T, R] = {
    require(ms1.isSound)
    require(ms2.isSound)
    require(ms1.t2 == ms2.t2)
    reductionImpliesEquivalence(ms1, ms2, ARSReflexivity(ms1.t2))
  }.ensuring(res => res.t1 == ms1.t1 && res.t2 == ms2.t1 && res.isSound)

  /**
    * * If two symmetric step sequences are well formed then their concatenation is well formed as well  
    */
  def concatWellFormed[T, R](@induct s1: ARSKFoldComposition[T, ARSSymmStep[T, R]], s2: ARSKFoldComposition[T, ARSSymmStep[T, R]]): Unit = {
    require(s1.isWellFormed)
    require(s2.isWellFormed)
  }.ensuring(_ => s1.concat(s2).isWellFormed)


  /**
    * * Short version: If t1 <-n-> t2 then t1 <->* t2 
    *
    * Long version: 
    *
    * Preconditions:
    *   - ms, the step sequence witnessing t1 <-n-> t12 is valid
    * 
    * Postcondition:
    *   There exist a sound proof that witnesses t1 <->* t2
    * 
    * * This proof is constructive and returns such a witness 
    */ 
  def symmClosureToEquivalence[T, R](ms: ARSKFoldComposition[T, ARSSymmStep[T, R]]): ARSEquivalence[T, R] = {
    require(ms.isValid)
    ms match
      case ARSIdentity(t) => ARSReflexivity(t)
      case ARSComposition(h, t) => 
        val eq: ARSEquivalence[T, R] = 
          h.unfold match
            case ARSBaseStepClass(s) => ARSBaseRelation[T, R](s)
            case ARSSymmStepClass(s) => ARSSymmetry[T, R](ARSBaseRelation[T, R](s))
        ARSTransitivity(eq, symmClosureToEquivalence(t))
  }.ensuring(res => res.isSound && res.t1 == ms.t1 && res.t2 == ms.t2)

  /**
    * * Short version: If t1 <-n-> t2 then t2 <-n-> t1 
    *
    * Long version: 
    *
    * Preconditions:
    *   - ms, the step sequence witnessing t1 <-n-> t2 is valid
    * 
    * Postcondition:
    *   There exist a valid proof that witnesses t2 <-n-> t1
    * 
    * * This proof is constructive and returns such a witness 
    */ 
  def symmClosureInverse[T, R](ms: ARSKFoldComposition[T, ARSSymmStep[T, R]]): ARSKFoldComposition[T, ARSSymmStep[T, R]] = {
    require(ms.isValid)
    val res = ms match
      case ARSIdentity(t) => ARSIdentity(t)
      case ARSComposition(h, t) => 
        concatWellFormed(symmClosureInverse(t), ARS1Fold(h.unfold.inverse.toARSStep))
        symmClosureInverse(t).concat(ARS1Fold(h.unfold.inverse.toARSStep))
    res
  }.ensuring(res => res.isValid && res.t1 == ms.t2 && res.t2 == ms.t1 && res.size == ms.size)

  /**
    * * Short version: If t1 <->* t2 then there exists a n such that t1 <-n-> t2 
    *
    * Long version: 
    *
    * Preconditions:
    *   - eq, a proof witnessing t1 <->* t12
    * 
    * Postcondition:
    *   There exist a valid proof that witnesses t1 <-n-> t2
    * 
    * * This proof is constructive and returns such a witness 
    * 
    * With symmClosureToEquivalence this proves that <->* = ⋃ <-n->
    */ 
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
  }.ensuring(res => res.isValid && res.t1 == eq.t1 && res.t2 == eq.t2)

}