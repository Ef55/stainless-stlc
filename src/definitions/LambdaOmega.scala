/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  * 
  *  This file defines the basic bloc of System F with type operators (TAPL Chap 29)
  *  Kinds, terms, types and environments are defined.
  * 
  * 
  */

import stainless.lang._
import stainless.collection._
import stainless.annotation._

object LambdaOmega {

  /**
    * Kind syntax as defined in Figure 30-1 of TAPL
    */
  sealed trait Kind
  case object ProperKind extends Kind
  case class ArrowKind(k1: Kind, k2: Kind) extends Kind

  /**
    * Types syntax as defined in Figure 30-1 of TAPL
    * De Bruijn indices are used to represent type variables (TAPL Chap 6)
    */
  sealed trait Type {

    /**
      * Set of free variables of a type also noted FV(T).
      * The set of free variables of a lambda is described in TAPL Chap 6.1
      * ! For practical reasons, in this implementation a list is used instead of a set.
      * ! Moreover, this function is never used in practice and exists to ensure the
      * ! corectness of alternative definitions below
      * 
      */
    @pure
    def freeVars: List[BigInt] = {
      decreases(this)
      this match
        case BasicType(_) => Nil()
        case ArrowType(t1, t2) => t1.freeVars ++ t2.freeVars
        case AppType(t1, t2) => t1.freeVars ++ t2.freeVars
        case AbsType(_, b) => b.freeVars.filter(x => x > 0).map(x => x - 1)
        case UniversalType(_, b) => b.freeVars.filter(x => x > 0).map(x => x - 1)
        case VariableType(j) => Cons(j, Nil())
    }
    
    /**
      * Checks whether there are free variable occurences in the range [c, c + d[.
      * Formally the function returns whether FV(T) ∩ [c, c + d[ ≠ ∅
      * ! The range is additive for practical reasons. This is strongly linked to d-place shifts with cutoff c (cf TypeTransformations file).
      * ! Moreover, the definition does not use sets as one would do on paper, but is inductive instead.
      * ! This choice of implementation is due to the fact that inductive definitions are way easier to deal with
      * ! in Stainless than data structures.
      * 
      * For the equivalence between this definition and the classical one cf. hasFreeVariablesInSoundness
      * 
      * * Basic property: Always false when d = 0
      */
    @pure
    def hasFreeVariablesIn(c: BigInt, d: BigInt): Boolean = {
      decreases(this)
      require(c >= 0)
      require(d >= 0)
      this match 
        case BasicType(_)           => false
        case ArrowType(t1, t2)      => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
        case VariableType(v)        => (c <= v) && (v < c+d)
        case AbsType(_, body)       => body.hasFreeVariablesIn(c+1, d)
        case UniversalType(_, body) => body.hasFreeVariablesIn(c+1, d)
        case AppType(t1, t2)        => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
    }.ensuring(res => (d == 0) ==> !res)

    /**
      * Checks whether there are free variable greater or equal to c in the type.
      * Formally the function returns whether FV(T) ∩ [c, ∞[ ≠ ∅
      * ! This is an inductive definition and not a set based one, for the same reasons as above.
      * 
      * For the equivalence between this definition and the classical one cf. hasFreeVariablesAboveSoundness
      */
    @pure
    def hasFreeVariablesAbove(c: BigInt): Boolean = {
      decreases(this)
      require(c >= 0)
      this match  
        case BasicType(_)           => false 
        case ArrowType(t1, t2)      => t1.hasFreeVariablesAbove(c) || t2.hasFreeVariablesAbove(c)
        case VariableType(v)        => v >= c
        case AbsType(_, body)       => body.hasFreeVariablesAbove(c+1)
        case UniversalType(_, body) => body.hasFreeVariablesAbove(c+1)
        case AppType(t1, t2)        => t1.hasFreeVariablesAbove(c) || t2.hasFreeVariablesAbove(c)
    }

    /**
      * Checks whether FV(T) = ∅
      * ! The body of the function relies on an inductive definition and not a set based one,
      * ! for the same reasons as above
      * 
      * For the equivalence between this definition and the classical one cf. isClosedSoundness
      */
    @pure
    def isClosed: Boolean = !hasFreeVariablesAbove(0)

    /**
      * Measure for types
      * ! This is not a formal definition, its only purpose is to ensure measure decreaseness
      */
    @pure
    def size: BigInt = {
      decreases(this)
      this match
        case BasicType(_) => BigInt(1)
        case ArrowType(t1, t2) => t1.size + t2.size + BigInt(1)
        case VariableType(_) => BigInt(1)
        case AbsType(_, body) => body.size + BigInt(1)
        case UniversalType(_, body) => body.size + BigInt(1)
        case AppType(t1, t2) => t1.size + t2.size + BigInt(1)
    }.ensuring(_ > BigInt(0))
  }

  case class BasicType(s: String) extends Type
  case class ArrowType(t1: Type, t2: Type) extends Type
  case class VariableType(j: BigInt) extends Type {require(j >= 0)}
  case class AbsType(argKind: Kind, body: Type) extends Type
  case class AppType(t1: Type, t2: Type) extends Type
  case class UniversalType(argKind: Kind, body: Type) extends Type

  /**
    * Terms syntax as defined in Figure 29-1 of TAPL
    * De Bruijn indices are used to represent term variables (TAPL Chap 6)
    */
  sealed trait Term {

    /**
      * Returns whether the term is a value as defined in Figure 29-1 of TAPL
      */
    @pure
    def isValue: Boolean = isInstanceOf[Abs] || isInstanceOf[TAbs]

    /**
      * Set of free variables of a term also noted FV(t).
      * The set of free variables of a lambda is described in TAPL Chap 6.1
      * ! For practical reasons, in this implementation a list is used instead of a set.
      * ! Moreover, this function is never used in practice and exists to ensure the
      * ! corectness of alternative definitions below
      */
    @pure
    def freeVars: List[BigInt] = {
      decreases(this)
      this match
        case App(t1, t2) => t1.freeVars ++ t2.freeVars
        case Abs(_, b) => b.freeVars.filter(x => x > 0).map(x => x - 1)
        case TApp(b, _) => b.freeVars
        case TAbs(_, b) => b.freeVars
        case Var(j) => Cons(j, Nil())
    }

    @pure
    def freeTypeVars: List[BigInt] = {
      decreases(this)
      this match
        case App(t1, t2) => t1.freeTypeVars ++ t2.freeTypeVars
        case Abs(argT, b) => argT.freeVars ++ b.freeTypeVars
        case TApp(b, arg) => b.freeTypeVars ++ arg.freeVars
        case TAbs(_, b) => b.freeTypeVars.filter(x => x > 0).map(x => x - 1)
        case Var(j) => Nil()
    }   

    /**
      * Checks whether there are free variable occurences in the range [c, c + d[.
      * Formally the function returns whether FV(T) ∩ [c, c + d[ ≠ ∅
      * ! The range is additive for practical reasons. This is strongly linked to d-place shifts with cutoff c (cf Transformations file).
      * ! Moreover, the definition does not use sets as one would do on paper, but is inductive instead.
      * ! This choice of implementation is due to the fact that inductive definitions are way easier to deal with
      * ! in Stainless than data structures.
      * 
      * For the equivalence between this definition and the classical one cf. hasFreeVariablesInSoundness
      * 
      * * Basic property: Always false when d = 0
      */
    @pure
    def hasFreeVariablesIn(c: BigInt, d: BigInt): Boolean = {
      decreases(this)
      require(c >= 0)
      require(d >= 0)
      this match
        case Var(k)         => (c <= k) && (k < c+d)
        case Abs(_, body)   => body.hasFreeVariablesIn(c+1, d)
        case App(t1, t2)    => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
        case TApp(b, _)     => b.hasFreeVariablesIn(c, d)
        case TAbs(_, b)     => b.hasFreeVariablesIn(c, d)

    }.ensuring(res => (d == 0) ==> !res)

    @pure
    def hasFreeTypeVariablesIn(c: BigInt, d: BigInt): Boolean = {
      decreases(this)
      require(c >= 0)
      require(d >= 0)
      this match
        case Var(k)          => false
        case Abs(argT, body) => argT.hasFreeVariablesIn(c, d) || body.hasFreeTypeVariablesIn(c, d)
        case App(t1, t2)     => t1.hasFreeTypeVariablesIn(c, d) || t2.hasFreeTypeVariablesIn(c, d)
        case TApp(b, arg)    => b.hasFreeTypeVariablesIn(c, d) || arg.hasFreeVariablesIn(c, d)
        case TAbs(_, b)      => b.hasFreeTypeVariablesIn(c+1, d)

    }.ensuring(res => (d == 0) ==> !res)

    /**
      * Checks whether there are free variable greater or equal to c in the term.
      * Formally the function returns whether FV(t) ∩ [c, ∞[ ≠ ∅
      * ! This is an inductive definition and not a set based one, for the same reasons as above.
      * 
      * For the equivalence between this definition and the classical one cf. hasFreeVariablesAboveSoundness
      */
    @pure
    def hasFreeVariablesAbove(c: BigInt): Boolean = {
      decreases(this)
      require(c >= 0)
      this match 
        case Var(v)      => v >= c
        case Abs(_, body)     => body.hasFreeVariablesAbove(c+1)
        case App(t1, t2)      => t1.hasFreeVariablesAbove(c) || t2.hasFreeVariablesAbove(c)
        case TApp(b, _)       => b.hasFreeVariablesAbove(c)
        case TAbs(_, b)       => b.hasFreeVariablesAbove(c)
    }

    @pure
    def hasFreeTypeVariablesAbove(c: BigInt): Boolean = {
      decreases(this)
      require(c >= 0)
      this match
        case Var(k)          => false
        case Abs(argT, body) => argT.hasFreeVariablesAbove(c) || body.hasFreeTypeVariablesAbove(c)
        case App(t1, t2)     => t1.hasFreeTypeVariablesAbove(c) || t2.hasFreeTypeVariablesAbove(c)
        case TApp(b, arg)    => b.hasFreeTypeVariablesAbove(c) || arg.hasFreeVariablesAbove(c)
        case TAbs(_, b)      => b.hasFreeTypeVariablesAbove(c+1)
    }

    /**
      * Checks whether FV(T) = ∅
      * ! The body of the function relies on an inductive definition and not a set based one,
      * ! for the same reasons as above
      * 
      * For the equivalence between this definition and the classical one cf. isClosedSoundness
      */
    @pure
    def isClosed: Boolean = !hasFreeVariablesAbove(0)

    @pure
    def isTypeClosed: Boolean = !hasFreeTypeVariablesAbove(0)

    /**
      * Measure for terms
      * ! This is not a formal definition, its only purpose is to ensure measure decreaseness
      */
    @pure
    def size: BigInt = {
      decreases(this)
      this match
        case Var(_) => BigInt(1)
        case Abs(_, body) => body.size + BigInt(1)
        case App(t1, t2) => t1.size + t2.size + BigInt(1)
        case TApp(b, t)  => b.size + t.size + BigInt(1)
        case TAbs(_, b)  => b.size + BigInt(1)
    }.ensuring(_ > BigInt(0))

  }
  case class Var(k: BigInt) extends Term { require(k >= 0) }
  case class Abs(argType: Type, body: Term) extends Term
  case class App(t1: Term, t2: Term) extends Term
  case class TApp(body: Term, typ: Type) extends Term
  case class TAbs(argKind: Kind, body: Term) extends Term

  /**
   * Kinding and typing contexts
   * Since De Bruijn indices are used, they can be represented by a list of respectevely
   * kinds and types (TAPL Chap 6.1)
   */
  type KindEnvironment = List[Kind]
  type TypeEnvironment = List[Type]

  extension (env: TypeEnvironment){

    @pure
    def hasFreeVariablesIn(c: BigInt, d: BigInt): Boolean = {
      decreases(env)
      require(c >= 0)
      require(d >= 0)
      env match
        case Nil() => false
        case Cons(h, t) => h.hasFreeVariablesIn(c, d) || t.hasFreeVariablesIn(c, d)
    }.ensuring(res => (d == 0) ==> !res)

  }

}

object LambdaOmegaProperties{
  import LambdaOmega._
  import ListProperties.*
  import BigIntListProperties.*

  object Types {

    /**
      * * ∀x ∈ FV(T), x ≥ 0
      */
    @pure @opaque @inlineOnce
    def freeVarsNonNeg(t: Type): Unit = {
      decreases(t)
      t match
        case BasicType(_) => ()
        case VariableType(_) => ()
        case AppType(t1, t2) =>
          freeVarsNonNeg(t1)
          freeVarsNonNeg(t2)
          ListSpecs.listAppendValidProp(t2.freeVars, t1.freeVars, _ >= 0)
        case ArrowType(t1, t2) =>
          freeVarsNonNeg(t1)
          freeVarsNonNeg(t2)
          ListSpecs.listAppendValidProp(t2.freeVars, t1.freeVars, _ >= 0)
        case AbsType(k, body) => 
          freeVarsNonNeg(body)
          filterGtGe(body.freeVars, 0)
          mapAddSub(body.freeVars.filter(_ >= 1), 1)
          filterMapAddGe(body.freeVars, -1, 0)
          mapAddSub(body.freeVars, 1)
          filterGeTwice(body.freeVars.map(_ - 1), 0, 0)
        case UniversalType(k, body) => 
          freeVarsNonNeg(body)
          filterGtGe(body.freeVars, 0)
          mapAddSub(body.freeVars.filter(_ >= 1), 1)
          filterMapAddGe(body.freeVars, -1, 0)
          mapAddSub(body.freeVars, 1)
          filterGeTwice(body.freeVars.map(_ - 1), 0, 0)
    }.ensuring(t.freeVars.forall(_ >= 0))
  
    /**
     * Proves the soundness of hasFreeVariablesIn
     *
     * * T.hasFreeVariablesIn(c, d) <=> FV(T) ∩ [c, c + d[ ≠ ∅
     */
    @pure @opaque @inlineOnce
    def hasFreeVariablesInSoundness(t: Type, c: BigInt, d: BigInt): Unit = {
      decreases(t)
      require(c >= 0)
      require(d >= 0)
      filterSplitGeLt(t.freeVars, c, c + d)
      t match
        case BasicType(_) => ()
        case AppType(t1, t2) => 
          hasFreeVariablesInSoundness(t1, c, d)
          hasFreeVariablesInSoundness(t2, c, d)
          filterSplitGeLt(t1.freeVars, c, c + d)
          filterSplitGeLt(t2.freeVars, c, c + d)
          concatFilter(t1.freeVars.filter(c <= _), t2.freeVars.filter(c <= _), _ < c + d)
          concatFilter(t1.freeVars, t2.freeVars, c <= _)
        case ArrowType(t1, t2) =>
          hasFreeVariablesInSoundness(t1, c, d)
          hasFreeVariablesInSoundness(t2, c, d)
          filterSplitGeLt(t1.freeVars, c, c + d)
          filterSplitGeLt(t2.freeVars, c, c + d)
          concatFilter(t1.freeVars.filter(c <= _), t2.freeVars.filter(c <= _), _ < c + d)
          concatFilter(t1.freeVars, t2.freeVars, c <= _)
        case VariableType(j) => ()
        case AbsType(_, b) => 
          hasFreeVariablesInSoundness(b, c + 1, d)
          filterGeLe(b.freeVars.filter(_ > 0).map(_ - 1), c)
          mapAddSub(b.freeVars.filter(_ > 0), 1)
          filterMapAddGe(b.freeVars.filter(_ > 0), -1, c)
          filterGtGe(b.freeVars, 0)
          filterGeTwice(b.freeVars, 1, c + 1)  
          filterMapAddLt(b.freeVars.filter(_ >= c + 1), -1, c + d)     
          filterGeLe(b.freeVars, c + 1)
          filterSplitGeLt(b.freeVars, c + 1, c + 1 + d)
          assert(t.freeVars.filter(x => c <= x && x < c + d) == b.freeVars.filter(x => c + 1 <= x && x < c + 1 + d).map(_ + - 1)) //needed
        case UniversalType(_, b) => 
          hasFreeVariablesInSoundness(b, c + 1, d)
          filterGeLe(b.freeVars.filter(_ > 0).map(_ - 1), c)
          mapAddSub(b.freeVars.filter(_ > 0), 1)
          filterMapAddGe(b.freeVars.filter(_ > 0), -1, c)
          filterGtGe(b.freeVars, 0)
          filterGeTwice(b.freeVars, 1, c + 1)  
          filterMapAddLt(b.freeVars.filter(_ >= c + 1), -1, c + d)     
          filterGeLe(b.freeVars, c + 1)
          filterSplitGeLt(b.freeVars, c + 1, c + 1 + d)
          assert(t.freeVars.filter(x => c <= x && x < c + d) == b.freeVars.filter(x => c + 1 <= x && x < c + 1 + d).map(_ + - 1)) //needed              
    }.ensuring(t.freeVars.filter(x => c <= x && x < c + d).isEmpty == !t.hasFreeVariablesIn(c, d))

    /**
     * Proves the soundness of hasFreeVariablesAbove
     *
     * * T.hasFreeVariablesAbove(c) <=> FV(T) ∩ [c, ∞[ ≠ ∅
     */
    @inlineOnce @opaque @pure
    def hasFreeVariablesAboveSoundness(t: Type, c: BigInt): Unit = {
      decreases(t)
      require(c >= 0)
      t match
        case BasicType(_) => ()
        case AppType(t1, t2) => 
          hasFreeVariablesAboveSoundness(t1, c)
          hasFreeVariablesAboveSoundness(t2, c)
          concatFilter(t1.freeVars, t2.freeVars, _ >= c)
        case ArrowType(t1, t2) =>
          hasFreeVariablesAboveSoundness(t1, c)
          hasFreeVariablesAboveSoundness(t2, c)
          concatFilter(t1.freeVars, t2.freeVars, _ >= c)
        case VariableType(_) => ()
        case AbsType(_, b) => 
          hasFreeVariablesAboveSoundness(b, c + 1)
          mapAddSub(b.freeVars.filter(_ > 0), 1)
          mapAddSub(b.freeVars.filter(_ > 0).filter(_ >= c + 1), 1)
          filterMapAddGe(b.freeVars.filter(_ > 0), -1, c)
          filterCommutative(b.freeVars, _ > 0, _ >= c + 1)
        case UniversalType(_, b) => 
          hasFreeVariablesAboveSoundness(b, c + 1)
          mapAddSub(b.freeVars.filter(_ > 0), 1)
          mapAddSub(b.freeVars.filter(_ > 0).filter(_ >= c + 1), 1)
          filterMapAddGe(b.freeVars.filter(_ > 0), -1, c)
          filterCommutative(b.freeVars, _ > 0, _ >= c + 1)
    }.ensuring(t.freeVars.filter(_ >= c).isEmpty == !t.hasFreeVariablesAbove(c))

    /**
     * Proves the soundness of isClosed
     *
     * * T.isClosed <=> FV(T) = ∅
     */  
    @inlineOnce @opaque @pure
    def isClosedSoundness(t: Type): Unit = {
      freeVarsNonNeg(t)
      hasFreeVariablesAboveSoundness(t, 0)
    }.ensuring(t.freeVars.isEmpty == t.isClosed)


    /**
      * * Short version: If d2 ≤ d1, FV(T) ∩ [c, c + d1[ = ∅ => FV(T) ∩ [c, c + d2[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - d2 and c are non negative
      *   - d1 >= d2
      *   - T has no free variable occurences between c and c + d1
      * 
      * Postcondition:
      *   T has no free variable occurences between c and c + d2
      */
    @inlineOnce @opaque @pure
    def boundRangeDecrease(t: Type, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
      decreases(t)
      require(d2 >= 0)
      require(d1 >= d2)
      require(c >= 0)
      require(!t.hasFreeVariablesIn(c, d1))

      t match
        case BasicType(_) => ()
        case ArrowType(t1, t2) => 
          boundRangeDecrease(t1, c, d1, d2)
          boundRangeDecrease(t2, c, d1, d2)
        case VariableType(_) => ()
        case AbsType(_, body) => 
          boundRangeDecrease(body, c+1, d1, d2)
        case UniversalType(_, body) => 
          boundRangeDecrease(body, c+1, d1, d2)
        case AppType(t1, t2) => 
          boundRangeDecrease(t1, c, d1, d2)
          boundRangeDecrease(t2, c, d1, d2)

    }.ensuring(!t.hasFreeVariablesIn(c, d2))

    /**
      * * Short version: If c1 ≤ c2, FV(T) ∩ [c1, c1 + d[ = ∅ => FV(T) ∩ [c2, c1 + d[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - c1 is non negative
      *   - c1 <= c2 <= c1 + d
      *   - T has no free variable occurences between c1 and c1 + d
      * 
      * Postcondition:
      *   T has no free variable occurences between c2 and d - (c2 - c1) + c2 (= c1 + d)
      */
    @inlineOnce @opaque @pure
    def boundRangeIncreaseCutoff(t: Type, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
      decreases(t)
      require(0 <= c1)
      require(c1 <= c2)
      require(c2 <= c1 + d)
      require(!t.hasFreeVariablesIn(c1, d))

      t match 
        case BasicType(_) => ()
        case ArrowType(t1, t2) => 
          boundRangeIncreaseCutoff(t1, c1, c2, d)
          boundRangeIncreaseCutoff(t2, c1, c2, d)
        case VariableType(v) => ()
        case AbsType(_, body) => 
          boundRangeIncreaseCutoff(body, c1 + 1, c2 + 1, d)
        case UniversalType(_, body) => 
          boundRangeIncreaseCutoff(body, c1 + 1, c2 + 1, d)
        case AppType(t1, t2) => 
          boundRangeIncreaseCutoff(t1, c1, c2, d)
          boundRangeIncreaseCutoff(t2, c1, c2, d)
        
    }.ensuring(!t.hasFreeVariablesIn(c2, d - (c2 - c1)))

    /**
      * * Short version: FV(T) ∩ [a, a + b[ = ∅ /\  FV(T) ∩ [a + b, a + b + c[ = ∅ => FV(T) ∩ [a, a + b + c[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - a, b and c are non negative
      *   - T has no free variable occurences between a and a + b
      *   - T has no free variable occurences between a + b and a + b + c
      * 
      * Postcondition:
      *   T has no free variable occurences between a and a + b + c
      */
    @inlineOnce @opaque @pure
    def boundRangeConcatenation(t: Type, a: BigInt, b: BigInt, c: BigInt): Unit = {
      decreases(t)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(!t.hasFreeVariablesIn(a, b))
      require(!t.hasFreeVariablesIn(a + b, c))

      t match
        case BasicType(_) => ()
        case ArrowType(t1, t2) => 
          boundRangeConcatenation(t1, a, b, c)
          boundRangeConcatenation(t2, a, b, c)
        case VariableType(v) => ()
        case AbsType(_, body) => boundRangeConcatenation(body, a + 1, b, c)
        case UniversalType(_, body) => boundRangeConcatenation(body, a + 1, b, c)
        case AppType(t1, t2) => 
          boundRangeConcatenation(t1, a, b, c)
          boundRangeConcatenation(t2, a, b, c)

    }.ensuring(!t.hasFreeVariablesIn(a, b + c))
    
  }

  object Terms {

    /**
      * * ∀x ∈ FV(t), x ≥ 0
      */
    @pure @opaque @inlineOnce
    def freeVarsNonNeg(t: Term): Unit = {
      decreases(t)
      t match
        case Var(_) => ()
        case App(t1, t2) =>
          freeVarsNonNeg(t1)
          freeVarsNonNeg(t2)
          ListSpecs.listAppendValidProp(t2.freeVars, t1.freeVars, _ >= 0)
        case Abs(k, body) => 
          freeVarsNonNeg(body)
          filterGtGe(body.freeVars, 0)
          mapAddSub(body.freeVars.filter(_ >= 1), 1)
          filterMapAddGe(body.freeVars, -1, 0)
          mapAddSub(body.freeVars, 1)
          filterGeTwice(body.freeVars.map(_ - 1), 0, 0)
        case TApp(b, _) => freeVarsNonNeg(b)
        case TAbs(_, b) => freeVarsNonNeg(b)
    }.ensuring(t.freeVars.forall(_ >= 0))
  
    /**
     * Proves the soundness of hasFreeVariablesIn
     * 
     * * t.hasFreeVariablesIn(c, d) <=> FV(t) ∩ [c, c + d[ ≠ ∅
     */
    @pure @opaque @inlineOnce
    def hasFreeVariablesInSoundness(t: Term, c: BigInt, d: BigInt): Unit = {
      decreases(t)
      require(c >= 0)
      require(d >= 0)
      filterSplitGeLt(t.freeVars, c, c + d)
      t match
        case App(t1, t2) => 
          hasFreeVariablesInSoundness(t1, c, d)
          hasFreeVariablesInSoundness(t2, c, d)
          filterSplitGeLt(t1.freeVars, c, c + d)
          filterSplitGeLt(t2.freeVars, c, c + d)
          concatFilter(t1.freeVars.filter(c <= _), t2.freeVars.filter(c <= _), _ < c + d)
          concatFilter(t1.freeVars, t2.freeVars, c <= _)
        case Var(j) => ()
        case Abs(_, b) => 
          hasFreeVariablesInSoundness(b, c + 1, d)
          filterGeLe(b.freeVars.filter(_ > 0).map(_ - 1), c)
          mapAddSub(b.freeVars.filter(_ > 0), 1)
          filterMapAddGe(b.freeVars.filter(_ > 0), -1, c)
          filterGtGe(b.freeVars, 0)
          filterGeTwice(b.freeVars, 1, c + 1)  
          filterMapAddLt(b.freeVars.filter(_ >= c + 1), -1, c + d)     
          filterGeLe(b.freeVars, c + 1)
          filterSplitGeLt(b.freeVars, c + 1, c + 1 + d)
          assert(t.freeVars.filter(x => c <= x && x < c + d) == b.freeVars.filter(x => c + 1 <= x && x < c + 1 + d).map(_ + - 1)) //needed
        case TApp(b, _) => hasFreeVariablesInSoundness(b, c, d)
        case TAbs(_, b) => hasFreeVariablesInSoundness(b, c, d)
    }.ensuring(t.freeVars.filter(x => c <= x && x < c + d).isEmpty == !t.hasFreeVariablesIn(c, d))

    /**
     * Proves the soundness of hasFreeVariablesAbove
     * 
     * * t.hasFreeVariablesAbove(c) <=> FV(t) ∩ [c, ∞[ ≠ ∅
     */
    @inlineOnce @opaque @pure
    def hasFreeVariablesAboveSoundness(t: Term, c: BigInt): Unit = {
      decreases(t)
      require(c >= 0)
      t match
        case App(t1, t2) => 
          hasFreeVariablesAboveSoundness(t1, c)
          hasFreeVariablesAboveSoundness(t2, c)
          concatFilter(t1.freeVars, t2.freeVars, _ >= c)
        case Var(j) => ()
        case Abs(_, b) => 
          hasFreeVariablesAboveSoundness(b, c + 1)
          mapAddSub(b.freeVars.filter(_ > 0), 1)
          mapAddSub(b.freeVars.filter(_ > 0).filter(_ >= c + 1), 1)
          filterMapAddGe(b.freeVars.filter(_ > 0), -1, c)
          filterCommutative(b.freeVars, _ > 0, _ >= c + 1)
        case TApp(b, _) => hasFreeVariablesAboveSoundness(b, c)
        case TAbs(_, b) => hasFreeVariablesAboveSoundness(b, c)
    }.ensuring(t.freeVars.filter(_ >= c).isEmpty == !t.hasFreeVariablesAbove(c))

    /**
     * Proves the soundness of isClosed
     *
     * * t.isClosed <=> FV(t) = ∅
     */
    @inlineOnce @opaque @pure
    def isClosedSoundness(t: Term): Unit = {
      freeVarsNonNeg(t)
      hasFreeVariablesAboveSoundness(t, 0)
    }.ensuring(t.freeVars.isEmpty == t.isClosed)

    /**
      * * Short version: If d2 ≤ d1, FV(t) ∩ [c, c + d1[ = ∅ => FV(t) ∩ [c, c + d2[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - d2 and c are non negative
      *   - d1 >= d2
      *   - t has no free variable occurences between c and c + d1
      * 
      * Postcondition:
      *   t has no free variable occurences between c and c + d2
      */
    @inlineOnce @opaque @pure
    def boundRangeDecrease(t: Term, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
      decreases(t)
      require(d1 >= 0 && d2 >= 0)
      require(c >= 0)
      require(d2 <= d1)
      require(!t.hasFreeVariablesIn(c, d1))

      t match
        case Var(v) => ()
        case Abs(_, body) => 
          boundRangeDecrease(body, c+1, d1, d2)
        case App(t1, t2) => 
          boundRangeDecrease(t1, c, d1, d2)
          boundRangeDecrease(t2, c, d1, d2)
        case TApp(b, _) => boundRangeDecrease(b, c, d1, d2)
        case TAbs(_, b) => boundRangeDecrease(b, c, d1, d2)

    }.ensuring(!t.hasFreeVariablesIn(c, d2))

    @inlineOnce @opaque @pure
    def boundTypeRangeDecrease(t: Term, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
      decreases(t)
      require(d1 >= 0 && d2 >= 0)
      require(c >= 0)
      require(d2 <= d1)
      require(!t.hasFreeTypeVariablesIn(c, d1))

      t match
        case Var(v) => ()
        case Abs(argT, body) => 
          Types.boundRangeDecrease(argT, c, d1, d2)
          boundTypeRangeDecrease(body, c, d1, d2)
        case App(t1, t2) => 
          boundTypeRangeDecrease(t1, c, d1, d2)
          boundTypeRangeDecrease(t2, c, d1, d2)
        case TApp(b, arg) => 
          boundTypeRangeDecrease(b, c, d1, d2)
          Types.boundRangeDecrease(arg, c, d1, d2)
        case TAbs(_, b) => boundTypeRangeDecrease(b, c + 1, d1, d2)

    }.ensuring(!t.hasFreeTypeVariablesIn(c, d2))


    /**
      * * Short version: If c1 ≤ c2, FV(t) ∩ [c1, c1 + d[ = ∅ => FV(t) ∩ [c2, c1 + d[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - c1 is non negative
      *   - c1 <= c2 <= c1 + d
      *   - t has no free variable occurences between c1 and c1 + d
      * 
      * Postcondition:
      *   t has no free variable occurences between c2 and d - (c2 - c1) + c2 (= c1 + d)
      */
    @inlineOnce @opaque @pure
    def boundRangeIncreaseCutoff(t: Term, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
      decreases(t)
      require(c1 >= 0 && c2 >= 0)
      require(0 <= d && c2 - c1 <= d)
      require(c1 <= c2)
      require(!t.hasFreeVariablesIn(c1, d))

      t match 
        case Var(v) => ()
        case Abs(_, body) => boundRangeIncreaseCutoff(body, c1 + 1, c2 + 1, d)
        case App(t1, t2) => 
          boundRangeIncreaseCutoff(t1, c1, c2, d)
          boundRangeIncreaseCutoff(t2, c1, c2, d)
        case TApp(b, _) => boundRangeIncreaseCutoff(b, c1, c2, d)
        case TAbs(_, b) => boundRangeIncreaseCutoff(b, c1, c2, d)
        
    }.ensuring(!t.hasFreeVariablesIn(c2, d - (c2 - c1)))

    @inlineOnce @opaque @pure
    def boundTypeRangeIncreaseCutoff(t: Term, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
      decreases(t)
      require(c1 >= 0 && c2 >= 0)
      require(0 <= d && c2 - c1 <= d)
      require(c1 <= c2)
      require(!t.hasFreeTypeVariablesIn(c1, d))

      t match 
        case Var(v) => ()
        case Abs(argT, body) => 
          Types.boundRangeIncreaseCutoff(argT, c1, c2, d)
          boundTypeRangeIncreaseCutoff(body, c1, c2, d)
        case App(t1, t2) => 
          boundTypeRangeIncreaseCutoff(t1, c1, c2, d)
          boundTypeRangeIncreaseCutoff(t2, c1, c2, d)
        case TApp(b, arg) => 
          boundTypeRangeIncreaseCutoff(b, c1, c2, d)
          Types.boundRangeIncreaseCutoff(arg, c1, c2, d)
        case TAbs(_, b) => boundTypeRangeIncreaseCutoff(b, c1 + 1, c2 + 1, d)
        
    }.ensuring(!t.hasFreeTypeVariablesIn(c2, d - (c2 - c1)))

    /**
      * * Short version: FV(t) ∩ [a, a + b[ = ∅ /\  FV(t) ∩ [a + b, a + b + c[ = ∅ => FV(t) ∩ [a, a + b + c[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - a, b and c are non negative
      *   - t has no free variable occurences between a and a + b
      *   - t has no free variable occurences between a + b and a + b + c
      * 
      * Postcondition:
      *   t has no free variable occurences between a and a + b + c
      */
    @inlineOnce @opaque @pure
    def boundRangeConcatenation(t: Term, a: BigInt, b: BigInt, c: BigInt): Unit = {
      decreases(t)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(!t.hasFreeVariablesIn(a, b))
      require(!t.hasFreeVariablesIn(a + b, c))

      t match
        case Var(v) => ()
        case Abs(_, body) => boundRangeConcatenation(body, a + 1, b, c)
        case App(t1, t2) => 
          boundRangeConcatenation(t1, a, b, c)
          boundRangeConcatenation(t2, a, b, c)
        case TApp(bt, _) => boundRangeConcatenation(bt, a, b, c)
        case TAbs(_, bt) => boundRangeConcatenation(bt, a, b, c)

    }.ensuring(!t.hasFreeVariablesIn(a, b + c))

    @inlineOnce @opaque @pure
    def boundTypeRangeConcatenation(t: Term, a: BigInt, b: BigInt, c: BigInt): Unit = {
      decreases(t)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(!t.hasFreeTypeVariablesIn(a, b))
      require(!t.hasFreeTypeVariablesIn(a + b, c))

      t match
        case Var(v) => ()
        case Abs(argT, body) => 
          Types.boundRangeConcatenation(argT, a, b, c)
          boundTypeRangeConcatenation(body, a, b, c)
        case App(t1, t2) => 
          boundTypeRangeConcatenation(t1, a, b, c)
          boundTypeRangeConcatenation(t2, a, b, c)
        case TApp(bt, arg) => 
          boundTypeRangeConcatenation(bt, a, b, c)
          Types.boundRangeConcatenation(arg, a, b, c)
        case TAbs(_, bt) => boundTypeRangeConcatenation(bt, a + 1, b, c)

    }.ensuring(!t.hasFreeTypeVariablesIn(a, b + c))
    
  }

  object Env {

    def freeVariablesApply(env: TypeEnvironment, c: BigInt, d: BigInt, j: BigInt): Unit = {
      decreases(env)
      require(c >= 0)
      require(d >= 0)
      require(0 <= j)
      require(j < env.length)
      require(!env.hasFreeVariablesIn(c, d))
    
      env match
        case Nil() => ()
        case Cons(h, t) => if j == 0 then () else freeVariablesApply(t, c, d, j - 1)

    }.ensuring(!env(j).hasFreeVariablesIn(c, d))

    /**
      * * Short version: If d2 ≤ d1, FV(T) ∩ [c, c + d1[ = ∅ => FV(T) ∩ [c, c + d2[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - d2 and c are non negative
      *   - d1 >= d2
      *   - T has no free variable occurences between c and c + d1
      * 
      * Postcondition:
      *   T has no free variable occurences between c and c + d2
      */
    @inlineOnce @opaque @pure
    def boundRangeDecrease(env: TypeEnvironment, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
      decreases(env)
      require(d2 >= 0)
      require(d1 >= d2)
      require(c >= 0)
      require(!env.hasFreeVariablesIn(c, d1))

      env match
        case Nil() => ()
        case Cons(h, t) => 
          LambdaOmegaProperties.Types.boundRangeDecrease(h, c, d1, d2)
          boundRangeDecrease(t, c, d1, d2)

    }.ensuring(!env.hasFreeVariablesIn(c, d2))

    /**
      * * Short version: If c1 ≤ c2, FV(T) ∩ [c1, c1 + d[ = ∅ => FV(T) ∩ [c2, c1 + d[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - c1 is non negative
      *   - c1 <= c2 <= c1 + d
      *   - T has no free variable occurences between c1 and c1 + d
      * 
      * Postcondition:
      *   T has no free variable occurences between c2 and d - (c2 - c1) + c2 (= c1 + d)
      */
    @inlineOnce @opaque @pure
    def boundRangeIncreaseCutoff(env: TypeEnvironment, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
      decreases(env)
      require(0 <= c1)
      require(c1 <= c2)
      require(c2 <= c1 + d)
      require(!env.hasFreeVariablesIn(c1, d))

      env match
        case Nil() => ()
        case Cons(h, t) => 
          LambdaOmegaProperties.Types.boundRangeIncreaseCutoff(h, c1, c2, d)
          boundRangeIncreaseCutoff(t, c1, c2, d)
        
    }.ensuring(!env.hasFreeVariablesIn(c2, d - (c2 - c1)))

    /**
      * * Short version: FV(T) ∩ [a, a + b[ = ∅ /\  FV(T) ∩ [a + b, a + b + c[ = ∅ => FV(T) ∩ [a, a + b + c[ = ∅
      * 
      * Long version:
      * 
      * Preconditions:
      *   - a, b and c are non negative
      *   - T has no free variable occurences between a and a + b
      *   - T has no free variable occurences between a + b and a + b + c
      * 
      * Postcondition:
      *   T has no free variable occurences between a and a + b + c
      */
    @inlineOnce @opaque @pure
    def boundRangeConcatenation(env: TypeEnvironment, a: BigInt, b: BigInt, c: BigInt): Unit = {
      decreases(env)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(!env.hasFreeVariablesIn(a, b))
      require(!env.hasFreeVariablesIn(a + b, c))

      env match
        case Nil() => ()
        case Cons(h, t) => 
          LambdaOmegaProperties.Types.boundRangeConcatenation(h, a, b, c)
          boundRangeConcatenation(t, a, b, c)

    }.ensuring(!env.hasFreeVariablesIn(a, b + c))
    
  }
}