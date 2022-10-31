/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  * 
  *  This file defines the basic bloc of simply typed lambda calculus with type operators (TAPL Chap 29)
  *  Kind, term, types and environments are defined
  * 
  * 
  */

import stainless.lang._
import stainless.collection._
import stainless.annotation._

object LambdaOmega {

  /**
    * Kind syntax as defined in Figure 29-1 of TAPL
    */
  sealed trait Kind
  case object ProperKind extends Kind
  case class ArrowKind(k1: Kind, k2: Kind) extends Kind

  /**
    * Types syntax as defined in Figure 29-1 of TAPL
    * De Brujin notation is used to represent type variables (TAPL Chap 6)
    */
  sealed trait Type {

    /**
      * Determines which types are considered as values in our calculus.
      * ! This definition is informal and is only meant to give us a nice criteria
      * ! to determine which types can be deterministically reduced or not.
      * TODO add a reference to the theorem
      */
    @pure
    def isValue: Boolean = 
      this match
        case AbsType(_, body) => true
        case BasicType(_) => true
        case ArrowType(t1, t2) => t1.isValue && t2.isValue
        case _ => false

    /**
      * Set of free variables of a type also noted FV(T).
      * The set of free variables of a lambda is described in TAPL Chap 6.1
      * ! For practical reasons, in this implementation a list is used instead of a set.
      * ! Moreover, this function will never be used in proofs and exists to ensure the
      * ! corectness of alternative definitions below
      * 
      * TODO convert it to a set
      * 
      */
    @pure
    def freeVars: List[BigInt] = {
      this match
        case BasicType(_) => Nil()
        case ArrowType(t1, t2) => t1.freeVars ++ t2.freeVars
        case AppType(t1, t2) => t1.freeVars ++ t2.freeVars
        case AbsType(_, b) => b.freeVars.filter(x => x > 0).map(x => x - 1)
        case VariableType(j) => Cons(j, Nil())
    }
    
    /**
      * Checks whether there are free variable occurences in the range [c, c + d].
      * Formally the function returns whether FV(T) ∩ [c, c + d] ≠ ∅
      * ! The range is additive for practical reasons. This is strongly linked to d-place shifts with cutoff c (cf Transformations file).
      * ! Moreover, the definition does not use sets as one would do on paper, but is inductive instead.
      * ! This choice of implementation is due to the fact that inductive definitions are way easier to deal with
      * ! in Stainless than data structures.
      * 
      * For the equivalence between this definition and the classical one cf. hasFreeVariablesInSoundness
      * 
      * Basic property: Always false when d = 0
      */
    @pure
    def hasFreeVariablesIn(c: BigInt, d: BigInt): Boolean = {
      require(c >= 0)
      require(d >= 0)
      this match 
        case BasicType(_)         => false
        case ArrowType(t1, t2)    => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
        case VariableType(v)      => (c <= v) && (v < c+d)
        case AbsType(_, body)     => body.hasFreeVariablesIn(c+1, d)
        case AppType(t1, t2)      => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
    }.ensuring(res => (d == 0) ==> !res)

    /**
      * Checks whether there are free variable greater or equal to c in the type.
      * Formally the function returns whether FV(T) ∩ [c, ∞[ ≠ ∅
      * ! This is an inductive definition and not a set based one, for the same reasons as above.
      * 
      * For the equivalence between this definition and the classical one cf. hasFreeVariablesAboveSoundness
      */
    def hasFreeVariablesAbove(c: BigInt): Boolean = {
      require(c >= 0)
      this match 
        case BasicType(_)         => false 
        case ArrowType(t1, t2)    => t1.hasFreeVariablesAbove(c) || t2.hasFreeVariablesAbove(c)
        case VariableType(v)      => v >= c
        case AbsType(_, body)     => body.hasFreeVariablesAbove(c+1)
        case AppType(t1, t2)      => t1.hasFreeVariablesAbove(c) || t2.hasFreeVariablesAbove(c)
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
      this match
        case BasicType(_) => BigInt(1)
        case ArrowType(t1, t2) => t1.size + t2.size
        case VariableType(_) => BigInt(1)
        case AbsType(_, body) => body.size + BigInt(1)
        case AppType(t1, t2) => t1.size + t2.size
    }.ensuring(_ > BigInt(0))
  }

  case class BasicType(s: String) extends Type
  case class ArrowType(t1: Type, t2: Type) extends Type
  case class VariableType(j: BigInt) extends Type {require(j >= 0)}
  case class AbsType(argKind: Kind, body: Type) extends Type
  case class AppType(t1: Type, t2: Type) extends Type

  // /**
  //   * Terms syntax as defined in Figure 29-1 of TAPL
  //   * De Brujin notation is used to represent term variables (TAPL Chap 6)
  //   */
  // sealed trait Term {

  //   /**
  //     * Returns whether the term is a value as defined in Figure 29-1 of TAPL
  //     */
  //   @pure
  //   def isValue: Boolean = 
  //       this match 
  //           case Abs(_, _) => true
  //           case _         => false 
            
  //   /**
  //     * Checks whether there are free variable occurences in the range [c, c + d].
  //     * Formally the function returns whether FV(T) ∩ [c, c + d] ≠ ∅
  //     * ! The range is additive for practical reasons. This is strongly linked to d-place shifts with cutoff c (cf Transformations file).
  //     * ! Moreover, the definition does not use sets as one would do on paper, but is inductive instead.
  //     * ! This choice of implementation is due to the fact that inductive definitions are way easier to deal with
  //     * ! in Stainless than data structures.
  //     * 
  //     * For the equivalence between this definition and the classical one cf. hasFreeVariablesInSoundness
  //     * 
  //     * Basic property: Always false when d = 0
  //     */
  //   @pure
  //   def hasFreeVariablesIn(c: BigInt, d: BigInt): Boolean = {
  //     require(c >= 0)
  //     require(d >= 0)
  //     this match
  //       case Var(k)         => (c <= k) && (k < c+d)
  //       case Abs(_, body)   => body.hasFreeVariablesIn(c+1, d)
  //       case App(t1, t2)    => t1.hasFreeVariablesIn(c, d) || t2.hasFreeVariablesIn(c, d)
  //       case Fix(f)         => f.hasFreeVariablesIn(c, d)

  //   }.ensuring(res => (d == 0) ==> !res)

  //   @pure
  //   def isClosed: Boolean = 
  //     def rec(t: Term, c: BigInt): Boolean = 
  //       t match 
  //         case Var(k)         => k < c
  //         case Abs(_, body)   => rec(body, c+1)
  //         case App(t1, t2)    => rec(t1, c) && rec(t2, c)
  //         case Fix(f)         => rec(f, c)     
  //     rec(this, 0)

  // }
  // case class Var(k: BigInt) extends Term { require(k >= 0) }
  // case class Abs(argType: Type, body: Term) extends Term
  // case class App(t1: Term, t2: Term) extends Term
  // case class Fix(t: Term) extends Term

  type KindEnvironment = List[Kind]
  type TypeEnvironment = List[Type]

  @pure
  def hasFreeVariablesIn(env: TypeEnvironment, c: BigInt, d: BigInt): Boolean = {
    require(c >= 0)
    require(d >= 0)

    env match 
      case Nil() => false
      case Cons(h, t) => h.hasFreeVariablesIn(c, d) || hasFreeVariablesIn(t, c, d)

  }.ensuring(res =>
    ( !res ==> env.forall(!_.hasFreeVariablesIn(c, d)) ) &&
    ( res ==> env.exists(_.hasFreeVariablesIn(c, d)) ) &&
    ( (d == 0) ==> !res )
  )
}

object LambdaOmegaProperties{
  import LambdaOmega._
  import ListProperties.*
  import BigIntListProperties.*

  // object Terms {
  //   @opaque @pure
  //   def boundRangeDecrease(t: Term, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
  //     require(d1 >= 0 && d2 >= 0)
  //     require(c >= 0)
  //     require(d2 <= d1)
  //     require(!t.hasFreeVariablesIn(c, d1))

  //     t match
  //       case Var(_) => ()
  //       case Abs(targ, body) => 
  //         boundRangeDecrease(body, c + 1, d1, d2)
  //       case App(t1, t2) => 
  //         boundRangeDecrease(t1, c, d1, d2)
  //         boundRangeDecrease(t2, c, d1, d2)
  //       case Fix(f) => boundRangeDecrease(f, c, d1, d2)
      
  //   }.ensuring(!t.hasFreeVariablesIn(c, d2))

  //   @opaque @pure
  //   def boundRangeIncreaseCutoff(t: Term, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
  //     require(c1 >= 0 && c2 >= 0)
  //     require(0 <= d && c2 - c1 <= d)
  //     require(c1 <= c2)
  //     require(!t.hasFreeVariablesIn(c1, d))

  //     t match
  //       case Var(_) => ()
  //       case Abs(targ, body) => boundRangeIncreaseCutoff(body, c1 + 1, c2 + 1, d)
  //       case App(t1, t2) =>
  //         boundRangeIncreaseCutoff(t1, c1, c2, d)
  //         boundRangeIncreaseCutoff(t2, c1, c2, d)
  //       case Fix(f) => boundRangeIncreaseCutoff(f, c1, c2, d)
  //   }.ensuring(!t.hasFreeVariablesIn(c2, d - (c2 - c1)))

  //   @opaque @pure
  //   def boundRangeConcatenation(t: Term, a: BigInt, b: BigInt, c: BigInt): Unit = {
  //     require(a >= 0)
  //     require(b >= 0)
  //     require(c >= 0)
  //     require(!t.hasFreeVariablesIn(a, b))
  //     require(!t.hasFreeVariablesIn(a + b, c))

  //     t match
  //       case Var(k) => ()
  //       case Abs(targ, body) => 
  //         boundRangeConcatenation(body, a + 1, b, c)
  //       case App(t1, t2) => 
  //         boundRangeConcatenation(t1, a, b, c)
  //         boundRangeConcatenation(t2, a, b, c)
  //       case Fix(f) => boundRangeConcatenation(f, a, b, c)

  //   }.ensuring(!t.hasFreeVariablesIn(a, b + c))
  // }

  object Types {

    def freeVarsNonNeg(t: Type): Unit = {
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
    }.ensuring(t.freeVars.forall(_ >= 0))
  
    def hasFreeVariablesInSoundness(t: Type, c: BigInt, d: BigInt): Unit = {
      require(c >= 0)
      require(d >= 0)
      filterSplitGeLt(t.freeVars, c, c + d)
      assert(t.freeVars.filter(x => c <= x && x < c + d) == t.freeVars.filter(c <= _).filter(_ < c + d))
      t match
        case BasicType(_) => ()
        case AppType(t1, t2) => 
          hasFreeVariablesInSoundness(t1, c, d)
          hasFreeVariablesInSoundness(t2, c, d)
          concatFilter(t1.freeVars.filter(c <= _), t2.freeVars.filter(c <= _), _ < c + d)
          concatFilter(t1.freeVars, t2.freeVars, c <= _)
        case ArrowType(t1, t2) =>
          hasFreeVariablesInSoundness(t1, c, d)
          hasFreeVariablesInSoundness(t2, c, d)
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
          //This assertion is needed in order to help Stainless to verify the proof quickly!!!
          assert(t.freeVars.filter(x => c <= x && x < c + d) == b.freeVars.filter(x => c + 1 <= x && x < c + 1 + d).map(_ + - 1))
          
    }.ensuring(t.freeVars.filter(x => c <= x && x < c + d).isEmpty == !t.hasFreeVariablesIn(c, d))


    @opaque @pure
    def hasFreeVariablesAboveSoundness(t: Type, c: BigInt): Unit = {
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
        case VariableType(j) => ()
        case AbsType(_, b) => 
          hasFreeVariablesAboveSoundness(b, c + 1)
          mapAddSub(b.freeVars.filter(_ > 0), 1)
          mapAddSub(b.freeVars.filter(_ > 0).filter(_ >= c + 1), 1)
          filterMapAddGe(b.freeVars.filter(_ > 0), -1, c)
          filterCommutative(b.freeVars, _ > 0, _ >= c + 1)
    }.ensuring(t.freeVars.filter(_ >= c).isEmpty == !t.hasFreeVariablesAbove(c))
  
    @opaque @pure
    def isClosedSoundness(t: Type): Unit = {
      freeVarsNonNeg(t)
      hasFreeVariablesAboveSoundness(t, 0)
    }.ensuring(t.freeVars.isEmpty == t.isClosed)

    @opaque @pure
    def boundRangeDecrease(t: Type, c: BigInt, d1: BigInt, d2: BigInt): Unit = {
      require(d1 >= 0 && d2 >= 0)
      require(c >= 0)
      require(d2 <= d1)
      require(!t.hasFreeVariablesIn(c, d1))

      t match
        case BasicType(_) => ()
        case ArrowType(t1, t2) => 
          boundRangeDecrease(t1, c, d1, d2)
          boundRangeDecrease(t2, c, d1, d2)
        case VariableType(v) => ()
        case AbsType(_, body) => boundRangeDecrease(body, c+1, d1, d2)
        case AppType(t1, t2) => 
          boundRangeDecrease(t1, c, d1, d2)
          boundRangeDecrease(t2, c, d1, d2)

    }.ensuring(!t.hasFreeVariablesIn(c, d2))

    @opaque @pure
    def boundRangeIncreaseCutoff(t: Type, c1: BigInt, c2: BigInt, d: BigInt): Unit = {
      require(c1 >= 0 && c2 >= 0)
      require(0 <= d && c2 - c1 <= d)
      require(c1 <= c2)
      require(!t.hasFreeVariablesIn(c1, d))

      t match 
        case BasicType(_) => ()
        case ArrowType(t1, t2) => 
          boundRangeIncreaseCutoff(t1, c1, c2, d)
          boundRangeIncreaseCutoff(t2, c1, c2, d)
        case VariableType(v) => ()
        case AbsType(_, body) => boundRangeIncreaseCutoff(body, c1 + 1, c2 + 1, d)
        case AppType(t1, t2) => 
          boundRangeIncreaseCutoff(t1, c1, c2, d)
          boundRangeIncreaseCutoff(t2, c1, c2, d)
        
    }.ensuring(!t.hasFreeVariablesIn(c2, d - (c2 - c1)))

    @opaque @pure
    def boundRangeConcatenation(t: Type, a: BigInt, b: BigInt, c: BigInt): Unit = {
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
        case AppType(t1, t2) => 
          boundRangeConcatenation(t1, a, b, c)
          boundRangeConcatenation(t2, a, b, c)

    }.ensuring(!t.hasFreeVariablesIn(a, b + c))
    
  }

}