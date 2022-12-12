/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  * 
  *  This file defines De Bruijn indices operations such as shift and substitutions and their main properties (TAPL Chap 6).
  *  De Bruijn indices for types are covered here whereas terms are covered in TermTransformations.
  */
import stainless.lang._
import stainless.collection._
import stainless.annotation._

import LambdaOmega._

object TypeTransformations {
  
  import TypeTransformationsProperties._

  /**
    * d place shift of a type above cutoff c - TAPL Definition 6.2.1
    */
  @pure
  def shift(t: Type, d: BigInt, c: BigInt): Type = {
    decreases(t)
    require(c >= 0)
    require(d < 0 ==> !t.hasFreeVariablesIn(c, -d))
    t match 
      case BasicType(_) => t
      case ArrowType(t1, t2) => ArrowType(shift(t1, d, c), shift(t2, d, c))
      case VariableType(k) => if (k < c) VariableType(k) else VariableType(k + d)
      case AbsType(arg, body) => AbsType(arg, shift(body, d, c + 1))
      case AppType(t1, t2) => AppType(shift(t1, d, c), shift(t2, d, c))
  }.ensuring(_.size == t.size)

  /**
  * Substitution of a type s for variable number j in type t - TAPL Definition 6.2.4
  */
  @pure
  def substitute(t: Type, j: BigInt, s: Type): Type = {
    decreases(t)
    t match 
      case BasicType(_) => t
      case ArrowType(t1, t2) => ArrowType(substitute(t1, j, s), substitute(t2, j, s))
      case VariableType(k) => if(j == k) s else t  
      case AbsType(k, b) => AbsType(k, substitute(b, j + 1, shift(s, 1, 0)))
      case AppType(t1, t2) => AppType(substitute(t1, j, s), substitute(t2, j, s))
  }

  // ↑⁻¹( [0 -> ↑¹(arg)]body )
  @pure
  def absSubstitution(body: Type, arg: Type): Type = {
    boundRangeShift(arg, 1, 0, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
  }

  // def shift(env: TypeEnvironment, d: BigInt, c: BigInt): TypeEnvironment = {
  //   require(c >= 0)
  //   require(if(d < 0) !hasFreeVariablesIn(env, c, -d) else true)
    
  //   env match {
  //     case Nil() => Nil[Type]()
  //     case Cons(h, t) => {
  //       Cons(shift(h, d, c), shift(t, d, c))
  //     }
  //   }
  // }.ensuring(res => res.length == env.length)

  // def substitute(env: TypeEnvironment, d: BigInt, typ: Type): TypeEnvironment = {
  //   env.map(substitute(_, d, typ))
  // }
}

object TypeTransformationsProperties {
  import LambdaOmegaProperties.Types._
  import TypeTransformations._

  /**
   * * Short version: If J ∉ FV(T), [J -> S]T = T
   * 
   * Long version:
   *
   * Preconditions:
   *   - j is non negative
   *   - FV(t) ∩ [j, j + 1[ = ∅
   * 
   * Postcondition:
   *   - [j -> S]t = t
   */
  @inlineOnce @opaque @pure
  def boundRangeSubstitutionIdentity(t: Type, j: BigInt, typ: Type): Unit = {
    decreases(t)
    require(j >= 0)
    require(!t.hasFreeVariablesIn(j, 1))

    t match 
      case VariableType(_) => ()
      case BasicType(_) =>  ()
      case AbsType(_, body) => 
        boundRangeSubstitutionIdentity(body, j+1, shift(typ, 1 ,0))
      case ArrowType(t1, t2) => 
        boundRangeSubstitutionIdentity(t1, j, typ)
        boundRangeSubstitutionIdentity(t2, j, typ)
      case AppType(t1, t2) => 
        boundRangeSubstitutionIdentity(t1, j, typ)
        boundRangeSubstitutionIdentity(t2, j, typ)

  }.ensuring(substitute(t, j, typ) == t)

  /**
    * A 0 place shift does not affect the time
    */
  @inlineOnce @opaque @pure
  def shift0Identity(t: Type, c: BigInt): Unit = {
    decreases(t)
    require(c >= 0)
    t match 
      case VariableType(_) => ()
      case BasicType(_) => ()
      case AbsType(_, body) => 
        shift0Identity(body, c+1)
      case ArrowType(t1, t2) => 
        shift0Identity(t1, c)
        shift0Identity(t2, c)
      case AppType(t1, t2) => 
        shift0Identity(t1, c)
        shift0Identity(t2, c)

  }.ensuring(shift(t, 0, c) == t)

  /**
    * This theorem states how to compose two shifts into one bigger shift under some conditions
    * 
    * * Short and less general version: shift(shift(T, a, c), b, c) == shift(T, a + b, c)
    * 
    * Long version:
    *
    * Preconditions:
    *   - a, c and d are non negative (could be generalized for a < 0 as well)
    *   - d <= c + a
    *   - FV(t) ∩ [c, d[ = ∅ if c <= d, otherwise invert c and d
    *   - b >= - a
    * 
    * Postcondition:
    *   - If b < 0, FV(shift(t, a, c)) ∩ [d, d - b[ = ∅ (not interesting, but needed in order to express the second result)
    *   - shift(shift(t, a, c), b, d) == shift(t, a + b, c)
    * 
    */
  @inlineOnce @opaque @pure
  def boundRangeShiftComposition(t: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    decreases(t)
    require(a >= 0)
    require(c >= 0)
    require(d >= 0)
    require(d <= c + a)
    require(if(d < c) !t.hasFreeVariablesIn(d, c - d) else !t.hasFreeVariablesIn(c, d - c))
    require(-b <= a)


    if d < c then
      boundRangeShift(t, a, c, c, 0)
      boundRangeShift(t, a, c, d, c - d)
      boundRangeConcatenation(shift(t, a, c), d, c - d, a)
      boundRangeDecrease(shift(t, a, c), d, c - d + a, a)
    else
      boundRangeShift(t, a, c, c, d - c)
      boundRangeIncreaseCutoff(shift(t, a, c), c, d, a + d - c)

    if b < 0 then boundRangeDecrease(shift(t, a, c), d, a, -b) else () 

    t match 
      case VariableType(_) => ()
      case BasicType(_) => ()
      case AbsType(_, body) => 
        boundRangeShiftComposition(body, a, b, c + 1, d + 1)
      case ArrowType(t1, t2) => 
        boundRangeShiftComposition(t1, a, b, c, d)
        boundRangeShiftComposition(t2, a, b, c, d)
      case AppType(t1, t2) => 
        boundRangeShiftComposition(t1, a, b, c, d)
        boundRangeShiftComposition(t2, a, b, c, d)

  }.ensuring(
    (b < 0 ==> !shift(t, a, c).hasFreeVariablesIn(d, -b)) &&
    shift(shift(t, a, c), b, d) == shift(t, a + b, c)
  )

  /**
    * Describes exactly how free variables behave after shifts
    */
  @inlineOnce @opaque @pure
  def boundRangeShift(t: Type, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
    decreases(t)
    require(c >= 0)
    require(b >= 0)
    require(a >= 0)
    require(d < 0 ==> !t.hasFreeVariablesIn(c, -d))

    t match
      case BasicType(_)       => ()
      case VariableType(_)    => ()
      case AbsType(_, body)   => 
        boundRangeShift(body, d, c+1, a + 1, b)
      case ArrowType(t1, t2)  => 
        boundRangeShift(t1, d, c, a, b)
        boundRangeShift(t2, d, c, a, b)
      case AppType(t1, t2)    => 
        boundRangeShift(t1, d, c, a, b)
        boundRangeShift(t2, d, c, a, b)

  }.ensuring(
      !t.hasFreeVariablesIn(a, b)
        ==
      (if d >= 0 then 
        ((c >= a && c <= a + b)           ==> !shift(t, d, c).hasFreeVariablesIn(a, b + d)) &&
        ((c <= a + b)                     ==> !shift(t, d, c).hasFreeVariablesIn(a + d, b)) &&
        ((c >= a)                         ==> !shift(t, d, c).hasFreeVariablesIn(a, b))
      else
        ((a + b <= c)                     ==> !shift(t, d, c).hasFreeVariablesIn(a, b)) &&
        ((a + b >= c && a <= c)           ==> !shift(t, d, c).hasFreeVariablesIn(a, c - a)) &&
        ((a + b >= -d + c && a <= -d + c) ==> !shift(t, d, c).hasFreeVariablesIn(c, a + b + d - c)) &&
        ((a >= -d + c)                    ==> !shift(t, d, c).hasFreeVariablesIn(a + d, b)))
    )

  /**
    * * Short version: If FV(S) ∩ [0, J + 1[ = ∅, then J ∉ FV([J -> S]T)
    * 
    * Long version:
    * 
    * Preconditions:
    *   - j is a non negative type variable
    *   - FV(S) ∩ [0, j + 1[ = ∅
    * 
    * Postcondition:
    *  FV([j -> S]T) ∩ [j, j + 1[ = ∅
    */
  @inlineOnce @opaque @pure
  def boundRangeSubstitutionLemma(t: Type, j: BigInt, s: Type): Unit = {
    decreases(t)
    require(j >= 0)
    require(!s.hasFreeVariablesIn(0, j+1))

    t match 
      case BasicType(_) => ()
      case VariableType(_) => 
        boundRangeIncreaseCutoff(s, 0, j, j+1)
      case AbsType(_, body) => 
        boundRangeShift(s, 1, 0, 0, j+1)
        boundRangeIncreaseCutoff(shift(s, 1, 0), 0, j + 1, j+2)
        boundRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
      case ArrowType(t1, t2) =>
        boundRangeSubstitutionLemma(t1, j, s)
        boundRangeSubstitutionLemma(t2, j, s)
      case AppType(t1, t2) => 
        boundRangeSubstitutionLemma(t1, j, s)
        boundRangeSubstitutionLemma(t2, j, s)
  }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(j, 1))


  /** 
    * The four following theorems state under which conditions, two shifts commute
    */
  @inlineOnce @opaque @pure
  def shiftCommutativityPosPos(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    decreases(subs)
    require(a >= 0)
    require(b >= 0)
    require(c >= 0)
    require(d >= 0)
  
    subs match 
      case BasicType(_) => ()
      case ArrowType(t1, t2) =>
        shiftCommutativityPosPos(t1, b, c, a, d)
        shiftCommutativityPosPos(t2, b, c, a, d)
      case AppType(t1, t2) => 
        shiftCommutativityPosPos(t1, b, c, a, d)
        shiftCommutativityPosPos(t2, b, c, a, d)
      case VariableType(v) => ()
      case AbsType(_, t) => shiftCommutativityPosPos(t, b, c+1, a, d+1) 
      
  }.ensuring(
    if d <= c                then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
    if d - b >= c            then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
    if d >= c && d - b <= c  then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, c), b, c) else
    true)

  @inlineOnce @opaque @pure
  def shiftCommutativityPosNeg(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit = {
    decreases(subs)
    require(c >= 0)
    require(d >= 0)
    require(b >= 0)
    require(a < 0)
    require(if d >= c && b >= d - c  then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(c, -a) else
            if b <= d - c            then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d - b, -a) else
            if -a <= c - d           then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d, -a) else
            if d <= c && -a >= c - d then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) else
            true) 

    subs match 
      case BasicType(_) => ()
      case ArrowType(t1, t2) =>
        shiftCommutativityPosNeg(t1, b, c, a, d)
        shiftCommutativityPosNeg(t2, b, c, a, d)
      case AppType(t1, t2) => 
        shiftCommutativityPosNeg(t1, b, c, a, d)
        shiftCommutativityPosNeg(t2, b, c, a, d)
      case VariableType(_) => ()
      case AbsType(_, t) => shiftCommutativityPosNeg(t, b, c+1, a, d+1) 
      
  }.ensuring(
    if d >= c && b >= d - c  then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(c, -a) &&
                                  shift(shift(subs, b, c), a, d) == shift(shift(subs, a, c), b, c) else
    if b <= d - c            then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d - b, -a) &&
                                  shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
    if -a <= c - d           then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) &&
                                  shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
    if d <= c && -a >= c - d then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) &&
                                  shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, d)
    else true)

  @inlineOnce @opaque @pure
  def shiftCommutativityNegPos(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit = {
    decreases(subs)
    require(c >= 0)
    require(d >= 0)
    require(b < 0)
    require(a >= 0)
    require(!subs.hasFreeVariablesIn(c, -b))
    
    //Weaker but more complex precond
    // require(if d >= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) else 
    //         if d <= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) else
    //         true) 

    subs match 
      case BasicType(_) => ()
      case ArrowType(t1, t2) =>
        shiftCommutativityNegPos(t1, b, c, a, d)
        shiftCommutativityNegPos(t2, b, c, a, d)
      case AppType(t1, t2) => 
        shiftCommutativityNegPos(t1, b, c, a, d)
        shiftCommutativityNegPos(t2, b, c, a, d)
      case VariableType(_) => ()
      case AbsType(_, t) => shiftCommutativityNegPos(t, b, c+1, a, d+1) 
      
  }.ensuring(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) && 
                                      shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
              if d <= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) && 
                                      shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
              true)


  @inlineOnce @opaque @pure
  def shiftCommutativityNegNeg(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    decreases(subs)
    require(c >= 0)
    require(d >= 0)
    require(a < 0)
    require(b < 0)
    require(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d - b, -a) else
            if d <= c && -a <= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) else 
            if d <= c && -a >= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
                                                            !shift(subs, b, c).hasFreeVariablesIn(d, -a) else
            true) 

    subs match 
      case BasicType(_) => ()
      case ArrowType(t1, t2) =>
        shiftCommutativityNegNeg(t1, b, c, a, d)
        shiftCommutativityNegNeg(t2, b, c, a, d)
      case AppType(t1, t2) => 
        shiftCommutativityNegNeg(t1, b, c, a, d)
        shiftCommutativityNegNeg(t2, b, c, a, d)
      case VariableType(_) => ()
      case AbsType(_, t) => shiftCommutativityNegNeg(t, b, c+1, a, d+1) 
      
  }.ensuring(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d - b, -a) && 
                                            !shift(subs, a, d - b).hasFreeVariablesIn(c, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
                                            shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
              if d <= c && -a <= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
                                            !shift(subs, a, d).hasFreeVariablesIn(c + a, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
                                            shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
              if d <= c && -a >= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
                                            !shift(subs, a, d).hasFreeVariablesIn(d, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
                                            shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, d) else
              true)


  /**
    * States how shift and substitution commute
    */
  @inlineOnce @opaque @pure
  def shiftSubstitutionCommutativity(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    decreases(typ)
    require(k >= 0)
    require(c >= 0)
    require(
      if s < 0 then 
        !typ.hasFreeVariablesIn(c, -s) && !subs.hasFreeVariablesIn(c, -s)
      else true)

    typ match 
      case BasicType(_) => ()
      case ArrowType(t1, t2) => 
        shiftSubstitutionCommutativity(t1, s, c, k, subs)
        shiftSubstitutionCommutativity(t2, s, c, k, subs)
      case AppType(t1, t2) => 
        shiftSubstitutionCommutativity(t1, s, c, k, subs)
        shiftSubstitutionCommutativity(t2, s, c, k, subs)
      case VariableType(v) => 
        if c >= 0 && c <= k && s < 0 then
          boundRangeShiftComposition(subs, -s, s, c, c)
          if v >= c && k == v + s then
              boundRangeShiftComposition(subs, -s, s, c, c)
              shift0Identity(subs, c)          
          else ()
        else ()
      case AbsType(argK, t) => 
        if s >= 0 then
          shiftCommutativityPosPos(subs, s, c, 1, 0)
        else
          boundRangeShift(subs, 1, 0, c, -s)
          if c > k then
            shiftCommutativityNegPos(subs, s, c, 1, 0)
          else
            shiftCommutativityPosPos(subs, -s, c, 1, 0)
        shiftSubstitutionCommutativity(t, s, c+1, k+1, shift(subs, 1, 0))

  }.ensuring(
    if s >= 0 then
      if c >= 0 && c <= k then shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k+s, shift(subs, s, c))
                          else shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k, shift(subs, s, c))
    else if c >= 0 && c <= k 
      then !substitute(typ, k - s, shift(subs, -s, c)).hasFreeVariablesIn(c, -s) && 
            shift(substitute(typ, k - s, shift(subs, -s, c)), s, c) == substitute(shift(typ, s, c), k, subs)
      else !substitute(typ, k, subs).hasFreeVariablesIn(c, -s) && 
            shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k, shift(subs, s, c))
  )

  /**
    * Describes how free variables behave after substitutions
    */
  @inlineOnce @opaque @pure
  def boundRangeSubstitutionLemma(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    decreases(t)
    require(j >= 0)
    require(a >= 0)
    require(b >= 0)
    require(c >= 0)
    require(d >= 0)
    require(!s.hasFreeVariablesIn(c, a))
    require(!t.hasFreeVariablesIn(d, b))

    t match 
      case BasicType(_) =>  ()
      case ArrowType(t1, t2) => 
        boundRangeSubstitutionLemma(t1, j, s, a, b, c, d)
        boundRangeSubstitutionLemma(t2, j, s, a, b, c, d)
      case AppType(t1, t2) => 
        boundRangeSubstitutionLemma(t1, j, s, a, b, c, d)
        boundRangeSubstitutionLemma(t2, j, s, a, b, c, d)
      case VariableType(_) => 
        if c <= d then
          if c + a >= d + b then
            boundRangeIncreaseCutoff(s, c, d, a)
            boundRangeDecrease(s, d, a - (d - c), b) 
          else if c + a <= d + b && c + a >= d then
            boundRangeDecrease(t, d, b, a - (d - c))
            boundRangeIncreaseCutoff(s, c, d, a)
          else ()
        else 
          if c + a <= d + b then
            boundRangeIncreaseCutoff(t, d, c, b)
            boundRangeDecrease(t, c, b - (c - d), a)
          else if c + a >= d + b && c <= d + b then
            boundRangeDecrease(s, c, a, b - (c - d))
            boundRangeIncreaseCutoff(t, d, c, b)
          else ()
      case AbsType(_, body) =>
        if c > 0 then
          boundRangeShift(s, 1, 0, c, a)
        else
          boundRangeShift(s, 1, 0, 0, a)
          boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
        boundRangeSubstitutionLemma(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)
  }.ensuring(
    if c <= d then
      if c + a >= d + b               then !substitute(t, j, s).hasFreeVariablesIn(d, b) else
      if c + a <= d + b && c + a >= d then !substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c))
      else true /*non trivial range*/
    else
      if c + a <= d + b               then !substitute(t, j, s).hasFreeVariablesIn(c, a) else
      if c + a >= d + b && c <= d + b then !substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d))
      else true /*non trivial range*/)




  /**
    * States how substitution commutes (mentioned in proof of TAPL Lemma 30.3.4)
    * 
    * * Short version: If J ∉ FV(U) and J ≠ K then [K -> U][J -> S]T = [J -> [K -> U]S][K -> U]T
    * 
    * Long version:
    *  
    * Preconditions:
    *   - j ≠ k are non negative type variables
    *   - FV(u) ∩ [j, j + 1[ = ∅
    * 
    * Postcondition:
    *   [h -> u][j -> s]t = [j -> [k -> u]s][k -> u]t
    */
  @inlineOnce @opaque @pure
  def substitutionCommutativity(t: Type, j: BigInt, s: Type, k: BigInt, u: Type): Unit = {
    decreases(t)
    require(j >= 0)
    require(k >= 0)
    require(j != k)
    require(!u.hasFreeVariablesIn(j, 1))

    t match 
      case VariableType(i) => if i == k then boundRangeSubstitutionIdentity(u, j, substitute(s, k, u)) else ()
      
      case BasicType(_) => ()
      case ArrowType(t1, t2) => 
        substitutionCommutativity(t1, j, s, k, u)
        substitutionCommutativity(t2, j, s, k, u)
      
      case AppType(t1, t2) => 
        substitutionCommutativity(t1, j, s, k, u)
        substitutionCommutativity(t2, j, s, k, u)
      
      case AbsType(_, b) => 
        shiftSubstitutionCommutativity(s, 1, 0, k, u)
        boundRangeShift(u, 1, 0, j, 1)
        substitutionCommutativity(b, j+1, shift(s, 1, 0), k+1, shift(u, 1, 0))
  }.ensuring(
    substitute(substitute(t, j, s), k, u)
    ==
    substitute(substitute(t, k, u), j, substitute(s, k, u))
  )

  
  /**
   * States how free variable behave when reducing redexed
   * 
   * * Short version: FV((λ.T1)(T2)) ∩ [c, c + d[ = ∅ => FV(↑⁻¹([0 -> ↑¹T2]T1)) ∩ [c, c + d[ = ∅
   * 
   * Long version:
   * 
   * Preconditions:
   *   - c and d are non negative integers
   *   - FV(arg) ∩ [c, c + d[ = ∅ (arg = T2 in the above statement)
   *   - FV(body) ∩ [c + 1, c + 1 + d[ = ∅ (body = T1 in the above statement)
   *   ! These two conditions imply FV((λ.body)(arg)) ∩ [c, c + d[ = ∅
   * 
   * Postcondition:
   *   FV(↑⁻¹([0 -> ↑¹arg]body)) ∩ [c, c + d[ = ∅
   */
  @inlineOnce @opaque @pure
  def boundRangeAbsSubst(body: Type, arg: Type, c: BigInt, d: BigInt) = {
    require(c >= 0)
    require(d >= 0)
    require(!arg.hasFreeVariablesIn(c, d))
    require(!body.hasFreeVariablesIn(c + 1, d))

    boundRangeShift(arg, 1, 0, c, d)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0), d, d, c + 1, c + 1)
    boundRangeShift(arg, 1, 0, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    boundRangeShift(substitute(body, 0, shift(arg, 1, 0)), -1, 0, c + 1, d)
  }.ensuring(!absSubstitution(body, arg).hasFreeVariablesIn(c, d))

  /**
    * States how shift commutes with redex reduction 
    * 
    * * Short version: shift(↑⁻¹([0 -> ↑¹T2]T1), d, c) = ↑⁻¹([0 -> ↑¹shift(T2, d, c)]shift(T1, d, c + 1))
    * 
    * Long version:
    *  
    * Preconditions:
    *   - c is a non negative integer
    *   - if d < 0 then  FV(arg) ∩ [c, c + d[ = ∅ and FV(body) ∩ [c + 1, c + 1 + d[ = ∅ (where body = T1 and arg = T2
    *     in the above version)
    *   ! Therefore if d < 0 then FV((λ.body)(arg)) ∩ [c, c + d[ = ∅
    * 
    * Postcondition:
    *   shift(↑⁻¹([0 -> ↑¹arg]body), d, c) = ↑⁻¹([0 -> ↑¹shift(arg, d, c)]shift(body, d, c + 1))
    */
  @inlineOnce @opaque @pure
  def shiftAbsSubstitutionCommutativity(body: Type, arg: Type, d: BigInt, c: BigInt) = {
    require(c >= 0)
    require(d < 0 ==> (!arg.hasFreeVariablesIn(c, -d) && !body.hasFreeVariablesIn(c + 1, -d)))

    boundRangeShift(arg, 1, 0, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))

    if d < 0 then
      boundRangeShift(arg, 1, 0, c, -d)
      boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0), -d, -d, c + 1, c + 1)
      boundRangeShift(substitute(body, 0, shift(arg, 1, 0)), -1, 0, c + 1, -d)
      shiftCommutativityNegNeg(substitute(body, 0, shift(arg, 1, 0)), -1, 0, d, c)
      shiftSubstitutionCommutativity(body, d, c + 1, 0, shift(arg, 1, 0))
      shiftCommutativityPosNeg(arg, 1, 0, d, c + 1)
    else
      shiftCommutativityNegPos(substitute(body, 0, shift(arg, 1, 0)), -1, 0, d, c)
      shiftSubstitutionCommutativity(body, d, c + 1, 0, shift(arg, 1, 0))
      shiftCommutativityPosPos(arg, d, c, 1, 0)
  }.ensuring(_ => shift(absSubstitution(body, arg), d, c) == absSubstitution(shift(body, d, c + 1), shift(arg, d, c)))

  /**
    * States how substitution commutes with redex reduction 
    * 
    * * Short version: If 0 ∉ FV(S) then [J -> S]↑⁻¹([0 -> ↑¹T2]T1) = ↑⁻¹([0 -> ↑¹[J -> S]T2][J + 1 -> ↑¹S]T1)
    * 
    * Long version: (where body = T1 and arg = T2)
    *  
    * Preconditions:
    *   - j is a non negative type variable
    *   - FV(s) ∩ [0, 1[ = ∅
    * 
    * Postcondition:
    *   [j -> s]↑⁻¹([0 -> ↑¹arg]body) = ↑⁻¹([0 -> ↑¹[j -> s]arg][j + 1 -> ↑¹s]body
    */
  @inlineOnce @opaque @pure
  def absSubstSubstCommutativity(body: Type, arg: Type, j: BigInt, s: Type): Unit = {
    require(j >= 0)
    require(!s.hasFreeVariablesIn(0, 1))

    boundRangeShift(arg, 1, 0, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    shiftSubstitutionCommutativity(substitute(body, 0, shift(arg, 1, 0)), -1, 0, j, s)
    boundRangeShift(s, 1, 0, 0, 0)
    substitutionCommutativity(body, 0, shift(arg, 1, 0), j + 1, shift(s, 1, 0))
    shiftSubstitutionCommutativity(arg, 1, 0, j, s)

  }.ensuring(
    substitute(absSubstitution(body, arg), j, s)
    ==
    absSubstitution(substitute(body, j + 1, shift(s, 1, 0)), substitute(arg, j, s))
  )    
}

