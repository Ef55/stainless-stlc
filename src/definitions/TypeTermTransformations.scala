/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  * 
  *  This file defines De Bruijn indices operations such as shift and substitutions and their main properties (TAPL Chap 6).
  *  De Bruijn indices for terms are covered here whereas types are covered in TypeTransformations.
  */
import stainless.lang._
import stainless.collection._
import stainless.annotation._

import LambdaOmega._
import TypeTransformations._

object TypeTermTransformations {
  
  import TypeTransformationsProperties._
  import TypeTermTransformationsProperties._

  /**
    * d place shift of a term above cutoff c - TAPL Definition 6.2.1
    */
  @pure
  def shiftType(t: Term, d: BigInt, c: BigInt): Term = {
    require(c >= 0)
    require((d < 0) ==> !t.hasFreeTypeVariablesIn(c, -d))
    decreases(t)
    t match 
      case Var(k) => Var(k)
      case Abs(arg, body) => Abs(shift(arg, d, c), shiftType(body, d, c))
      case App(t1, t2) => App(shiftType(t1, d, c), shiftType(t2, d, c))
      case TApp(body, typ) => TApp(shiftType(body, d, c), shift(typ, d, c))
      case TAbs(arg, body) => TAbs(arg, shiftType(body, d, c + 1))
  }.ensuring(_.size == t.size)

  /**
  * Substitution of a term s for variable number j in term t - TAPL Definition 6.2.4
  */
  @pure
  def substituteType(t: Term, j: BigInt, s: Type): Term = {
    decreases(t)
    t match 
      case Var(k) => Var(k)
      case Abs(argT, b) => Abs(substitute(argT, j, s), substituteType(b, j, s))
      case App(t1, t2) => App(substituteType(t1, j, s), substituteType(t2, j, s))
      case TApp(body, typ) => TApp(substituteType(body, j, s), substitute(typ, j, s))
      case TAbs(arg, body) => TAbs(arg, substituteType(body, j + 1, shift(s, 1, 0)))
  }

  // ↑⁻¹[0 -> ↑¹(arg)]body
  @pure
  def absSubstitutionType(body: Term, arg: Type): Term = {
    boundRangeShift(arg, 1, 0, 0, 0)
    boundTypeRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    shiftType(substituteType(body, 0, shift(arg, 1, 0)), -1, 0)
  }
}

object TypeTermTransformationsProperties {
  import LambdaOmegaProperties.Terms._
  import LambdaOmegaProperties.Types._
  import TypeTermTransformations._
  import TypeTransformationsProperties._

  /**
   * * Short version: If j ∉ FV(t), [j -> s]t = t
   * 
   * Long version:
   *
   * Preconditions:
   *   - j is non negative
   *   - FV(t) ∩ [j, j + 1[ = ∅
   * 
   * Postcondition:
   *   - [j -> s]t = t
   */
  @inlineOnce @opaque @pure
  def boundTypeRangeSubstitutionIdentity(t: Term, j: BigInt, typ: Type): Unit = {
    decreases(t)
    require(j >= 0)
    require(!t.hasFreeTypeVariablesIn(j, 1))


    t match 
      case Var(_) => ()
      case Abs(argT, body) => 
        boundRangeSubstitutionIdentity(argT, j, typ)
        boundTypeRangeSubstitutionIdentity(body, j, typ)
      case App(t1, t2) => 
        boundTypeRangeSubstitutionIdentity(t1, j, typ)
        boundTypeRangeSubstitutionIdentity(t2, j, typ)
      case TApp(body, arg) => 
        boundTypeRangeSubstitutionIdentity(body, j, typ)
        boundRangeSubstitutionIdentity(arg, j, typ)
      case TAbs(_, body) => 
        boundTypeRangeSubstitutionIdentity(body, j + 1, shift(typ, 1, 0))

  }.ensuring(substituteType(t, j, typ) == t)

  /**
    * A 0 place shift does not affect the time
    */
  @inlineOnce @opaque @pure
  def shiftType0Identity(t: Term, c: BigInt): Unit = {
    decreases(t)
    require(c >= 0)

    t match 
      case Var(_) => ()
      case Abs(argT, body) => 
        shift0Identity(argT, c)
        shiftType0Identity(body, c)
      case App(t1, t2) => 
        shiftType0Identity(t1, c)
        shiftType0Identity(t2, c)
      case TApp(body, arg) => 
        shiftType0Identity(body, c)
        shift0Identity(arg, c)
      case TAbs(_, body) => 
        shiftType0Identity(body, c + 1)

  }.ensuring(shiftType(t, 0, c) == t)

  /**
    * This theorem states how to compose two shifts into one bigger shift under some conditions
    * 
    * * Short and less general version: shift(shift(t, a, c), b, c) == shift(t, a + b, c)
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
  def boundTypeRangeShiftComposition(t: Term, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    decreases(t)
    require(a >= 0)
    require(c >= 0)
    require(d >= 0)
    require(d <= c + a)
    require(if d < c then !t.hasFreeTypeVariablesIn(d, c - d) else !t.hasFreeTypeVariablesIn(c, d - c))
    require(-b <= a)


    if d < c then
      boundTypeRangeShift(t, a, c, c, 0)
      boundTypeRangeShift(t, a, c, d, c - d)
      boundTypeRangeConcatenation(shiftType(t, a, c), d, c - d, a)
      boundTypeRangeDecrease(shiftType(t, a, c), d, c - d + a, a)
    else
      boundTypeRangeShift(t, a, c, c, d - c)
      boundTypeRangeIncreaseCutoff(shiftType(t, a, c), c, d, a + d - c)

    if b < 0 then boundTypeRangeDecrease(shiftType(t, a, c), d, a, -b) else ()

    t match 
      case Var(_) => ()
      case Abs(arg, body) => 
        boundRangeShiftComposition(arg, a, b, c, d)
        boundTypeRangeShiftComposition(body, a, b, c, d)
      case App(t1, t2) => 
        boundTypeRangeShiftComposition(t1, a, b, c, d)
        boundTypeRangeShiftComposition(t2, a, b, c, d)
      case TApp(body, arg) => 
        boundTypeRangeShiftComposition(body, a, b, c, d)
        boundRangeShiftComposition(arg, a, b, c, d)
      case TAbs(_, body) => boundTypeRangeShiftComposition(body, a, b, c + 1, d + 1)
  }.ensuring(
    (b < 0 ==> !shiftType(t, a, c).hasFreeTypeVariablesIn(d, -b)) &&
    shiftType(shiftType(t, a, c), b, d) == shiftType(t, a + b, c)
  )

  /**
    * Describes exactly how free variables behave after shifts
    */
  @inlineOnce @opaque @pure
  def boundTypeRangeShift(t: Term, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
    decreases(t)
    require(c >= 0)
    require(b >= 0)
    require(a >= 0)
    require(d < 0 ==> !t.hasFreeTypeVariablesIn(c, -d))

    t match
      case Var(_) => ()
      case Abs(argT, body) => 
        boundTypeRangeShift(body, d, c, a, b)
        boundRangeShift(argT, d, c, a, b)        
      case App(t1, t2) => 
        boundTypeRangeShift(t1, d, c, a, b)
        boundTypeRangeShift(t2, d, c, a, b)
      case TApp(body, arg) => 
        boundTypeRangeShift(body, d, c, a, b)
        boundRangeShift(arg, d, c, a, b)
      case TAbs(_, body) => 
        boundTypeRangeShift(body, d, c+1, a + 1, b)

  }.ensuring(
      !t.hasFreeTypeVariablesIn(a, b)
        ==
      (if d >= 0 then
        ((c >= a && c <= a + b)           ==> !shiftType(t, d, c).hasFreeTypeVariablesIn(a, b + d)) &&
        ((c <= a + b)                     ==> !shiftType(t, d, c).hasFreeTypeVariablesIn(a + d, b)) &&
        ((c >= a)                         ==> !shiftType(t, d, c).hasFreeTypeVariablesIn(a, b))
      else 
        ((a + b <= c)                     ==> !shiftType(t, d, c).hasFreeTypeVariablesIn(a, b)) &&
        ((a + b >= c && a <= c)           ==> !shiftType(t, d, c).hasFreeTypeVariablesIn(a, c - a)) &&
        ((a + b >= -d + c && a <= -d + c) ==> !shiftType(t, d, c).hasFreeTypeVariablesIn(c, a + b + d - c)) &&
        ((a >= -d + c)                    ==> !shiftType(t, d, c).hasFreeTypeVariablesIn(a + d, b)) 
      )
    )

  /**
    * * Short version: If FV(s) ∩ [0, j + 1[ = ∅, then J ∉ FV([j -> s]t)
    * 
    * Long version:
    * 
    * Preconditions:
    *   - j is a non negative variable
    *   - FV(S) ∩ [0, j + 1[ = ∅
    * 
    * Postcondition:
    *  FV([j -> S]T) ∩ [j, j + 1[ = ∅
    */
  @inlineOnce @opaque @pure
  def boundTypeRangeSubstitutionLemma(t: Term, j: BigInt, s: Type): Unit = {
    decreases(t)
    require(j >= 0)
    require(!s.hasFreeVariablesIn(0, j+1))

    t match
      case Var(_) => ()
      case Abs(argT, body) => 
        boundRangeSubstitutionLemma(argT, j, s)
        boundTypeRangeSubstitutionLemma(body, j, s)
      case App(t1, t2) => 
        boundTypeRangeSubstitutionLemma(t1, j, s)
        boundTypeRangeSubstitutionLemma(t2, j, s)
      case TApp(body, arg) => 
        boundTypeRangeSubstitutionLemma(body, j, s)
        boundRangeSubstitutionLemma(arg, j, s)
      case TAbs(_, body) => 
        boundRangeShift(s, 1, 0, 0, j+1)
        LambdaOmegaProperties.Types.boundRangeIncreaseCutoff(shift(s, 1, 0), 0, j + 1, j+2)
        boundTypeRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
        
        
        boundTypeRangeSubstitutionLemma(body, j, s)

  }.ensuring(!substituteType(t, j, s).hasFreeTypeVariablesIn(j, 1))


  /** 
    * The four following theorems state under which conditions, two shifts commute
    */
  @inlineOnce @opaque @pure
  def shiftTypeCommutativityPosPos(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    decreases(subs)
    require(a >= 0)
    require(b >= 0)
    require(c >= 0)
    require(d >= 0)
  
    subs match 
      case App(t1, t2) => 
        shiftTypeCommutativityPosPos(t1, b, c, a, d)
        shiftTypeCommutativityPosPos(t2, b, c, a, d)
      case Var(_) => ()
      case Abs(argT, t) => 
        shiftCommutativityPosPos(argT, b, c, a, d) 
        shiftTypeCommutativityPosPos(t, b, c, a, d) 
      case TApp(body, arg) => 
        shiftTypeCommutativityPosPos(body, b, c, a, d)
        shiftCommutativityPosPos(arg, b, c, a, d) 
      case TAbs(_, body) => shiftTypeCommutativityPosPos(body, b, c + 1, a, d + 1) 
      
  }.ensuring(
    if d <= c                then shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d), b, c + a) else
    if d - b >= c            then shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d - b), b, c) else
    if d >= c && d - b <= c  then shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, c), b, c) else
    true)

  @inlineOnce @opaque @pure
  def shiftTypeCommutativityPosNeg(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit = {
    require(c >= 0)
    require(d >= 0)
    require(b >= 0)
    require(a < 0)
    require(if d >= c && b >= d - c  then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) && !subs.hasFreeTypeVariablesIn(c, -a) else
            if b <= d - c            then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) || !subs.hasFreeTypeVariablesIn(d - b, -a) else
            if -a <= c - d           then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) || !subs.hasFreeTypeVariablesIn(d, -a) else
            if d <= c && -a >= c - d then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) && !subs.hasFreeTypeVariablesIn(d, -a) else
            true)
    decreases(subs)

    subs match 
      case App(t1, t2) => 
        shiftTypeCommutativityPosNeg(t1, b, c, a, d)
        shiftTypeCommutativityPosNeg(t2, b, c, a, d)
      case Var(_) => ()
      case Abs(argT, t) => 
        shiftCommutativityPosNeg(argT, b, c, a, d)
        shiftTypeCommutativityPosNeg(t, b, c, a, d)
      case TApp(body, arg) => 
        shiftTypeCommutativityPosNeg(body, b, c, a, d)
        shiftCommutativityPosNeg(arg, b, c, a, d)
      case TAbs(_, body) => shiftTypeCommutativityPosNeg(body, b, c + 1, a, d + 1)

  }.ensuring(
    if d >= c && b >= d - c  then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) && !subs.hasFreeTypeVariablesIn(c, -a) &&
                                  shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, c), b, c) else
    if b <= d - c            then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) && !subs.hasFreeTypeVariablesIn(d - b, -a) &&
                                  shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d - b), b, c) else
    if -a <= c - d           then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) && !subs.hasFreeTypeVariablesIn(d, -a) &&
                                  shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d), b, c + a) else
    if d <= c && -a >= c - d then !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) && !subs.hasFreeTypeVariablesIn(d, -a) &&
                                  shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d), b, d)
    else true)

  @inlineOnce @opaque @pure
  def shiftTypeCommutativityNegPos(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit = {
    decreases(subs)
    require(c >= 0)
    require(d >= 0)
    require(b < 0)
    require(a >= 0)
    require(!subs.hasFreeTypeVariablesIn(c, -b))
    
    //Weaker but more complex precond
    // require(if d >= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) else 
    //         if d <= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) else
    //         true) 

    subs match {
      case App(t1, t2) => 
        shiftTypeCommutativityNegPos(t1, b, c, a, d)
        shiftTypeCommutativityNegPos(t2, b, c, a, d)
      case Var(_) => ()
      case Abs(argT, body) => 
        shiftCommutativityNegPos(argT, b, c, a, d) 
        shiftTypeCommutativityNegPos(body, b, c, a, d) 
      case TApp(body, argT) => 
        shiftTypeCommutativityNegPos(body, b, c, a, d)
        shiftCommutativityNegPos(argT, b, c, a, d)
      case TAbs(_, body) => shiftTypeCommutativityNegPos(body, b, c + 1, a, d + 1)
      
    }
  }.ensuring(if d >= c                then !subs.hasFreeTypeVariablesIn(c, -b) && !shiftType(subs, a, d - b).hasFreeTypeVariablesIn(c, - b) && 
                                      shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d - b), b, c) else
              if d <= c                then !subs.hasFreeTypeVariablesIn(c, -b) && !shiftType(subs, a, d).hasFreeTypeVariablesIn(c + a, - b) && 
                                      shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d), b, c + a) else
              true)


  @inlineOnce @opaque @pure
  def shiftTypeCommutativityNegNeg(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit = {
    decreases(subs)
    require(c >= 0)
    require(d >= 0)
    require(a < 0)
    require(b < 0)
    require(if d >= c                then !subs.hasFreeTypeVariablesIn(c, -b) && !subs.hasFreeTypeVariablesIn(d - b, -a) else
            if d <= c && -a <= c - d then !subs.hasFreeTypeVariablesIn(c, -b) && !subs.hasFreeTypeVariablesIn(d, -a) else 
            if d <= c && -a >= c - d then !subs.hasFreeTypeVariablesIn(c, -b) && !subs.hasFreeTypeVariablesIn(d, -a) && 
                                                            !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) else
            true)

    subs match {
      case App(t1, t2) => 
        shiftTypeCommutativityNegNeg(t1, b, c, a, d)
        shiftTypeCommutativityNegNeg(t2, b, c, a, d)
      case Var(_) => ()
      case Abs(argT, body) => 
        shiftCommutativityNegNeg(argT, b, c, a, d)
        shiftTypeCommutativityNegNeg(body, b, c, a, d)
      case TApp(body, argT) => 
        shiftTypeCommutativityNegNeg(body, b, c, a, d)
        shiftCommutativityNegNeg(argT, b, c, a, d)
      case TAbs(_, body) => shiftTypeCommutativityNegNeg(body, b, c+1, a, d+1) 
        
      
    }
  }.ensuring( if d >= c                then !subs.hasFreeTypeVariablesIn(c, -b) && !subs.hasFreeTypeVariablesIn(d - b, -a) && 
                                            !shiftType(subs, a, d - b).hasFreeTypeVariablesIn(c, -b) && !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) &&
                                            shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d - b), b, c) else
              if d <= c && -a <= c - d then !subs.hasFreeTypeVariablesIn(c, -b) && !subs.hasFreeTypeVariablesIn(d, -a) && 
                                            !shiftType(subs, a, d).hasFreeTypeVariablesIn(c + a, -b) && !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) &&
                                            shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d), b, c + a) else
              if d <= c && -a >= c - d then !subs.hasFreeTypeVariablesIn(c, -b) && !subs.hasFreeTypeVariablesIn(d, -a) && 
                                            !shiftType(subs, a, d).hasFreeTypeVariablesIn(d, -b) && !shiftType(subs, b, c).hasFreeTypeVariablesIn(d, -a) &&
                                            shiftType(shiftType(subs, b, c), a, d) == shiftType(shiftType(subs, a, d), b, d) else
              true)


  /**
    * States how shift and substitution commute
    */
  @inlineOnce @opaque @pure
  def shiftTypeSubstitutionCommutativity(t: Term, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    decreases(t)
    require(k >= 0)
    require(c >= 0)
    require(
      if s < 0 then 
        !t.hasFreeTypeVariablesIn(c, -s) && !subs.hasFreeVariablesIn(c, -s)
      else true)

    t match {
      case App(t1, t2) => 
        shiftTypeSubstitutionCommutativity(t1, s, c, k, subs)
        shiftTypeSubstitutionCommutativity(t2, s, c, k, subs)
      case Var(_) => ()
      case Abs(argT, body) => 
        shiftTypeSubstitutionCommutativity(body, s, c, k, subs)
        shiftSubstitutionCommutativity(argT, s, c, k, subs)
      case TApp(body, argT) => 
        shiftTypeSubstitutionCommutativity(body, s, c, k, subs)
        shiftSubstitutionCommutativity(argT, s, c, k, subs)
      case TAbs(_, body) => 
        if s >= 0 then
          shiftCommutativityPosPos(subs, s, c, 1, 0)
        else
          boundRangeShift(subs, 1, 0, c, -s)
          if c > k then
            shiftCommutativityNegPos(subs, s, c, 1, 0)
          else
            shiftCommutativityPosPos(subs, -s, c, 1, 0)
        shiftTypeSubstitutionCommutativity(body, s, c+1, k+1, shift(subs, 1, 0))
    }
  }.ensuring(
    if s >= 0 then
      if c >= 0 && c <= k then shiftType(substituteType(t, k, subs), s, c) == substituteType(shiftType(t, s, c), k+s, shift(subs, s, c))
                          else shiftType(substituteType(t, k, subs), s, c) == substituteType(shiftType(t, s, c), k, shift(subs, s, c))
    else if c >= 0 && c <= k 
      then !substituteType(t, k - s, shift(subs, -s, c)).hasFreeTypeVariablesIn(c, -s) && 
            shiftType(substituteType(t, k - s, shift(subs, -s, c)), s, c) == substituteType(shiftType(t, s, c), k, subs)
      else !substituteType(t, k, subs).hasFreeTypeVariablesIn(c, -s) && 
            shiftType(substituteType(t, k, subs), s, c) == substituteType(shiftType(t, s, c), k, shift(subs, s, c))
  )

  /**
    * Describes how free variables behave after substitutions
    */
  @inlineOnce @opaque @pure
  def boundTypeRangeSubstitutionLemma(t: Term, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    decreases(t)
    require(j >= 0)
    require(a >= 0)
    require(b >= 0)
    require(c >= 0)
    require(d >= 0)
    require(!s.hasFreeVariablesIn(c, a))
    require(!t.hasFreeTypeVariablesIn(d, b))

    t match 
      case App(t1, t2) => 
        boundTypeRangeSubstitutionLemma(t1, j, s, a, b, c, d)
        boundTypeRangeSubstitutionLemma(t2, j, s, a, b, c, d)
      case Var(_) => ()
      case Abs(argT, body) =>
        boundTypeRangeSubstitutionLemma(body, j, s, a, b, c, d)
        boundRangeSubstitutionLemma(argT, j, s, a, b, c, d)
      case TApp(body, argT) => 
        boundTypeRangeSubstitutionLemma(body, j, s, a, b, c, d)
        boundRangeSubstitutionLemma(argT, j, s, a, b, c, d)
      case TAbs(_, body) => 
        if c > 0 then
          boundRangeShift(s, 1, 0, c, a)
        else
          boundRangeShift(s, 1, 0, 0, a)
          LambdaOmegaProperties.Types.boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
        boundTypeRangeSubstitutionLemma(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)
  }.ensuring(
    if c <= d then
      if c + a >= d + b               then !substituteType(t, j, s).hasFreeTypeVariablesIn(d, b) else
      if c + a <= d + b && c + a >= d then !substituteType(t, j, s).hasFreeTypeVariablesIn(d, a - (d - c))
      else true /*non trivial range*/
    else
      if c + a <= d + b               then !substituteType(t, j, s).hasFreeTypeVariablesIn(c, a) else
      if c + a >= d + b && c <= d + b then !substituteType(t, j, s).hasFreeTypeVariablesIn(c, b - (c - d))
      else true /*non trivial range*/)




  /**
    * States how substitution commutes (mentioned in proof of TAPL Lemma 30.3.4)
    * 
    * * Short version: If j ∉ FV(u) and j ≠ k then [k -> u][j -> s]t = [j -> [k -> u]s][k -> u]t
    * 
    * Long version:
    *  
    * Preconditions:
    *   - j ≠ k are non negative variables
    *   - FV(u) ∩ [j, j + 1[ = ∅
    * 
    * Postcondition:
    *   [h -> u][j -> s]t = [j -> [k -> u]s][k -> u]t
    */
  @inlineOnce @opaque @pure
  def substitutionTypeCommutativity(t: Term, j: BigInt, s: Type, k: BigInt, u: Type): Unit = {
    decreases(t)
    require(j >= 0)
    require(k >= 0)
    require(j != k)
    require(!u.hasFreeVariablesIn(j, 1))

    t match 
      case Var(i) => ()
      case App(t1, t2) => 
        substitutionTypeCommutativity(t1, j, s, k, u)
        substitutionTypeCommutativity(t2, j, s, k, u)
      case Abs(argT, b) => 
        substitutionCommutativity(argT, j, s, k, u)
        substitutionTypeCommutativity(b, j, s, k, u)
      case TApp(body, arg) => 
        substitutionTypeCommutativity(body, j, s, k, u)
        substitutionCommutativity(arg, j, s, k, u)
      case TAbs(_, body) => 
        shiftSubstitutionCommutativity(s, 1, 0, k, u)
        boundRangeShift(u, 1, 0, j, 1)
        substitutionTypeCommutativity(body, j+1, shift(s, 1, 0), k+1, shift(u, 1, 0))
  }.ensuring(
    substituteType(substituteType(t, j, s), k, u)
    ==
    substituteType(substituteType(t, k, u), j, substitute(s, k, u))
  )

  
  /**
   * States how free variable behave when reducing redexed
   * 
   * * Short version: FV((λ.t1)(t2)) ∩ [c, c + d[ = ∅ => FV(↑⁻¹([0 -> ↑¹t2]t1)) ∩ [c, c + d[ = ∅
   * 
   * Long version:
   * 
   * Preconditions:
   *   - c and d are non negative integers
   *   - FV(arg) ∩ [c, c + d[ = ∅ (arg = t2 in the above statement)
   *   - FV(body) ∩ [c + 1, c + 1 + d[ = ∅ (body = T1 in the above statement)
   *   ! These two conditions imply FV((λ.body)(arg)) ∩ [c, c + d[ = ∅
   * 
   * Postcondition:
   *   FV(↑⁻¹([0 -> ↑¹arg]body)) ∩ [c, c + d[ = ∅
   */
  @inlineOnce @opaque @pure
  def boundTypeRangeAbsSubst(body: Term, arg: Type, c: BigInt, d: BigInt) = {
    require(c >= 0)
    require(d >= 0)
    require(!arg.hasFreeVariablesIn(c, d))
    require(!body.hasFreeTypeVariablesIn(c + 1, d))

    boundRangeShift(arg, 1, 0, c, d)
    boundTypeRangeSubstitutionLemma(body, 0, shift(arg, 1, 0), d, d, c + 1, c + 1)
    boundRangeShift(arg, 1, 0, 0, 0)
    boundTypeRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    boundTypeRangeShift(substituteType(body, 0, shift(arg, 1, 0)), -1, 0, c + 1, d)
  }.ensuring(!absSubstitutionType(body, arg).hasFreeTypeVariablesIn(c, d))

  /**
    * States how shift commutes with redex reduction 
    * 
    * * Short version: shift(↑⁻¹([0 -> ↑¹t2]t1), d, c) = ↑⁻¹([0 -> ↑¹shift(t2, d, c)]shift(t1, d, c + 1))
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
  def shiftTypeAbsSubstitutionCommutativity(body: Term, arg: Type, d: BigInt, c: BigInt) = {
    require(c >= 0)
    require(d < 0 ==> (!arg.hasFreeVariablesIn(c, -d) && !body.hasFreeTypeVariablesIn(c + 1, -d)))

    boundRangeShift(arg, 1, 0, 0, 0)
    boundTypeRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))

    if d < 0 then
      boundRangeShift(arg, 1, 0, c, -d)
      boundTypeRangeSubstitutionLemma(body, 0, shift(arg, 1, 0), -d, -d, c + 1, c + 1)
      boundTypeRangeShift(substituteType(body, 0, shift(arg, 1, 0)), -1, 0, c + 1, -d)
      shiftTypeCommutativityNegNeg(substituteType(body, 0, shift(arg, 1, 0)), -1, 0, d, c)
      shiftTypeSubstitutionCommutativity(body, d, c + 1, 0, shift(arg, 1, 0))
      shiftCommutativityPosNeg(arg, 1, 0, d, c + 1)
    else
      shiftTypeCommutativityNegPos(substituteType(body, 0, shift(arg, 1, 0)), -1, 0, d, c)
      shiftTypeSubstitutionCommutativity(body, d, c + 1, 0, shift(arg, 1, 0))
      shiftCommutativityPosPos(arg, d, c, 1, 0)
  }.ensuring(_ => shiftType(absSubstitutionType(body, arg), d, c) == absSubstitutionType(shiftType(body, d, c + 1), shift(arg, d, c)))

  /**
    * States how substitution commutes with redex reduction 
    * 
    * * Short version: If 0 ∉ FV(s) then [j -> s]↑⁻¹([0 -> ↑¹t2]t1) = ↑⁻¹([0 -> ↑¹[j -> s]t2][j + 1 -> ↑¹s]t1)
    * 
    * Long version: (where body = t1 and arg = t2)
    *  
    * Preconditions:
    *   - j is a non negative variable
    *   - FV(s) ∩ [0, 1[ = ∅
    * 
    * Postcondition:
    *   [j -> s]↑⁻¹([0 -> ↑¹arg]body) = ↑⁻¹([0 -> ↑¹[j -> s]arg][j + 1 -> ↑¹s]body
    */
  @inlineOnce @opaque @pure
  def absSubstSubstCommutativity(body: Term, arg: Type, j: BigInt, s: Type): Unit = {
    require(j >= 0)
    require(!s.hasFreeVariablesIn(0, 1))

    boundRangeShift(arg, 1, 0, 0, 0)
    boundTypeRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    shiftTypeSubstitutionCommutativity(substituteType(body, 0, shift(arg, 1, 0)), -1, 0, j, s)
    boundRangeShift(s, 1, 0, 0, 0)
    substitutionTypeCommutativity(body, 0, shift(arg, 1, 0), j + 1, shift(s, 1, 0))
    shiftSubstitutionCommutativity(arg, 1, 0, j, s)

  }.ensuring(
    substituteType(absSubstitutionType(body, arg), j, s)
    ==
    absSubstitutionType(substituteType(body, j + 1, shift(s, 1, 0)), substitute(arg, j, s))
  )    
}
     