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

object TermTransformations {
  
  import TermTransformationsProperties._

  /**
    * d place shift of a term above cutoff c - TAPL Definition 6.2.1
    */
  @pure
  def shift(t: Term, d: BigInt, c: BigInt): Term = {
    require(c >= 0)
    require(if(d < 0){!t.hasFreeVariablesIn(c, -d)} else true)
    t match {
      case Var(k) => if (k < c) Var(k) else Var(k + d)
      case Abs(arg, body) => Abs(arg, shift(body, d, c + 1))
      case App(t1, t2) => App(shift(t1, d, c), shift(t2, d, c))
    }
  }.ensuring(_.size == t.size)

  /**
  * Substitution of a term s for variable number j in term t - TAPL Definition 6.2.4
  */
  @pure
  def substitute(t: Term, j: BigInt, s: Term): Term = {
    t match {
      case Var(k) => if(j == k) s else t  
      case Abs(k, b) => Abs(k, substitute(b, j + 1, shift(s, 1, 0)))
      case App(t1, t2) => App(substitute(t1, j, s), substitute(t2, j, s))
    }
  }

  // ↑⁻¹[0 -> ↑¹(arg)]body
  @pure
  def absSubstitution(body: Term, arg: Term): Term = {
    assert(!arg.hasFreeVariablesIn(0, 0))
    boundRangeShift(arg, 1, 0, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
  }

  // def shift(env: TypeEnvironment, d: BigInt, c: BigInt): TypeEnvironment = {
  //   require(c >= 0)
  //   require(if(d < 0) !hasFreeVariablesIn(env, c, -d) else true)
    
  //   env match {
  //     case Nil() => Nil[Term]()
  //     case Cons(h, t) => {
  //       Cons(shift(h, d, c), shift(t, d, c))
  //     }
  //   }
  // }.ensuring(res => res.length == env.length)

  // def substitute(env: TypeEnvironment, d: BigInt, typ: Term): TypeEnvironment = {
  //   env.map(substitute(_, d, typ))
  // }
}

object TermTransformationsProperties {
  import LambdaOmegaProperties.Terms._
  import TermTransformations._

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
  @opaque @pure
  def boundRangeSubstitutionIdentity(t: Term, j: BigInt, typ: Term): Unit = {
    require(j >= 0)
    require(!t.hasFreeVariablesIn(j, 1))

    t match {
      case Var(k) => ()
      case Abs(_, body) => {
        boundRangeSubstitutionIdentity(body, j+1, shift(typ, 1 ,0))
      }
      case App(t1, t2) => {
        boundRangeSubstitutionIdentity(t1, j, typ)
        boundRangeSubstitutionIdentity(t2, j, typ)
      }
    }

  }.ensuring(
    substitute(t, j, typ) == t
  )

  /**
    * A 0 place shift does not affect the time
    */
  @opaque @pure
  def shift0Identity(t: Term, c: BigInt): Unit = {
    require(c >= 0)
    t match {
      case Var(k) => ()
      case Abs(_, body) => {
        shift0Identity(body, c+1)
      }
      case App(t1, t2) => {
        shift0Identity(t1, c)
        shift0Identity(t2, c)
      }
    }
  }.ensuring(shift(t, 0, c) == t)

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
  @opaque @pure
  def boundRangeShiftComposition(t: Term, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    require(a >= 0)
    require(c >= 0)
    require(d >= 0)
    require(d <= c + a)
    require(if(d < c) !t.hasFreeVariablesIn(d, c - d) else !t.hasFreeVariablesIn(c, d - c))
    require(-b <= a)


    if (d < c){
      boundRangeShift(t, a, c, c, 0)
      boundRangeShift(t, a, c, d, c - d)
      boundRangeConcatenation(shift(t, a, c), d, c - d, a)
      boundRangeDecrease(shift(t, a, c), d, c - d + a, a)
    }
    else{
      boundRangeShift(t, a, c, c, d - c)
      boundRangeIncreaseCutoff(shift(t, a, c), c, d, a + d - c)
    }

    assert(!shift(t, a, c).hasFreeVariablesIn(d, a))
    if(b < 0){
      boundRangeDecrease(shift(t, a, c), d, a, -b)      
    }
    else{
      ()
    }

    t match {
      case Var(_) => ()
      case Abs(_, body) => {
        boundRangeShiftComposition(body, a, b, c + 1, d + 1)
      }
      case App(t1, t2) => {
        boundRangeShiftComposition(t1, a, b, c, d)
        boundRangeShiftComposition(t2, a, b, c, d)
      }
    }
  }.ensuring(
    (b < 0 ==> !shift(t, a, c).hasFreeVariablesIn(d, -b)) &&
    shift(shift(t, a, c), b, d) == shift(t, a + b, c)
  )

  /**
    * Describes exactly how free variables behave after shifts
    */
  @opaque @pure
  def boundRangeShift(t: Term, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
    require(c >= 0)
    require(b >= 0)
    require(a >= 0)
    require(d < 0 ==> !t.hasFreeVariablesIn(c, -d))

    t match
      case Var(_)    => ()
      case Abs(_, body)   => 
        boundRangeShift(body, d, c+1, a + 1, b)
      case App(t1, t2)    => 
        boundRangeShift(t1, d, c, a, b)
        boundRangeShift(t2, d, c, a, b)

  }.ensuring(
      !t.hasFreeVariablesIn(a, b)
        ==
      (if(d >= 0){
        (if(c >= a && c <= a + b)           {!shift(t, d, c).hasFreeVariablesIn(a, b + d)} else {true}) &&
        (if(c <= a + b)                     {!shift(t, d, c).hasFreeVariablesIn(a + d, b)} else {true}) &&
        (if(c >= a)                         {!shift(t, d, c).hasFreeVariablesIn(a, b)} else {true})
      }
      else{
        (if(a + b <= c)                     {!shift(t, d, c).hasFreeVariablesIn(a, b)} else true) &&
        (if(a + b >= c && a <= c)           {!shift(t, d, c).hasFreeVariablesIn(a, c - a)} else true) &&
        (if(a + b >= -d + c && a <= -d + c) {!shift(t, d, c).hasFreeVariablesIn(c, a + b + d - c)} else true) &&
        (if(a >= -d + c)                    {!shift(t, d, c).hasFreeVariablesIn(a + d, b)} else true) 
      })
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
  @opaque @pure
  def boundRangeSubstitutionLemma(t: Term, j: BigInt, s: Term): Unit = {
    require(j >= 0)
    require(!s.hasFreeVariablesIn(0, j+1))

    t match {
      case Var(k) => {
        boundRangeIncreaseCutoff(s, 0, j, j+1)
      }
      case Abs(_, body) => {
        boundRangeShift(s, 1, 0, 0, j+1)
        boundRangeIncreaseCutoff(shift(s, 1, 0), 0, j + 1, j+2)
        boundRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
      }
      case App(t1, t2) => {
        boundRangeSubstitutionLemma(t1, j, s)
        boundRangeSubstitutionLemma(t2, j, s)
      }
    }
  }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(j, 1))


  /** 
    * The four following theorems state under which conditions, two shifts commute
    */
  @opaque @pure
  def shiftCommutativityPosPos(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    require(a >= 0)
    require(b >= 0)
    require(c >= 0)
    require(d >= 0)
  
    subs match {
      case App(t1, t2) => 
        shiftCommutativityPosPos(t1, b, c, a, d)
        shiftCommutativityPosPos(t2, b, c, a, d)
      case Var(v) => ()
      case Abs(_, t) => shiftCommutativityPosPos(t, b, c+1, a, d+1) 
      
    }
  }.ensuring(
    if d <= c                then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
    if d - b >= c            then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
    if d >= c && d - b <= c  then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, c), b, c) else
    true)

  @opaque @pure
  def shiftCommutativityPosNeg(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    require(c >= 0)
    require(d >= 0)
    require(b >= 0)
    require(a < 0)
    require(if d >= c && b >= d - c  then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(c, -a) else
            if b <= d - c            then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d - b, -a) else
            if -a <= c - d           then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d, -a) else
            if d <= c && -a >= c - d then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) else
            true) 

    subs match {
      case App(t1, t2) => 
        shiftCommutativityPosNeg(t1, b, c, a, d)
        shiftCommutativityPosNeg(t2, b, c, a, d)
      case Var(v) => ()
      case Abs(_, t) => shiftCommutativityPosNeg(t, b, c+1, a, d+1) 
      
    }
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

  @opaque @pure
  def shiftCommutativityNegPos(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    require(c >= 0)
    require(d >= 0)
    require(b < 0)
    require(a >= 0)
    require(!subs.hasFreeVariablesIn(c, -b))
    
    //Weaker but more complex precond
    // require(if d >= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) else 
    //         if d <= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) else
    //         true) 

    subs match {
      case App(t1, t2) => 
        shiftCommutativityNegPos(t1, b, c, a, d)
        shiftCommutativityNegPos(t2, b, c, a, d)
      case Var(v) => ()
      case Abs(_, t) => shiftCommutativityNegPos(t, b, c+1, a, d+1) 
      
    }
  }.ensuring(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) && 
                                      shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
              if d <= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) && 
                                      shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
              true)


  @opaque @pure
  def shiftCommutativityNegNeg(subs: Term, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    require(c >= 0)
    require(d >= 0)
    require(a < 0)
    require(b < 0)
    require(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d - b, -a) else
            if d <= c && -a <= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) else 
            if d <= c && -a >= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
                                                            !shift(subs, b, c).hasFreeVariablesIn(d, -a) else
            true) 

    subs match {
      case App(t1, t2) => 
        shiftCommutativityNegNeg(t1, b, c, a, d)
        shiftCommutativityNegNeg(t2, b, c, a, d)
      case Var(v) => ()
      case Abs(_, t) => shiftCommutativityNegNeg(t, b, c+1, a, d+1) 
      
    }
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
  @opaque @pure
  def shiftSubstitutionCommutativity(typ: Term, s: BigInt, c: BigInt, k: BigInt, subs: Term): Unit = {
    require(k >= 0)
    require(c >= 0)
    require(
      if s < 0 then 
        !typ.hasFreeVariablesIn(c, -s) && !subs.hasFreeVariablesIn(c, -s)
      else true)

    typ match {
      case App(t1, t2) => {
        shiftSubstitutionCommutativity(t1, s, c, k, subs)
        shiftSubstitutionCommutativity(t2, s, c, k, subs)
      }
      case Var(v) => 
        if c >= 0 && c <= k && s < 0 then
          boundRangeShiftComposition(subs, -s, s, c, c)
          if (v >= c && k == v + s){
              boundRangeShiftComposition(subs, -s, s, c, c)
              shift0Identity(subs, c)          
          }
        else ()
      case Abs(argK, t) => {
        if s >= 0 then
          shiftCommutativityPosPos(subs, s, c, 1, 0)
        else
          boundRangeShift(subs, 1, 0, c, -s)
          if c > k then
            shiftCommutativityNegPos(subs, s, c, 1, 0)
          else
            shiftCommutativityPosPos(subs, -s, c, 1, 0)
        shiftSubstitutionCommutativity(t, s, c+1, k+1, shift(subs, 1, 0))
      }
    }
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
  @opaque @pure
  def boundRangeSubstitutionLemma(t: Term, j: BigInt, s: Term, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    require(j >= 0)
    require(a >= 0)
    require(b >= 0)
    require(c >= 0)
    require(d >= 0)
    require(!s.hasFreeVariablesIn(c, a))
    require(!t.hasFreeVariablesIn(d, b))

    t match 
      case App(t1, t2) => 
        boundRangeSubstitutionLemma(t1, j, s, a, b, c, d)
        boundRangeSubstitutionLemma(t2, j, s, a, b, c, d)
      case Var(v) => 
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
      case Abs(_, body) =>
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
  @opaque @pure
  def substitutionCommutativity(t: Term, j: BigInt, s: Term, k: BigInt, u: Term): Unit = {
    require(j >= 0)
    require(k >= 0)
    require(j != k)
    require(!u.hasFreeVariablesIn(j, 1))

    t match 
      case Var(i) => 
        if(i == k) {
          boundRangeSubstitutionIdentity(u, j, substitute(s, k, u))
        }
      case App(t1, t2) => 
        substitutionCommutativity(t1, j, s, k, u)
        substitutionCommutativity(t2, j, s, k, u)
      
      case Abs(_, b) => 
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
  @opaque @pure
  def boundRangeAbsSubst(body: Term, arg: Term, c: BigInt, d: BigInt) = {
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
  @opaque @pure
  def shiftAbsSubstitutionCommutativity(body: Term, arg: Term, d: BigInt, c: BigInt) = {
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
  @opaque @pure
  def absSubstSubstCommutativity(body: Term, arg: Term, j: BigInt, s: Term): Unit = {
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
     