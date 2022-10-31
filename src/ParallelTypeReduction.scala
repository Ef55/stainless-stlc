/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  * 
  *  This file defines parallel type reduction its properties (TAPL Chap 30.3)
  *  One of the main results of the file is the proof of confluence for parallel type reduction.
  * 
  * 
  */

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import TypeTransformations._
import TypeTransformationsProperties._

object ParallelTypeReduction{
  /**
    * Derivation tree for a parallel type reduction step of the form type1 => type2, as defined in Figure 30-3 of TAPL
    */
  sealed trait ParallelReductionDerivation{

    @pure
    def type1: Type = 
      this match
        case ReflDerivation(t) => t 
        case ArrowDerivation(t1, _, _, _) => t1
        case AbsDerivation(t1, _, _) => t1
        case AppDerivation(t1, _, _, _) => t1
        case AppAbsDerivation(abs, arg, _, _, _, _) => AppType(abs, arg)

    @pure
    def type2: Type = 
      this match
        case ReflDerivation(t) => t 
        case ArrowDerivation(_, t2, _, _) => t2
        case AbsDerivation(_, t2, _) => t2
        case AppDerivation(_, t2, _, _) => t2
        case AppAbsDerivation(_, _, body2, arg2, _, _) => absSubstitution(body2, arg2)


    /**
      * Measure for parallel reduction derivation trees
      * ! This is not a formal definition, its only purpose is to ensure measure decreaseness
      */
    @opaque @pure
    def size: BigInt = {
      this match
        case ReflDerivation(_) => BigInt(1)
        case ArrowDerivation(_, _, ed1, ed2) => ed1.size + ed2.size
        case AbsDerivation(_, _, ed) => ed.size + BigInt(1)
        case AppDerivation(_, _, ed1, ed2) => ed1.size + ed2.size
        case AppAbsDerivation(_, _, _, _, tt1, tt2) => tt1.size + tt2.size
    }.ensuring(_ > BigInt(0))

    /**
      * Returns whether the derivation tree is sound.
      * For each derivation rule checks whether:
      * - each subtree is also sound
      * - the conclusions of the subtrees are the premises of the rule.
      */
    @pure
    def isSound: Boolean = 
      this match 
        case ReflDerivation(_) => true
        case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
          prd1.isSound && prd2.isSound && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) => 
          prd.isSound && prd.type1 == b1 && prd.type2 == b2 && k1 == k2
        case AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
          prd1.isSound && prd2.isSound && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AppAbsDerivation(AbsType(argK, body1), arg1, body2, arg2, tt1, tt2) => 
          tt1.isSound && tt2.isSound && tt1.type1 == body1 && tt1.type2 == body2 &&
          tt2.type1 == arg1 && tt2.type2 == arg2 
  }
  /**
    * Parallel reduction rules as listed in TAPL Figure 30-3
    */
  case class ReflDerivation(t: Type) extends ParallelReductionDerivation
  case class ArrowDerivation(t1: ArrowType, t2: ArrowType, ed1: ParallelReductionDerivation, ed2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AbsDerivation(t1: AbsType, t2: AbsType, ed: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppDerivation(t1: AppType, t2: AppType, ed: ParallelReductionDerivation, ed2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppAbsDerivation(abs1: AbsType, arg1: Type, body2: Type, arg2: Type , tt1: ParallelReductionDerivation, tt2: ParallelReductionDerivation) extends ParallelReductionDerivation

  /**
    * Transitive and reflexive closure of parallel reduction relation also noted type1 =>* type2 (TAPL Chapter 30.3).
    * ! In this implementation multistep reduction is represented as a list of parallel reduction steps and
    * ! not as the closure of a relation.
    * TODO Show the equivalence between the two representations.
    */
  sealed trait MultiStepParallelReduction{

    /**
      * Number of reduction steps in the list
      */
    def size: BigInt = {
      this match 
        case NilParallelReduction(_) => BigInt(0)
        case ConsParallelReduction(_, tail) => tail.size + 1
    }.ensuring(_ >= 0)

    def type1: Type = 
      this match
        case NilParallelReduction(t) => t
        case ConsParallelReduction(head, tail) => head.type1

    def type2: Type = 
      this match
        case NilParallelReduction(t) => t
        case ConsParallelReduction(head, tail) => tail.type2

    def concat(prd2: MultiStepParallelReduction): MultiStepParallelReduction =
      this match
        case NilParallelReduction(t) => prd2
        case ConsParallelReduction(h, t) => ConsParallelReduction(h, t.concat(prd2))
       

    /**
      * Returns whether the reduction is sound.
      * Each step must be sound and the types of the reduction steps must coincide i.e. the list has to be of the form
      * (Tn-1 => type2, Tn-2 => Tn-1, ..., T1 => T2, type1 => T1)
      */
    def isSound: Boolean = 
      this match
        case NilParallelReduction(_) => true
        case ConsParallelReduction(head, tail) => head.isSound && tail.isSound && head.type2 == tail.type1
  }

  case class NilParallelReduction(t: Type) extends MultiStepParallelReduction
  case class ConsParallelReduction(head: ParallelReductionDerivation, tail: MultiStepParallelReduction) extends MultiStepParallelReduction



}

object ParallelTypeReductionProperties {

  import ParallelTypeReduction._

    /**
    * * Short version: If T1 => T2 and FV(T1) ∩ [a, a + b] = ∅ then FV(T2) ∩ [a, a + b] = ∅
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd, the derivation tree witnessing T1 => T2, is sound
    *   - a and b are both non negative
    *   - FV(T1) ∩ [a, a + b] = ∅
    * 
    * Postcondition:
    *   - FV(T2) ∩ [a, a + b] = ∅
    * 
    */
  @opaque @pure
  def reduceBoundRange(sd: ParallelReductionDerivation, a: BigInt, b: BigInt): Unit = {
    require(sd.isSound)
    require(a >= 0)
    require(b >= 0)
    require(!sd.type1.hasFreeVariablesIn(a, b))

    sd match
      case ReflDerivation(t) => ()
      case ArrowDerivation(_, _, prd1, prd2) => 
        reduceBoundRange(prd1, a, b)
        reduceBoundRange(prd2, a, b)
      case AppDerivation(_, _, prd1, prd2) => 
        reduceBoundRange(prd1, a, b)
        reduceBoundRange(prd2, a, b)
      case AbsDerivation(_, _, prd) =>
        reduceBoundRange(prd, a + 1, b)
      case AppAbsDerivation(_, _, _, _, prd1, prd2) =>
        reduceBoundRange(prd1, a + 1, b)
        reduceBoundRange(prd2, a, b)  
        boundRangeAbsSubst(prd1.type2, prd2.type2, a, b)
    
  }.ensuring(_ => !sd.type2.hasFreeVariablesIn(a, b))

  /**
    * * Short version: If T1 => T2 then shift(T1, d, c) => shift(T1, d, c)
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd, the derivation tree witnessing T1 => T2, is sound
    *   - c is non negative
    *   - in case d is negative then FV(T1) ∩ [c, c - d] = ∅ (cf. negative shifts definition)
    * 
    * Postcondition:
    *   There exists a sound derivation tree witnessing shift(T1, d, c) => shift(T2, d, c)
    * * The proof is constructive and returns this derivation tree
    */
  @opaque @pure
  def reduceShift(sd: ParallelReductionDerivation, d: BigInt, c: BigInt): ParallelReductionDerivation = {
    require(sd.isSound)
    require(c >= 0)
    require(if d < 0 then !sd.type1.hasFreeVariablesIn(c, -d) else true)

    if d < 0 then 
      reduceBoundRange(sd, c, -d) 
    else 
      true

    sd match
      case ReflDerivation(t) => ReflDerivation(shift(t, d, c))
      case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
        val res1 = reduceShift(prd1, d, c)
        val res2 = reduceShift(prd2, d, c)
        ArrowDerivation(ArrowType(shift(t11, d, c), shift(t12, d, c)), ArrowType(shift(t21, d, c), shift(t22, d, c)), res1, res2)
      case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) =>
        val res1 = reduceShift(prd, d, c + 1)
        AbsDerivation(AbsType(k1, res1.type1), AbsType(k2, res1.type2), res1)
      case AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
        val res1 = reduceShift(prd1, d, c)
        val res2 = reduceShift(prd2, d, c)
        AppDerivation(AppType(shift(t11, d, c), shift(t12, d, c)), AppType(shift(t21, d, c), shift(t22, d, c)), res1, res2)
      case AppAbsDerivation(AbsType(argK, body1), arg1, body2, arg2, prd1, prd2) =>
        if d < 0 then 
          reduceBoundRange(prd1, c + 1, -d)
          reduceBoundRange(prd2, c, -d)  
        else 
          true
        val resBody = reduceShift(prd1, d, c + 1)
        val resArg = reduceShift(prd2, d, c)
        shiftAbsSubstitutionCommutativity(body2, arg2, d, c)
        AppAbsDerivation(AbsType(argK, shift(body1, d, c + 1)), shift(arg1, d, c), shift(body2, d, c + 1), shift(arg2, d, c), resBody, resArg)
      case _ => ReflDerivation(shift(sd.type1, d, c))
    
  }.ensuring(res => 
    res.type1 == shift(sd.type1, d, c) &&
    res.type2 == shift(sd.type2, d, c) &&
    res.isSound)

  /**
    * TAPL Lemma 30.3.6
    * * Short version: If S1 => S2 then T[j := S1] => T[j := S2]
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd, the derivation tree witnessing S1 => S2, is sound
    *   - j is non negative
    * 
    * Postcondition:
    *   There exists a sound derivation tree witnessing T[j := S1] => T[j := S2]
    * * The proof is constructive and returns this derivation tree
    */
  @opaque @pure
  def reduceReflSubst(t: Type, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
    require(sd.isSound)
    require(j >= 0)
    t match
      case ArrowType(t1, t2) =>
        val d1 = reduceReflSubst(t1, j, sd)
        val d2 = reduceReflSubst(t2, j, sd)
        ArrowDerivation(ArrowType(d1.type1, d2.type1), ArrowType(d1.type2, d2.type2), d1, d2)
      case AppType(t1, t2) =>
        val d1 = reduceReflSubst(t1, j, sd)
        val d2 = reduceReflSubst(t2, j, sd)
        AppDerivation(AppType(d1.type1, d2.type1), AppType(d1.type2, d2.type2), d1, d2)
      case AbsType(k, body) =>
        val bd = reduceReflSubst(body, j + 1, reduceShift(sd, 1, 0))
        AbsDerivation(AbsType(k, bd.type1), AbsType(k, bd.type2), bd)
      case BasicType(_) => ReflDerivation(t)
      case VariableType(v) => if j == v then sd else ReflDerivation(t)
  }.ensuring(res => 
    res.isSound &&
    res.type1 == substitute(t, j, sd.type1) &&
    res.type2 == substitute(t, j, sd.type2))

  /**
    * TAPL Lemma 30.3.7
    * * Short version: If T1 => T2 and S1 => S2 then T1[j := S1] => T2[j := S2]
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd and td, the derivation trees respectively witnessing S1 => S2 and T1 => T2, are sound
    *   - j is non negative
    * ! - all occurences of the variable 0 inside S1 need to be bound
    *
    * Postcondition:
    *   There exists a sound derivation tree witnessing T1[j := S1] => T2[j := S2]
    * * The proof is constructive and returns this derivation tree
    */
  @opaque @pure
  def reduceSubst(td: ParallelReductionDerivation, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
    require(td.isSound)
    require(sd.isSound)
    require(j >= 0)
    require(!sd.type1.hasFreeVariablesIn(0, 1))
    
    reduceBoundRange(sd, 0, 1)
    boundRangeShift(sd.type1, 1, 0, 0, 0)
    boundRangeShift(sd.type2, 1, 0, 0, 0)

    td match
      case ReflDerivation(t) => reduceReflSubst(td.type1, j, sd)
      case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), td1, td2) =>
        val rs1 = reduceSubst(td1, j, sd)
        val rs2 = reduceSubst(td2, j, sd)
        ArrowDerivation(ArrowType(rs1.type1, rs2.type1), ArrowType(rs1.type2, rs2.type2), rs1, rs2)
      case AppDerivation(AppType(t11, t12), AppType(t21, t22), td1, td2) =>
        val rs1 = reduceSubst(td1, j, sd)
        val rs2 = reduceSubst(td2, j, sd)
        AppDerivation(AppType(rs1.type1, rs2.type1), AppType(rs1.type2, rs2.type2), rs1, rs2)
      case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), bd) =>
        val rs = reduceSubst(bd, j + 1, reduceShift(sd, 1, 0))
        AbsDerivation(AbsType(k1, rs.type1), AbsType(k2, rs.type2), rs)
      case AppAbsDerivation(AbsType(argK, body), arg1, body2, arg2, td1, td2) => 
        val rsh = reduceShift(sd, 1, 0)
        val rs1 = reduceSubst(td1, j + 1, rsh)
        val rs2 = reduceSubst(td2, j, sd)
        absSubstSubstCommutativity(body2, arg2, j, sd.type2)
        AppAbsDerivation(AbsType(argK, rs1.type1), rs2.type1, rs1.type2, rs2.type2, rs1, rs2)
      case _ => td

  }.ensuring(res =>
    res.isSound &&
    res.type1 == substitute(td.type1, j, sd.type1) &&
    res.type2 == substitute(td.type2, j, sd.type2))
  
  @opaque @pure
  def reduceAbsSubst(bd: ParallelReductionDerivation, ad: ParallelReductionDerivation): ParallelReductionDerivation = {
    require(bd.isSound)
    require(ad.isSound)

    boundRangeShift(ad.type1, 1, 0, 0, 0)
    val shiftArg = reduceShift(ad, 1, 0)
    reduceBoundRange(shiftArg, 0, 1)
    val subst = reduceSubst(bd, 0, shiftArg)
    boundRangeSubstitutionLemma(bd.type1, 0, shift(ad.type1, 1, 0))
    reduceShift(subst, -1, 0)

  }.ensuring(res =>
    res.isSound &&
    res.type1 == absSubstitution(bd.type1, ad.type1) &&
    res.type2 == absSubstitution(bd.type2, ad.type2))

  /**
    * Diamond Property - TAPL Lemma 30.3.8
    * * Short version: If T1 => T2 and T1 => T3 then there exits a type T4 such that T2 => T4 and T3 => T4
    * 
    * Long version:
    * 
    * Preconditions:
    *   - prd1, the derivation tree witnessing T11 => T2 is sound
    *   - prd2, the derivation tree witnessing T12 => T3 is sound
    *   - T11 = T12 (= T1 in the above theorem statement)
    *
    * Postcondition:
    *   There exists two sound derivation trees respectevely witnessing T => T41 and T' => T42 such that:
    *     - T = T2
    *     - T'= T3
    *     - T41 = T42
    * * The proof is constructive and returns this pair of derivations trees
    */
  def diamondProperty(prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation): (ParallelReductionDerivation, ParallelReductionDerivation) = {
    decreases(prd1.size + prd2.size)
    require(prd1.isSound)
    require(prd2.isSound)
    require(prd1.type1 == prd2.type1)

    if prd1.type2 == prd2.type2 then
      (ReflDerivation(prd1.type2), ReflDerivation(prd2.type2))
    else
      (prd1, prd2) match 
        case (ReflDerivation(t), _) => (prd2, ReflDerivation(prd2.type2))
        case (_, ReflDerivation(t)) => (ReflDerivation(prd1.type2), prd1)
        case (ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd11, prd12), ArrowDerivation(ArrowType(t31, t32), ArrowType(t41, t42), prd21, prd22)) =>
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (ArrowDerivation(ArrowType(dP11.type1, dP21.type1), ArrowType(dP11.type2, dP21.type2), dP11, dP21), ArrowDerivation(ArrowType(dP12.type1, dP22.type1), ArrowType(dP12.type2, dP22.type2), dP12, dP22))
        case (AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd11), AbsDerivation(AbsType(k3, b3), AbsType(k4, b4), prd12)) =>
          val (dP1, dP2) = diamondProperty(prd11, prd12)
          (AbsDerivation(AbsType(k2, dP1.type1), AbsType(k2, dP1.type2), dP1), AbsDerivation(AbsType(k2, dP2.type1), AbsType(k2, dP2.type2), dP2))
        case (AppDerivation(AppType(t11, t12), AppType(t21, t22), prd11, prd12), AppDerivation(AppType(t31, t32), AppType(t41, t42), prd21, prd22)) =>
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (AppDerivation(AppType(dP11.type1, dP21.type1), AppType(dP11.type2, dP21.type2), dP11, dP21), AppDerivation(AppType(dP12.type1, dP22.type1), AppType(dP12.type2, dP22.type2), dP12, dP22))
        case (AppAbsDerivation(AbsType(k, body11), arg11, body12, arg12, prd11, prd12), AppAbsDerivation(AbsType(_, body21), arg21, body22, arg22, prd21, prd22)) => 
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (reduceAbsSubst(dP11, dP21), reduceAbsSubst(dP12, dP22))
        case (AppAbsDerivation(AbsType(k, body1), arg1, body2, arg2, prd11, prd12), AppDerivation(AppType(AbsType(_, t11), t12), AppType(AbsType(_, t21), t22), prd, prd22)) => 
          prd match
            case AbsDerivation(_, _, prd21) => 
              val (dP11, dP12) = diamondProperty(prd11, prd21)
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (reduceAbsSubst(dP11, dP21), AppAbsDerivation(AbsType(k, dP12.type1), dP22.type1, dP12.type2, dP22.type2, dP12, dP22))
            case ReflDerivation(body) => 
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (reduceAbsSubst(ReflDerivation(body2), dP21), AppAbsDerivation(AbsType(k, body1), dP22.type1, body2, dP22.type2, prd11, dP22))
            case _ => (ReflDerivation(prd1.type2), ReflDerivation(prd2.type2))
          
        case (AppDerivation(AppType(AbsType(_, t11), t12), AppType(AbsType(_, t21), t22), prd, prd12), AppAbsDerivation(AbsType(k, body1), arg1, body2, arg2, prd21, prd22)) => 
          prd match
            case AbsDerivation(_, _, prd11) => 
              val (dP11, dP12) = diamondProperty(prd11, prd21)
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (AppAbsDerivation(AbsType(k, dP11.type1), dP21.type1, dP11.type2, dP21.type2, dP11, dP21), reduceAbsSubst(dP12, dP22))
            case ReflDerivation(body) => 
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (AppAbsDerivation(AbsType(k, body1), dP21.type1, body2, dP21.type2, prd21, dP21), reduceAbsSubst(ReflDerivation(body2), dP22))
            case _ => (ReflDerivation(prd1.type2), ReflDerivation(prd2.type2))
          
        case _ => (ReflDerivation(prd1.type2), ReflDerivation(prd2.type2))
  }.ensuring(res => res._1.type1 == prd1.type2 &&
                    res._2.type1 == prd2.type2 &&
                    res._1.type2 == res._2.type2 &&
                    res._1.isSound && res._2.isSound)

  def concatSoundness(@induct prd1: MultiStepParallelReduction, prd2: MultiStepParallelReduction): Unit = {
    require(prd1.isSound)
    require(prd2.isSound)
    require(prd1.type2 == prd2.type1)
  }.ensuring(prd1.concat(prd2).isSound)

  /** 
    * * Short version: If T1 =>* T2 and T1 => T3 then there exits a type T4 such that T2 => T4 and T3 =>* T4
    * 
    * Long version:
    * 
    * Preconditions:
    *   - prd1, the list of derivation trees witnessing T11 =>* T2 is sound
    *   - prd2, the list of derivation trees witnessing T12 =>* T3 is sound
    *   - T11 = T12 (= T1 in the above theorem statement)
    *
    * Postcondition:
    *   There exists two sound list of derivation trees respectevely witnessing T =>* T41 and T' =>* T42 such that:
    *     - T = T2
    *     - T'= T3
    *     - T41 = T42
    * * The proof is constructive and returns this pair of list
    */
  def confluenceStripe(prd1: MultiStepParallelReduction, h2: ParallelReductionDerivation): (ParallelReductionDerivation, MultiStepParallelReduction) = {
    require(prd1.isSound)
    require(h2.isSound)
    require(h2.type1 == prd1.type1)

    prd1 match
      case NilParallelReduction(t) => (h2, NilParallelReduction(h2.type2))
      case ConsParallelReduction(h, t) =>
        val (dP1, dP2) = diamondProperty(h, h2)
        val (conf1, conf2) = confluenceStripe(t, dP1)
        (conf1, ConsParallelReduction(dP2, conf2))

  }.ensuring(res =>
    res._1.type2 == res._2.type2 &&
    res._1.type1 == prd1.type2 &&
    res._2.type1 == h2.type2 &&
    res._1.isSound && res._2.isSound &&
    res._2.size == prd1.size)

  /**
    * Confluence - TAPL Lemma 30.3.9
    * 
    * * Short version: If T1 =>* T2 and T1 =>* T3 then there exits a type T4 such that T2 =>* T4 and T3 =>* T4
    * 
    * Long version:
    * 
    * Preconditions:
    *   - prd1, the list of derivation trees witnessing T11 =>* T2 is sound
    *   - prd2, the list of derivation trees witnessing T12 =>* T3 is sound
    *   - T11 = T12 (= T1 in the above theorem statement)
    *
    * Postcondition:
    *   There exists two sound list of derivation trees respectevely witnessing T =>* T41 and T' =>* T42 such that:
    *     - T = T2
    *     - T'= T3
    *     - T41 = T42
    * * The proof is constructive and returns this pair of list
    */
  def confluence(prd1: MultiStepParallelReduction, prd2: MultiStepParallelReduction): (MultiStepParallelReduction, MultiStepParallelReduction) = {
    decreases(prd1.size + prd2.size)
    require(prd1.isSound)
    require(prd2.isSound)
    require(prd1.type1 == prd2.type1)

    (prd1, prd2) match
      case (NilParallelReduction(t1), NilParallelReduction(t2)) => (NilParallelReduction(t1), NilParallelReduction(t1))
      case (NilParallelReduction(_t), ConsParallelReduction(head, tail)) => (ConsParallelReduction(head, tail), NilParallelReduction(prd2.type2))
      case (ConsParallelReduction(head, tail), NilParallelReduction(_)) => (NilParallelReduction(prd1.type2), ConsParallelReduction(head, tail))
      case (ConsParallelReduction(head1, tail1), ConsParallelReduction(head2, tail2)) =>
        val (red11, prd12) = confluenceStripe(prd1, head2)
        val (conf1, conf2) = confluence(prd12, tail2)
        (ConsParallelReduction(red11, conf1), conf2)
  }.ensuring(res => 
    res._1.type2 == res._2.type2 &&
    res._1.type1 == prd1.type2 &&
    res._2.type1 == prd2.type2 &&
    res._1.isSound && res._2.isSound &&
    res._2.size == prd1.size && res._1.size == prd2.size
  )
}