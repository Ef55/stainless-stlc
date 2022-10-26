/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  * 
  *  This file defines type equivalence and its properties (TAPL Chap 30.3)
  *  One of the main results of the file is the proof of confluence for parallel type reduction.
  * 
  * 
  */



import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import Transformations.Types._
import TransformationsProperties.Types._

object TypeReduction{


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

    // def isEquivalence: Boolean = {
    //   this match {
    //     case ReflDerivation(_) => true
    //     case SymmDerivation(t1, t2, ed) => ed.isEquivalence && ed.type1 == t2 && ed.type2 == t1
    //     case TransDerivation(t1, t2, ed1, ed2) => 
    //       ed1.isEquivalence && ed2.isEquivalence && ed1.type1 == t1 &&
    //       ed2.type2 == t2 && ed1.type2 == ed2.type1
    //     case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ed1, ed2) =>
    //       ed1.isEquivalence && ed2.isEquivalence && ed1.type1 == t11 &&
    //       ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
    //     case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), ed) => 
    //       ed.isEquivalence && ed.type1 == b1 && ed.type2 == b2 && k1 == k2
    //     case AppDerivation(AppType(t11, t12), AppType(t21, t22), ed1, ed2) =>
    //       ed1.isEquivalence && ed2.isEquivalence && ed1.type1 == t11 &&
    //       ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
    //     case AppAbsDerivation(AppType(AbsType(argK, body), t2), t3) =>
    //       t3 == absSubstitution(body, t2) 
    //     case AppAbsDerivation(_, _) => false
    //   }
    // }

    /**
      * Returns whether the derivation tree is sound.
      * For each derivation rule checks whether:
      * - each subtree is also sound
      * - the conclusions of the subtrees are the premises of the rule.
      */
    @pure
    def isValid: Boolean = 
      this match 
        case ReflDerivation(_) => true
        case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
          prd1.isValid && prd2.isValid && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) => 
          prd.isValid && prd.type1 == b1 && prd.type2 == b2 && k1 == k2
        case AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
          prd1.isValid && prd2.isValid && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AppAbsDerivation(AbsType(argK, body1), arg1, body2, arg2, tt1, tt2) => 
          tt1.isValid && tt2.isValid && tt1.type1 == body1 && tt1.type2 == body2 &&
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

  // def reducesTo(t1: Type, t2: Type): Option[ParallelReductionDerivation] = {
  //   decreases(t1.size + t2.size)
  //   if(t1 == t2){
  //     Some(ReflDerivation(t1))
  //   }
  //   else{
  //     (t1, t2) match{
  //       case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
  //         (reducesTo(t11, t21), reducesTo(t12, t22)) match {
  //             case (Some(prd1), Some(prd2)) => Some(ArrowDerivation(at1, at2, prd1, prd2))
  //             case _ => None()
  //         }
  //       case (at1@AbsType(k1, body1), at2@AbsType(k2, body2)) =>
  //         reducesTo(body1, body2) match {
  //             case Some(prd) if k1 == k2 => Some(AbsDerivation(at1, at2, prd))
  //             case _ => None()
  //         }
        
  //       case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => Some(AppAbsDerivation(at1, t3))
  //       case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
  //         (reducesTo(t11, t21), reducesTo(t12, t22)) match {
  //             case (Some(prd1), Some(prd2)) => Some(AppDerivation(at1, at2, prd1, prd2))
  //             case _ => None()
  //         }
  //       case (_, _) => None()
  //     }
  //   }
  // }

  // def reducesToSoundness(t1: Type, t2: Type): Unit = {
  //   require(reducesTo(t1, t2).isDefined)
  //   decreases(t1.size + t2.size)
  //   if(t1 == t2){
  //     ()
  //   }
  //   else{
  //     (t1, t2) match{
  //       case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
  //         reducesToSoundness(t11, t21)
  //         reducesToSoundness(t12, t22)
  //       case (at1@AbsType(k1, body1), at2@AbsType(k2, body2)) =>
  //         reducesToSoundness(body1, body2)
  //       case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => ()
  //       case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
  //         reducesToSoundness(t11, t21)
  //         reducesToSoundness(t12, t22)
  //       case (_, _) => ()
  //       }
  //     }
  // }.ensuring(_ => reducesTo(t1, t2).get.isValid)

  // def reducesToCompleteness(prd: ParallelReductionDerivation): Unit = {
  //   require(prd.isValid)
  //   prd match
  //     case ReflDerivation(t) => ()
  //     case ArrowDerivation(ArrowType(_, _), ArrowType(_, _), prd1, prd2) =>
  //       reducesToCompleteness(prd1)
  //       reducesToCompleteness(prd2)
  //     case AbsDerivation(AbsType(_, _), AbsType(_, _), prd1) =>
  //       reducesToCompleteness(prd1)
  //     case AppDerivation(AppType(_, _), AppType(_, _), prd1, prd2) =>
  //       reducesToCompleteness(prd1)
  //       reducesToCompleteness(prd2)
  //     case AppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => ()
  //     case _ => ()
  // }.ensuring(_ => reducesTo(prd.type1, prd.type2). isDefined)


  /**
    * * Short version: If T1 => T2 and FV(T1) ∩ [a, a + b] = ∅ then FV(T2) ∩ [a, a + b] = ∅
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd the derivation tree witnessing T1 => T2 is sound
    *   - a and b are both non negative
    *   - FV(T1) ∩ [a, a + b] = ∅
    * 
    * Postcondition:
    *   - FV(T2) ∩ [a, a + b] = ∅
    * 
    */
  @opaque @pure
  def reduceBoundRange(sd: ParallelReductionDerivation, a: BigInt, b: BigInt): Unit = {
    require(sd.isValid)
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
    *   - sd the derivation tree witnessing T1 => T2 is sound
    *   - c is non negative
    *   - in case d is negative then FV(T1) ∩ [c, c - d] = ∅ (cf. negative shifts definition)
    * 
    * Postcondition:
    *   There exists a sound derivation tree witnessing shift(T1, d, c) => shift(T2, d, c)
    * * The proof is constructive and returns this derivation tree
    */
  @opaque @pure
  def reduceShift(sd: ParallelReductionDerivation, d: BigInt, c: BigInt): ParallelReductionDerivation = {
    require(sd.isValid)
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
    res.isValid)

  /**
    * TAPL Lemma 30.3.6
    * * Short version: If S1 => S2 then T[j := S1] => T[j := S2]
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd the derivation tree witnessing S1 => S2 is sound
    *   - j is non negative
    * 
    * Postcondition:
    *   There exists a sound derivation tree witnessing T[j := S1] => T[j := S2]
    * * The proof is constructive and returns this derivation tree
    */
  @opaque @pure
  def reduceReflSubst(t: Type, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
    require(sd.isValid)
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
    res.isValid &&
    res.type1 == substitute(t, j, sd.type1) &&
    res.type2 == substitute(t, j, sd.type2))

  /**
    * TAPL Lemma 30.3.7
    * * Short version: If T1 => T2 and S1 => S2 then T1[j := S1] => T2[j := S2]
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd and td the derivation trees respectively witnessing S1 => S2 and T1 => T2 are sound
    *   - j is non negative
    * ! - all occurences of the variable 0 inside S1 need to be bound
    * 
    * Postcondition:
    *   There exists a sound derivation tree witnessing T1[j := S1] => T2[j := S2]
    * * The proof is constructive and returns this derivation tree
    */
  @opaque @pure
  def reduceSubst(td: ParallelReductionDerivation, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
    require(td.isValid)
    require(sd.isValid)
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
    res.isValid &&
    res.type1 == substitute(td.type1, j, sd.type1) &&
    res.type2 == substitute(td.type2, j, sd.type2))
  
  @opaque @pure
  def reduceAbsSubst(bd: ParallelReductionDerivation, ad: ParallelReductionDerivation): ParallelReductionDerivation = {
    require(bd.isValid)
    require(ad.isValid)

    boundRangeShift(ad.type1, 1, 0, 0, 0)
    val shiftArg = reduceShift(ad, 1, 0)
    reduceBoundRange(shiftArg, 0, 1)
    val subst = reduceSubst(bd, 0, shiftArg)
    boundRangeSubstitutionLemma(bd.type1, 0, shift(ad.type1, 1, 0))
    reduceShift(subst, -1, 0)

  }.ensuring(res =>
    res.isValid &&
    res.type1 == absSubstitution(bd.type1, ad.type1) &&
    res.type2 == absSubstitution(bd.type2, ad.type2))

  def diamondProperty(prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation): (ParallelReductionDerivation, ParallelReductionDerivation) = {
    decreases(prd1.size + prd2.size)
    require(prd1.type1 == prd2.type1)
    require(prd1.isValid)
    require(prd2.isValid)
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
                    res._1.isValid && res._2.isValid)

  sealed trait MultiStepParallelReduction{

    def size: BigInt = {
      this match 
        case SingleStepParalellReduction(_) => BigInt(1)
        case SeveralStepParallelReduction(_, tail) => tail.size + 1
    }.ensuring(_ > BigInt(0))    

    def last: ParallelReductionDerivation =
      this match
        case SingleStepParalellReduction(red) => red
        case SeveralStepParallelReduction(last, _) => last
    
    def type1: Type = 
      this match
        case SingleStepParalellReduction(red) => red.type1
        case SeveralStepParallelReduction(_, tail) => tail.type1

    def type2: Type = 
      this match
        case SingleStepParalellReduction(red) => red.type2
        case SeveralStepParallelReduction(last, _) => last.type2

    def isValid: Boolean = 
      this match
        case SingleStepParalellReduction(red) => red.isValid
        case SeveralStepParallelReduction(last, tail) => 
          last.isValid && tail.isValid && last.type1 == tail.type2
  }

  case class SingleStepParalellReduction(red: ParallelReductionDerivation) extends MultiStepParallelReduction
  case class SeveralStepParallelReduction(last: ParallelReductionDerivation, tail: MultiStepParallelReduction) extends MultiStepParallelReduction

  def confluence(prd1: MultiStepParallelReduction, prd2: MultiStepParallelReduction): (MultiStepParallelReduction, MultiStepParallelReduction) = {
    decreases(prd1.size + prd2.size)
    require(prd1.type1 == prd2.type1)
    require(prd1.isValid)
    require(prd2.isValid)

    (prd1, prd2) match
      case (SingleStepParalellReduction(red1), SingleStepParalellReduction(red2)) => 
        val (dP1, dP2) = diamondProperty(red1, red2)
        (SingleStepParalellReduction(dP1), SingleStepParalellReduction(dP2))
      case (SingleStepParalellReduction(red1), SeveralStepParallelReduction(last, tail)) =>
        val (conf1, conf2) = confluence(prd1, tail)
        conf2 match 
          case SingleStepParalellReduction(red) => 
              val (dP1, dP2) = diamondProperty(red, last)
              (SeveralStepParallelReduction(dP1, conf1), SingleStepParalellReduction(dP2))
          case _ => //never happens
            (prd1, prd2)
      case (SeveralStepParallelReduction(last, tail), SingleStepParalellReduction(red2)) =>
        val (conf1, conf2) = confluence(tail, prd2)
        conf1 match 
          case SingleStepParalellReduction(red) => 
              val (dP1, dP2) = diamondProperty(last, red)
              (SingleStepParalellReduction(dP1), SeveralStepParallelReduction(dP2, conf2))
          case _ => //never happens
            (prd1, prd2)
      case (SeveralStepParallelReduction(last1, tail1), SeveralStepParallelReduction(last2, tail2)) =>
        val (conf11, conf12) = confluence(prd1, tail2)
        val (conf21, conf22) = confluence(tail1, prd2)
        val (dP1, dP2) = diamondProperty(conf12.last, conf21.last)
        (SeveralStepParallelReduction(dP1, conf11), SeveralStepParallelReduction(dP2, conf22))
  }.ensuring(res => 
    res._1.type2 == res._2.type2 &&
    res._1.type1 == prd1.type2 &&
    res._2.type1 == prd2.type2 &&
    res._1.isValid && res._2.isValid &&
    res._2.size == prd1.size && res._1.size == prd2.size
  )

  sealed trait DetReductionDerivation{
    def type1: Type = {
      this match{
        case DetArrow1Derivation(t1, _, _) => t1
        case DetArrow2Derivation(t1, _, _) => t1
        case DetApp1Derivation(t1, _, _) => t1
        case DetApp2Derivation(t1, _, _) => t1
        case DetBetaDerivation(t1, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case DetArrow1Derivation(_, t2, _) => t2
        case DetArrow2Derivation(_, t2, _) => t2
        case DetApp1Derivation(_, t2, _) => t2
        case DetApp2Derivation(_, t2, _) => t2
        case DetBetaDerivation(_, t2) => t2
      }
    }

    def isValid: Boolean = {
      this match {
        case DetArrow1Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1) =>
          prd1.isValid && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetArrow2Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd2) =>
          prd2.isValid && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
        case DetApp1Derivation(AppType(t11, t12), AppType(t21, t22), prd1) =>
          prd1.isValid && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetApp2Derivation(AppType(t11, t12), AppType(t21, t22), prd2) =>
          prd2.isValid && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
        case DetBetaDerivation(AppType(AbsType(argK, body), t12), t3) => t3 == absSubstitution(body, t12) 
        case _ => false
      }
    }
  }
  case class DetArrow1Derivation(t1: ArrowType, t2: ArrowType, prd1: DetReductionDerivation) extends DetReductionDerivation
  case class DetArrow2Derivation(t1: ArrowType, t2: ArrowType, prd2: DetReductionDerivation) extends DetReductionDerivation
  case class DetApp1Derivation(t1: AppType, t2: AppType, prd1: DetReductionDerivation) extends DetReductionDerivation
  case class DetApp2Derivation(t1: AppType, t2: AppType, prd2: DetReductionDerivation) extends DetReductionDerivation
  case class DetBetaDerivation(t1: AppType, t2: Type) extends DetReductionDerivation

  def detReducesTo(t1: Type, t2: Type): Option[DetReductionDerivation] = {
    decreases(t1.size + t2.size)
    (t1, t2) match{
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => Some(DetArrow1Derivation(at1, at2, prd1))
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => Some(DetArrow2Derivation(at1, at2, prd2))
              case _ => None()
            }
        }
      case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => Some(DetBetaDerivation(at1, t3))
      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => Some(DetApp1Derivation(at1, at2, prd1))
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => Some(DetApp2Derivation(at1, at2, prd2))
              case _ => None()
            }
        }
      case (_, _) => None()
      }
    }

  def detReduce(t: Type): Option[DetReductionDerivation] = {
    t match{
      case at@ArrowType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => Some(DetArrow1Derivation(at, ArrowType(prd1.type2, t12), prd1))
          case _ => detReduce(t12) match{
            case Some(prd2) => Some(DetArrow2Derivation(at, ArrowType(t11, prd2.type2), prd2))
            case _ => None()
          }
        }
      case (at@AppType(t11, t12)) =>
        detReduce(t11) match {
          case Some(prd1) => Some(DetApp1Derivation(at, AppType(prd1.type2, t12), prd1))
          case _ => detReduce(t12) match {
            case Some(prd2) => Some(DetApp2Derivation(at, AppType(t11, prd2.type2), prd2))
            case _ => t11 match {
              case AbsType(argK, body) => Some(DetBetaDerivation(at, absSubstitution(body, t12)))
              case _ => None()
            }
          }
        }
      case _ => None()
    }
  }

  def detReducesToSoundness(t1: Type, t2: Type): Unit = {
    require(detReducesTo(t1, t2).isDefined)
    decreases(t1.size + t2.size)
    (t1, t2) match{
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => detReducesToSoundness(t11, t21)
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => detReducesToSoundness(t12, t22)
              case _ => ()
            }
        }
      case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => ()
      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => detReducesToSoundness(t11, t21)
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => detReducesToSoundness(t12, t22)
              case _ => ()
            }
        }
      case (_, _) => ()
    }
  }.ensuring(_ => detReducesTo(t1, t2).get.isValid)

  @opaque @pure
  def detReducesToCompleteness(drd: DetReductionDerivation): Unit = {
    require(drd.isValid)
    drd match {
      case DetArrow1Derivation(ArrowType(t11, t12), ArrowType(t21, t22), drd1) =>
        detReducesToCompleteness(drd1)
      case DetArrow2Derivation(ArrowType(t11, t12), ArrowType(t21, t22), drd2) =>
        detReducesToCompleteness(drd2)
      case DetApp1Derivation(AppType(t11, t12), AppType(t21, t22), drd1) =>
        detReducesToCompleteness(drd1)
      case DetApp2Derivation(AppType(t11, t12), AppType(t21, t22), drd2) =>
        detReducesToCompleteness(drd2)
      case DetBetaDerivation(AppType(AbsType(argK, body), t12), t3) => ()
      case _ => ()
    }
  }.ensuring(_ => detReducesTo(drd.type1, drd.type2).isDefined)

  @opaque @pure
  def detReduceSoundness(t: Type): Unit = {
    require(detReduce(t).isDefined)
    t match{
      case at@ArrowType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReduceSoundness(t11)
          case _ => detReduce(t12) match{
            case Some(prd2) => detReduceSoundness(t12)
            case None() => ()
          }
        }
      case at@AppType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReduceSoundness(t11)
          case _ => detReduce(t12) match {
            case Some(prd2) => detReduceSoundness(t12)
            case _ => t11 match {
              case AbsType(argK, body) => ()
              case _ => ()
            }
          }
        }
      case _ => ()
      }
  }.ensuring(_ => detReduce(t).get.isValid)

  @opaque @pure
  def detReducesToReduce(t: Type): Unit = {
    require(detReduce(t).isDefined)
    t match{
      case at@ArrowType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReducesToReduce(t11)
          case _ => detReduce(t12) match{
            case Some(prd2) => 
              detReducesToReduce(t12)
            case None() => () 
          }
        }
      case at@AppType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReducesToReduce(t11)
          case _ => detReduce(t12) match {
            case Some(prd2) => detReducesToReduce(t12)
            case _ => t11 match {
                case AbsType(argK, body) => ()
                case _ => ()
            }
          }
        }
      case _ => ()
      }
  }.ensuring(_ => detReducesTo(t, detReduce(t).get.type2).isDefined)

  // def reduceSubst(td: ParallelReductionDerivation, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
  //   require(td.isValid)
  //   require(sd.isValid)
    
  //   td match
  //     case ReflDerivation(t) =>


  //   td.type1 match
  //     case bt@BasicType(_) => ReflDerivation(bt)
  //     case AbsType(k, body) => 
  //       val bodyDeriv = reduceSubst()
  //       AbsDerivation(AbsType(k, substitute(body, j, sd.type1)), )
  //     case _ => ReflDerivation(td.type1)

  // }.ensuring(res =>
  //   res.isValid &&
  //   res.type1 == substitute(td.type1, j, sd.type1)
  //   res.type2 == substitute(td.type2, j, sd.type2))


  // def properNormalFormsAreEquivalent(eq: ParallelReductionDerivation){
  //   require(eq.isValid)
  //   require(deriveKind(eq).isDefined)
  //   require(deriveKind().isDefined)
  // }

  sealed trait DetMultiStepReductionDerivation{

    def type1: Type = {
      this match{
        case DetReflDerivation(t) => t
        case DetSingleStepDerivation(rd) => rd.type1
        case DetTransDerivation(t1, _, _, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case DetReflDerivation(t) => t
        case DetSingleStepDerivation(rd) => rd.type2
        case DetTransDerivation(_, t2, _, _) => t2
      }
    }

    def isValid: Boolean = {
      this match{
        case DetReflDerivation(_) => true
        case DetSingleStepDerivation(rd) => rd.isValid
        case DetTransDerivation(t1, t2, rd1, rd2) => 
          t1 == rd1.type1 && t2 == rd2.type2 && rd1.type2 == rd2.type1 &&
          rd1.isValid && rd2.isValid
      }
    }

  }

  case class DetReflDerivation(t: Type) extends DetMultiStepReductionDerivation
  case class DetSingleStepDerivation(rd: DetReductionDerivation) extends DetMultiStepReductionDerivation
  case class DetTransDerivation(t1: Type, t2: Type, rd1: DetMultiStepReductionDerivation, rd2: DetMultiStepReductionDerivation) extends DetMultiStepReductionDerivation

  // def detMultiStepReduce(t: Type): DetMultiStepReductionDerivation = {
  //   detReduce(t) match {
  //     case Some(ssd) => 
  //       val msd = detMultiStepReduce(ssd.type2)
  //       DetTransDerivation(ssd.type1, msd.type2, DetSingleStepDerivation(ssd), msd) 
  //     case None() => DetReflDerivation(t)
  //   }
  // }

  // def detMultiStepReduceSoundness(t: Type): Unit = {
  //   detReduce(t) match {
  //     case Some(ssd) => detMultiStepReduceSoundness(ssd.type2)
  //     case None() => ()
  //   }
  // }.ensuring(detMultiStepReduce(t).isValid)


  }
