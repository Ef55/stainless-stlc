/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  *    - [TRAT] Term Rewriting and All That, Franz Baader and Tobias Nipkow, 1998, Cambridge University Press
  * 
  *  This file defines parallel type reduction its properties (TAPL Chap 30.3)
  *  One of the main results of the file is the proof of confluence for parallel type reduction.
  */

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import TypeTransformations._
import TypeTransformationsProperties._
import ARS._
import ARSProperties._

object ParallelTypeReduction{
  /**
    * Derivation tree for a parallel type reduction step of the form type1 => type2, as defined in Figure 30-3 of TAPL
    * It represents a proof of the reduction.
    */
  sealed trait ParallelReductionDerivation{

    @pure
    def type1: Type = 
      decreases(this)
      this match
        case ReflDerivation(t) => t 
        case ArrowTypeDerivation(t1, _, _, _) => t1
        case AbsTypeDerivation(t1, _, _) => t1
        case AppTypeDerivation(t1, _, _, _) => t1
        case AppAbsTypeDerivation(abs, arg, _, _, _, _) => AppType(abs, arg)

    @pure
    def type2: Type = 
      decreases(this)
      this match
        case ReflDerivation(t) => t 
        case ArrowTypeDerivation(_, t2, _, _) => t2
        case AbsTypeDerivation(_, t2, _) => t2
        case AppTypeDerivation(_, t2, _, _) => t2
        case AppAbsTypeDerivation(_, _, body2, arg2, _, _) => absSubstitution(body2, arg2)


    /**
      * Measure for parallel reduction derivation trees
      * ! This is not a formal definition, its only purpose is to ensure measure decreaseness
      */
    @pure
    def size: BigInt = {
      decreases(this)
      this match
        case ReflDerivation(_) => BigInt(1)
        case ArrowTypeDerivation(_, _, ed1, ed2) => ed1.size + ed2.size + BigInt(1)
        case AbsTypeDerivation(_, _, ed) => ed.size + BigInt(1)
        case AppTypeDerivation(_, _, ed1, ed2) => ed1.size + ed2.size + BigInt(1)
        case AppAbsTypeDerivation(_, _, _, _, tt1, tt2) => tt1.size + tt2.size + BigInt(1)
    }.ensuring(_ > BigInt(0))

    /**
      * Returns whether the derivation tree is sound.
      * Therefore, isSound is a verifier for the proof system generated by the reduction rules.
      * 
      * For each derivation rule it checks whether:
      * - each subtree is also sound
      * - the conclusions of the subtrees are the premises of the rule.
      */
    @pure
    def isSound: Boolean = 
      decreases(this)
      this match 
        case ReflDerivation(_) => true
        case ArrowTypeDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
          prd1.isSound && prd2.isSound && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AbsTypeDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) => 
          prd.isSound && prd.type1 == b1 && prd.type2 == b2 && k1 == k2
        case AppTypeDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
          prd1.isSound && prd2.isSound && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AppAbsTypeDerivation(AbsType(argK, body1), arg1, body2, arg2, tt1, tt2) => 
          tt1.isSound && tt2.isSound && tt1.type1 == body1 && tt1.type2 == body2 &&
          tt2.type1 == arg1 && tt2.type2 == arg2 

    /**
      * Converts the tree into parallel type reduction step
      * ! This function is needed as ParallelReductionDerivation does not extend ARSStep
      * ! for technical reasons mentioned in the ARS file
      * 
      * * Basic property: the resulting reduction step is well formed
      */
    @opaque @pure @inlineOnce
    def toARSStep: ParallelReductionStep = {
      (this, type1, type2, isSound)
    }.ensuring(res => res.isWellFormed && res.unfold == this)
  }

  /**
    * Parallel reduction rules as listed in TAPL Figure 30-3
    */
  case class ReflDerivation(t: Type) extends ParallelReductionDerivation
  case class ArrowTypeDerivation(t1: ArrowType, t2: ArrowType, ed1: ParallelReductionDerivation, ed2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AbsTypeDerivation(t1: AbsType, t2: AbsType, ed: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppTypeDerivation(t1: AppType, t2: AppType, ed: ParallelReductionDerivation, ed2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppAbsTypeDerivation(abs1: AbsType, arg1: Type, body2: Type, arg2: Type , tt1: ParallelReductionDerivation, tt2: ParallelReductionDerivation) extends ParallelReductionDerivation

  type ParallelReductionStep = ARSStep[Type, ParallelReductionDerivation]
  type MultiStepParallelReduction = ARSKFoldComposition[Type, ParallelReductionDerivation]

  /**
    * Equivalence witnesses between two types
    * ! This other yet equivalent definition of type equivalence is not the same as in the book.
    * ! The proof of equivalence between both definitions (TAPL Lemma 30.3.5) involves technical tree
    * ! transformations and is therefore not implemented yet.
    */
  type ParallelEquivalence = ARSEquivalence[Type, ParallelReductionDerivation]
  /**
    * Yet other equivalent definition of type equivalence
    * ! This definition will never be used in practice except to prove Church Rosser Property
    */
  type ParallelEquivalenceSeq = ARSKFoldComposition[Type, ARSSymmStep[Type, ParallelReductionDerivation]]

  extension (s: ParallelReductionStep){
    @pure
    def isWellFormed: Boolean = s.unfold.type1 == s.t1 && s.unfold.type2 == s.t2 && s.unfold.isSound == s.isSound
    @pure
    def isValid: Boolean = s.isSound && s.isWellFormed
  }

  extension (ms: MultiStepParallelReduction){
    @pure
    def isWellFormed: Boolean =
      decreases(ms)
      ms match
        case ARSIdentity(t) => true
        case ARSComposition(h, t) => h.isWellFormed && t.isWellFormed
    @pure
    def isValid: Boolean = {
      decreases(ms)
      ms match
          case ARSIdentity(t) => true
          case ARSComposition(h, t) => h.isValid && t.isValid && h.t2 == t.t1
    }.ensuring(_ == (ms.isSound && ms.isWellFormed))
  }

  extension (ms: ParallelEquivalence){
    @pure
    def isWellFormed: Boolean =
      decreases(ms)
      ms match
        case ARSReflexivity(t) => true
        case ARSBaseRelation(r) => r.isWellFormed
        case ARSTransitivity(r1, r2) => r1.isWellFormed && r2.isWellFormed
        case ARSSymmetry(r) => r.isWellFormed
    @pure
    def isValid: Boolean = {
      decreases(ms)
      ms match
        case ARSReflexivity(t) => true
        case ARSBaseRelation(r) => r.isValid
        case ARSTransitivity(r1, r2) => r1.isValid && r2.isValid && r1.t2 == r2.t1
        case ARSSymmetry(r) => r.isValid 
    }.ensuring(_ == (ms.isSound && ms.isWellFormed))
  }

}

object ParallelTypeReductionValidity{

  import ParallelTypeReduction.*

  extension (s: ARSSymmStep[Type, ParallelReductionDerivation]) {
    @pure
    def isDeepValid: Boolean = {
      s match
        case ARSBaseStepClass(s) => s.isValid
        case ARSSymmStepClass(s) => s.isValid
    }
  }

  extension (eq: ParallelEquivalenceSeq) {
    @pure
    def isDeepValid: Boolean =
      decreases(eq)
      eq match
        case ARSIdentity(t) => true
        case ARSComposition(h, t) => h.unfold.isDeepValid && t.isDeepValid
  }

  @pure @inlineOnce @opaque
  def concatWellFormed(@induct s1: MultiStepParallelReduction, s2: MultiStepParallelReduction): Unit = {
    require(s1.isWellFormed)
    require(s2.isWellFormed)
  }.ensuring(s1.concat(s2).isWellFormed)

  @pure @inlineOnce @opaque
  def toReflTransWellFormed(@induct ms: MultiStepParallelReduction): Unit = {
    require(ms.isWellFormed)
  }.ensuring(ms.toReflTrans.isWellFormed)

  @pure @opaque @inlineOnce
  def kFoldInverseToReflTransWellFormed(ms: MultiStepParallelReduction): Unit = {
    require(ms.isValid)
    toReflTransWellFormed(ms)
  }.ensuring(kFoldInverseToReflTrans(ms).isWellFormed)

  @pure @opaque @inlineOnce
  def reductionImpliesEquivalenceWellFormed(ms1: MultiStepParallelReduction, ms2: MultiStepParallelReduction, eq: ParallelEquivalence): Unit = {
    require(ms1.isValid)
    require(ms2.isValid)
    require(eq.isValid)
    require(ms1.t2 == eq.t1)
    require(ms2.t2 == eq.t2)
    toReflTransWellFormed(ms1)
    kFoldInverseToReflTransWellFormed(ms2)
  }.ensuring(reductionImpliesEquivalence(ms1, ms2, eq).isWellFormed)

  @pure @opaque @inlineOnce
  def reduceSameFormEquivalentWellFormed(ms1: MultiStepParallelReduction, ms2: MultiStepParallelReduction): Unit = {
    require(ms1.isValid)
    require(ms2.isValid)
    require(ms1.t2 == ms2.t2)
    reductionImpliesEquivalenceWellFormed(ms1, ms2, ARSReflexivity(ms1.t2))
  }.ensuring(reduceSameFormEquivalent(ms1, ms2).isWellFormed)

  @pure @opaque @inlineOnce
  def concatDeepValid(@induct s1: ParallelEquivalenceSeq, s2: ParallelEquivalenceSeq): Unit = {
    require(s1.isDeepValid)
    require(s2.isDeepValid  )
  }.ensuring(_ => s1.concat(s2).isDeepValid)

  @pure @opaque @inlineOnce
  def inverseDeepValid(@induct s: ARSSymmStep[Type, ParallelReductionDerivation]): Unit = {
    require(s.isDeepValid)
  }.ensuring(s.inverse.isDeepValid)

  @pure @opaque @inlineOnce
  def symmClosureInverseDeepValid(eq: ParallelEquivalenceSeq): Unit = {
    decreases(eq)
    require(eq.isValid && eq.isDeepValid)
    eq match
      case ARSIdentity(_) => ()
      case ARSComposition(h, t) =>
        symmClosureInverseDeepValid(t)
        inverseDeepValid(h.unfold)
        assert(h.unfold.inverse.isDeepValid)
        assert(ARS1Fold(h.unfold.inverse.toARSStep).isDeepValid)
        concatDeepValid(symmClosureInverse(t), ARS1Fold(h.unfold.inverse.toARSStep))
  }.ensuring(symmClosureInverse(eq).isDeepValid)

  @pure @opaque @inlineOnce
  def equivalenceToSymmClosureDeepValid(eq: ParallelEquivalence): Unit ={
    decreases(eq)
    require(eq.isValid)
    
    eq match
      case ARSReflexivity(t) => ()
      case ARSSymmetry(r) => 
        r match
          case ARSSymmetry(r2) =>  equivalenceToSymmClosureDeepValid(r2)
          case ARSTransitivity(r1, r2) => 
            equivalenceToSymmClosureDeepValid(r2)
            equivalenceToSymmClosureDeepValid(r1)
            symmClosureInverseDeepValid(equivalenceToSymmClosure(r2))
            symmClosureInverseDeepValid(equivalenceToSymmClosure(r1))
            concatDeepValid(symmClosureInverse(equivalenceToSymmClosure(r2)), symmClosureInverse(equivalenceToSymmClosure(r1)))
          case ARSReflexivity(t) => ()
          case ARSBaseRelation(r2) => ()
      case ARSTransitivity(r1, r2) => 
        equivalenceToSymmClosureDeepValid(r2)
        equivalenceToSymmClosureDeepValid(r1)
        concatDeepValid(equivalenceToSymmClosure(r1), equivalenceToSymmClosure(r2))
      case ARSBaseRelation(r) => ()
  }.ensuring(equivalenceToSymmClosure(eq).isDeepValid)

}

object ParallelTypeReductionProperties {

  import ParallelTypeReduction._
  import ParallelTypeReductionValidity._

    /**
    * * Short version: If T1 => T2 and FV(T1) ∩ [a, a + b[ = ∅ then FV(T2) ∩ [a, a + b[ = ∅
    * 
    * Long version:
    * 
    * Preconditions:
    *   - sd, the derivation tree witnessing T1 => T2, is sound
    *   - a and b are both non negative
    *   - FV(T1) ∩ [a, a + b[ = ∅
    * 
    * Postcondition:
    *   - FV(T2) ∩ [a, a + b[ = ∅
    * 
    */
  @inlineOnce @opaque @pure
  def reduceBoundRange(sd: ParallelReductionDerivation, a: BigInt, b: BigInt): Unit = {
    decreases(sd)
    require(sd.isSound)
    require(a >= 0)
    require(b >= 0)
    require(!sd.type1.hasFreeVariablesIn(a, b))

    sd match
      case ReflDerivation(t) => ()
      case ArrowTypeDerivation(_, _, prd1, prd2) => 
        reduceBoundRange(prd1, a, b)
        reduceBoundRange(prd2, a, b)
      case AppTypeDerivation(_, _, prd1, prd2) => 
        reduceBoundRange(prd1, a, b)
        reduceBoundRange(prd2, a, b)
      case AbsTypeDerivation(_, _, prd) =>
        reduceBoundRange(prd, a + 1, b)
      case AppAbsTypeDerivation(_, _, _, _, prd1, prd2) =>
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
    *   - in case d is negative then FV(T1) ∩ [c, c - d[ = ∅ (cf. negative shifts definition)
    * 
    * Postcondition:
    *   There exists a sound derivation tree witnessing shift(T1, d, c) => shift(T2, d, c)
    * * The proof is constructive and returns this derivation tree
    */
  @inlineOnce @opaque @pure
  def reduceShift(sd: ParallelReductionDerivation, d: BigInt, c: BigInt): ParallelReductionDerivation = {
    decreases(sd)
    require(sd.isSound)
    require(c >= 0)
    require(d < 0 ==> !sd.type1.hasFreeVariablesIn(c, -d))

    if d < 0 then 
      reduceBoundRange(sd, c, -d) 
    else 
      true

    sd match
      case ReflDerivation(t) => ReflDerivation(shift(t, d, c))
      case ArrowTypeDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
        val res1 = reduceShift(prd1, d, c)
        val res2 = reduceShift(prd2, d, c)
        ArrowTypeDerivation(ArrowType(shift(t11, d, c), shift(t12, d, c)), ArrowType(shift(t21, d, c), shift(t22, d, c)), res1, res2)
      case AbsTypeDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) =>
        val res1 = reduceShift(prd, d, c + 1)
        AbsTypeDerivation(AbsType(k1, res1.type1), AbsType(k2, res1.type2), res1)
      case AppTypeDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
        val res1 = reduceShift(prd1, d, c)
        val res2 = reduceShift(prd2, d, c)
        AppTypeDerivation(AppType(shift(t11, d, c), shift(t12, d, c)), AppType(shift(t21, d, c), shift(t22, d, c)), res1, res2)
      case AppAbsTypeDerivation(AbsType(argK, body1), arg1, body2, arg2, prd1, prd2) =>
        if d < 0 then 
          reduceBoundRange(prd1, c + 1, -d)
          reduceBoundRange(prd2, c, -d)  
        else 
          true
        val resBody = reduceShift(prd1, d, c + 1)
        val resArg = reduceShift(prd2, d, c)
        shiftAbsSubstitutionCommutativity(body2, arg2, d, c)
        AppAbsTypeDerivation(AbsType(argK, shift(body1, d, c + 1)), shift(arg1, d, c), shift(body2, d, c + 1), shift(arg2, d, c), resBody, resArg)
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
  @inlineOnce @opaque @pure
  def reduceReflSubst(t: Type, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
    decreases(t)
    require(sd.isSound)
    require(j >= 0)
    t match
      case ArrowType(t1, t2) =>
        val d1 = reduceReflSubst(t1, j, sd)
        val d2 = reduceReflSubst(t2, j, sd)
        ArrowTypeDerivation(ArrowType(d1.type1, d2.type1), ArrowType(d1.type2, d2.type2), d1, d2)
      case AppType(t1, t2) =>
        val d1 = reduceReflSubst(t1, j, sd)
        val d2 = reduceReflSubst(t2, j, sd)
        AppTypeDerivation(AppType(d1.type1, d2.type1), AppType(d1.type2, d2.type2), d1, d2)
      case AbsType(k, body) =>
        val bd = reduceReflSubst(body, j + 1, reduceShift(sd, 1, 0))
        AbsTypeDerivation(AbsType(k, bd.type1), AbsType(k, bd.type2), bd)
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
  @inlineOnce @opaque @pure
  def reduceSubst(td: ParallelReductionDerivation, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
    decreases(td)
    require(td.isSound)
    require(sd.isSound)
    require(j >= 0)
    require(!sd.type1.hasFreeVariablesIn(0, 1))
    
    reduceBoundRange(sd, 0, 1)
    boundRangeShift(sd.type1, 1, 0, 0, 0)
    boundRangeShift(sd.type2, 1, 0, 0, 0)

    td match
      case ReflDerivation(t) => reduceReflSubst(td.type1, j, sd)
      case ArrowTypeDerivation(ArrowType(t11, t12), ArrowType(t21, t22), td1, td2) =>
        val rs1 = reduceSubst(td1, j, sd)
        val rs2 = reduceSubst(td2, j, sd)
        ArrowTypeDerivation(ArrowType(rs1.type1, rs2.type1), ArrowType(rs1.type2, rs2.type2), rs1, rs2)
      case AppTypeDerivation(AppType(t11, t12), AppType(t21, t22), td1, td2) =>
        val rs1 = reduceSubst(td1, j, sd)
        val rs2 = reduceSubst(td2, j, sd)
        AppTypeDerivation(AppType(rs1.type1, rs2.type1), AppType(rs1.type2, rs2.type2), rs1, rs2)
      case AbsTypeDerivation(AbsType(k1, b1), AbsType(k2, b2), bd) =>
        val rs = reduceSubst(bd, j + 1, reduceShift(sd, 1, 0))
        AbsTypeDerivation(AbsType(k1, rs.type1), AbsType(k2, rs.type2), rs)
      case AppAbsTypeDerivation(AbsType(argK, body), arg1, body2, arg2, td1, td2) => 
        val rsh = reduceShift(sd, 1, 0)
        val rs1 = reduceSubst(td1, j + 1, rsh)
        val rs2 = reduceSubst(td2, j, sd)
        absSubstSubstCommutativity(body2, arg2, j, sd.type2)
        AppAbsTypeDerivation(AbsType(argK, rs1.type1), rs2.type1, rs1.type2, rs2.type2, rs1, rs2)
      case _ => td

  }.ensuring(res =>
    res.isSound &&
    res.type1 == substitute(td.type1, j, sd.type1) &&
    res.type2 == substitute(td.type2, j, sd.type2))

  /**
    * * Short version: If λX.B1 => λX.B2 and A1 => A2 then B1[X := A1] => B2[X := A2]
    * 
    * Long version:
    * 
    * Preconditions:
    *   - bd and ad, the derivation trees respectively witnessing B1 => B2 and A1 => A2, are sound
    *
    * Postcondition:
    *   There exists a sound derivation tree witnessing absSubstitution(B1, A1) => absSubstitution(B2, A2)
    * * The proof is constructive and returns this list
    */
  @inlineOnce @opaque @pure
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
  @inlineOnce @opaque @pure
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
        case (ArrowTypeDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd11, prd12), ArrowTypeDerivation(ArrowType(t31, t32), ArrowType(t41, t42), prd21, prd22)) =>
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (ArrowTypeDerivation(ArrowType(dP11.type1, dP21.type1), ArrowType(dP11.type2, dP21.type2), dP11, dP21), ArrowTypeDerivation(ArrowType(dP12.type1, dP22.type1), ArrowType(dP12.type2, dP22.type2), dP12, dP22))
        case (AbsTypeDerivation(AbsType(k1, b1), AbsType(k2, b2), prd11), AbsTypeDerivation(AbsType(k3, b3), AbsType(k4, b4), prd12)) =>
          val (dP1, dP2) = diamondProperty(prd11, prd12)
          (AbsTypeDerivation(AbsType(k2, dP1.type1), AbsType(k2, dP1.type2), dP1), AbsTypeDerivation(AbsType(k2, dP2.type1), AbsType(k2, dP2.type2), dP2))
        case (AppTypeDerivation(AppType(t11, t12), AppType(t21, t22), prd11, prd12), AppTypeDerivation(AppType(t31, t32), AppType(t41, t42), prd21, prd22)) =>
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (AppTypeDerivation(AppType(dP11.type1, dP21.type1), AppType(dP11.type2, dP21.type2), dP11, dP21), AppTypeDerivation(AppType(dP12.type1, dP22.type1), AppType(dP12.type2, dP22.type2), dP12, dP22))
        case (AppAbsTypeDerivation(AbsType(k, body11), arg11, body12, arg12, prd11, prd12), AppAbsTypeDerivation(AbsType(_, body21), arg21, body22, arg22, prd21, prd22)) => 
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (reduceAbsSubst(dP11, dP21), reduceAbsSubst(dP12, dP22))
        case (AppAbsTypeDerivation(AbsType(k, body1), arg1, body2, arg2, prd11, prd12), AppTypeDerivation(AppType(AbsType(_, t11), t12), AppType(AbsType(_, t21), t22), prd, prd22)) => 
          prd match
            case AbsTypeDerivation(_, _, prd21) => 
              val (dP11, dP12) = diamondProperty(prd11, prd21)
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (reduceAbsSubst(dP11, dP21), AppAbsTypeDerivation(AbsType(k, dP12.type1), dP22.type1, dP12.type2, dP22.type2, dP12, dP22))
            case ReflDerivation(body) => 
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (reduceAbsSubst(ReflDerivation(body2), dP21), AppAbsTypeDerivation(AbsType(k, body1), dP22.type1, body2, dP22.type2, prd11, dP22))
            case _ => Unreachable
          
        case (AppTypeDerivation(AppType(AbsType(_, t11), t12), AppType(AbsType(_, t21), t22), prd, prd12), AppAbsTypeDerivation(AbsType(k, body1), arg1, body2, arg2, prd21, prd22)) => 
          prd match
            case AbsTypeDerivation(_, _, prd11) => 
              val (dP11, dP12) = diamondProperty(prd11, prd21)
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (AppAbsTypeDerivation(AbsType(k, dP11.type1), dP21.type1, dP11.type2, dP21.type2, dP11, dP21), reduceAbsSubst(dP12, dP22))
            case ReflDerivation(body) => 
              val (dP21, dP22) = diamondProperty(prd12, prd22)
              (AppAbsTypeDerivation(AbsType(k, body1), dP21.type1, body2, dP21.type2, prd21, dP21), reduceAbsSubst(ReflDerivation(body2), dP22))
            case _ => Unreachable
          
        case _ => Unreachable
  }.ensuring(res => res._1.type1 == prd1.type2 &&
                    res._2.type1 == prd2.type2 &&
                    res._1.type2 == res._2.type2 &&
                    res._1.isSound && res._2.isSound)

  /** 
    * Semi Confluence - TRAT Definition 2.1.4
    * 
    * * Short version: If T1 =k=> T2 and T1 => T3 then there exits a type T4 such that T2 => T4 and T3 =k=> T4
    * 
    * Long version:
    * 
    * Preconditions:
    *   - prd1, the list of derivation step witnessing T11 =k=> T2 is sound
    *   - h2, the derivation step witnessing T12 => T3 is sound
    *   - T11 = T12 (= T1 in the above theorem statement)
    *
    * Postcondition:
    *   There exists two sound list of derivation trees respectevely witnessing T => T41 and T' =k=> T42 such that:
    *     - T = T2
    *     - T'= T3
    *     - T41 = T42
    * * The proof is constructive and returns this pair of list
    */
  @pure @inlineOnce @opaque
  def semiConfluence(prd1: MultiStepParallelReduction, h2: ParallelReductionStep): (ParallelReductionStep, MultiStepParallelReduction) = {
    decreases(prd1)
    require(prd1.isValid)
    require(h2.isValid)
    require(h2.t1 == prd1.t1)

    prd1 match
      case ARSIdentity(t) => (h2, ARSIdentity(h2.t2))
      case ARSComposition(h, t) =>
        assert(h.isValid) //needed
        val (dP1, dP2) = diamondProperty(h.unfold, h2.unfold)
        val (conf1, conf2) = semiConfluence(t, dP1.toARSStep)
        //assert(dP2.toARSStep.isValid) //needed
        (conf1, ARSComposition(dP2.toARSStep, conf2))
  }.ensuring(res =>
    res._1.t2 == res._2.t2 &&
    res._1.t1 == prd1.t2 &&
    res._2.t1 == h2.t2 &&
    res._1.isValid && res._2.isValid &&
    res._2.size == prd1.size)

  /**
    * Confluence - TRAT Definition 2.1.3, TAPL Lemma 30.3.9
    * 
    * * Short version: If T1 =n=> T2 and T1 =m=> T3 then there exits a type T4 such that T2 =m=> T4 and T3 =n=> T4
    * 
    * Long version:
    * 
    * Preconditions:
    *   - prd1, the list of derivation trees witnessing T11 =n=> T2 is sound
    *   - prd2, the list of derivation trees witnessing T12 =m=> T3 is sound
    *   - T11 = T12 (= T1 in the above theorem statement)
    *
    * Postcondition:
    *   There exists two sound list of derivation trees respectevely witnessing T =m=> T41 and T' =n=> T42 such that:
    *     - T = T2
    *     - T'= T3
    *     - T41 = T42
    * * The proof is constructive and returns this pair of list
    */
  @pure @inlineOnce @opaque
  def confluence(prd1: MultiStepParallelReduction, prd2: MultiStepParallelReduction): (MultiStepParallelReduction, MultiStepParallelReduction) = {
    decreases(prd1.size + prd2.size)
    require(prd1.isValid)
    require(prd2.isValid)
    require(prd1.t1 == prd2.t1)

    (prd1, prd2) match
      case (ARSIdentity(t1), ARSIdentity(t2)) => (ARSIdentity(t1), ARSIdentity(t1))
      case (ARSIdentity(_), ARSComposition(head, tail)) => (ARSComposition(head, tail), ARSIdentity(prd2.t2))
      case (ARSComposition(head, tail), ARSIdentity(_)) => (ARSIdentity(prd1.t2), ARSComposition(head, tail))
      case (ARSComposition(head1, tail1), ARSComposition(head2, tail2)) =>
        val (red11, prd12) = semiConfluence(prd1, head2)
        val (conf1, conf2) = confluence(prd12, tail2)
        (ARSComposition(red11, conf1), conf2)
  }.ensuring(res => 
    res._1.t2 == res._2.t2 &&
    res._1.t1 == prd1.t2 &&
    res._2.t1 == prd2.t2 &&
    res._1.isValid && res._2.isValid &&
    res._2.size == prd1.size && res._1.size == prd2.size 
  )

  /**
    * Church Rosser Property - TRAT Definition 2.1.3, TAPL Corollary 30.3.11
    * 
    * * Short version: If T1 ≡ T2 then there exits a type T3 such that T1 =m=> T3 and T2 =n=> T3
    * 
    * Long version:
    * 
    * Preconditions:
    *   - eq, the witness of T1 ≡ T2 is valid and deeply valid
    *
    * Postcondition:
    *   There exists two sound list of derivation trees respectevely witnessing T =m=> T31 and T' =n=> T32 such that:
    *     - T = T1
    *     - T'= T2
    *     - T31 = T32
    * * The proof is constructive and returns this pair of list
    */
  @pure @inlineOnce @opaque
  def churchRosser(eq: ParallelEquivalenceSeq): (MultiStepParallelReduction, MultiStepParallelReduction) = {
    decreases(eq)
    require(eq.isValid && eq.isDeepValid)

    ARS.isValidInd(eq)

    eq match
      case ARSIdentity(t1) => (ARSIdentity(t1), ARSIdentity(t1))
      case ARSComposition(h, t) => 
        val (cr1, cr2) = churchRosser(t)
        assert(h.isValid) //needed
        h.unfold match
          case ARSBaseStepClass(s) => (ARSComposition(s, cr1), cr2)
          case ARSSymmStepClass(s) => 
            val (sc1, sc2) = semiConfluence(cr1, s)
            concatWellFormed(cr2, ARS1Fold(sc1))
            (sc2, cr2.concat(ARS1Fold(sc1)))

  }.ensuring(res => 
    res._1.t2 == res._2.t2 &&
    res._1.t1 == eq.t1 &&
    res._2.t1 == eq.t2 &&
    res._1.isValid && res._2.isValid
  )

  /**
    * Same theorem as above with an equivalent definition of equivalence instead
    */
  @pure @inlineOnce @opaque
  def churchRosser(eq: ParallelEquivalence): (MultiStepParallelReduction, MultiStepParallelReduction) = {
    require(eq.isValid)
    equivalenceToSymmClosureDeepValid(eq)
    churchRosser(equivalenceToSymmClosure(eq))

  }.ensuring(res => 
    res._1.t2 == res._2.t2 &&
    res._1.t1 == eq.t1 &&
    res._2.t1 == eq.t2 &&
    res._1.isValid && res._2.isValid
  )

  @pure @inlineOnce @opaque
  def arrowMultiStepReduction(s1: Type, s2: Type, red: MultiStepParallelReduction): (MultiStepParallelReduction, MultiStepParallelReduction) = {
    decreases(red)
    require(red.isValid)
    require(red.t1 == ArrowType(s1, s2))

    red match
      case ARSIdentity(_) => (ARSIdentity(s1), ARSIdentity(s2))
      case ARSComposition(h, t) =>
        assert(h.isValid) //needed
        assert(h.unfold.type1.isInstanceOf[ArrowType]) //needed
        h.unfold match
          case ReflDerivation(_) => arrowMultiStepReduction(s1, s2, t)
          case ArrowTypeDerivation(_, ArrowType(s3, s4), br1, br2) =>
            val (sdr1, sdr2) = arrowMultiStepReduction(s3, s4, t)
            (ARSComposition(br1.toARSStep, sdr1), ARSComposition(br2.toARSStep, sdr2))
          case _ => Unreachable
    
  }.ensuring(
    res => 
      res._1.isValid &&
      res._2.isValid &&
      res._1.t1 == s1 &&
      res._2.t1 == s2 &&
      red.t2 == ArrowType(res._1.t2, res._2.t2)
  )

  @opaque @inlineOnce @pure
  def arrowEquivalence(s1: Type, s2: Type, s3: Type, s4: Type, eq: ParallelEquivalence): (ParallelEquivalence, ParallelEquivalence) = {
    require(eq.isValid)
    require(eq.t1 == ArrowType(s1, s2))
    require(eq.t2 == ArrowType(s3, s4))

    val (pr1, pr2) = churchRosser(eq)
    val (spr11, spr12) = arrowMultiStepReduction(s1, s2, pr1)
    val (spr21, spr22) = arrowMultiStepReduction(s3, s4, pr2)
    reduceSameFormEquivalentWellFormed(spr11, spr21)
    reduceSameFormEquivalentWellFormed(spr12, spr22)
    (reduceSameFormEquivalent(spr11, spr21), reduceSameFormEquivalent(spr12, spr22))
    
  }.ensuring(
    res => 
      res._1.isValid &&
      res._2.isValid &&
      res._1.t1 == s1 &&
      res._2.t1 == s2 &&
      res._1.t2 == s3 &&
      res._2.t2 == s4
  )

  /**
   * Soudness of reduction mapping for ArrowTypeDerivation
   * 
   * * Short version: If T1 =k=> T1' and T2 =k'=> T2' then (T1 -> T2) =max(k, k')=> (T1' -> T2')
   * 
   * Long version:
   *
   * Preconditions:
   *   - prd1, the step sequence witnessing T1 =k=> T1' isValid
   *   - prd2, the step sequence witnessing T2 =k=> T2' isValid
   * 
   * Postcondition:
   *   There exists a step sequence witnessing (T -> S) =n=> (T' -> S') such that:
   *     - T  = T1
   *     - T' = T1'
   *     - S  = T2
   *     - S' = T2'
   *     - n  = max(k, k')
   * 
   * * The proof is constructive and outputs this step sequence
   */
  @pure @opaque @inlineOnce
  def arrowDerivationMap(prd1: MultiStepParallelReduction, prd2: MultiStepParallelReduction): MultiStepParallelReduction = {
    decreases(prd1.size + prd2.size)
    require(prd1.isValid)
    require(prd2.isValid)

    (prd1, prd2) match
      case (ARSIdentity(t1), ARSIdentity(t2))               => ARSIdentity(ArrowType(t1, t2))
      case (ARSComposition(h1, t1), ARSIdentity(t2))        => 
        assert(max(t1.size, prd2.size) + 1 == prd1.size )
        ARSComposition(ArrowTypeDerivation(ArrowType(h1.t1, t2), ArrowType(h1.t2, t2), h1.unfold, ReflDerivation(t2)).toARSStep, arrowDerivationMap(t1, prd2))
      case (ARSIdentity(t1), ARSComposition(h2, t2))        => 
        assert(max(prd1.size, t2.size) + 1 == prd2.size )
        ARSComposition(ArrowTypeDerivation(ArrowType(t1, h2.t1), ArrowType(t1, h2.t2), ReflDerivation(t1), h2.unfold).toARSStep, arrowDerivationMap(prd1, t2))
      case (ARSComposition(h1, t1), ARSComposition(h2, t2)) => ARSComposition(ArrowTypeDerivation(ArrowType(h1.t1, h2.t1), ArrowType(h1.t2, h2.t2), h1.unfold, h2.unfold).toARSStep, arrowDerivationMap(t1, t2))
    
  }.ensuring(res => res.isValid && res.t1 == ArrowType(prd1.t1, prd2.t1) && res.t2 == ArrowType(prd1.t2, prd2.t2) && res.size == max(prd1.size, prd2.size))
  
  /**
   * Soudness of reduction mapping for AppTypeDerivation
   * 
   * * Short version: If T1 =k=> T1' and T2 =k'=> T2' then T1 T2 =max(k, k')=> T1' T2'
   * 
   * Long version:
   *
   * Preconditions:
   *   - prd1, the step sequence witnessing T1 =k=> T1' isValid
   *   - prd2, the step sequence witnessing T2 =k=> T2' isValid
   * 
   * Postcondition:
   *   There exists a step sequence witnessing T S =n=> T' S' such that:
   *     - T  = T1
   *     - T' = T1'
   *     - S  = T2
   *     - S' = T2'
   *     - n  = max(k, k')
   * 
   * * The proof is constructive and outputs this step sequence
   */
  @pure @opaque @inlineOnce
  def appDerivationMap(prd1: MultiStepParallelReduction, prd2: MultiStepParallelReduction): MultiStepParallelReduction = {
    decreases(prd1.size + prd2.size)
    require(prd1.isValid)
    require(prd2.isValid)

    (prd1, prd2) match
      case (ARSIdentity(t1), ARSIdentity(t2))               => ARSIdentity(AppType(t1, t2))
      case (ARSComposition(h1, t1), ARSIdentity(t2))        => 
        assert(max(t1.size, prd2.size) + 1 == prd1.size )
        ARSComposition(AppTypeDerivation(AppType(h1.t1, t2), AppType(h1.t2, t2), h1.unfold, ReflDerivation(t2)).toARSStep, appDerivationMap(t1, prd2))
      case (ARSIdentity(t1), ARSComposition(h2, t2))        => 
        assert(max(prd1.size, t2.size) + 1 == prd2.size )
        ARSComposition(AppTypeDerivation(AppType(t1, h2.t1), AppType(t1, h2.t2), ReflDerivation(t1), h2.unfold).toARSStep, appDerivationMap(prd1, t2))
      case (ARSComposition(h1, t1), ARSComposition(h2, t2)) => ARSComposition(AppTypeDerivation(AppType(h1.t1, h2.t1), AppType(h1.t2, h2.t2), h1.unfold, h2.unfold).toARSStep, appDerivationMap(t1, t2))
    
  }.ensuring(res => res.isValid && res.t1 == AppType(prd1.t1, prd2.t1) && res.t2 == AppType(prd1.t2, prd2.t2) && res.size == max(prd1.size, prd2.size))
 
  /**
   * Soudness of reduction mapping for AbsTypeDerivation
   * 
   * * Short version: If T1 =k=> T2 then λ.T1 =k=> λ.T2
   * 
   * Long version:
   *
   * Preconditions:
   *   - prd, the step sequence witnessing T1 =k=> T2 isValid
   * 
   * Postcondition:
   *   There exists a step sequence witnessing λ.T =k'=> λ.T' such that:
   *     - T  = T1
   *     - T' = T2
   *     - k  = k'
   * 
   * * The proof is constructive and outputs this step sequence
   */
  @pure @opaque @inlineOnce
  def absDerivationMap(k: Kind, prd: MultiStepParallelReduction): MultiStepParallelReduction = {
    decreases(prd)
    require(prd.isValid)
    prd match
      case ARSIdentity(b) => ARSIdentity(AbsType(k, b))
      case ARSComposition(h, t) => ARSComposition(AbsTypeDerivation(AbsType(k, h.t1), AbsType(k, h.t2), h.unfold).toARSStep, absDerivationMap(k, t))
    
  }.ensuring(res => res.isValid && res.t1 == AbsType(k, prd.t1) && res.t2 == AbsType(k, prd.t2) && res.size == prd.size)

  @pure @opaque @inlineOnce
  def arrowEquivalenceMap(eq1: ParallelEquivalence, eq2: ParallelEquivalence): ParallelEquivalence = {
    require(eq1.isValid)
    require(eq2.isValid)
    val (prd11, prd12) = churchRosser(eq1)
    val (prd21, prd22) = churchRosser(eq2)
    val arrowPrd1 = arrowDerivationMap(prd11, prd21)
    val arrowPrd2 = arrowDerivationMap(prd12, prd22)
    reduceSameFormEquivalentWellFormed(arrowPrd1, arrowPrd2)
    reduceSameFormEquivalent(arrowPrd1, arrowPrd2)

  }.ensuring(res => res.isValid && res.t1 == ArrowType(eq1.t1, eq2.t1) && res.t2 == ArrowType(eq1.t2, eq2.t2))

  @pure @opaque @inlineOnce
  def appEquivalenceMap(eq1: ParallelEquivalence, eq2: ParallelEquivalence): ParallelEquivalence = {
    require(eq1.isValid)
    require(eq2.isValid)
    val (prd11, prd12) = churchRosser(eq1)
    val (prd21, prd22) = churchRosser(eq2)
    val appPrd1 = appDerivationMap(prd11, prd21)
    val appPrd2 = appDerivationMap(prd12, prd22)
    reduceSameFormEquivalentWellFormed(appPrd1, appPrd2)
    reduceSameFormEquivalent(appPrd1, appPrd2)

  }.ensuring(res => res.isValid && res.t1 == AppType(eq1.t1, eq2.t1) && res.t2 == AppType(eq1.t2, eq2.t2))
   
  @pure @opaque @inlineOnce
  def absEquivalenceMap(k: Kind, eq: ParallelEquivalence): ParallelEquivalence = {
    require(eq.isValid)
    val (prd1, prd2) = churchRosser(eq)
    val absPrd1 = absDerivationMap(k, prd1)
    val absPrd2 = absDerivationMap(k, prd2)
    reduceSameFormEquivalentWellFormed(absPrd1, absPrd2)
    reduceSameFormEquivalent(absPrd1, absPrd2)

  }.ensuring(res => res.isValid && res.t1 == AbsType(k, eq.t1) && res.t2 == AbsType(k, eq.t2))
   
}