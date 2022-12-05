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
import ParallelTypeReductionProperties._
import EvalTypeReductionProperties._
import ParallelTypeReduction._
import EvalTypeReduction._
import TypeTransformations._
import ARS._

object ARSEquivalences{

  def parallelToEval(prd: ParallelReductionDerivation): MultiStepEvalReduction = {
    require(prd.isSound)
    prd match
      case ParallelTypeReduction.ReflDerivation(t) => ARSIdentity(t)
      case ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
        val conv1 = parallelToEval(prd1)
        val conv2 = parallelToEval(prd2)
        val arr1 = arrowDerivationLMap(conv1, t12)
        val arr2 = arrowDerivationRMap(t21, conv2)
        EvalTypeReduction.concatWellFormed(arr1, arr2)
        arr1.concat(arr2)
      case ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
        val conv1 = parallelToEval(prd1)
        val conv2 = parallelToEval(prd2)
        val app1 = appDerivationLMap(conv1, t12)
        val app2 = appDerivationRMap(t21, conv2)
        EvalTypeReduction.concatWellFormed(app1, app2)
        app1.concat(app2)
      case ParallelTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) =>
        val conv = parallelToEval(prd)
        absDerivationMap(k1, conv)
      case ParallelTypeReduction.AppAbsDerivation(AbsType(k, body1), arg1, body2, arg2, prd1, prd2) =>
        val conv1 = parallelToEval(prd1)
        val conv2 = parallelToEval(prd2)
        val step1 = appDerivationLMap(absDerivationMap(k, conv1), arg1)
        val step2 = appDerivationRMap(AbsType(k, body2), conv2)
        EvalTypeReduction.concatWellFormed(step1, step2)
        EvalTypeReduction.concatWellFormed(step1.concat(step2), ARS1Fold(EvalTypeReduction.AppAbsDerivation(AbsType(k, body2), arg2).toARSStep))
        (step1.concat(step2)).concat(ARS1Fold(EvalTypeReduction.AppAbsDerivation(AbsType(k, body2), arg2).toARSStep))
      case _ => Unreacheable
  }.ensuring(res => res.isValid && res.t1 == prd.type1 && res.t2 == prd.type2)

  def parallelToEval(prd: MultiStepParallelReduction): MultiStepEvalReduction = {
    decreases(prd.size)
    require(prd.isValid)
    prd match
      case ARSIdentity(t) => ARSIdentity(t)
      case ARSComposition(h, t) => 
        EvalTypeReduction.concatWellFormed(parallelToEval(h.unfold), parallelToEval(t))
        parallelToEval(h.unfold).concat(parallelToEval(t))
  }.ensuring(res => res.isValid && res.t1 == prd.t1 && res.t2 == prd.t2)

  def parallelToEval(prd: ParallelEquivalence): EvalEquivalence = {
    decreases(prd.size)
    require(prd.isValid)
    prd match
      case ARSReflexivity(t) => ARSReflexivity(t)
      case ARSSymmetry(r) => ARSSymmetry(parallelToEval(r))
      case ARSTransitivity(r1, r2) => ARSTransitivity(parallelToEval(r1), parallelToEval(r2))
      case ARSBaseRelation(r) =>
        toReflTransWellFormed(parallelToEval(r.unfold))
        parallelToEval(r.unfold).toReflTrans
  }.ensuring(res => res.isValid && res.t1 == prd.t1 && res.t2 == prd.t2)

  def evalToParallel(prd: EvalReductionDerivation): ParallelReductionDerivation = {
    require(prd.isSound)
    (prd match
      case EvalTypeReduction.ArrowDerivationL(ArrowType(t11, t12), ArrowType(t21, t22), rd) => ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), evalToParallel(rd), ParallelTypeReduction.ReflDerivation(t12))
      case EvalTypeReduction.ArrowDerivationR(ArrowType(t11, t12), ArrowType(t21, t22), rd) => ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ParallelTypeReduction.ReflDerivation(t11), evalToParallel(rd))
      case EvalTypeReduction.AppDerivationL(AppType(t11, t12), AppType(t21, t22), rd) => ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), evalToParallel(rd), ParallelTypeReduction.ReflDerivation(t12))
      case EvalTypeReduction.AppDerivationR(AppType(t11, t12), AppType(t21, t22), rd) => ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), ParallelTypeReduction.ReflDerivation(t11), evalToParallel(rd))
      case EvalTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), rd) => ParallelTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), evalToParallel(rd))
      case EvalTypeReduction.AppAbsDerivation(abs, arg) => ParallelTypeReduction.AppAbsDerivation(abs, arg, abs.body, arg, ParallelTypeReduction.ReflDerivation(abs.body), ParallelTypeReduction.ReflDerivation(arg)))
    
  }.ensuring(res => res.isSound && res.type1 == prd.type1 && res.type2 == prd.type2)

  def evalToParallel(prd: MultiStepEvalReduction): MultiStepParallelReduction = {
    decreases(prd.size)
    require(prd.isValid)
    prd match
      case ARSIdentity(t) => ARSIdentity(t)
      case ARSComposition(h, t) => ARSComposition(evalToParallel(h.unfold).toARSStep, evalToParallel(t))
  }.ensuring(res => res.isValid && res.t1 == prd.t1 && res.t2 == prd.t2 && prd.size == res.size)

  def evalToParallel(prd: EvalEquivalence): ParallelEquivalence = {
    decreases(prd.size)
    require(prd.isValid)
    prd match
      case ARSReflexivity(t) => ARSReflexivity(t)
      case ARSSymmetry(r) => ARSSymmetry(evalToParallel(r))
      case ARSTransitivity(r1, r2) => ARSTransitivity(evalToParallel(r1), evalToParallel(r2))
      case ARSBaseRelation(r) => ARSBaseRelation(evalToParallel(r.unfold).toARSStep)
  }.ensuring(res => res.isValid && res.t1 == prd.t1 && res.t2 == prd.t2)
}