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

object ARSEquivalences{


  def parallelToUsual(prd: ParallelReductionDerivation): MultiStepEvalReduction = {
    require(prd.isSound)
    prd match
      case ParallelTypeReduction.ReflDerivation(t) => NilEvalReduction(t)
      case ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
        val conv1 = parallelToUsual(prd1)
        val conv2 = parallelToUsual(prd2)
        val arr1 = arrowDerivationLMap(conv1, t12)
        val arr2 = arrowDerivationRMap(t21, conv2)
        arr1.concat(arr2)
      case ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
        val conv1 = parallelToUsual(prd1)
        val conv2 = parallelToUsual(prd2)
        val app1 = appDerivationLMap(conv1, t12)
        val app2 = appDerivationRMap(t21, conv2)
        app1.concat(app2)
      case ParallelTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) =>
        val conv = parallelToUsual(prd)
        absDerivationMap(k1, conv)
      case ParallelTypeReduction.AppAbsDerivation(AbsType(k, body1), arg1, body2, arg2, prd1, prd2) =>
        val conv1 = parallelToUsual(prd1)
        val conv2 = parallelToUsual(prd2)
        val step1 = appDerivationLMap(absDerivationMap(k, conv1), arg1)
        val step2 = appDerivationRMap(AbsType(k, body2), conv2)
        val temp = ConsEvalReduction(EvalTypeReduction.AppAbsDerivation(AbsType(k, body2), arg2), NilEvalReduction(absSubstitution(body2, arg2)))
        assert(temp.isSound && temp.type1 == AppType(AbsType(k, body2), arg2) && temp.type2 == absSubstitution(body2, arg2))
        (step1.concat(step2)).concat(ConsEvalReduction(EvalTypeReduction.AppAbsDerivation(AbsType(k, body2), arg2), NilEvalReduction(absSubstitution(body2, arg2))))
      case _ => NilEvalReduction(BasicType(""))
  }.ensuring(res => res.isSound && res.type1 == prd.type1 && res.type2 == prd.type2)

  def parallelToUsual(prd: MultiStepParallelReduction): MultiStepEvalReduction = {
    require(prd.isSound)
    prd match
      case NilParallelReduction(t) => NilEvalReduction(t)
      case ConsParallelReduction(h, t) => parallelToUsual(h).concat(parallelToUsual(t))
  }.ensuring(res => res.isSound && res.type1 == prd.type1 && res.type2 == prd.type2)

  def usualToParallel(prd: EvalReductionDerivation): ParallelReductionDerivation = {
    require(prd.isSound)
    prd match
      case EvalTypeReduction.ArrowDerivationL(ArrowType(t11, t12), ArrowType(t21, t22), rd) => ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), usualToParallel(rd), ParallelTypeReduction.ReflDerivation(t12))
      case EvalTypeReduction.ArrowDerivationR(ArrowType(t11, t12), ArrowType(t21, t22), rd) => ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ParallelTypeReduction.ReflDerivation(t11), usualToParallel(rd))
      case EvalTypeReduction.AppDerivationL(AppType(t11, t12), AppType(t21, t22), rd) => ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), usualToParallel(rd), ParallelTypeReduction.ReflDerivation(t12))
      case EvalTypeReduction.AppDerivationR(AppType(t11, t12), AppType(t21, t22), rd) => ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), ParallelTypeReduction.ReflDerivation(t11), usualToParallel(rd))
      case EvalTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), rd) => ParallelTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), usualToParallel(rd))
      case EvalTypeReduction.AppAbsDerivation(abs, arg) => ParallelTypeReduction.AppAbsDerivation(abs, arg, abs.body, arg, ParallelTypeReduction.ReflDerivation(abs.body), ParallelTypeReduction.ReflDerivation(arg))
    
  }.ensuring(res => res.isSound && res.type1 == prd.type1 && res.type2 == prd.type2)

  def usualToParallel(prd: MultiStepEvalReduction): MultiStepParallelReduction = {
    require(prd.isSound)
    prd match
      case NilEvalReduction(t) => NilParallelReduction(t)
      case ConsEvalReduction(h, t) => ConsParallelReduction(usualToParallel(h), usualToParallel(t))
  }.ensuring(res => res.isSound && res.type1 == prd.type1 && res.type2 == prd.type2 && prd.size == res.size)
}