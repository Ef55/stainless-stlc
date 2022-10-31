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

object ARSEquivalences{


  // def parallelToUsual(prd: ParallelReductionDerivation): MultiStepUsualReduction = {
  //   require(prd.isSound)
  //   prd match
  //     case ReflDerivation(t) => NilUsualReduction(t)
  //     case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
  //       val conv1 = parallelToUsual(prd1)
  //       val conv2 = parallelToUsual(prd2)
  //       Cons(ArrowDerivationL(t11, 
    
  // }.ensuring(res => res.isSound && res.type1 == prd.type1 && res.type2 == prd.type2)

  def usualToParallel(prd: UsualTypeReduction.UsualReductionDerivation): ParallelTypeReduction.ParallelReductionDerivation = {
    require(prd.isSound)
    prd match
      case UsualTypeReduction.ArrowDerivationL(ArrowType(t11, t12), ArrowType(t21, t22), rd) => ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), usualToParallel(rd), ParallelTypeReduction.ReflDerivation(t12))
      case UsualTypeReduction.ArrowDerivationR(ArrowType(t11, t12), ArrowType(t21, t22), rd) => ParallelTypeReduction.ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ParallelTypeReduction.ReflDerivation(t11), usualToParallel(rd))
      case UsualTypeReduction.AppDerivationL(AppType(t11, t12), AppType(t21, t22), rd) => ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), usualToParallel(rd), ParallelTypeReduction.ReflDerivation(t12))
      case UsualTypeReduction.AppDerivationR(AppType(t11, t12), AppType(t21, t22), rd) => ParallelTypeReduction.AppDerivation(AppType(t11, t12), AppType(t21, t22), ParallelTypeReduction.ReflDerivation(t11), usualToParallel(rd))
      case UsualTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), rd) => ParallelTypeReduction.AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), usualToParallel(rd))
      case UsualTypeReduction.AppAbsDerivation(abs, arg) => ParallelTypeReduction.AppAbsDerivation(abs, arg, abs.body, arg, ParallelTypeReduction.ReflDerivation(abs.body), ParallelTypeReduction.ReflDerivation(arg))
    
  }.ensuring(res => res.isSound && res.type1 == prd.type1 && res.type2 == prd.type2)

}