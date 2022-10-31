/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  * 
  *  This file defines usual reduction, applied at the type level.
  * 
  * 
  */

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import TypeTransformations._

object UsualTypeReduction{
  /**
    * Derivation tree for a parallel type reduction step of the form type1 => type2, as defined in Figure 30-3 of TAPL
    */
  sealed trait UsualReductionDerivation{

    @pure
    def type1: Type = 
      this match
        case ArrowDerivationL(t1, _, _) => t1
        case ArrowDerivationR(t1, _, _) => t1
        case AbsDerivation(t1, _, _) => t1
        case AppDerivationL(t1, _, _) => t1
        case AppDerivationR(t1, _, _) => t1
        case AppAbsDerivation(abs, arg) => AppType(abs, arg)

    @pure
    def type2: Type = 
      this match
        case ArrowDerivationL(_, t2, _) => t2
        case ArrowDerivationR(_, t2, _) => t2
        case AbsDerivation(_, t2, _) => t2
        case AppDerivationL(_, t2, _) => t2
        case AppDerivationR(_, t2, _) => t2
        case AppAbsDerivation(abs, arg) => absSubstitution(abs.body, arg)


    /**
      * Measure for parallel reduction derivation trees
      * ! This is not a formal definition, its only purpose is to ensure measure decreaseness
      */
    @opaque @pure
    def size: BigInt = {
      this match
        case ArrowDerivationL(_, _, rd) => rd.size + 1 
        case ArrowDerivationR(_, _, rd) => rd.size + 1
        case AbsDerivation(_, _, rd) => rd.size + 1
        case AppDerivationL(_, _, rd) => rd.size + 1
        case AppDerivationR(_, _, rd) => rd.size + 1
        case AppAbsDerivation(abs, arg) => BigInt(1)
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
        case ArrowDerivationL(ArrowType(t11, t12), ArrowType(t21, t22), rd) => 
          rd.isSound && rd.type1 == t11 && rd.type2 == t21 && t12 == t22
        case ArrowDerivationR(ArrowType(t11, t12), ArrowType(t21, t22), rd) =>
          rd.isSound && rd.type1 == t12 && rd.type2 == t22 && t11 == t21
        case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), rd) => 
          rd.isSound && rd.type1 == b1 && rd.type2 == b2 && k1 == k2
        case AppDerivationL(AppType(t11, t12), AppType(t21, t22), rd) =>
          rd.isSound && rd.type1 == t11 && rd.type2 == t21 && t12 == t22
        case AppDerivationR(AppType(t11, t12), AppType(t21, t22), rd) =>
          rd.isSound && rd.type1 == t12 && rd.type2 == t22 && t11 == t21
        case AppAbsDerivation(_, _) => true
  }
  /**
    * Parallel reduction rules as listed in TAPL Figure 30-3
    */
  case class ArrowDerivationL(t1: ArrowType, t2: ArrowType, rd: UsualReductionDerivation) extends UsualReductionDerivation
  case class ArrowDerivationR(t1: ArrowType, t2: ArrowType, rd: UsualReductionDerivation) extends UsualReductionDerivation
  case class AbsDerivation(t1: AbsType, t2: AbsType, rd: UsualReductionDerivation) extends UsualReductionDerivation
  case class AppDerivationL(t1: AppType, t2: AppType, rd: UsualReductionDerivation) extends UsualReductionDerivation
  case class AppDerivationR(t1: AppType, t2: AppType, rd: UsualReductionDerivation) extends UsualReductionDerivation
  case class AppAbsDerivation(abs: AbsType, arg: Type) extends UsualReductionDerivation

  /**
    * Transitive and reflexive closure of parallel reduction relation also noted type1 =>* type2 (TAPL Chapter 30.3).
    * ! In this implementation multistep reduction is represented as a list of parallel reduction steps and
    * ! not as the closure of a relation.
    * TODO Show the equivalence between the two representations.
    */
  sealed trait MultiStepUsualReduction{

    /**
      * Number of reduction steps in the list
      */
    def size: BigInt = {
      this match 
        case NilUsualReduction(_) => BigInt(0)
        case ConsUsualReduction(_, tail) => tail.size + 1
    }.ensuring(_ >= 0)

    def type1: Type = 
      this match
        case NilUsualReduction(t) => t
        case ConsUsualReduction(head, tail) => head.type1

    def type2: Type = 
      this match
        case NilUsualReduction(t) => t
        case ConsUsualReduction(head, tail) => tail.type2

    def concat(prd2: MultiStepUsualReduction): MultiStepUsualReduction = {
      this match
        case NilUsualReduction(t) => prd2
        case ConsUsualReduction(h, t) => ConsUsualReduction(h, t.concat(prd2))
    }.ensuring(res => 
      (isSound && prd2.isSound && type2 == prd2.type1) ==> (res.isSound && res.type1 == type1 && res.type2 == prd2.type2))
    /**
      * Returns whether the reduction is sound.
      * Each step must be sound and the types of the reduction steps must coincide i.e. the list has to be of the form
      * (Tn-1 => type2, Tn-2 => Tn-1, ..., T1 => T2, type1 => T1)
      */
    def isSound: Boolean = 
      this match
        case NilUsualReduction(_) => true
        case ConsUsualReduction(head, tail) => head.isSound && tail.isSound && head.type2 == tail.type1
  }

  case class NilUsualReduction(t: Type) extends MultiStepUsualReduction
  case class ConsUsualReduction(head: UsualReductionDerivation, tail: MultiStepUsualReduction) extends MultiStepUsualReduction


}

object UsualTypeReductionProperties {

  import UsualTypeReduction._

  def arrowDerivationLMap(prd1: MultiStepUsualReduction, t2: Type): MultiStepUsualReduction = {
    require(prd1.isSound)
    prd1 match
      case NilUsualReduction(t1) => NilUsualReduction(ArrowType(t1, t2))
      case ConsUsualReduction(h, t) => ConsUsualReduction(ArrowDerivationL(ArrowType(h.type1, t2), ArrowType(h.type2, t2), h), arrowDerivationLMap(t, t2))
    
  }.ensuring(res => res.isSound && res.type1 == ArrowType(prd1.type1, t2) && res.type2 == ArrowType(prd1.type2, t2) && res.size == prd1.size)

  def arrowDerivationRMap(t1: Type, prd2: MultiStepUsualReduction): MultiStepUsualReduction = {
    require(prd2.isSound)
    prd2 match
      case NilUsualReduction(t2) => NilUsualReduction(ArrowType(t1, t2))
      case ConsUsualReduction(h, t) => ConsUsualReduction(ArrowDerivationR(ArrowType(t1, h.type1), ArrowType(t1, h.type2), h), arrowDerivationRMap(t1, t))
    
  }.ensuring(res => res.isSound && res.type1 == ArrowType(t1, prd2.type1) && res.type2 == ArrowType(t1, prd2.type2) && res.size == prd2.size)

  def appDerivationLMap(prd1: MultiStepUsualReduction, t2: Type): MultiStepUsualReduction = {
    require(prd1.isSound)
    prd1 match
      case NilUsualReduction(t1) => NilUsualReduction(AppType(t1, t2))
      case ConsUsualReduction(h, t) => ConsUsualReduction(AppDerivationL(AppType(h.type1, t2), AppType(h.type2, t2), h), appDerivationLMap(t, t2))
    
  }.ensuring(res => res.isSound && res.type1 == AppType(prd1.type1, t2) && res.type2 == AppType(prd1.type2, t2) && res.size == prd1.size)

  def appDerivationRMap(t1: Type, prd2: MultiStepUsualReduction): MultiStepUsualReduction = {
    require(prd2.isSound)
    prd2 match
      case NilUsualReduction(t2) => NilUsualReduction(AppType(t1, t2))
      case ConsUsualReduction(h, t) => ConsUsualReduction(AppDerivationR(AppType(t1, h.type1), AppType(t1, h.type2), h), appDerivationRMap(t1, t))
    
  }.ensuring(res => res.isSound && res.type1 == AppType(t1, prd2.type1) && res.type2 == AppType(t1, prd2.type2) && res.size == prd2.size)

  def absDerivationMap(k: Kind, prd: MultiStepUsualReduction): MultiStepUsualReduction = {
    require(prd.isSound)
    prd match
      case NilUsualReduction(b) => NilUsualReduction(AbsType(k, b))
      case ConsUsualReduction(h, t) => ConsUsualReduction(AbsDerivation(AbsType(k, h.type1), AbsType(k, h.type2), h), absDerivationMap(k, t))
    
  }.ensuring(res => res.isSound && res.type1 == AbsType(k, prd.type1) && res.type2 == AbsType(k, prd.type2) && res.size == prd.size)

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
  // def confluence(prd1: MultiStepUsualReduction, prd2: MultiStepUsualReduction): (MultiStepUsualReduction, MultiStepUsualReduction) = {
  //   decreases(prd1.size + prd2.size)
  //   require(prd1.isSound)
  //   require(prd2.isSound)
  //   require(prd1.type1 == prd2.type1)

  //   (prd1, prd2) match
  //     case (NilUsualReduction(t1), NilUsualReduction(t2)) => (NilUsualReduction(t1), NilUsualReduction(t1))
  //     case (NilUsualReduction(_t), ConsUsualReduction(head, tail)) => (ConsUsualReduction(head, tail), NilUsualReduction(prd2.type2))
  //     case (ConsUsualReduction(head, tail), NilUsualReduction(_)) => (NilUsualReduction(prd1.type2), ConsUsualReduction(head, tail))
  //     case (ConsUsualReduction(head1, tail1), ConsUsualReduction(head2, tail2)) =>
  //       val (red11, prd12) = confluenceStripe(prd1, head2)
  //       val (conf1, conf2) = confluence(prd12, tail2)
  //       (ConsUsualReduction(red11, conf1), conf2)
  // }.ensuring(res => 
  //   res._1.type2 == res._2.type2 &&
  //   res._1.type1 == prd1.type2 &&
  //   res._2.type1 == prd2.type2 &&
  //   res._1.isSound && res._2.isSound &&
  //   res._2.size == prd1.size && res._1.size == prd2.size
  // )
}