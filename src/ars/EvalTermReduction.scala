/**
  *  References: 
  *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
  *    - [TRAT] Term Rewriting and All That, Franz Baader and Tobias Nipkow, 1998, Cambridge University Press
  * 
  *  This file defines usual reduction, applied at the term level.
  * 
  * 
  */

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import TermTransformations._
import TypeTermTransformations._
import ARS._
import ARSProperties._

object EvalTermReduction{

  /**
    * Derivation tree for an usual term reduction step of the form term1 => term2.
    * The evaluation rules are alsmost the same as the one for terms in lambda calculus (TAPL Figure 5.3).
    * 
    * The tree represents a proof of the reduction.
    */
  sealed trait EvalReductionDerivation{

    @pure
    def term1: Term = 
      this match
        case AbsDerivation(t1, _, _) => t1
        case AppDerivationL(t1, _, _) => t1
        case AppDerivationR(t1, _, _) => t1
        case AppAbsDerivation(abs, arg) => App(abs, arg)
        case TAbsDerivation(t1, _, _) => t1
        case TAppDerivation(t1, _, _) => t1
        case TAppAbsDerivation(abs, arg) => TApp(abs, arg)

    @pure
    def term2: Term = 
      this match
        case AbsDerivation(_, t2, _) => t2
        case AppDerivationL(_, t2, _) => t2
        case AppDerivationR(_, t2, _) => t2
        case AppAbsDerivation(abs, arg) => absSubstitution(abs.body, arg)
        case TAbsDerivation(_, t2, _) => t2
        case TAppDerivation(_, t2, _) => t2
        case TAppAbsDerivation(abs, arg) => absSubstitutionType(abs.body, arg)

    /**
      * Measure for evaluation reduction derivation trees
      * ! This is not a formal definition, its only purpose is to ensure measure decreaseness
      */
    @pure
    def size: BigInt = {
      decreases(this)
      this match
        case AbsDerivation(_, _, rd) => rd.size + 1
        case AppDerivationL(_, _, rd) => rd.size + 1
        case AppDerivationR(_, _, rd) => rd.size + 1
        case AppAbsDerivation(abs, arg) => BigInt(1)
        case TAbsDerivation(_, _, rd) => rd.size + 1
        case TAppDerivation(_, _, rd) => rd.size + 1
        case TAppAbsDerivation(abs, arg) => BigInt(1)
    }.ensuring(_ > BigInt(0))

    /**
      * Returns whether the derivation tree is sound.
      * Therefore, isSound is a verifier for the proof system generated by the reduction rules.
      *
      * For each derivation rule checks whether:
      * - each subtree is also sound
      * - the conclusions of the subtrees are the premises of the rule.
      */
    @pure
    def isSound: Boolean = 
      decreases(this)
      this match
        case AbsDerivation(Abs(k1, b1), Abs(k2, b2), rd) => 
          rd.isSound && rd.term1 == b1 && rd.term2 == b2 && k1 == k2
        case AppDerivationL(App(t11, t12), App(t21, t22), rd) =>
          rd.isSound && rd.term1 == t11 && rd.term2 == t21 && t12 == t22
        case AppDerivationR(App(t11, t12), App(t21, t22), rd) =>
          rd.isSound && rd.term1 == t12 && rd.term2 == t22 && t11 == t21
        case TAbsDerivation(TAbs(k1, b1), TAbs(k2, b2), rd) => 
          rd.isSound && rd.term1 == b1 && rd.term2 == b2 && k1 == k2
        case TAppDerivation(TApp(b1, t1), TApp(b2, t2), rd) => 
          rd.isSound && rd.term1 == b1 && rd.term2 == b2 && t1 == t2
        case TAppAbsDerivation(_, _) => true
        case AppAbsDerivation(_, _) => true
  }

  /**
    * Evaluation reduction rules inspired from TAPL Figure 5-3
    */
  case class AbsDerivation(t1: Abs, t2: Abs, rd: EvalReductionDerivation) extends EvalReductionDerivation
  case class AppDerivationL(t1: App, t2: App, rd: EvalReductionDerivation) extends EvalReductionDerivation
  case class AppDerivationR(t1: App, t2: App, rd: EvalReductionDerivation) extends EvalReductionDerivation
  case class AppAbsDerivation(abs: Abs, arg: Term) extends EvalReductionDerivation
  case class TAbsDerivation(t1: TAbs, t2: TAbs, rd: EvalReductionDerivation) extends EvalReductionDerivation
  case class TAppDerivation(t1: TApp, t2: TApp, rd: EvalReductionDerivation) extends EvalReductionDerivation
  case class TAppAbsDerivation(abs: TAbs, arg: Type) extends EvalReductionDerivation

  // /**
  //  * Outputs the set of all the terns to to which t reduces to along with the proof of the reduction
  //  * 
  //  * ! Lists are used here instead of sets since their are easier to deal with in Stainless
  //  */
  // @pure 
  // def reduce(t: Term): List[EvalReductionDerivation] = {
  //   decreases(t)
  //   t match
  //     case Var(_) => Nil()
  //     case abs@Abs(k, b) => reduce(b).map(b2 => AbsDerivation(abs, Abs(k, b2.term2), b2))
  //     case app@App(t1, t2) =>
  //       val l1: List[EvalReductionDerivation] = reduce(t1).map(t1d => AppDerivationL(app, App(t1d.term2, t2), t1d))
  //       val l2: List[EvalReductionDerivation] = reduce(t2).map(t2d => AppDerivationR(app, App(t1, t2d.term2), t2d))
  //       val l3: List[EvalReductionDerivation] = t1 match
  //         case abs@Abs(k, b) =>
  //           Cons(AppAbsDerivation(abs, t2), Nil())
  //         case _ => Nil()
  //       (l1 ++ l2) ++ l3
  // }

  // /**
  //   * Decider procedure for reduction
  //   * If t1 -> t2 then the algorithm output a proof that witnesses the reduction
  //   */
  // @pure
  // def reducesTo(t1: Term, t2: Term): Option[EvalReductionDerivation] = {
  //   reduce(t1).filter((r: EvalReductionDerivation) => r.term2 == t2) match
  //     case Nil() => None()
  //     case Cons(h, t) => Some(h)
  // }

  // /**
  //   * List of technical lemmas needed to prove soundness of reduce
  //   */
  // @pure @opaque @inlineOnce
  // def reduceSoundnessLemmaAbs(@induct l: List[EvalReductionDerivation], k: Type, b: Term): Unit = {
  //   require(l.forall(_.isSound))
  //   require(l.forall(_.term1 == b))
  // }.ensuring(l.forall(b2 => AbsDerivation(Abs(k, b), Abs(k, b2.term2), b2).isSound) &&
  //            l.forall(b2 => AbsDerivation(Abs(k, b), Abs(k, b2.term2), b2).term1 == Abs(k, b)))

  // @pure @opaque @inlineOnce
  // def reduceSoundnessLemmaAppL(@induct l: List[EvalReductionDerivation], t1: Term, t2: Term): Unit = {
  //   require(l.forall(_.isSound))
  //   require(l.forall(_.term1 == t1))
  // }.ensuring(l.forall(t1d => AppDerivationL(App(t1, t2), App(t1d.term2, t2), t1d).isSound) &&
  //            l.forall(t1d => AppDerivationL(App(t1, t2), App(t1d.term2, t2), t1d).term1 == App(t1, t2)))

  // @pure @opaque @inlineOnce
  // def reduceSoundnessLemmaAppR(@induct l: List[EvalReductionDerivation], t1: Term, t2: Term): Unit = {
  //   require(l.forall(_.isSound))
  //   require(l.forall(_.term1 == t2))
  // }.ensuring(l.forall(t2d => AppDerivationR(App(t1, t2), App(t1, t2d.term2), t2d).isSound) &&
  //            l.forall(t2d => AppDerivationR(App(t1, t2), App(t1, t2d.term2), t2d).term1 == App(t1, t2)))

  // /**
  //   * Soudness of reduce
  //   * That is all the proofs in the set outputed by reduce are sound and they all witness T -> T' for some T'
  //   */
  // @pure @opaque @inlineOnce
  // def reduceSoundness(t: Term): Unit = {
  //   decreases(t)
  //   t match
  //     case Var(_) => ()
  //     case abs@Abs(k, b) => 
  //       reduceSoundness(b)
  //       reduceSoundnessLemmaAbs(reduce(b), k, b)
  //       ListSpecs.mapPred[EvalReductionDerivation, EvalReductionDerivation](reduce(b), (b2: EvalReductionDerivation) => AbsDerivation(abs, Abs(k, b2.term2), b2), (r: EvalReductionDerivation) => r.isSound)
  //       ListSpecs.mapPred[EvalReductionDerivation, EvalReductionDerivation](reduce(b), (b2: EvalReductionDerivation) => AbsDerivation(abs, Abs(k, b2.term2), b2), (r: EvalReductionDerivation) => r.term1 == t)

  //       assert(reduce(b).map((b2: EvalReductionDerivation) => AbsDerivation(abs, Abs(k, b2.term2), b2)).forall((r: EvalReductionDerivation) => r.isSound))

  //     case app@App(t1, t2) =>
  //       reduceSoundness(t1)
  //       reduceSoundness(t2)
  //       reduceSoundnessLemmaAppL(reduce(t1), t1, t2)
  //       reduceSoundnessLemmaAppR(reduce(t2), t1, t2)
  //       ListSpecs.mapPred[EvalReductionDerivation, EvalReductionDerivation](reduce(t1), (t1d: EvalReductionDerivation) => AppDerivationL(app, App(t1d.term2, t2), t1d), (r: EvalReductionDerivation) => r.isSound)
  //       ListSpecs.mapPred[EvalReductionDerivation, EvalReductionDerivation](reduce(t1), (t1d: EvalReductionDerivation) => AppDerivationL(app, App(t1d.term2, t2), t1d), (r: EvalReductionDerivation) => r.term1 == t)
  //       ListSpecs.mapPred[EvalReductionDerivation, EvalReductionDerivation](reduce(t2), (t2d: EvalReductionDerivation) => AppDerivationR(app, App(t1, t2d.term2), t2d), (r: EvalReductionDerivation) => r.isSound)
  //       ListSpecs.mapPred[EvalReductionDerivation, EvalReductionDerivation](reduce(t2), (t2d: EvalReductionDerivation) => AppDerivationR(app, App(t1, t2d.term2), t2d), (r: EvalReductionDerivation) => r.term1 == t)
  //       val l1: List[EvalReductionDerivation] = reduce(t1).map((t1d: EvalReductionDerivation) => AppDerivationL(app, App(t1d.term2, t2), t1d))
  //       val l2: List[EvalReductionDerivation] = reduce(t2).map((t2d: EvalReductionDerivation) => AppDerivationR(app, App(t1, t2d.term2), t2d))
  //       ListProperties.concatForall[EvalReductionDerivation](l1, l2, (r: EvalReductionDerivation) => r.isSound)
  //       ListProperties.concatForall[EvalReductionDerivation](l1, l2, (r: EvalReductionDerivation) => r.term1 == t)
  //       val l3: List[EvalReductionDerivation] = t1 match
  //         case abs@Abs(k, b) =>
  //           Cons(AppAbsDerivation(abs, t2), Nil())
  //         case _ => Nil()
  //       assert((l1 ++ l2).forall((r: EvalReductionDerivation) => r.isSound))
  //       assert((l1 ++ l2).forall((r: EvalReductionDerivation) => r.term1 == t))
  //       ListProperties.concatForall[EvalReductionDerivation](l1 ++ l2, l3, (r: EvalReductionDerivation) => r.isSound)
  //       ListProperties.concatForall[EvalReductionDerivation](l1 ++ l2, l3, (r: EvalReductionDerivation) => r.term1 == t)
  //       t1 match
  //         case abs@Abs(k, b) =>
  //           assert((Cons(AppAbsDerivation(abs, t2), Nil())).forall((r: EvalReductionDerivation) => r.isSound))
  //           assert((Cons(AppAbsDerivation(abs, t2), Nil())).forall((r: EvalReductionDerivation) => r.term1 == t))
  //         case _ => ()
        
  // }.ensuring(reduce(t).forall((r: EvalReductionDerivation) => r.isSound) && reduce(t).forall((r: EvalReductionDerivation) => r.term1 == t))

  // /**
  //  * Completeness of reduce
  //  * That is if T1 -> T2 then T2 ∈ reduce(T1)
  //  */
  // @pure @opaque @inlineOnce
  // def reduceCompleteness(r: EvalReductionDerivation): Unit = {
  //   require(r.isSound)
  //   decreases(r)
    
  //   r match
  //     case AbsDerivation(Abs(k1, b1), Abs(k2, b2), rd) => 
  //       reduceCompleteness(rd)
  //       ListProperties.mapContains(reduce(b1), (bd: EvalReductionDerivation) => AbsDerivation(Abs(k1, b1), Abs(k2, bd.term2), bd), rd)
  //       val l: List[EvalReductionDerivation] = reduce(b1).map(bd => AbsDerivation(Abs(k1, b1), Abs(k2, bd.term2), bd))

  //     case AppDerivationL(App(t11, t12), App(t21, t22), rd) =>
  //       reduceCompleteness(rd)
  //       ListProperties.mapContains(reduce(t11), (t1d: EvalReductionDerivation) => AppDerivationL(App(t11, t12), App(t1d.term2, t12), t1d), rd)
  //       val l1: List[EvalReductionDerivation] = reduce(t11).map(t1d => AppDerivationL(App(t11, t12), App(t1d.term2, t12), t1d))
  //       val l2: List[EvalReductionDerivation] = reduce(t12).map(t2d => AppDerivationR(App(t11, t12), App(t11, t2d.term2), t2d))
  //       val l3: List[EvalReductionDerivation] = 
  //         t11 match
  //           case abs@Abs(k, b) =>
  //             Cons(AppAbsDerivation(abs, t12), Nil())
  //           case _ => Nil()
  //       ListProperties.concatContains(l1, l2, r)
  //       ListProperties.concatContains(l1 ++ l2, l3, r)

  //     case AppDerivationR(App(t11, t12), App(t21, t22), rd) =>
  //       reduceCompleteness(rd)
  //       ListProperties.mapContains(reduce(t12), (t2d: EvalReductionDerivation) => AppDerivationR(App(t11, t12), App(t11, t2d.term2), t2d), rd)
  //       val l1: List[EvalReductionDerivation] = reduce(t11).map(t1d => AppDerivationL(App(t11, t12), App(t1d.term2, t12), t1d))
  //       val l2: List[EvalReductionDerivation] = reduce(t12).map(t2d => AppDerivationR(App(t11, t12), App(t11, t2d.term2), t2d))
  //       val l3: List[EvalReductionDerivation] = 
  //         t11 match
  //           case abs@Abs(k, b) =>
  //             Cons(AppAbsDerivation(abs, t12), Nil())
  //           case _ => Nil()
  //       ListProperties.concatContains(l1, l2, r)
  //       ListProperties.concatContains(l1 ++ l2, l3, r)

  //     case AppAbsDerivation(t11, t12) =>         
  //       val l1: List[EvalReductionDerivation] = reduce(t11).map(t1d => AppDerivationL(App(t11, t12), App(t1d.term2, t12), t1d))
  //       val l2: List[EvalReductionDerivation] = reduce(t12).map(t2d => AppDerivationR(App(t11, t12), App(t11, t2d.term2), t2d))
  //       val l3: List[EvalReductionDerivation] = 
  //         t11 match
  //           case abs@Abs(k, b) =>
  //             Cons(AppAbsDerivation(abs, t12), Nil())
  //           case _ => Nil()
  //       ListProperties.concatContains(l1 ++ l2, l3, r)
  // }.ensuring(reduce(r.term1).contains(r))

  // /**
  //  * Normal form - TRAT Section 2.1.1
  //  */
  // @pure
  // def isEvalNormalForm(t: Term): Boolean = {
  //   reduce(t).isEmpty
  // }

  /**
    * Call by value Reduction - TAPL 5.1 Operational Semantics
    * Reduction strategy where lambda abstractions are not reduced
    * The procedure outputs a proof witnessing the reduction
    */
  @pure
  def callByValueReduce(t: Term): Option[EvalReductionDerivation] = {
    decreases(t)
    t match
      case (at@App(t11, t12)) =>
        callByValueReduce(t11) match 
          case Some(prd1) => Some(AppDerivationL(at, App(prd1.term2, t12), prd1))
          case _ => callByValueReduce(t12) match 
            case Some(prd2) => Some(AppDerivationR(at, App(t11, prd2.term2), prd2))
            case _ => t11 match 
              case abs@Abs(_, _) => Some(AppAbsDerivation(abs, t12))
              case _ => None()
      case (tapp@TApp(body, arg)) => 
        callByValueReduce(body) match 
          case Some(bdr) => Some(TAppDerivation(tapp, TApp(bdr.term2, arg), bdr))
          case _ => body match 
            case tabs@TAbs(_, _) => Some(TAppAbsDerivation(tabs, arg))
            case _ => None()
      case _ => None()
  }.ensuring( _ match
    case Some(erd) => erd.isSound && erd.term1 == t
    case None()    => true
  )

  /**
    * Outputs if T1 -> T2 according to full beta reduction
    * If it is the case, outputs a proof of the reduction
    */
  @pure
  def callByValueReducesTo(t1: Term, t2: Term): Option[EvalReductionDerivation] = {
    callByValueReduce(t1) match
      case Some(prd) => if prd.term2 == t2 then Some(prd) else None()
      case None() => None()
  }.ensuring(_ match
    case Some(erd) => erd.isSound && erd.term1 == t1 && erd.term2 == t2
    case None()    => true)

}