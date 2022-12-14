import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

import LambdaOmega._

object TypeReductionDecidability{

  import ARSEquivalences._
  import EvalTypeReduction._
  import EvalTypeReductionConfluence._
  import EvalTypeReductionValidity._
  import EvalTypeReductionProperties._

  /**
   * Procedure that reduces a type to its normal form.
   * Outputs a sequence of steps witnessing the reduction.
   * ! Termination is not proved yet as it requires Normalization of lambda calculus
   * 
   * Basic property: the step sequence witnessing T -k-> T' is valid and T' is a normal form
   */
  @pure
  def reduceToNormalForm(t: Type): MultiStepEvalReduction = {
    reduceIffFullBetaReduce(t)
    fullBetaReduce(t) match
      case None() => ARS.ARSIdentity(t)
      case Some(r) => 
        fullBetaReduceSoundness(t)
        ARS.ARSComposition(r.toARSStep, reduceToNormalForm(r.type2))
  }.ensuring(res => res.isValid && res.t1 == t && isEvalNormalForm(res.t2))

  @pure
  def reduceToNormalForm(env: TypeEnvironment): List[MultiStepEvalReduction] = {
    decreases(env)

    env match
      case Nil() => Nil()
      case Cons(h, t) => Cons(reduceToNormalForm(h), reduceToNormalForm(t))

  }.ensuring(res => res.forall(_.isValid))

  @pure @inlineOnce @opaque
  def reduceToNormalFormApply(@induct env: TypeEnvironment, j: BigInt): Unit = {
    require(0 <= j)
    require(j <= env.length)
  }.ensuring(reduceToNormalForm(env)(j).isValid && reduceToNormalForm(env)(j).t1 == env(j) && isEvalNormalForm(reduceToNormalForm(env)(j).t2))

  /**
    * Decider for type equivalence - TAPL 30.3 Decidability
    * 
    * If the inputs are equivalent the algorithm outputs a proof of the type equivalence.
    * ! Termination is not proved yet as it requires Normalization of lambda calculus
    * 
    * The prodcedure is sound, that is the proof outputed by the decider witnesses T1 ≡ T2 and is valid (i.e. is accepted by the verifier)
    */
  @pure
  def isEquivalentTo(t1: Type, t2: Type): Option[ParallelTypeReduction.ParallelEquivalence] = {
    val msr1 = reduceToNormalForm(t1)
    val msr2 = reduceToNormalForm(t2)
    if msr1.t2 == msr2.t2 then
      reduceSameFormEquivalentWellFormed(msr1, msr2)
      Some(evalToParallel(ARSProperties.reduceSameFormEquivalent(msr1, msr2)))
    else None()
  }.ensuring(res => res.isDefined ==>
    (res.get.isValid &&
     res.get.t1 == t1 &&
     res.get.t2 == t2))

  /**
    * The equivalence procedure is complete
    * That is if two types are equivalent then the decision procedure will output a proof that witness it
    */
  @pure @opaque @inlineOnce
  def isEquivalentToCompleteness(eq: EvalEquivalence): Unit = {
    require(eq.isValid)
    val msr1: MultiStepEvalReduction = reduceToNormalForm(eq.t1)
    val msr2: MultiStepEvalReduction = reduceToNormalForm(eq.t2)
    reductionPreserveEquivalenceWellFormed(msr1, msr2, eq)
    val eqf = ARSProperties.reductionPreserveEquivalence(msr1, msr2, eq)
    equivalentNormalFormEqual(eqf)
  }.ensuring(isEquivalentTo(eq.t1, eq.t2).isDefined)

}

object KindingDecidability {

  import Kinding._

  @pure
  def decideKind(env: KindEnvironment, t: Type): Option[KindDerivation] = {
    decreases(t)
    t match 
      case bt@BasicType(_) => Some(BasicKindingDerivation(env, bt))
      case v@VariableType(j) => if (j < env.size) Some(VariableKindingDerivation(env, env(j), v)) else None()
      case arr@ArrowType(t1, t2) => 
        (decideKind(env, t1), decideKind(env, t2)) match 
          case (Some(kd1), Some(kd2)) => 
            if(kd1.k == ProperKind && kd2.k == ProperKind)
              Some(ArrowKindingDerivation(env, ProperKind, arr, kd1, kd2))
            
            else
              None()
            
          
          case (_, _) => None()
        
      
      case abs@AbsType(argK, body) => 
        decideKind(argK :: env, body) match 
          case None() => None()
          case Some(kb) => Some(AbsKindingDerivation(env, ArrowKind(argK, kb.k), abs, kb))
        
      
      case app@AppType(t1, t2) => 
        (decideKind(env, t1), decideKind(env, t2)) match 
          case (Some(kd1), Some(kd2)) => 
            kd1.k match
              case ArrowKind(argK, bodyK) if (argK == kd2.k) => 
                Some(AppKindingDerivation(env, bodyK, app, kd1, kd2))
              case _ => None()
            
          
          case (_, _) => None()
  }.ensuring(res => res.isDefined ==>
    (res.get.isSound && 
     res.get.typ == t && 
     res.get.env == env))
        
  @pure
  def decideKind(t: Type): Option[KindDerivation] = {
    decideKind(Nil(), t)
  }.ensuring(res => (res.isDefined ==>
    (res.get.isSound && 
     res.get.typ == t && 
     res.get.env == Nil())))
  

  @inlineOnce @opaque @pure
  def decideKindCompleteness(@induct kd: KindDerivation): Unit = {
    require(kd.isSound)
  }.ensuring(decideKind(kd.env, kd.typ) == Some(kd))

  @pure
  def decideWellFormedness(env: TypeEnvironment): Option[List[KindDerivation]] = {
    decreases(env)
    env match
      case Nil() => Some(Nil())
      case Cons(h, t) => 
        (decideKind(h), decideWellFormedness(t)) match
          case (None(), _)          => None()
          case (_, None())          => None()
          case (Some(sh), Some(st)) => Some(Cons(sh, st))
  }.ensuring(res => res.isDefined ==> isWellFormed(env, res.get))

  @pure
  def decideWellFormednessCompleteness(env: TypeEnvironment, wf: List[KindDerivation]): Unit = {
    decreases(env.length + wf.length)
    require(isWellFormed(env, wf))
    (env, wf) match
      case (Cons(h1, t1), Cons(h2, t2)) => 
        decideKindCompleteness(h2)
        decideWellFormednessCompleteness(t1, t2)
      case _ => ()
  }.ensuring(res => decideWellFormedness(env) == Some(wf))

}

object TypingDecidability {
  
  import Typing._
  import TypingProperties._
  import Kinding._
  import KindingProperties._
  import KindingDecidability._
  import TypeReductionDecidability._
  import EvalTypeReduction._
  import EvalTypeReductionProperties._
  import EvalTypeReductionConfluence._
  import ARSEquivalences._
  
  @pure
  def decideType(env: TypeEnvironment, t: Term): Option[TypeDerivation] = {
    decreases(t)

    decideWellFormedness(env) match
      case Some(wf) =>
        assert(decideWellFormedness(env).isDefined) //needed
        t match
          case v@Var(j) => 
            if j < env.length then 
              val envIdxRed: MultiStepEvalReduction = reduceToNormalForm(env(j))
              val envIdxEquiv: ParallelTypeReduction.ParallelEquivalence = evalMultiStepToParallelEq(envIdxRed)
              isWellFormedApply(env, wf, j)
              Some(EquivTypingDerivation(env, envIdxEquiv.t2, v, VarTypingDerivation(env, env(j), v), envIdxEquiv, kindEvalMultiStepPreservation(wf(j), envIdxRed)))
            else 
              None()
          case abs@Abs(argT, body) => 
            val reducedArgT: MultiStepEvalReduction = reduceToNormalForm(argT)
            decideType(Cons(argT, env), body) match
              case None() => None()
              case Some(btd) => 
                assert(decideType(Cons(argT, env), body).isDefined)
                assert(btd.isSound) //needed
                isEvalNormalFormArrowMap(reducedArgT.t2, btd.t)
                val reducedArrow: MultiStepEvalReduction = arrowDerivationLMap(reducedArgT, btd.t)
                decideKind(argT) match
                  case Some(kd) if kd.k == ProperKind => 
                    assert(decideKind(argT).isDefined)
                    val td: TypeDerivation = AbsTypingDerivation(env, ArrowType(argT, btd.t), abs, kd, btd)
                    val arrKd: KindDerivation = ArrowKindingDerivation(Nil(), ProperKind, ArrowType(reducedArgT.t2, btd.t), kindEvalMultiStepPreservation(kd, reducedArgT), soundTypingHasProperKind(btd, Cons(kd, wf)))
                    assert(td.isSound) //needed
                    assert(arrKd.isSound) //needed
                    Some(EquivTypingDerivation(env, ArrowType(reducedArgT.t2, btd.t), abs, td, evalMultiStepToParallelEq(reducedArrow), arrKd))
                  case _ => None()
          case app@App(t1, t2) => 
            (decideType(env, t1), decideType(env, t2)) match
              case (None(), _)            => None()
              case (_, None())            => None()
              case (Some(td1), Some(td2)) => 
                td1.t match 
                  case ArrowType(typ1, typ2) if typ1 == td2.t => 
                    assert(decideType(env, t1).isDefined)
                    assert(decideType(env, t2).isDefined)
                    isEvalNormalFormInnerMap(ArrowType(typ1, typ2))
                    Some(AppTypingDerivation(env, typ2, app, td1, td2))
                  case _ => None()
      case None() => None()

  }.ensuring(res => (res.isDefined ==> 
    (res.get.env  == env         &&
     res.get.term == t           &&
     isEvalNormalForm(res.get.t) &&
     res.get.isSound)))
  
  @pure
  def decideType(t: Term): Option[TypeDerivation] = {
    decideType(Nil(), t)
  }.ensuring(res => (res.isDefined ==> 
    (res.get.env  == Nil()       &&
     res.get.term == t           &&
     isEvalNormalForm(res.get.t) &&
     res.get.isSound)))

  @pure @inlineOnce @opaque
  def decideTypeCompleteness(td: TypeDerivation, wf: List[KindDerivation]): ParallelTypeReduction.ParallelEquivalence = {
    decreases(td)
    require(td.isSound)
    require(Kinding.isWellFormed(td.env, wf))

    decideWellFormednessCompleteness(td.env, wf)

    td match
      case VarTypingDerivation(env, typ, Var(j)) => 
        val envIdxRed: MultiStepEvalReduction = reduceToNormalForm(env(j))
        val envIdxEquiv: ParallelTypeReduction.ParallelEquivalence = evalMultiStepToParallelEq(envIdxRed)   
        envIdxEquiv
      case AbsTypingDerivation(env, ArrowType(typ1, typ2), Abs(argT, body), kd, btd) =>
        val bodyEq = decideTypeCompleteness(btd, Cons(kd, wf))
        val argEq = evalMultiStepToParallelEq(reduceToNormalForm(argT))
        ParallelTypeReductionProperties.arrowEquivalenceMap(argEq, bodyEq)
      case AppTypingDerivation(env, typ, App(t1, t2), td1, td2) =>
        val arrowEq = decideTypeCompleteness(td1, wf)
        decideTypeCompleteness(td2, wf)
        val arrowRed = evalToParallel(equivalenceToReductionNormalForm(arrowEq))
        td1.t match
          case ArrowType(typ1, typ2) if typ1 == td2.t => 
            val (arrLRed, arrRRed) = ParallelTypeReductionProperties.arrowMultiStepReduction(typ1, typ2, arrowRed)
            assert(decideType(env, t1).isDefined)
            assert(decideType(env, t2).isDefined)
            assert(decideType(env, App(t1, t2)).isDefined)
            assert(decideType(env, App(t1, t2)).get.isSound)
            assert(decideType(env, App(t1, t2)).get.isInstanceOf[AppTypingDerivation])
            assert(decideType(env, t1).get.isSound)
            assert(decideType(env, t1).get.t.isInstanceOf[ArrowType])
            (arrowEq.t1, arrowEq.t2) match
              case (ArrowType(t11, t12), ArrowType(t21, t22)) =>
                val (arrEq1, arrEq2) = ParallelTypeReductionProperties.arrowEquivalence(t11, t12, t21, t22, arrowEq)
                assert(arrEq2.isValid)
                assert(arrEq2.t1 == typ)
                assert(arrEq2.t2 == decideType(env, App(t1, t2)).get.t)
                arrEq2
              case _ => Unreacheable
          case _ => Unreacheable

      case EquivTypingDerivation(env, typ, term, btd, equiv, kd) => 
        val bodyEq = decideTypeCompleteness(btd, wf)
        ARS.ARSTransitivity(ARS.ARSSymmetry(equiv), bodyEq)
      case _ => Unreacheable
      

  }.ensuring(res => 
    decideType(td.env, td.term).isDefined &&
    res.isValid &&
    res.t1 == td.t &&
    res.t2 == decideType(td.env, td.term).get.t)

}