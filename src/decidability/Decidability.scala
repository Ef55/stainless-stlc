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

  }.ensuring(res => res.forall(_.isValid) && res.length == env.length)

  @pure @inlineOnce @opaque
  def reduceToNormalFormApply(env: TypeEnvironment, j: BigInt): Unit = {
    require(0 <= j)
    require(j < env.length)
    decreases(env)
    env match
      case Nil() => Unreachable
      case Cons(typ, tail) => if j > 0 then reduceToNormalFormApply(tail, j - 1) else ()
    
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
  }.ensuring(res => res match
    case Some(resEq) =>
      resEq.isValid &&
      resEq.t1 == t1 &&
      resEq.t2 == t2
    case None() => true)

  /**
    * The equivalence procedure is complete
    * That is if two types are equivalent then the decision procedure will output a proof that witness it
    */
  @pure @opaque @inlineOnce
  def isEquivalentToCompleteness(equiv: ParallelTypeReduction.ParallelEquivalence): Unit = {
    require(equiv.isValid)
    val eq = parallelToEval(equiv)
    val msr1: MultiStepEvalReduction = reduceToNormalForm(eq.t1)
    val msr2: MultiStepEvalReduction = reduceToNormalForm(eq.t2)
    reductionPreserveEquivalenceWellFormed(msr1, msr2, eq)
    val eqf = ARSProperties.reductionPreserveEquivalence(msr1, msr2, eq)
    equivalentNormalFormEqual(eqf)
  }.ensuring(isEquivalentTo(equiv.t1, equiv.t2).isDefined)

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
  }.ensuring(res => res match
    case Some(resTd) => 
      resTd.isSound && 
      resTd.typ == t && 
      resTd.env == env
    case None() => true)
        
  @pure
  def decideKind(t: Type): Option[KindDerivation] = {
    decideKind(Nil(), t)
  }.ensuring(res => res match
    case Some(resTd) => 
      resTd.isSound && 
      resTd.typ == t && 
      resTd.env == Nil()
    case None() => true)
  

  @inlineOnce @opaque @pure
  def decideKindCompleteness(@induct kd: KindDerivation): Unit = {
    require(kd.isSound)
  }.ensuring(decideKind(kd.env, kd.typ) == Some(kd))

  @inlineOnce @opaque @pure
  def decideWellFormedness(env: TypeEnvironment): Option[List[KindDerivation]] = {
    decreases(env)
    env match
      case Nil() => Some(Nil())
      case Cons(h, t) => 
        (decideKind(h), decideWellFormedness(t)) match
          case (Some(sh), Some(st)) if sh.k == ProperKind => 
            Some(Cons(sh, st))
          case _ =>  None()
  }.ensuring(res => res match
    case Some(wf) => 
      isWellFormed(env, wf)
    case None() => true)


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
                assert(btd.isSound) //needed
                isEvalNormalFormArrowMap(reducedArgT.t2, btd.t)
                val reducedArrow: MultiStepEvalReduction = arrowDerivationLMap(reducedArgT, btd.t)
                decideKind(argT) match
                  case Some(kd) if kd.k == ProperKind => 
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
                    isEvalNormalFormInnerMap(ArrowType(typ1, typ2))
                    Some(AppTypingDerivation(env, typ2, app, td1, td2))
                  case _ => None()
      case None() => None()

  }.ensuring(res => res match
    case Some(resTd) => 
      resTd.env  == env         &&
      isEvalNormalForm(resTd.t) &&
      resTd.term == t           &&
      resTd.isSound
    case None() => true)
  
  @pure
  def decideType(t: Term): Option[TypeDerivation] = {
    decideType(Nil(), t)
  }.ensuring(res => res match
    case Some(resTd) => 
      resTd.env  == Nil()       &&
      isEvalNormalForm(resTd.t) &&
      resTd.term == t           &&
      resTd.isSound
    case None() => true)

  @pure @inlineOnce @opaque
  def decideTypeCompleteness(td: TypeDerivation, wf: List[KindDerivation]): ParallelTypeReduction.ParallelEquivalence = {
    decreases(td)
    require(td.isSound)
    require(Kinding.isWellFormed(td.env, wf))

    decideWellFormednessCompleteness(td.env, wf)

    td match
      case VarTypingDerivation(env, typ, Var(j)) => 
        val envIdxRed: MultiStepEvalReduction = reduceToNormalForm(env(j))
        evalMultiStepToParallelEq(envIdxRed)  
      case AbsTypingDerivation(env, ArrowType(typ1, typ2), Abs(argT, body), kd, btd) =>
        val bodyEq = decideTypeCompleteness(btd, Cons(kd, wf))
        decideType(Cons(argT, env), body) match
          case Some(dT) =>
            decideKindCompleteness(kd)
            decideKind(argT) match
              case Some(dK) if dK == kd && dK.k == ProperKind =>
                val argEq = evalMultiStepToParallelEq(reduceToNormalForm(argT))
                ParallelTypeReductionProperties.arrowEquivalenceMap(argEq, bodyEq)
                // assert(decideType(td.env, td.term) match
                //   case Some(dT) =>
                //     ress.isValid &&
                //     ress.t1 == td.t &&
                //     ress.t2 == dT.t
                //   case _ => false)
                // ress
              case _ => Unreachable
          case _ => Unreachable

      case AppTypingDerivation(env, typ, App(t1, t2), td1, td2) =>

        val t1Eq = decideTypeCompleteness(td1, wf)
        val t2Eq = decideTypeCompleteness(td2, wf)

        (decideType(env, t1), decideType(env, t2)) match
          case (Some(dT1), Some(dT2)) => 
            
            val t1EvalRed = equivalenceToReductionNormalForm(t1Eq)
            val t2EvalRed = equivalenceToReductionNormalForm(t2Eq)
            val t1ParaRed = evalToParallel(t1EvalRed)
            val t2ParaRed = evalToParallel(t2EvalRed)

            td1.t match
              case ArrowType(typ1, typ2) if typ1 == td2.t => 
                val (arrLParaRed, arrRParaRed) = ParallelTypeReductionProperties.arrowMultiStepReduction(typ1, typ2, t1ParaRed)
                val arrLEvalRed = parallelToEval(arrLParaRed)
                val arrREvalRed = parallelToEval(arrRParaRed)

                dT1.t match 
                  case ArrowType(dTyp1, dTyp2)  => 
                    isEvalNormalFormInnerMap(t1ParaRed.t2)
                    uniqueNormalForm(arrLEvalRed, t2EvalRed)

                    decideType(env, App(t1, t2)) match
                      case Some(AppTypingDerivation(env0, dTyp20, App(t10, t20), dT10, dT20)) 
                      if env == env0 && dTyp2 == dTyp20 && t10 == t1 && t20 == t2 && dT10 == dT1 && dT20 == dT2=>
                        val (arrEq1, arrEq2) = ParallelTypeReductionProperties.arrowEquivalence(typ1, typ2, dTyp1, dTyp2, t1Eq)
                        arrEq2
                      case _ => Unreachable 
                  case _ => Unreachable
              case _ => Unreachable
          case _ => Unreachable

      case EquivTypingDerivation(env, typ, term, btd, equiv, kd) => 
        val bodyEq = decideTypeCompleteness(btd, wf)

        decideType(env, btd.term) match
          case Some(dT) =>
            assert(ARS.ARSSymmetry(equiv).isValid)
            assert(ARS.ARSSymmetry(equiv).t1 == typ)
            assert(ARS.ARSSymmetry(equiv).t2 == btd.t)
            ARS.ARSTransitivity(ARS.ARSSymmetry(equiv), bodyEq)  
          case _ => Unreachable    
      case _ => Unreachable

  }.ensuring(res => decideType(td.env, td.term) match
    case Some(dT) =>
      res.isValid &&
      res.t1 == td.t &&
      res.t2 == dT.t
    case _ => false)

  @pure
  def decideTypeChecking(env: TypeEnvironment, t: Term, found: Type): Option[TypeDerivation] = {
    decideKind(found) match
      case Some(kd) if kd.k == ProperKind => 
        decideType(env, t) match
          case Some(normalFormDer) =>
            isEquivalentTo(normalFormDer.t, found) match
              case Some(equiv) => 
                assert(normalFormDer.term == t)
                assert(normalFormDer.t == equiv.t1)
                assert(found == equiv.t2)
                Some(EquivTypingDerivation(env, found, t, normalFormDer, equiv, kd))
              case _ => None()
          case _ => None()
      case _ => None()

  }.ensuring(res => res match
    case Some(resTd) => 
      resTd.env  == env   &&
      resTd.t    == found &&
      resTd.term == t     &&
      resTd.isSound
    case None() => true)

  @pure
  def decideTypeChecking(t: Term, found: Type): Option[TypeDerivation] = {
    decideTypeChecking(Nil(), t, found)
  }.ensuring(res => res match
    case Some(resTd) => 
      resTd.env  == Nil()   &&
      resTd.t    == found   &&
      resTd.term == t       &&
      resTd.isSound
    case None() => true)

  @pure @inlineOnce @opaque
  def decideTypeCheckingCompleteness(td: TypeDerivation, wf: List[KindDerivation]): Unit = {
    require(td.isSound)
    require(Kinding.isWellFormed(td.env, wf))
    val kd = soundTypingHasProperKind(td, wf)
    decideKindCompleteness(kd)
    decideKind(td.t) match
      case Some(kd) if kd.k == ProperKind => 
        val equiv = decideTypeCompleteness(td, wf)
        decideType(td.env, td.term) match
          case Some(normalFormDer) =>
            isEquivalentToCompleteness(equiv) 
            isEquivalentTo(normalFormDer.t, td.t) match
              case Some(equiv) => ()
              case _ => Unreachable
          case _ => Unreachable
      case _ => Unreachable
  }.ensuring(decideTypeChecking(td.env, td.term, td.t) match
    case Some(dT) =>
      dT.term == td.term &&
      dT.t    == td.t    &&
      dT.env  == td.env
    case _ => false)

}