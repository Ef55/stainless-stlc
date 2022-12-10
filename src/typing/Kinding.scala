import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Kinding {
  import LambdaOmega._

  sealed trait KindDerivation{

    def env: KindEnvironment = this match
      case BasicKindingDerivation(e, _) => e
      case VariableKindingDerivation(e, _, _) => e
      case AbsKindingDerivation(e, _, _, _) => e
      case AppKindingDerivation(e, _, _, _, _) => e
      case ArrowKindingDerivation(e, _, _, _, _) => e

    

    def k: Kind = this match
      case BasicKindingDerivation(_, _) => ProperKind
      case VariableKindingDerivation(_, k, _) => k
      case AbsKindingDerivation(_, k, _, _) => k
      case AppKindingDerivation(_, k, _, _, _) => k
      case ArrowKindingDerivation(_, k, _, _, _) => k
  

    def typ: Type = this match
      case BasicKindingDerivation(_, typ) => typ
      case VariableKindingDerivation(_, _, typ) => typ
      case AbsKindingDerivation(_, _, typ, _) => typ
      case AppKindingDerivation(_, _, typ, _, _) => typ
      case ArrowKindingDerivation(_, _, typ, _, _) => typ
    
    def isSound: Boolean = 
      this match
        case BasicKindingDerivation(_, _) => true
        case VariableKindingDerivation(env, k, VariableType(j)) => 
          (j < env.size) &&
          env(j) == k
        
        case ArrowKindingDerivation(_, k, ArrowType(t1, t2), bkd1, bkd2) => 
          bkd1.isSound && bkd2.isSound && // Premises are valid
          bkd1.typ == t1 && bkd2.typ == t2 && bkd1.env == env && bkd2.env == env && // and have matching attributes
          bkd1.k == ProperKind && bkd2.k == ProperKind && k == ProperKind
        
        case AbsKindingDerivation(env, ArrowKind(k1, k2), AbsType(argK, body), bkd) => 
          bkd.isSound && // Premise is valid,
          bkd.typ == body && bkd.env == argK :: env && // and has matching attributes
          argK == k1 && bkd.k == k2 // Types are correct
        
        case AbsKindingDerivation(_ ,_, _, _) => false // An abstraction should always have an arrow type...
        case AppKindingDerivation(env, k, AppType(t1, t2), bkd1, bkd2) => 
          bkd1.isSound && bkd2.isSound && // Premises are valid
          bkd1.typ == t1 && bkd2.typ == t2 && bkd1.env == env && bkd2.env == env && // and have matching attributes
          bkd1.k == ArrowKind(bkd2.k, k) // The body has expected type 
        case _ => Unreacheable   
    
    def ===(that: KindDerivation): Boolean = 
      this.k == that.k && this.env == that.env
  }
  
  case class BasicKindingDerivation(e: KindEnvironment, typ: BasicType) extends KindDerivation
  case class VariableKindingDerivation(e: KindEnvironment, k: Kind, typ: VariableType) extends KindDerivation
  case class AbsKindingDerivation(e: KindEnvironment, k: Kind, typ: AbsType, bkd: KindDerivation) extends KindDerivation
  case class AppKindingDerivation(e: KindEnvironment, k: Kind, typ: AppType, bkd1: KindDerivation, bkd2: KindDerivation) extends KindDerivation
  case class ArrowKindingDerivation(e: KindEnvironment, k: Kind, typ: ArrowType, bkd1: KindDerivation, bkd2: KindDerivation) extends KindDerivation

  def deriveKind(env: KindEnvironment, t: Type): Option[KindDerivation] = 
    t match 
      case bt@BasicType(_) => Some(BasicKindingDerivation(env, bt))
      case v@VariableType(j) => if (j < env.size) Some(VariableKindingDerivation(env, env(j), v)) else None()
      case arr@ArrowType(t1, t2) => 
        (deriveKind(env, t1), deriveKind(env, t2)) match 
          case (Some(kd1), Some(kd2)) => 
            if(kd1.k == ProperKind && kd2.k == ProperKind)
              Some(ArrowKindingDerivation(env, ProperKind, arr, kd1, kd2))
            
            else
              None()
            
          
          case (_, _) => None()
        
      
      case abs@AbsType(argK, body) => 
        deriveKind(argK :: env, body) match 
          case None() => None()
          case Some(kb) => Some(AbsKindingDerivation(env, ArrowKind(argK, kb.k), abs, kb))
        
      
      case app@AppType(t1, t2) => 
        (deriveKind(env, t1), deriveKind(env, t2)) match 
          case (Some(kd1), Some(kd2)) => 
            kd1.k match
              case ArrowKind(argK, bodyK) if (argK == kd2.k) => 
                Some(AppKindingDerivation(env, bodyK, app, kd1, kd2))
              case _ => None()
            
          
          case (_, _) => None()
        
      
    
  
  
  def deriveKind(t: Type): Option[KindDerivation] = deriveKind(Nil(), t)
  

  def isWellFormed(env: TypeEnvironment, wf: List[KindDerivation]): Boolean = {
    (env, wf) match
      case (Nil(), Nil()) => true
      case (Cons(h1, t1), Cons(h2, t2)) => h2.isSound && h1 == h2.typ && h2.env == Nil() && h2.k == ProperKind && isWellFormed(t1, t2)
      case _ => false
  }.ensuring(_ ==> (wf.length == env.length))

}
 


object KindingProperties{
  import LambdaOmega._
  import Kinding._
  import ListProperties._
  import ParallelTypeReduction._
  import ParallelTypeReductionProperties._
  import ParallelTypeReductionValidity._
  import ARS._

  /// Type derivations
  @opaque @pure
  def deriveKindCompleteness(@induct kd: KindDerivation): Unit = {
    require(kd.isSound)
  }.ensuring(deriveKind(kd.env, kd.typ) == Some(kd))

  @opaque @pure
  def deriveKindSoundness(env: KindEnvironment, t: Type): Unit = {
    require(deriveKind(env, t).isDefined)
    t match 
      case BasicType(_) => ()
      case VariableType(_) => ()
      case AbsType(argK, body) => 
        deriveKindSoundness(argK :: env, body)
      
      case ArrowType(t1, t2) => 
        deriveKindSoundness(env, t1)
        deriveKindSoundness(env, t2)
      
      case AppType(t1, t2) => 
        deriveKindSoundness(env, t1)
        deriveKindSoundness(env, t2)
      
    
  }.ensuring(
    deriveKind(env, t).get.isSound && 
    deriveKind(env, t).get.typ == t && 
    deriveKind(env, t).get.env == env
  )

  @opaque @pure
  def kindDerivationUniqueness(kd1: KindDerivation, kd2: KindDerivation): Unit = {
    require(kd1.isSound)
    require(kd2.isSound)
    require(kd1.typ == kd2.typ)
    require(kd1.env == kd2.env)

    deriveKindCompleteness(kd1)
    deriveKindCompleteness(kd2)
  }.ensuring(kd1 == kd2)


  def arrowKindingInversion(kd: KindDerivation): Unit = {
    require(kd.typ.isInstanceOf[ArrowType])
  }.ensuring(kd.isInstanceOf[ArrowKindingDerivation])

  def isWellFormedApply(env: TypeEnvironment, wf: List[KindDerivation], j: BigInt): Unit = {
    require(Kinding.isWellFormed(env, wf))
    require(j < env.length)
    require(0 <= j) 
    (env, wf) match
      case (Nil(), Nil()) => ()
      case (Cons(h1, t1), Cons(h2, t2)) => 
        if j > 0 then isWellFormedApply(t1, t2, j - 1) else ()
      case _ => Unreacheable
  }.ensuring(wf(j).isSound && wf(j).env == Nil() && wf(j).k == ProperKind && wf(j).typ == env(j))

  @opaque @inlineOnce @pure
  def kindEnvironmentWeakening(kd: KindDerivation, envExt: KindEnvironment): KindDerivation = {
    require(kd.isSound)
    kd match 
      case BasicKindingDerivation(env, bt) => BasicKindingDerivation(env ++ envExt, bt)
      case VariableKindingDerivation(env, k, vt@VariableType(j)) => 
        concatFirstIndexing(env, envExt, j)
        VariableKindingDerivation(env ++ envExt, k, vt)
      
      case AbsKindingDerivation(env, k, at@AbsType(argKind, body), bkd) => 
        val resBkd = kindEnvironmentWeakening(bkd, envExt)
        AbsKindingDerivation(env ++ envExt, k, at, resBkd)
      
      case AppKindingDerivation(env, k, at@AppType(t1, t2), bk1, bk2) => 
        val resBk1 = kindEnvironmentWeakening(bk1, envExt)
        val resBk2 = kindEnvironmentWeakening(bk2, envExt)
        AppKindingDerivation(env ++ envExt, k, at, resBk1, resBk2)
      case ArrowKindingDerivation(env, k, at@ArrowType(t1, t2), bk1, bk2) => 
        val resBk1 = kindEnvironmentWeakening(bk1, envExt)
        val resBk2 = kindEnvironmentWeakening(bk2, envExt)
        ArrowKindingDerivation(env ++ envExt, k, at, resBk1, resBk2)
      case _ => Unreacheable
    
  }.ensuring(res => 
    res.isSound && 
    ( res.env == kd.env ++ envExt ) && 
    ( res.typ == kd.typ) && 
    ( res.k == kd.k )
  )

  @opaque @inlineOnce @pure
  def variableTypeEnvironmentStrengthening(v: BigInt, k: Kind, env: KindEnvironment, envExt: KindEnvironment): KindDerivation = {
    require(0 <= v)
    require(v < env.length)
    require(VariableKindingDerivation(env ++ envExt, k, VariableType(v)).isSound)
    concatFirstIndexing(env, envExt, v)
    VariableKindingDerivation(env, k, VariableType(v))
  }.ensuring(res => 
    res.isSound && 
    ( res.env == env ) && 
    ( res.k == k ) && 
    ( res.typ == VariableType(v) )
  )

  @opaque @inlineOnce @pure
  def variableTypeEnvironmentUpdate(v: BigInt, k: Kind, env: KindEnvironment, oldEnv: KindEnvironment, newEnv: KindEnvironment): KindDerivation = {
    require(0 <= v)
    require(v < env.length)
    require(VariableKindingDerivation(env ++ oldEnv, k, VariableType(v)).isSound) 
    val v2 = variableTypeEnvironmentStrengthening(v, k, env, oldEnv) 
    kindEnvironmentWeakening(v2, newEnv)
  }.ensuring(res => 
    res.isSound && 
    ( res.env == (env ++ newEnv) ) && 
    ( res.k == k ) && 
    ( res.typ == VariableType(v) )
  )

  @opaque @inlineOnce @pure
  def insertKindInEnv(env1: KindEnvironment, insert: Kind, env2: KindEnvironment, kd: KindDerivation): KindDerivation = {
    require(kd.isSound)
    require(env1 ++ env2 == kd.env)

    val newEnv = env1 ++ (insert :: env2)

    kd match 
      case BasicKindingDerivation(_, bt) => BasicKindingDerivation(newEnv, bt)
      case VariableKindingDerivation(_, k, VariableType(j)) => 
        if (j < env1.size)
          variableTypeEnvironmentUpdate(j, k, env1, env2, insert :: env2)
        
        else
          insertionIndexing(env1, env2, insert, j)
          VariableKindingDerivation(newEnv, k, VariableType(j + 1))
         
      
      case AbsKindingDerivation(_, k, AbsType(argK, body), bkd) => 
        val resBkd = insertKindInEnv(argK :: env1, insert, env2, bkd)
        AbsKindingDerivation(newEnv, k, AbsType(argK, resBkd.typ), resBkd)
      
      case AppKindingDerivation(_, k, AppType(t1, t2), kd1, kd2) => 
        val resKd1 = insertKindInEnv(env1, insert, env2, kd1)
        val resKd2 = insertKindInEnv(env1, insert, env2, kd2)
        AppKindingDerivation(newEnv, k, AppType(resKd1.typ, resKd2.typ), resKd1, resKd2)
      
      case ArrowKindingDerivation(_, k, ArrowType(t1, t2), kd1, kd2) => 
        val resKd1 = insertKindInEnv(env1, insert, env2, kd1)
        val resKd2 = insertKindInEnv(env1, insert, env2, kd2)
        ArrowKindingDerivation(newEnv, k, ArrowType(resKd1.typ, resKd2.typ), resKd1, resKd2)
      case _ => Unreacheable
      
    
    
  }.ensuring(res =>
    res.isSound &&
    ( res.typ == TypeTransformations.shift(kd.typ, 1, env1.size) ) &&
    ( res.env == env1 ++ (insert :: env2) ) &&
    ( kd.k == res.k )
  )

  @opaque @inlineOnce @pure
  def insertKindEnvInEnv(env1: KindEnvironment, insert: KindEnvironment, env2: KindEnvironment, kd: KindDerivation): KindDerivation = {
    require(kd.isSound)
    require(env1 ++ env2 == kd.env)
    
    insert match
      case Nil() => 
        TypeTransformationsProperties.shift0Identity(kd.typ, env1.size)
        kd
      case Cons(h, t) =>
        TypeTransformationsProperties.boundRangeShiftComposition(kd.typ, t.length, 1, env1.size, env1.size)
        consConcat(h, t, env2)
        insertKindInEnv(env1, h, (t ++ env2), insertKindEnvInEnv(env1, t, env2, kd))
    

  }.ensuring(res =>
    res.isSound &&
    ( res.typ == TypeTransformations.shift(kd.typ, insert.length, env1.size) ) &&
    ( res.env == env1 ++ (insert ++ env2) ) &&
    ( kd.k == res.k )
  )

  @opaque @inlineOnce @pure
  def removeKindInEnv(env1: KindEnvironment, remove: Kind, env2: KindEnvironment, kd: KindDerivation): KindDerivation = {
    require(kd.isSound)
    require(kd.env == env1 ++ (remove :: env2))
    require(!kd.typ.hasFreeVariablesIn(env1.size, 1))

    val newEnv = env1 ++ env2

    kd match 
      case BasicKindingDerivation(_, bt) => BasicKindingDerivation(newEnv, bt)
      case v@VariableKindingDerivation(_, k, VariableType(j)) => 
        if (j < env1.size)
          val res = variableTypeEnvironmentUpdate(j, k, env1, remove :: env2, env2)
          res
        
        else
          insertionIndexing(env1, env2, remove, j - 1)
          val res = VariableKindingDerivation(newEnv, k, VariableType(j - 1))
          res
         
      
      case AbsKindingDerivation(_, k, AbsType(argKind, body), bkd) => 
        val resBkd = removeKindInEnv(argKind :: env1, remove, env2, bkd)
        val res = AbsKindingDerivation(newEnv, k, AbsType(argKind, resBkd.typ), resBkd)
        res
      
      case AppKindingDerivation(_, k, AppType(t1, t2), kd1, kd2) => 
        val resKd1 = removeKindInEnv(env1, remove, env2, kd1)
        val resKd2 = removeKindInEnv(env1, remove, env2, kd2)
        val res = AppKindingDerivation(newEnv, k, AppType(resKd1.typ, resKd2.typ), resKd1, resKd2)
        res
      case ArrowKindingDerivation(_, k, ArrowType(t1, t2), kd1, kd2) => 
        val resKd1 = removeKindInEnv(env1, remove, env2, kd1)
        val resKd2 = removeKindInEnv(env1, remove, env2, kd2)
        val res = ArrowKindingDerivation(newEnv, k, ArrowType(resKd1.typ, resKd2.typ), resKd1, resKd2)
        res
      case _ => Unreacheable

  }.ensuring(res =>
    res.isSound &&
    ( res.typ == TypeTransformations.shift(kd.typ, -1, env1.size) ) &&
    ( res.env == env1 ++ env2 ) &&
    ( kd.k == res.k)
  )


  @opaque @inlineOnce @pure
  def kindPreservationUnderSubst(td: KindDerivation, j: BigInt, sd: KindDerivation): KindDerivation = { 
    require(td.isSound)
    require(sd.isSound)
    require(td.env == sd.env)
    require(0 <= j && j < td.env.size)
    require(td.env(j) == sd.k)

    val result: Type = TypeTransformations.substitute(td.typ, j, sd.typ)

    td match 
      case BasicKindingDerivation(_, _) => td
      case VariableKindingDerivation(_, _, VariableType(k)) => if j == k then sd else td
      case AbsKindingDerivation(env, typ, AbsType(argKind, body), bkd) => 
        val d0 = insertKindInEnv(Nil(), argKind, td.env, sd)
        val d1 = kindPreservationUnderSubst(bkd, j+1, d0) // Fragile: require 3/5
        AbsKindingDerivation(env, typ, AbsType(argKind, d1.typ), d1)   
      case AppKindingDerivation(env, typ, AppType(t1, t2), kd1, kd2) => 
        val td1p = kindPreservationUnderSubst(kd1, j, sd)
        val td2p = kindPreservationUnderSubst(kd2, j, sd)
        AppKindingDerivation(env, typ, AppType(td1p.typ, td2p.typ), td1p, td2p)
      case ArrowKindingDerivation(env, typ, ArrowType(t1, t2), kd1, kd2) => 
        val td1p = kindPreservationUnderSubst(kd1, j, sd)
        val td2p = kindPreservationUnderSubst(kd2, j, sd)
        ArrowKindingDerivation(env, typ, ArrowType(td1p.typ, td2p.typ), td1p, td2p)
      case _ => Unreacheable
  }.ensuring(res =>
    res.isSound &&
    ( res.typ == TypeTransformations.substitute(td.typ, j, sd.typ) ) &&
    ( td === res )
  )

  @opaque @inlineOnce @pure
  def kindPreservationUnderAbsSubst(bkd: KindDerivation, argKd: KindDerivation): KindDerivation = {
    require(bkd.isSound)
    require(argKd.isSound)
    require(bkd.env == argKd.k :: argKd.env)
          
    val sd1 = insertKindInEnv(Nil(), argKd.k, argKd.env, argKd)
    val sd2 = kindPreservationUnderSubst(bkd, 0, sd1)

    TypeTransformationsProperties.boundRangeShift(argKd.typ, 1, 0, 0, 0)
    TypeTransformationsProperties.boundRangeSubstitutionLemma(bkd.typ, 0, sd1.typ)

    removeKindInEnv(Nil(), argKd.k, argKd.env, sd2)
  }.ensuring(res => 
    res.isSound &&
    ( res.typ == TypeTransformations.absSubstitution(bkd.typ, argKd.typ)) &&
    ( res.env == argKd.env ) &&
    ( res.k == bkd.k)
  )

  @opaque @inlineOnce @pure
  def kindPreservation(kd: KindDerivation, red: ParallelReductionDerivation): KindDerivation = {
    require(kd.isSound)
    require(red.isSound)
    require(red.type1 == kd.typ)

    (kd, red) match
      case (_, ReflDerivation(_)) => kd
      case (AbsKindingDerivation(env, k, AbsType(argKind, body), bkd), AbsTypeDerivation(t1, t2, rd)) => 
        val bodyPreservation = kindPreservation(bkd, rd)
        AbsKindingDerivation(env, k, t2, bodyPreservation)
      case (ArrowKindingDerivation(env, k, ArrowType(t11, t12), kd1, kd2), ArrowTypeDerivation(_, ArrowType(t21, t22), brd1, brd2)) =>
        val bodyPreservation1 = kindPreservation(kd1, brd1)
        val bodyPreservation2 = kindPreservation(kd2, brd2)
        ArrowKindingDerivation(env, k, ArrowType(t21, t22), bodyPreservation1, bodyPreservation2)        
      case (AppKindingDerivation(env, k, AppType(typ1, typ2), kd1, kd2), AppTypeDerivation(t1, AppType(t21, t22), brd1, brd2)) => 
        val bodyPreservation1 = kindPreservation(kd1, brd1)
        val bodyPreservation2 = kindPreservation(kd2, brd2)
        AppKindingDerivation(env, k, AppType(t21, t22), bodyPreservation1, bodyPreservation2)
      case (AppKindingDerivation(env, k, AppType(AbsType(argK1, body11), arg11), AbsKindingDerivation(_, _, _, bkd), kd2), AppAbsTypeDerivation(AbsType(argK2, body21), arg21, body22, arg22, rdBody, rdArg)) =>
        val bodyPreservation = kindPreservation(bkd, rdBody)
        val argPreservation = kindPreservation(kd2, rdArg)
        kindPreservationUnderAbsSubst(bodyPreservation, argPreservation)
      case _ => Unreacheable
  }.ensuring(res => 
    res.isSound &&
    ( res.typ == red.type2 ) &&
    ( res.env == kd.env ) &&
    ( res.k == kd.k)
  )

  @opaque @inlineOnce @pure
  def kindMultiStepPreservation(kd: KindDerivation, red: MultiStepParallelReduction): KindDerivation = {
    require(kd.isSound)
    require(red.isValid)
    require(red.t1 == kd.typ)

    red match
      case ARSIdentity(_) => kd
      case ARSComposition(h, t) => 
        assert(h.isValid)
        val headPres = kindPreservation(kd, h.unfold)
        kindMultiStepPreservation(headPres, t)
  }.ensuring(res => 
    res.isSound &&
    ( res.typ == red.t2 ) &&
    ( res.env == kd.env ) &&
    ( res.k == kd.k)
  )
  @opaque @inlineOnce @pure
  def kindEquivalencePreservation(kd1: KindDerivation, kd2: KindDerivation, eq: ParallelEquivalenceSeq): Unit  = {
    require(kd1.isSound)
    require(kd2.isSound)
    require(kd1.env == kd2.env)
    require(eq.isValid && eq.isDeepValid)
    require(eq.t1 == kd1.typ)
    require(eq.t2 == kd2.typ)

    val (prd1, prd2) = churchRosser(eq)
    val res1 = kindMultiStepPreservation(kd1, prd1)
    val res2 = kindMultiStepPreservation(kd2, prd2)
    kindDerivationUniqueness(res1, res2)

  }.ensuring(kd1.k == kd2.k)

}