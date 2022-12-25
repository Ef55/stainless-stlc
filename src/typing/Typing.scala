import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._


import LambdaOmega._
import Kinding._
import ParallelTypeReduction._


object Typing {

  import ARS._
  import TypeTransformations._

  sealed trait TypeDerivation {

    @pure
    def kindEnv: KindEnvironment = this match 
      case VarTypingDerivation(e, _, _, _) => e
      case AbsTypingDerivation(e, _, _, _, _, _) => e
      case AppTypingDerivation(e, _, _, _, _, _) => e
      case EquivTypingDerivation(e, _, _, _, _, _, _) => e
      case TAbsTypingDerivation(e, _, _, _, _) => e
      case TAppTypingDerivation(e, _, _, _, _, _) => e

    @pure
    def typeEnv: TypeEnvironment = this match 
      case VarTypingDerivation(_, e, _, _) => e
      case AbsTypingDerivation(_, e, _, _, _, _) => e
      case AppTypingDerivation(_, e, _, _, _, _) => e
      case EquivTypingDerivation(_, e, _, _, _, _, _) => e
      case TAbsTypingDerivation(_, e, _, _, _) => e
      case TAppTypingDerivation(_, e, _, _, _, _) => e

    @pure
    def t: Type = this match 
      case VarTypingDerivation(_, _, t, _) => t
      case AbsTypingDerivation(_, _, t, _, _, _) => t
      case AppTypingDerivation(_, _, t, _, _, _) => t
      case EquivTypingDerivation(_, _, t, _, _, _, _) => t
      case TAbsTypingDerivation(_, _, t, _, _) => t
      case TAppTypingDerivation(_, _, t, _, _, _) => t

    @pure
    def term: Term = this match
      case VarTypingDerivation(_, _, _, term) => term
      case AbsTypingDerivation(_, _, _, term, _, _) => term
      case AppTypingDerivation(_, _, _, term, _, _) => term
      case EquivTypingDerivation(_, _, _, term, _, _, _) => term
      case TAbsTypingDerivation(_, _, _, term, _) => term
      case TAppTypingDerivation(_, _, _, term, _, _) => term

    @pure
    def isSound: Boolean = 
      decreases(this)
      this match
        case VarTypingDerivation(kEnv, tEnv, t, Var(k)) => 
          (k < tEnv.size) && // Variable in environment
          tEnv(k) == t       // and has the correct type
        case AbsTypingDerivation(kEnv, tEnv, ArrowType(typ1, typ2), Abs(typ, body), kd, btd) => 
          btd.isSound && // Premise is valid,
          btd.term == body && btd.typeEnv == typ :: tEnv && btd.kindEnv == kEnv &&// and has matching attributes
          typ == typ1 && btd.t == typ2 && // Types are correct
          kd.isSound && kd.typ == typ1 && kd.k == ProperKind && kd.env == kEnv
        case AbsTypingDerivation(_, _, _, _, _, _) => false // An abstraction should always have an arrow type...
        case AppTypingDerivation(kEnv, tEnv, t, App(t1, t2), btd1, btd2) => 
          btd1.isSound && btd2.isSound && // Premises are valid
          btd1.term == t1 && btd2.term == t2 && btd1.typeEnv == tEnv && btd2.typeEnv == tEnv && // and have matching attributes
          btd1.kindEnv == kEnv && btd2.kindEnv == kEnv &&
          btd1.t == ArrowType(btd2.t, t) // The body has expected type
        case EquivTypingDerivation(kEnv, tEnv, typ, ter, td, eq, kd) => 
          td.isSound && eq.isValid && kd.isSound && // Premise is valid
          td.typeEnv == tEnv && td.kindEnv == kEnv && td.term == ter && // and has matching attributes
          eq.t1 == td.t && eq.t2 == typ &&
          kd.env == kEnv && kd.typ == typ && kd.k == ProperKind
        case TAbsTypingDerivation(kEnv, tEnv, UniversalType(k1, bTyp), TAbs(k2, body), btd) => 
          btd.isSound &&
          btd.term == body && btd.typeEnv == shift(tEnv, 1, 0) && btd.kindEnv == k2 :: kEnv &&
          k1 == k2 && btd.t == bTyp
        case TAbsTypingDerivation(_, _, _, _, _) => false
        case TAppTypingDerivation(kEnv, tEnv, t, TApp(body, arg), btd, kd) => 
          btd.isSound && kd.isSound &&
          kd.env == kEnv && kd.typ == arg &&
          btd.typeEnv == tEnv && btd.kindEnv == kEnv && btd.term == body &&
          (btd.t match
            case UniversalType(k, b) => kd.k == k && t == absSubstitution(b, arg)
            case _ => false)
        case _ => Unreachable

  }
  case class VarTypingDerivation(kEnv: KindEnvironment, tEnv: TypeEnvironment, typ: Type, ter: Var) extends TypeDerivation
  case class AbsTypingDerivation(kEnv: KindEnvironment, tEnv: TypeEnvironment, typ: Type, ter: Abs, kd: KindDerivation, btd: TypeDerivation) extends TypeDerivation
  case class AppTypingDerivation(kEnv: KindEnvironment, tEnv: TypeEnvironment, typ: Type, ter: App, btd1: TypeDerivation, btd2: TypeDerivation) extends TypeDerivation
  case class EquivTypingDerivation(kEnv: KindEnvironment, tEnv: TypeEnvironment, typ: Type, ter: Term, td: TypeDerivation, equiv: ParallelEquivalence, kd: KindDerivation) extends TypeDerivation
  case class TAbsTypingDerivation(kEnv: KindEnvironment, tEnv: TypeEnvironment, typ: Type, ter: TAbs, btd: TypeDerivation) extends TypeDerivation
  case class TAppTypingDerivation(kEnv: KindEnvironment, tEnv: TypeEnvironment, typ: Type, ter: TApp, btd: TypeDerivation, kd: KindDerivation) extends TypeDerivation

}


object TypingProperties {
  import Typing._
  import TypeTransformations.*
  import TypeTermTransformations.*
  import EvalTermReduction._  
  import ListProperties._
  import Kinding._
  import KindingProperties._
  import ARS._

  @pure @opaque @inlineOnce
  def soundTypingHasProperKind(td: TypeDerivation, wf: List[KindDerivation]): KindDerivation = {
    decreases(td)
    require(td.isSound)
    require(Kinding.isWellFormed(td.kindEnv, td.typeEnv, wf))
    
    td match
      case VarTypingDerivation(kEnv, tEnv, _, Var(j)) => 
        isWellFormedApply(kEnv, tEnv, wf, j)
        wf(j)
      case AbsTypingDerivation(kEnv, _, ArrowType(t1, t2), Abs(argK, _), kd, btd) => ArrowKindingDerivation(kEnv, ProperKind, ArrowType(t1, t2), kd, soundTypingHasProperKind(btd, Cons(kd, wf)))
      case AppTypingDerivation(_, _, _, _, td1, td2) => 
        val kd1 = soundTypingHasProperKind(td1, wf)
        assert(kd1.typ.isInstanceOf[ArrowType])
        arrowKindingInversion(kd1)
        kd1 match
          case ArrowKindingDerivation(_, _, _, _, kd12) => kd12
          case _ => Unreachable
      case EquivTypingDerivation(_, _, _, _, _, _, kd) => kd
      case TAbsTypingDerivation(kEnv, tEnv, _, TAbs(k, _), btd) => 
        UniversalKindingDerivation(kEnv, ProperKind, UniversalType(k, btd.t), soundTypingHasProperKind(btd, insertWellFormed(kEnv, tEnv, wf, k)))
      case TAppTypingDerivation(kEnv, _, _ , _, btd, kd) =>
        val kdBody = soundTypingHasProperKind(btd, wf)
        universalKindingInversion(kdBody)
        kdBody match
          case UniversalKindingDerivation(_, _, _, bkd) => kindPreservationUnderAbsSubst(bkd, kd)
          case _ => Unreachable
      case _ => Unreachable

  }.ensuring(res => 
    res.isSound &&
    res.env == td.kindEnv &&
    res.typ == td.t &&    
    res.k == ProperKind)

//   @inlineOnce @opaque @pure
//   def arrowTypingInversion(td: TypeDerivation): Unit = {
//     require(td.typeEnv.isEmpty)
//     require(td.kindEnv.isEmpty)
//     require(td.isSound)
//     require(td.t.isInstanceOf[ArrowType])
//     td match
//       case VarTypingDerivation(_, _, _, _) => Unreachable
//       case AbsTypingDerivation(_, _, _, _, _, _) => ()
//       case AppTypingDerivation(_, _, _, _, _, _, _) => 
//       case EquivTypingDerivation(_, _, _, _, btd, equiv, kd) => 

//   }.ensuring(td.term.isInstanceOf[Abs] || td.term.isInstanceOf[TApp])

// //   /// Progress
//   @pure @inlineOnce @opaque
//   def callByValueProgress(td: TypeDerivation): Unit = {
//     decreases(td)
//     require(td.isSound)
//     require(td.typeEnv.isEmpty)
//     require(td.kindEnv.isEmpty)
//     td match
//       case VarTypingDerivation(_, _, _, _) => ()
//       case AbsTypingDerivation(_, _, _, _, _, _) => ()
//       case AppTypingDerivation(_, _, _, _, btd1, btd2) => 
//         callByValueProgress(btd1)
//         callByValueProgress(btd2)
//       case EquivTypingDerivation(_, _, _, _, btd, _, _) => 
//         callByValueProgress(btd)
//       case TAbsTypingDerivation(_, _, _, _, _) => ()
//       case TAppTypingDerivation(_, _, _, _, btd, _) => 
//         callByValueProgress(btd)
    
//   }.ensuring(callByValueReduce(td.term).isDefined || td.term.isValue)


  /// Preservation

  @pure @opaque @inlineOnce
  def environmentWeakening(td: TypeDerivation, kEnvExt: KindEnvironment, tEnvExt: TypeEnvironment): TypeDerivation = {
    decreases(td)
    require(td.isSound)
    td match 
      case VarTypingDerivation(kEnv, tEnv,  typ, Var(k)) => 
        concatFirstIndexing(tEnv, tEnvExt, k)
        VarTypingDerivation(kEnv ++ kEnvExt, tEnv ++ tEnvExt, typ, Var(k))

      case AbsTypingDerivation(kEnv, tEnv, typ, Abs(argType, body), kd, btd) => 
        val resBtd = environmentWeakening(btd, kEnvExt, tEnvExt)
        val resKd  = kindEnvironmentWeakening(kd, kEnvExt)
        AbsTypingDerivation(kEnv ++ kEnvExt, tEnv ++ tEnvExt, typ, Abs(argType, body), resKd, resBtd)
      
      case AppTypingDerivation(kEnv, tEnv, typ, App(t1, t2), bt1, bt2) => 
        val resBt1 = environmentWeakening(bt1, kEnvExt, tEnvExt)
        val resBt2 = environmentWeakening(bt2, kEnvExt, tEnvExt)
        AppTypingDerivation(kEnv ++ kEnvExt, tEnv ++ tEnvExt, typ, App(t1, t2), resBt1, resBt2)

      case EquivTypingDerivation(kEnv, tEnv, typ, ter, btd, eq, kd) => 
        val resTd = environmentWeakening(btd, kEnvExt, tEnvExt)
        val resKd = kindEnvironmentWeakening(kd, kEnvExt)
        EquivTypingDerivation(kEnv ++ kEnvExt, tEnv ++ tEnvExt, typ, ter, resTd, eq, resKd)

      case TAbsTypingDerivation(kEnv, tEnv, typ, ter, btd) => 
        val resTd = environmentWeakening(btd, kEnvExt, tEnvExt)
        TAbsTypingDerivation(kEnv ++ kEnvExt, tEnv ++ tEnvExt, typ, ter, resTd)

      case TAppTypingDerivation(kEnv, tEnv, typ, ter, btd, kd) =>
        val resTd = environmentWeakening(btd, kEnvExt, tEnvExt)
        val resKd = kindEnvironmentWeakening(kd, kEnvExt)
        TAppTypingDerivation(kEnv ++ kEnvExt, tEnv ++ tEnvExt, typ, ter, resTd, resKd)

      case _ => Unreachable

  }.ensuring(res => 
    res.isSound &&
    res.kindEnv == td.kindEnv ++ kEnvExt &&
    res.typeEnv == td.typeEnv ++ tEnvExt && 
    res.term == td.term && 
    res.t == td.t
  )

  @pure @opaque @inlineOnce
  def variableEnvironmentStrengthening(k: BigInt, typ: Type, kEnv: KindEnvironment, tEnv: TypeEnvironment, kEnvExt: KindEnvironment, tEnvExt: TypeEnvironment): TypeDerivation = {
    require(0 <= k)
    require(k < tEnv.length)
    require(VarTypingDerivation(kEnv ++ kEnvExt, tEnv ++ tEnvExt, typ, Var(k)).isSound)
    concatFirstIndexing(tEnv, tEnvExt, k)
    VarTypingDerivation(kEnv, tEnv, typ, Var(k))
  }.ensuring(res => 
    res.isSound && 
    ( res.kEnv == kEnv ) &&
    ( res.tEnv == tEnv ) &&
    ( res.t == typ ) && 
    ( res.term == Var(k) )
  )

  @pure @inlineOnce @opaque
  def variableEnvironmentUpdate(k: BigInt, typ: Type, kEnv: KindEnvironment, tEnv: TypeEnvironment, kOldEnv: KindEnvironment, kNewEnv: KindEnvironment, tOldEnv: TypeEnvironment, tNewEnv: TypeEnvironment): TypeDerivation = {
    require(0 <= k)
    require(k < tEnv.length)
    require(VarTypingDerivation(kEnv ++ kOldEnv, tEnv ++ tOldEnv, typ, Var(k)).isSound) 
    val v2 = variableEnvironmentStrengthening(k, typ, kEnv, tEnv, kOldEnv, tOldEnv) 
    environmentWeakening(v2, kNewEnv, tNewEnv)
  }.ensuring(res => 
    res.isSound && 
    ( res.kindEnv == (kEnv ++ kNewEnv) ) && 
    ( res.typeEnv == (tEnv ++ tNewEnv) ) &&
    ( res.t == typ ) && 
    ( res.term == Var(k) )
  )

  @opaque @pure @inlineOnce
  def insertInTypeEnv(env1: TypeEnvironment, insert: Type, env2: TypeEnvironment, td: TypeDerivation): TypeDerivation = {
    decreases(td)
    require(td.isSound)
    require(env1 ++ env2 == td.typeEnv)

    val newEnv = env1 ++ (insert :: env2)

    td match 
      case VarTypingDerivation(kEnv, _, typ, Var(k)) => 
        if (k < env1.size) then
          variableEnvironmentUpdate(k, typ, kEnv, env1, Nil(), Nil(), env2, insert :: env2)
        else
          insertionIndexing(env1, env2, insert, k)
          VarTypingDerivation(kEnv, newEnv, typ, Var(k + 1))

      case AbsTypingDerivation(kEnv, _, typ, Abs(argType, body), kd, btd) =>
        val resBtd = insertInTypeEnv(argType :: env1, insert, env2, btd)
        AbsTypingDerivation(kEnv, newEnv, typ, Abs(argType, resBtd.term), kd, resBtd)

      case AppTypingDerivation(kEnv, _, typ, App(t1, t2), td1, td2) =>
        val resTd1 = insertInTypeEnv(env1, insert, env2, td1)
        val resTd2 = insertInTypeEnv(env1, insert, env2, td2)
        AppTypingDerivation(kEnv, newEnv, typ, App(resTd1.term, resTd2.term), resTd1, resTd2)

      case EquivTypingDerivation(kEnv, _, typ, ter, btd, equiv, kd) => 
        val resEtd = insertInTypeEnv(env1, insert, env2, btd)
        EquivTypingDerivation(kEnv, newEnv, typ, resEtd.term, resEtd, equiv, kd)

      case TAbsTypingDerivation(kEnv, _, typ, TAbs(k, body), btd) =>
        EnvTransformationsProperties.shiftConcat(env1, env2, 1, 0)
        EnvTransformationsProperties.shiftConcat(env1, insert :: env2, 1, 0)
        val resBtd = insertInTypeEnv(shift(env1, 1, 0), shift(insert, 1, 0), shift(env2, 1, 0), btd)
        TAbsTypingDerivation(kEnv, newEnv, typ, TAbs(k, resBtd.term), resBtd)

      case TAppTypingDerivation(kEnv, _, typ, TApp(body, arg), btd, kd) =>
        val resBtd = insertInTypeEnv(env1, insert, env2, btd)
        TAppTypingDerivation(kEnv, newEnv, typ, TApp(resBtd.term, arg), resBtd, kd)

      case _ => Unreachable
    
  }.ensuring(res =>
    res.isSound &&
    ( res.term == TermTransformations.shift(td.term, 1, env1.size)) &&
    ( res.kindEnv == td.kindEnv) &&
    ( res.typeEnv == env1 ++ (insert :: env2) ) &&
    ( td.t == res.t )
  )

  @opaque @pure @inlineOnce
  def removeInTypeEnv(env1: TypeEnvironment, remove: Type, env2: TypeEnvironment, td: TypeDerivation): TypeDerivation = {
    decreases(td)
    require(td.isSound)
    require(td.typeEnv == env1 ++ (remove :: env2))
    require(!td.term.hasFreeVariablesIn(env1.size, 1))

    val newEnv = env1 ++ env2

    td match 
      case VarTypingDerivation(kEnv, _, typ, Var(k)) => 
        if (k < env1.size) then
          variableEnvironmentUpdate(k, typ, kEnv, env1, Nil(), Nil(), remove :: env2, env2)
        else
          insertionIndexing(env1, env2, remove, k - 1)
          VarTypingDerivation(kEnv, newEnv, typ, Var(k - 1))

      case AbsTypingDerivation(kEnv, _, typ, Abs(argType, body), kd, btd) => 
        val resBtd = removeInTypeEnv(argType :: env1, remove, env2, btd)
        AbsTypingDerivation(kEnv, newEnv, typ, Abs(argType, resBtd.term), kd, resBtd)

      case AppTypingDerivation(kEnv, _, typ, App(t1, t2), td1, td2) => 
        val resTd1 = removeInTypeEnv(env1, remove, env2, td1)
        val resTd2 = removeInTypeEnv(env1, remove, env2, td2)
        AppTypingDerivation(kEnv, newEnv, typ, App(resTd1.term, resTd2.term), resTd1, resTd2)

      case EquivTypingDerivation(kEnv, _, typ, ter, btd, equiv, kd) => 
        val resEtd: TypeDerivation = removeInTypeEnv(env1, remove, env2, btd)
        EquivTypingDerivation(kEnv, newEnv, typ, resEtd.term, resEtd, equiv, kd)
  
      case TAbsTypingDerivation(kEnv, _, typ, TAbs(k, body), btd) =>
        EnvTransformationsProperties.shiftConcat(env1, env2, 1, 0)
        EnvTransformationsProperties.shiftConcat(env1, remove :: env2, 1, 0)
        val resBtd = removeInTypeEnv(shift(env1, 1, 0), shift(remove, 1, 0), shift(env2, 1, 0), btd)
        TAbsTypingDerivation(kEnv, newEnv, typ, TAbs(k, resBtd.term), resBtd)

      case TAppTypingDerivation(kEnv, _, typ, TApp(body, arg), btd, kd) =>
        val resBtd = removeInTypeEnv(env1, remove, env2, btd)
        TAppTypingDerivation(kEnv, newEnv, typ, TApp(resBtd.term, arg), resBtd, kd)

      case _ => Unreachable
      
  }.ensuring(res =>
    res.isSound &&
    ( res.term == TermTransformations.shift(td.term, -1, env1.size) ) &&
    ( res.typeEnv == env1 ++ env2 ) &&
    ( res.kindEnv == td.kindEnv ) &&
    ( td.t == res.t)
  )

  @opaque @pure @inlineOnce
  def insertInKindEnv(env1: KindEnvironment, insert: Kind, env2: KindEnvironment, td: TypeDerivation): TypeDerivation = {
    decreases(td)
    require(td.isSound)
    require(env1 ++ env2 == td.kindEnv)

    val newEnv = env1 ++ (insert :: env2)
    val newTEnv = TypeTransformations.shift(td.typeEnv, 1, env1.length)
    val newType = TypeTransformations.shift(td.t, 1, env1.length)

    td match 
      case VarTypingDerivation(_, tEnv, typ, Var(k)) => 
        EnvTransformationsProperties.shiftApply(tEnv, 1, env1.length, k)
        VarTypingDerivation(newEnv, newTEnv, newType, Var(k))

      case AbsTypingDerivation(_, tEnv, typ, Abs(argType, body), kd, btd) =>
        val resBtd = insertInKindEnv(env1, insert, env2, btd)
        val resKd = insertKindInEnv(env1, insert, env2, kd)
        AbsTypingDerivation(newEnv, newTEnv, newType, Abs(TypeTransformations.shift(argType, 1, env1.length), resBtd.term), resKd, resBtd)

      case AppTypingDerivation(_, tEnv, typ, App(t1, t2), td1, td2) =>
        val resTd1 = insertInKindEnv(env1, insert, env2, td1)
        val resTd2 = insertInKindEnv(env1, insert, env2, td2)
        AppTypingDerivation(newEnv, newTEnv, newType, App(resTd1.term, resTd2.term), resTd1, resTd2)

      case EquivTypingDerivation(_, tEnv, typ, ter, btd, equiv, kd) => 
        val resEtd   = insertInKindEnv(env1, insert, env2, btd)
        val resKd    = insertKindInEnv(env1, insert, env2, kd)
        val resEquiv = ParallelTypeReductionProperties.equivalenceShift(equiv, 1, env1.length)
        EquivTypingDerivation(newEnv, newTEnv, newType, resEtd.term, resEtd, resEquiv, resKd)

      case TAbsTypingDerivation(_, tEnv, typ, TAbs(k, body), btd) =>
        val resBtd = insertInKindEnv(k :: env1, insert, env2, btd)
        EnvTransformationsProperties.shiftCommutativityPosPos(tEnv, 1, env1.length, 1, 0)
        TAbsTypingDerivation(newEnv, newTEnv, newType, TAbs(k, resBtd.term), resBtd)

      case TAppTypingDerivation(_, tEnv, typ, TApp(body, arg), btd, kd) =>
        val resBtd = insertInKindEnv(env1, insert, env2, btd)
        val resKd  = insertKindInEnv(env1, insert, env2, kd)
        btd.t match
          case UniversalType(k, b) => 
            TypeTransformationsProperties.shiftAbsSubstitutionCommutativity(b, arg, 1, env1.size)
            TAppTypingDerivation(newEnv, newTEnv, newType, TApp(resBtd.term, TypeTransformations.shift(arg, 1, env1.length)), resBtd, resKd)
          case _ => Unreachable        
      case _ => Unreachable
    
  }.ensuring(res =>
    res.isSound &&
    ( res.term    == TypeTermTransformations.shiftType(td.term, 1, env1.length)) &&
    ( res.kindEnv == env1 ++ (insert :: env2) ) &&
    ( res.typeEnv == TypeTransformations.shift(td.typeEnv, 1, env1.length)) &&
    ( res.t       == TypeTransformations.shift(td.t, 1, env1.length))
  )

  @opaque @pure @inlineOnce
  def removeInKindEnv(env1: KindEnvironment, remove: Kind, env2: KindEnvironment, td: TypeDerivation): TypeDerivation = {
    decreases(td)
    require(td.isSound)
    require(env1 ++ (remove :: env2) == td.kindEnv)
    require(td.typeEnv.hasFreeVariablesIn(env1.length, 1))
    require(td.t.hasFreeVariablesIn(env1.length, 1))
    require(td.term.hasFreeTypeVariablesIn(env1.length, 1))

    val newEnv = env1 ++ env2
    val newTEnv = TypeTransformations.shift(td.typeEnv, -1, env1.length)
    val newType = TypeTransformations.shift(td.t, -1, env1.length)

    td match 
      case VarTypingDerivation(_, tEnv, typ, Var(k)) => 
        EnvTransformationsProperties.shiftApply(tEnv, -1, env1.length, k)
        VarTypingDerivation(newEnv, newTEnv, newType, Var(k))

      case AbsTypingDerivation(_, tEnv, typ, Abs(argType, body), kd, btd) =>
        val resBtd = removeInKindEnv(env1, remove, env2, btd)
        val resKd  = removeKindInEnv(env1, remove, env2, kd)
        AbsTypingDerivation(newEnv, newTEnv, newType, Abs(TypeTransformations.shift(argType, -1, env1.length), resBtd.term), resKd, resBtd)

      case AppTypingDerivation(_, tEnv, typ, App(t1, t2), td1, td2) =>
        val resTd1 = removeInKindEnv(env1, remove, env2, td1)
        val resTd2 = removeInKindEnv(env1, remove, env2, td2)
        AppTypingDerivation(newEnv, newTEnv, newType, App(resTd1.term, resTd2.term), resTd1, resTd2)

      case EquivTypingDerivation(_, tEnv, typ, ter, btd, equiv, kd) => 
        val resEtd   = removeInKindEnv(env1, remove, env2, btd)
        val resKd    = removeKindInEnv(env1, remove, env2, kd)
        val resEquiv = ParallelTypeReductionProperties.equivalenceShift(equiv, -1, env1.length)
        EquivTypingDerivation(newEnv, newTEnv, newType, resEtd.term, resEtd, resEquiv, resKd)

      case TAbsTypingDerivation(_, tEnv, typ, TAbs(k, body), btd) =>
        val resBtd = removeInKindEnv(k :: env1, remove, env2, btd)
        EnvTransformationsProperties.shiftCommutativityPosPos(tEnv, -1, env1.length, 1, 0)
        TAbsTypingDerivation(newEnv, newTEnv, newType, TAbs(k, resBtd.term), resBtd)

      case TAppTypingDerivation(_, tEnv, typ, TApp(body, arg), btd, kd) =>
        val resBtd = removeInKindEnv(env1, remove, env2, btd)
        val resKd  = removeKindInEnv(env1, remove, env2, kd)
        btd.t match
          case UniversalType(k, b) => 
            TypeTransformationsProperties.shiftAbsSubstitutionCommutativity(b, arg, -1, env1.size)
            TAppTypingDerivation(newEnv, newTEnv, newType, TApp(resBtd.term, TypeTransformations.shift(arg, -1, env1.length)), resBtd, resKd)
          case _ => Unreachable        
      case _ => Unreachable
    
  }.ensuring(res =>
    res.isSound &&
    ( res.term    == TypeTermTransformations.shiftType(td.term, -1, env1.length)) &&
    ( res.kindEnv == env1 ++ (remove :: env2) ) &&
    ( res.typeEnv == TypeTransformations.shift(td.typeEnv, -1, env1.length)) &&
    ( res.t       == TypeTransformations.shift(td.t, -1, env1.length))
  )


  @opaque @pure @inlineOnce
  def preservationUnderSubst(td: TypeDerivation, j: BigInt, sd: TypeDerivation): TypeDerivation = {
    decreases(td)
    require(td.isSound)
    require(sd.isSound)
    require(td.kindEnv == sd.kindEnv)
    require(td.typeEnv == sd.typeEnv)
    require(0 <= j && j < td.typeEnv.size)
    require(td.typeEnv(j) == sd.t)

    val result = TermTransformations.substitute(td.term, j, sd.term)

    td match 
      case VarTypingDerivation(kEnv, tEnv, env, typ, Var(k)) => if j == k then sd else td

      case AbsTypingDerivation(kEnv, tEnv, typ, Abs(argType, body), kd, btd) => 
        val d0 = insertTypeInEnv(Nil(), argType, td.env, sd)
        val d1 = preservationUnderSubst(btd, j+1, d0)
        AbsTypingDerivation(kEnv, tEnv, typ, Abs(argType, d1.term), kd, d1)

      case AppTypingDerivation(kEnv, tEnv, typ, App(t1, t2), td1, td2) => 
        val td1p = preservationUnderSubst(td1, j, sd)
        val td2p = preservationUnderSubst(td2, j, sd)
        AppTypingDerivation(kEnv, tEnv, typ, App(td1p.term, td2p.term), td1p, td2p)

      case EquivTypingDerivation(kEnv, tEnv, typ, term, btd, equiv, kd) => 
        val substD = preservationUnderSubst(btd, j, sd)
        EquivTypingDerivation(kEnv, tEnv, typ, substD.term, substD, equiv, kd)

      case TAppTypingDerivation(kEnv, tEnv, typ, term, btd) =>
        // val substD = preservationUnderSubst(btd, )
        TAppTypingDerivation(kEnv, tEnv, typ, substD.term, substD)
      
      case _ => Unreachable

  }.ensuring(res =>
    res.isSound &&
    res.term == TermTransformations.substitute(td.term, j, sd.term) &&
    res.t == td.t &&
    res.kindEnv == td.kindEnv &&
    res.typeEnv == td.typeEnv
  )

  // @opaque @pure @inlineOnce
  // def preservationUnderAbsSubst(bodyTd: TypeDerivation, argTd: TypeDerivation): TypeDerivation = {
  //   require(bodyTd.isSound)
  //   require(argTd.isSound)
  //   require(bodyTd.env == argTd.t :: argTd.env)

  //   val sd1 = insertTypeInEnv(Nil(), argTd.t, argTd.env, argTd)
  //   val sd2 = preservationUnderSubst(bodyTd, 0, sd1)

  //   TermTransformationsProperties.boundRangeShift(argTd.term, 1, 0, 0, 0)
  //   TermTransformationsProperties.boundRangeSubstitutionLemma(bodyTd.term, 0, sd1.term)

  //   removeTypeInEnv(Nil(), argTd.t, argTd.env, sd2)

  // }.ensuring(res => 
  //   res.isSound &&
  //   ( res.term == TermTransformations.absSubstitution(bodyTd.term, argTd.term)) &&
  //   ( res.env == argTd.env ) &&
  //   ( res.t == bodyTd.t)
  // )



  @pure @opaque @inlineOnce
  def inversionStrongLemmaAbs(argT: Type, body: Term, t1: Type, t2: Type, equiv: ParallelEquivalence, td: TypeDerivation, kd: KindDerivation): (ParallelEquivalence, TypeDerivation, KindDerivation) = {
    decreases(td)
    require(td.term == Abs(argT, body))
    require(td.isSound)
    require(equiv.isValid)
    require(equiv.t1 == td.t)
    require(equiv.t2 == ArrowType(t1, t2))
    require(kd.isSound)
    require(kd.k == ProperKind)
    require(kd.env == td.kindEnv)
    require(kd.typ == t2)

    td match
      case EquivTypingDerivation(_, _, _, _, btd, equiv2, _) =>
        val equivArrow: ParallelEquivalence = ARSTransitivity(equiv2, equiv)
        inversionStrongLemmaAbs(argT, body, t1, t2, equivArrow, btd, kd)
      case AbsTypingDerivation(kEnv, tEnv, ArrowType(s1, s2), _, kd2, btd) =>
        val (equiv1, equiv2) = ParallelTypeReductionProperties.arrowEquivalence(s1, s2, t1, t2, equiv)
        (ARSSymmetry(equiv1), EquivTypingDerivation(kEnv, Cons(argT, tEnv), t2, body, btd, equiv2, kd), kd2) 
      case _ => Unreachable

  }.ensuring(res =>
    res._1.isValid &&
    res._2.isSound &&
    res._3.isSound &&
    res._1.t1 == t1 &&
    res._1.t2 == argT &&
    res._2.typeEnv == Cons(argT, td.typeEnv) &&
    res._2.kindEnv == td.kindEnv &&
    res._2.t == t2 &&
    res._2.term == body &&
    res._3.env == td.kindEnv &&
    res._3.k == ProperKind &&
    res._3.typ == argT)

  @pure @opaque @inlineOnce
  def inversionWeakLemmaAbs(argT: Type, body: Term, t1: Type, t2: Type, td: TypeDerivation, wf: List[KindDerivation]): (ParallelEquivalence, TypeDerivation, KindDerivation) = {
    require(Kinding.isWellFormed(td.kindEnv, td.typeEnv, wf))
    require(td.isSound)
    require(td.t == ArrowType(t1, t2))
    require(td.term == Abs(argT, body))

    val arrowKd = soundTypingHasProperKind(td, wf)
    arrowKindingInversion(arrowKd)
    arrowKd match
      case ArrowKindingDerivation(_, _, _, _, kd2) =>
        inversionStrongLemmaAbs(argT, body, t1, t2, ARSReflexivity(ArrowType(t1, t2)), td, kd2)
      case _ => Unreachable

  }.ensuring(res =>
    res._1.isValid &&
    res._2.isSound &&
    res._3.isSound &&
    res._1.t1 == t1 &&
    res._1.t2 == argT &&
    res._2.typeEnv == Cons(argT, td.typeEnv) &&
    res._2.kindEnv == td.kindEnv &&
    res._2.t == t2 &&
    res._2.term == body &&
    res._3.env == td.kindEnv &&
    res._3.k == ProperKind &&
    res._3.typ == argT)

  // @opaque @inlineOnce @pure
  // def preservation(td: TypeDerivation, red: EvalReductionDerivation, wf: List[KindDerivation]): TypeDerivation = {
  //   decreases(td)
  //   require(td.isSound)
  //   require(red.isSound)
  //   require(red.term1 == td.term)
  //   require(Kinding.isWellFormed(td.env, wf))

  //   (td, red) match
  //     case (EquivTypingDerivation(env, typ, term, btd, equiv, kd), _) => 
  //       val bodyPreservation = preservation(btd, red, wf)
  //       EquivTypingDerivation(env, typ, bodyPreservation.term, bodyPreservation, equiv, kd)
  //     case (AbsTypingDerivation(env, typ, Abs(argType, body), kd, btd), AbsDerivation(t1, t2, rd)) => 
  //       val bodyPreservation = preservation(btd, rd, Cons(kd, wf))
  //       AbsTypingDerivation(env, typ, t2, kd, bodyPreservation)
  //     case (AppTypingDerivation(env, typ, App(t11, t12), td1, td2), AppDerivationL(t1, App(t21, t22), brd1)) => 
  //       val bodyPreservation = preservation(td1, brd1, wf)
  //       AppTypingDerivation(env, typ, App(t21, t12), bodyPreservation, td2)
  //     case (AppTypingDerivation(env, typ, App(t11, t12), td1, td2), AppDerivationR(t1, App(t21, t22), brd2)) => 
  //       val bodyPreservation = preservation(td2, brd2, wf)
  //       AppTypingDerivation(env, typ, App(t11, t22), td1, bodyPreservation)
  //     case (AppTypingDerivation(env, typ, App(Abs(argT1, body11), arg11), absTd, td2), AppAbsDerivation(Abs(argT2, body21), arg21)) =>
  //       absTd.t match
  //         case ArrowType(t1, t2) => 
  //           val (equiv, bodyDeriv, kd) = inversionWeakLemmaAbs(argT1, body11, t1, t2, absTd, wf)
  //           val argDeriv = EquivTypingDerivation(env, argT1, arg11, td2, equiv,kd)
  //           preservationUnderAbsSubst(bodyDeriv, argDeriv)
  //         case _ => Unreachable 
  //     case _ => Unreachable
  // }.ensuring(res => 
  //   res.isSound &&
  //   ( res.term == red.term2 ) &&
  //   ( res.env == td.env ) &&
  //   ( res.t == td.t)
  // )



}