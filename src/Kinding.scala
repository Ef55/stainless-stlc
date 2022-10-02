import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Kinding {
  import LambdaOmega._

  sealed trait KindDerivation{

    def env: KindEnvironment = this match
      case BasicTypeDerivation(e, _) => e
      case VariableTypeDerivation(e, _, _) => e
      case AbsTypeDerivation(e, _, _, _) => e
      case AppTypeDerivation(e, _, _, _, _) => e
      case ArrowTypeDerivation(e, _, _, _, _) => e

    

    def k: Kind = this match
      case BasicTypeDerivation(_, _) => ProperKind
      case VariableTypeDerivation(_, k, _) => k
      case AbsTypeDerivation(_, k, _, _) => k
      case AppTypeDerivation(_, k, _, _, _) => k
      case ArrowTypeDerivation(_, k, _, _, _) => k
  

    def typ: Type = this match
      case BasicTypeDerivation(_, typ) => typ
      case VariableTypeDerivation(_, _, typ) => typ
      case AbsTypeDerivation(_, _, typ, _) => typ
      case AppTypeDerivation(_, _, typ, _, _) => typ
      case ArrowTypeDerivation(_, _, typ, _, _) => typ
    
    def isValid: Boolean = 
      this match
        case BasicTypeDerivation(_, _) => true
        case VariableTypeDerivation(env, k, VariableType(j)) => 
          (j < env.size) &&
          env(j) == k
        
        case ArrowTypeDerivation(_, k, ArrowType(t1, t2), bkd1, bkd2) => 
          bkd1.isValid && bkd2.isValid && // Premises are valid
          bkd1.typ == t1 && bkd2.typ == t2 && bkd1.env == env && bkd2.env == env && // and have matching attributes
          bkd1.k == ProperKind && bkd2.k == ProperKind && k == ProperKind
        
        case AbsTypeDerivation(env, ArrowKind(k1, k2), AbsType(argK, body), bkd) => 
          bkd.isValid && // Premise is valid,
          bkd.typ == body && bkd.env == argK :: env && // and has matching attributes
          argK == k1 && bkd.k == k2 // Types are correct
        
        case AbsTypeDerivation(_ ,_, _, _) => false // An abstraction should always have an arrow type...
        case AppTypeDerivation(env, k, AppType(t1, t2), bkd1, bkd2) => 
          bkd1.isValid && bkd2.isValid && // Premises are valid
          bkd1.typ == t1 && bkd2.typ == t2 && bkd1.env == env && bkd2.env == env && // and have matching attributes
          bkd1.k == ArrowKind(bkd2.k, k) // The body has expected type    
    
    def ===(that: KindDerivation): Boolean = 
      this.k == that.k && this.env == that.env
  }
  
  case class BasicTypeDerivation(e: KindEnvironment, typ: BasicType) extends KindDerivation
  case class VariableTypeDerivation(e: KindEnvironment, k: Kind, typ: VariableType) extends KindDerivation
  case class AbsTypeDerivation(e: KindEnvironment, k: Kind, typ: AbsType, bkd: KindDerivation) extends KindDerivation
  case class AppTypeDerivation(e: KindEnvironment, k: Kind, typ: AppType, bkd1: KindDerivation, bkd2: KindDerivation) extends KindDerivation
  case class ArrowTypeDerivation(e: KindEnvironment, k: Kind, typ: ArrowType, bkd1: KindDerivation, bkd2: KindDerivation) extends KindDerivation

  def deriveKind(env: KindEnvironment, t: Type): Option[KindDerivation] = 
    t match 
      case bt@BasicType(_) => Some(BasicTypeDerivation(env, bt))
      case v@VariableType(j) => if (j < env.size) Some(VariableTypeDerivation(env, env(j), v)) else None()
      case arr@ArrowType(t1, t2) => 
        (deriveKind(env, t1), deriveKind(env, t2)) match 
          case (Some(kd1), Some(kd2)) => 
            if(kd1.k == ProperKind && kd2.k == ProperKind)
              Some(ArrowTypeDerivation(env, ProperKind, arr, kd1, kd2))
            
            else
              None()
            
          
          case (_, _) => None()
        
      
      case abs@AbsType(argK, body) => 
        deriveKind(argK :: env, body) match 
          case None() => None()
          case Some(kb) => Some(AbsTypeDerivation(env, ArrowKind(argK, kb.k), abs, kb))
        
      
      case app@AppType(t1, t2) => 
        (deriveKind(env, t1), deriveKind(env, t2)) match 
          case (Some(kd1), Some(kd2)) => 
            kd1.k match
              case ArrowKind(argK, bodyK) if (argK == kd2.k) => 
                Some(AppTypeDerivation(env, bodyK, app, kd1, kd2))
              case _ => None()
            
          
          case (_, _) => None()
        
      
    
  
  
  def deriveKind(t: Type): Option[KindDerivation] = 
    deriveKind(Nil(), t)
  
}
 


object TypingProperties{
  import LambdaOmega._
  import Kinding._
//   import Reduction._  
  import Transformations.{Terms => TermTr, Types => TypeTr}

  import ListProperties._
  // import STLCProperties. Types => TypeProp
  import TypeEquivalence._
  import TypeReduction._
  import TransformationsProperties.{Types => TypeTrProp}


  /// Type derivations
  @opaque @pure
  def deriveKindCompleteness(@induct kd: KindDerivation): Unit = {
    require(kd.isValid)
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
    deriveKind(env, t).get.isValid && 
    deriveKind(env, t).get.typ == t && 
    deriveKind(env, t).get.env == env
  )

  @opaque @pure
  def kindDerivationUniqueness(kd1: KindDerivation, kd2: KindDerivation): Unit = {
    require(kd1.isValid)
    require(kd2.isValid)
    require(kd1.typ == kd2.typ)
    require(kd1.env == kd2.env)

    deriveKindCompleteness(kd1)
    deriveKindCompleteness(kd2)
  }.ensuring(kd1 == kd2)

  def arrowKindNotRedIsAbsType(kd: KindDerivation): Unit = {
    require(kd.isValid)
    require(kd.env == Nil())
    require(kd.k.isInstanceOf[ArrowKind])
    require(!detReduce(kd.typ).isDefined)
    kd match
      case AppTypeDerivation(_, _, AppType(t1, t2), kd1, kd2) => 
        arrowKindNotRedIsAbsType(kd1)
        arrowKindNotRedIsAbsType(kd2)
      case _ => ()
  }.ensuring(kd.typ.isInstanceOf[AbsType])

  /// Progress
  @opaque @pure
  def detReduceProgress(kd: KindDerivation): Unit = {
    require(kd.env == Nil())
    require(kd.isValid)
    kd match
      case BasicTypeDerivation(_, _) => ()
      case VariableTypeDerivation(_, _, _) => ()
      case AbsTypeDerivation(_, _, _, _) => ()
      case AppTypeDerivation(_, _, AppType(t1, t2), kd1, kd2) => 
        if detReduce(t1).isDefined then
          detReduceProgress(kd1)
        else
          arrowKindNotRedIsAbsType(kd1)
        detReduceProgress(kd2)
      case ArrowTypeDerivation(_, _, ArrowType(t1, t2), kd1, kd2) => 
        detReduceProgress(kd1)
        detReduceProgress(kd2)
    
  }.ensuring(detReduce(kd.typ).isDefined || kd.typ.isValue)

  def valueNotReducible(kd: KindDerivation): Unit = {
    require(kd.typ.isValue)
    require(kd.isValid)
    kd match
      case BasicTypeDerivation(_, _) => ()
      case VariableTypeDerivation(_, _, _) => ()
      case AbsTypeDerivation(_, _, _, _) => ()
      case AppTypeDerivation(_, _, AppType(t1, t2), kd1, kd2) => ()
      case ArrowTypeDerivation(_, _, ArrowType(t1, t2), kd1, kd2) => 
        valueNotReducible(kd1)
        valueNotReducible(kd2)
  }.ensuring(!detReduce(kd.typ).isDefined)


  /// Preservation

  @opaque @pure
  def environmentWeakening(kd: KindDerivation, envExt: KindEnvironment): KindDerivation = {
    require(kd.isValid)
    kd match 
      case BasicTypeDerivation(env, bt) => BasicTypeDerivation(env ++ envExt, bt)
      case VariableTypeDerivation(env, k, vt@VariableType(j)) => 
        concatFirstIndexing(env, envExt, j)
        VariableTypeDerivation(env ++ envExt, k, vt)
      
      case AbsTypeDerivation(env, k, at@AbsType(argKind, body), bkd) => 
        val resBkd = environmentWeakening(bkd, envExt)
        AbsTypeDerivation(env ++ envExt, k, at, resBkd)
      
      case AppTypeDerivation(env, k, at@AppType(t1, t2), bk1, bk2) => 
        val resBk1 = environmentWeakening(bk1, envExt)
        val resBk2 = environmentWeakening(bk2, envExt)
        AppTypeDerivation(env ++ envExt, k, at, resBk1, resBk2)
      case ArrowTypeDerivation(env, k, at@ArrowType(t1, t2), bk1, bk2) => 
        val resBk1 = environmentWeakening(bk1, envExt)
        val resBk2 = environmentWeakening(bk2, envExt)
        ArrowTypeDerivation(env ++ envExt, k, at, resBk1, resBk2)

    
  }.ensuring(res => 
    res.isValid && 
    ( res.env == kd.env ++ envExt ) && 
    ( res.typ == kd.typ) && 
    ( res.k == kd.k )
  )

  @opaque @pure
  def variableTypeEnvironmentStrengthening(v: VariableTypeDerivation, env: KindEnvironment, envExt: KindEnvironment): KindDerivation = {
    require(v.env == env ++ envExt)
    require(v.isValid)
    require(v.typ.j < env.length)
    concatFirstIndexing(env, envExt, v.typ.j)
    VariableTypeDerivation(env, v.k, v.typ)
  }.ensuring(res => 
    res.isValid && 
    ( res.env == env ) && 
    ( res.k == v.k ) && 
    ( res.typ == v.typ )
  )

  @opaque @pure
  def variableTypeEnvironmentUpdate(v: VariableTypeDerivation, env: KindEnvironment, oldEnv: KindEnvironment, newEnv: KindEnvironment): KindDerivation = {
    require(v.env == env ++ oldEnv)
    require(v.isValid)
    require(v.typ.j < env.length)  
    val v2 = variableTypeEnvironmentStrengthening(v, env, oldEnv) 
    environmentWeakening(v2, newEnv)
  }.ensuring(res => 
    res.isValid && 
    ( res.env == (env ++ newEnv) ) && 
    ( res.k == v.k ) && 
    ( res.typ == v.typ )
  )

  @opaque @pure
  def insertKindInEnv(env1: KindEnvironment, insert: Kind, env2: KindEnvironment, kd: KindDerivation): KindDerivation = {
    require(kd.isValid)
    require(env1 ++ env2 == kd.env)

    val newEnv = env1 ++ (insert :: env2)

    kd match 
      case BasicTypeDerivation(_, bt) => BasicTypeDerivation(newEnv, bt)
      case v@VariableTypeDerivation(_, typ, VariableType(j)) => 
        if (j < env1.size)
          variableTypeEnvironmentUpdate(v, env1, env2, insert :: env2)
        
        else
          insertionIndexing(env1, env2, insert, j)
          VariableTypeDerivation(newEnv, typ, VariableType(j + 1))
         
      
      case AbsTypeDerivation(_, k, AbsType(argK, body), bkd) => 
        val resBkd = insertKindInEnv(argK :: env1, insert, env2, bkd)
        AbsTypeDerivation(newEnv, k, AbsType(argK, resBkd.typ), resBkd)
      
      case AppTypeDerivation(_, k, AppType(t1, t2), kd1, kd2) => 
        val resKd1 = insertKindInEnv(env1, insert, env2, kd1)
        val resKd2 = insertKindInEnv(env1, insert, env2, kd2)
        AppTypeDerivation(newEnv, k, AppType(resKd1.typ, resKd2.typ), resKd1, resKd2)
      
      case ArrowTypeDerivation(_, k, ArrowType(t1, t2), kd1, kd2) => 
        val resKd1 = insertKindInEnv(env1, insert, env2, kd1)
        val resKd2 = insertKindInEnv(env1, insert, env2, kd2)
        ArrowTypeDerivation(newEnv, k, ArrowType(resKd1.typ, resKd2.typ), resKd1, resKd2)
      
    
    
  }.ensuring(res =>
    res.isValid &&
    ( res.typ == TypeTr.shift(kd.typ, 1, env1.size) ) &&
    ( res.env == env1 ++ (insert :: env2) ) &&
    ( kd.k == res.k )
  )

  @opaque @pure
  def removeKindInEnv(env1: KindEnvironment, remove: Kind, env2: KindEnvironment, kd: KindDerivation): KindDerivation = {
    require(kd.isValid)
    require(kd.env == env1 ++ (remove :: env2))
    require(!kd.typ.hasFreeVariablesIn(env1.size, 1))

    val newEnv = env1 ++ env2

    kd match 
      case BasicTypeDerivation(_, bt) => BasicTypeDerivation(newEnv, bt)
      case v@VariableTypeDerivation(_, k, VariableType(j)) => 
        if (j < env1.size)
          val res = variableTypeEnvironmentUpdate(v, env1, remove :: env2, env2)
          res
        
        else
          insertionIndexing(env1, env2, remove, j - 1)
          val res = VariableTypeDerivation(newEnv, k, VariableType(j - 1))
          res
         
      
      case AbsTypeDerivation(_, k, AbsType(argKind, body), bkd) => 
        val resBkd = removeKindInEnv(argKind :: env1, remove, env2, bkd)
        val res = AbsTypeDerivation(newEnv, k, AbsType(argKind, resBkd.typ), resBkd)
        res
      
      case AppTypeDerivation(_, k, AppType(t1, t2), kd1, kd2) => 
        val resKd1 = removeKindInEnv(env1, remove, env2, kd1)
        val resKd2 = removeKindInEnv(env1, remove, env2, kd2)
        val res = AppTypeDerivation(newEnv, k, AppType(resKd1.typ, resKd2.typ), resKd1, resKd2)
        res
      case ArrowTypeDerivation(_, k, ArrowType(t1, t2), kd1, kd2) => 
        val resKd1 = removeKindInEnv(env1, remove, env2, kd1)
        val resKd2 = removeKindInEnv(env1, remove, env2, kd2)
        val res = ArrowTypeDerivation(newEnv, k, ArrowType(resKd1.typ, resKd2.typ), resKd1, resKd2)
        res

  }.ensuring(res =>
    res.isValid &&
    ( res.typ == TypeTr.shift(kd.typ, -1, env1.size) ) &&
    ( res.env == env1 ++ env2 ) &&
    ( kd.k == res.k)
  )


  @opaque @pure
  def preservationUnderSubst(td: KindDerivation, j: BigInt, sd: KindDerivation): KindDerivation = { 
    require(td.isValid)
    require(sd.isValid)
    require(td.env == sd.env)
    require(0 <= j && j < td.env.size)
    require(td.env(j) == sd.k)

    val result: Type = TypeTr.substitute(td.typ, j, sd.typ)

    td match 
      case BasicTypeDerivation(_, _) => td
      case VariableTypeDerivation(_, _, VariableType(k)) => if j == k then sd else td
      case AbsTypeDerivation(env, typ, AbsType(argKind, body), bkd) => 
        val d0 = insertKindInEnv(Nil(), argKind, td.env, sd)
        val d1 = preservationUnderSubst(bkd, j+1, d0) // Fragile: require 3/5
        AbsTypeDerivation(env, typ, AbsType(argKind, d1.typ), d1)   
      case AppTypeDerivation(env, typ, AppType(t1, t2), kd1, kd2) => 
        val td1p = preservationUnderSubst(kd1, j, sd)
        val td2p = preservationUnderSubst(kd2, j, sd)
        AppTypeDerivation(env, typ, AppType(td1p.typ, td2p.typ), td1p, td2p)
      case ArrowTypeDerivation(env, typ, ArrowType(t1, t2), kd1, kd2) => 
        val td1p = preservationUnderSubst(kd1, j, sd)
        val td2p = preservationUnderSubst(kd2, j, sd)
        ArrowTypeDerivation(env, typ, ArrowType(td1p.typ, td2p.typ), td1p, td2p)
  }.ensuring(res =>
    res.isValid &&
    ( res.typ == TypeTr.substitute(td.typ, j, sd.typ) ) &&
    ( td === res )
  )

  @opaque @pure
  def preservationUnderAbsSubst(env: KindEnvironment, absKd: AbsTypeDerivation, argKd: KindDerivation, k: Kind): KindDerivation = {
    require(absKd.isValid && argKd.isValid)
    require(absKd.env == env && argKd.env == env)
    require(absKd.typ.argKind == argKd.k)
    require(absKd.k == ArrowKind(argKd.k, k))

    val AbsType(argKind, _) = absKd.typ

    val sd0 = argKd
    val sd1 = insertKindInEnv(Nil(), argKind, sd0.env, sd0)
    val sd2 = preservationUnderSubst(absKd.bkd, 0, sd1)

    assert(!sd0.typ.hasFreeVariablesIn(0, 0))
    TypeTrProp.boundRangeShift(sd0.typ, 1, 0, 0, 0)
    TypeTrProp.boundRangeSubstitutionLemma(absKd.bkd.typ, 0, sd1.typ)
    removeKindInEnv(Nil(), argKind, env, sd2)
  }.ensuring(res => 
    res.isValid &&
    ( res.typ == TypeTr.absSubstitution(absKd.typ.body, argKd.typ)) &&
    ( res.env == env ) &&
    ( res.k == k)
  )

  // def properEquivalentValuesEquals(eq: EquivalenceDerivation, kd1: KindDerivation, kd2: KindDerivation): Unit ={
  //   require(eq.isValid)
  //   require(eq.type1 == kd1.typ)
  //   require(eq.type2 == kd2.typ)

  //   eq match
  //     case ReflEqDerivation(_) => ()
  //     case SymmEqDerivation(t1, t2, ed) => 
  //       properEquivalentValuesEquals(ed, kd2, kd1)
  //     case TransEqDerivation(t1, t2, ed1, ed2) => 
  //       deriveKind(Nil(), ed1.type2) match
  //         Some(bkd) => 

  //           properEquivalentValuesEquals(ed1, kd1, bkd)
  //           properEquivalentValuesEquals(ed2, bkd, kd2)
  //         None() =>  
  //       properEquivalentValuesEquals(ed1, kd1)
  //       properEquivalentValuesEquals(ed2, kd2)
  //     case ArrowEqDerivation(ArrowType(t11, t12), at2@ArrowType(t21, t22), ed1, ed2) =>
  //       ArrowTypeDerivation(kd1.env, ArrowKind(bkd21.k, bkd22.k), at2, bkd21, bkd22)
  //     // case AbsEqDerivation(AbsType(argKind, bkd), t2, ed) =>
  //     //   equivalentSameKind(ed,)
  //     case _ => ()


  // }.ensuring(_ => 
  //   (kd1.isValid && kd1.k == ProperKind && kd1.typ.isValue && kd1.env == Nil()) ==
  //   (kd2.isValid && kd2.k == ProperKind && kd2.typ.isValue && kd2.env == Nil())
  // )

  def equivalentSameKind(eq: EquivalenceDerivation, env: KindEnvironment, k: Kind): Unit = {
    require(eq.isValid)

    eq match
      case ReflEqDerivation(_) => ()
      case SymmEqDerivation(t1, t2, ed) => 
        equivalentSameKind(ed, env, k)
      case TransEqDerivation(t1, t2, ed1, ed2) => 
        equivalentSameKind(ed1, env, k)
        equivalentSameKind(ed2, env, k)
      case ArrowEqDerivation(ArrowType(t11, t12), at2@ArrowType(t21, t22), ed1, ed2) =>
        equivalentSameKind(ed1, env, k)
        equivalentSameKind(ed1, env, k)
      case AppEqDerivation(AppType(t11, t12), at2@AppType(t21, t22), ed1, ed2) =>
        equivalentSameKind(ed1, env, k)
        equivalentSameKind(ed1, env, k)
      case _ => ( )
    
  }.ensuring(_ => (deriveKind(env, eq.type1).isDefined && deriveKind(env, eq.type1).get.isValid && deriveKind(env, eq.type1).get == k) ==
                  (deriveKind(env, eq.type2).isDefined && deriveKind(env, eq.type1).get.isValid && deriveKind(env, eq.type2).get == k)    )

//   @opaque @pure
//   def preservation(td: KindDerivation, reduced: Type): KindDerivation = 
//     require(td.isValid)
//     require(reducesTo(td.typ, reduced).isDefined)
//     decreases(td)

//     val Some(rule) = reducesTo(td.typ, reduced)

//     td match 
//       case AbsTypeDerivation(env, typ, t@AbsType(argKind, body), bkd) => 
//         absReducesToSoundness(t, reduced)
//         assert(rule == AbsCongruence)
//         absCongruenceInversion(t, reduced)
//         val tp = reduced.asInstanceOf[AbsType]
//         val btdp = preservation(bkd, tp.body)
//         val tdp = AbsTypeDerivation(env, typ, tp, btdp)
//         assert(btdp.isValid)
//         assert(btdp.typ == tp.body)
//         assert(bkd.env == argKind :: td.env)
//         assert(btdp.env == bkd.env)
//         assert(typ.isInstanceOf[ArrowType])
//         val ArrowType(t1, t2) = typ
//         assert(t1 == argKind)
//         assert(t2 == btdp.t)
//         assert(tp == AbsType(argKind, btdp.typ))
//         assert(tdp.isValid)
//         tdp
//       
//       case AppTypeDerivation(env, typ, t@AppType(t1, t2), kd1, kd2) => 

//         assert(td.typ == t)
//         appReducesToSoundness(t, reduced)
//         rule match 
//           case App1Congruence => 
//             app1CongruenceInversion(t, reduced)
//             val tp = reduced.asInstanceOf[AppType]
//             val t1p = tp.t1

//             val td1p = preservation(kd1, t1p)
//             val tdp = AppTypeDerivation(env, typ, tp, td1p, kd2)
//             assert(td1p.isValid && kd2.isValid)
//             assert(tp == AppType(td1p.typ, kd2.typ))
//             assert(tdp.isValid)
//             tdp
//           
//           case App2Congruence => 
//             app2CongruenceInversion(t, reduced)
//             val tp = reduced.asInstanceOf[AppType]
//             val t2p = tp.t2
            
//             val td2p = preservation(kd2, t2p)
//             val tdp = AppTypeDerivation(env, typ, tp, kd1, td2p)
//             assert(tdp.isValid)
//             tdp
//           
//           case AbsAppReduction => 
//             absAppReductionInversion(t, reduced)
//             absDerivationInversion(kd1)
//             preservationUnderAbsSubst(env, kd1.asInstanceOf[AbsTypeDerivation], kd2, typ)
//           
//    
//     

//   .ensuring(res => 
//     res.isValid &&
//     ( res.typ == reduced ) &&
//     ( res === td )
//   )

}