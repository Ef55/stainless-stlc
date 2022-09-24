import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import Transformations.Types._

object TypeEquivalence{



  sealed trait EquivalenceDerivation{
    def type1: Type = {
      this match{
        case ReflDerivation(t) => t 
        case SymmDerivation(t1, _, _) => t1
        case TransDerivation(t1, _, _, _) => t1
        case ArrowDerivation(t1, _, _, _) => t1
        case AbsDerivation(t1, _, _) => t1
        case AppDerivation(t1, _, _, _) => t1
        case AppAbsDerivation(t1, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case ReflDerivation(t) => t 
        case SymmDerivation(_, t2, _) => t2
        case TransDerivation(_, t2, _, _) => t2
        case ArrowDerivation(_, t2, _, _) => t2
        case AbsDerivation(_, t2, _) => t2
        case AppDerivation(_, t2, _, _) => t2
        case AppAbsDerivation(_, t2) => t2
      }
    }

    def isValid: Boolean = {
      this match {
        case ReflDerivation(_) => true
        case SymmDerivation(t1, t2, ed) => ed.isValid && ed.type1 == t2 && ed.type2 == t1
        case TransDerivation(t1, t2, ed1, ed2) => 
          ed1.isValid && ed2.isValid && ed1.type1 == t1 &&
          ed2.type2 == t2 && ed1.type2 == ed2.type1
        case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ed1, ed2) =>
          ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
          ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
        case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), ed) => 
          ed.isValid && ed.type1 == b1 && ed.type2 == b2 && k1 == k2
        case AppDerivation(AppType(t11, t12), AppType(t21, t22), ed1, ed2) =>
          ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
          ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
        case AppAbsDerivation(AppType(AbsType(argK, body), t2), t3) =>
          t3 == absSubstitution(body, t2) 
        case AppAbsDerivation(_, _) => false
      }
    }
  }
  case class ReflDerivation(t: Type) extends EquivalenceDerivation
  case class SymmDerivation(t1: Type, t2: Type, ed: EquivalenceDerivation) extends EquivalenceDerivation
  case class TransDerivation(t1: Type, t2: Type, ed1: EquivalenceDerivation, ed2: EquivalenceDerivation) extends EquivalenceDerivation
  case class ArrowDerivation(t1: ArrowType, t2: ArrowType, ed1: EquivalenceDerivation, ed2: EquivalenceDerivation) extends EquivalenceDerivation
  case class AbsDerivation(t1: AbsType, t2: AbsType, ed: EquivalenceDerivation) extends EquivalenceDerivation
  case class AppDerivation(t1: AppType, t2: AppType, ed: EquivalenceDerivation, ed2: EquivalenceDerivation) extends EquivalenceDerivation
  case class AppAbsDerivation(t1: AppType, t2: Type) extends EquivalenceDerivation

}

object ParallelReduction{

  sealed trait ParallelReductionDerivation{
    def type1: Type = {
      this match{
        case ReflDerivation(t) => t 
        case ArrowDerivation(t1, _, _, _) => t1
        case AbsDerivation(t1, _, _) => t1
        case AppDerivation(t1, _, _, _) => t1
        case AppAbsDerivation(t1, _, _, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case ReflDerivation(t) => t 
        case ArrowDerivation(_, t2, _, _) => t2
        case AbsDerivation(_, t2, _) => t2
        case AppDerivation(_, t2, _, _) => t2
        case AppAbsDerivation(_, t2, _, _) => t2
      }
    }

    def isValid: Boolean = {
      this match {
        case ReflDerivation(_) => true
        case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
          prd1.isValid && prd2.isValid && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) => 
          prd.isValid && prd.type1 == b1 && prd.type2 == b2 && k1 == k2
        case AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
          prd1.isValid && prd2.isValid && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AppAbsDerivation(AppType(AbsType(argK, body), t2), t3, prd1, prd2) =>
          prd1.isValid && prd2.isValid && prd1.type1 == body &&
          prd2.type1 == t2 && t3 == absSubstitution(prd1.type2, prd2.type2) 
        case AppAbsDerivation(_, _, _, _) => false
      }
    }
  }
  case class ReflDerivation(t: Type) extends ParallelReductionDerivation
  case class ArrowDerivation(t1: ArrowType, t2: ArrowType, prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AbsDerivation(t1: AbsType, t2: AbsType, prd: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppDerivation(t1: AppType, t2: AppType, prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppAbsDerivation(t1: AppType, t2: Type, prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation) extends ParallelReductionDerivation

  def reducesTo(t1: Type, t2: Type): Option[ParallelReductionDerivation] = {
    if(t1 == t2){
      Some(ReflDerivation(t1))
    }
    else{
      (t1, t2) match{
        case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
           (reducesTo(t11, t21), reducesTo(t12, t22)) match {
              case (Some(prd1), Some(prd2)) => Some(ArrowDerivation(at1, at2, prd1, prd2))
              case _ => None()
           }
        case _ => None()
          }
      }
    }
  }