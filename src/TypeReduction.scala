import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import Transformations.Types._

object TypeReduction{



  sealed trait TypeToTypeDerivation{
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

    def size: BigInt = {
      this match
        case ReflDerivation(_) => BigInt(1)
        case SymmDerivation(_, _, ed) => ed.size + BigInt(1)
        case TransDerivation(_, _, ed1, ed2) => ed1.size + ed2.size
        case ArrowDerivation(_, _, ed1, ed2) => ed1.size + ed2.size
        case AbsDerivation(_, _, ed) => ed.size + BigInt(1)
        case AppDerivation(_, _, ed1, ed2) => ed1.size + ed2.size
        case AppAbsDerivation(_, _) => BigInt(1)
    }.ensuring(_ > BigInt(0))

    def isEquivalence: Boolean = {
      this match {
        case ReflDerivation(_) => true
        case SymmDerivation(t1, t2, ed) => ed.isEquivalence && ed.type1 == t2 && ed.type2 == t1
        case TransDerivation(t1, t2, ed1, ed2) => 
          ed1.isEquivalence && ed2.isEquivalence && ed1.type1 == t1 &&
          ed2.type2 == t2 && ed1.type2 == ed2.type1
        case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ed1, ed2) =>
          ed1.isEquivalence && ed2.isEquivalence && ed1.type1 == t11 &&
          ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
        case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), ed) => 
          ed.isEquivalence && ed.type1 == b1 && ed.type2 == b2 && k1 == k2
        case AppDerivation(AppType(t11, t12), AppType(t21, t22), ed1, ed2) =>
          ed1.isEquivalence && ed2.isEquivalence && ed1.type1 == t11 &&
          ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
        case AppAbsDerivation(AppType(AbsType(argK, body), t2), t3) =>
          t3 == absSubstitution(body, t2) 
        case AppAbsDerivation(_, _) => false
      }
    }

    def isParallelReduction: Boolean = {
      this match {
        case ReflDerivation(_) => true
        case ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1, prd2) =>
          prd1.isParallelReduction && prd2.isParallelReduction && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) => 
          prd.isParallelReduction && prd.type1 == b1 && prd.type2 == b2 && k1 == k2
        case AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
          prd1.isParallelReduction && prd2.isParallelReduction && prd1.type1 == t11 &&
          prd1.type2 == t21 && prd2.type1 == t12 && prd2.type2 == t22
        case AppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => t3 == absSubstitution(body, t12) 
        case _ => false
      }
    }
  }
  case class ReflDerivation(t: Type) extends TypeToTypeDerivation
  case class SymmDerivation(t1: Type, t2: Type, ed: TypeToTypeDerivation) extends TypeToTypeDerivation
  case class TransDerivation(t1: Type, t2: Type, ed1: TypeToTypeDerivation, ed2: TypeToTypeDerivation) extends TypeToTypeDerivation
  case class ArrowDerivation(t1: ArrowType, t2: ArrowType, ed1: TypeToTypeDerivation, ed2: TypeToTypeDerivation) extends TypeToTypeDerivation
  case class AbsDerivation(t1: AbsType, t2: AbsType, ed: TypeToTypeDerivation) extends TypeToTypeDerivation
  case class AppDerivation(t1: AppType, t2: AppType, ed: TypeToTypeDerivation, ed2: TypeToTypeDerivation) extends TypeToTypeDerivation
  case class AppAbsDerivation(t1: AppType, t2: Type) extends TypeToTypeDerivation

  def reducesTo(t1: Type, t2: Type): Option[TypeToTypeDerivation] = {
    decreases(t1.size + t2.size)
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
        case (at1@AbsType(k1, body1), at2@AbsType(k2, body2)) =>
          reducesTo(body1, body2) match {
              case Some(prd) if k1 == k2 => Some(AbsDerivation(at1, at2, prd))
              case _ => None()
          }
        
        case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => Some(AppAbsDerivation(at1, t3))
        case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
          (reducesTo(t11, t21), reducesTo(t12, t22)) match {
              case (Some(prd1), Some(prd2)) => Some(AppDerivation(at1, at2, prd1, prd2))
              case _ => None()
          }
        case (_, _) => None()
      }
    }
  }

  def reducesToSoundness(t1: Type, t2: Type): Unit = {
    require(reducesTo(t1, t2).isDefined)
    decreases(t1.size + t2.size)
    if(t1 == t2){
      ()
    }
    else{
      (t1, t2) match{
        case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
          reducesToSoundness(t11, t21)
          reducesToSoundness(t12, t22)
        case (at1@AbsType(k1, body1), at2@AbsType(k2, body2)) =>
          reducesToSoundness(body1, body2)
        case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => ()
        case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
          reducesToSoundness(t11, t21)
          reducesToSoundness(t12, t22)
        case (_, _) => ()
        }
      }
  }.ensuring(_ => reducesTo(t1, t2).get.isParallelReduction)

  def reducesToCompleteness(prd: TypeToTypeDerivation): Unit = {
    require(prd.isParallelReduction)
    prd match
      case ReflDerivation(t) => ()
      case ArrowDerivation(ArrowType(_, _), ArrowType(_, _), prd1, prd2) =>
        reducesToCompleteness(prd1)
        reducesToCompleteness(prd2)
      case AbsDerivation(AbsType(_, _), AbsType(_, _), prd1) =>
        reducesToCompleteness(prd1)
      case AppDerivation(AppType(_, _), AppType(_, _), prd1, prd2) =>
        reducesToCompleteness(prd1)
        reducesToCompleteness(prd2)
      case AppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => 
        assert(t3 == absSubstitution(body, t12))
        ()
      case _ => ()
  }.ensuring(_ => reducesTo(prd.type1, prd.type2).isDefined)

  // def reduceSubst(td: TypeToTypeDerivation, j: BigInt, sd: TypeToTypeDerivation): TypeToTypeDerivation = {
  //   require(td.isParallelReduction)
  //   require(sd.isParallelReduction)
    
  //   td match
  //     case ReflDerivation(t) =>


  //   td.type1 match
  //     case bt@BasicType(_) => ReflDerivation(bt)
  //     case AbsType(k, body) => 
  //       val bodyDeriv = reduceSubst()
  //       AbsDerivation(AbsType(k, substitute(body, j, sd.type1)), )
  //     case _ => ReflDerivation(td.type1)

  // }.ensuring(res =>
  //   res.isParallelReduction &&
  //   res.type1 == substitute(td.type1, j, sd.type1)
  //   res.type2 == substitute(td.type2, j, sd.type2))

  def diamondProperty(prd1: TypeToTypeDerivation, prd2: TypeToTypeDerivation): (TypeToTypeDerivation, TypeToTypeDerivation) = {
    decreases(prd1.size + prd2.size)
    require(prd1.type1 == prd2.type1)
    require(prd1.isParallelReduction)
    require(prd2.isParallelReduction)
    if prd1.type2 == prd2.type2 then
      (ReflDerivation(prd1.type2), ReflDerivation(prd2.type2))
    else
      (prd1, prd2) match 
        case (ReflDerivation(t), _) => (prd2, ReflDerivation(prd2.type2))
        case (_, ReflDerivation(t)) => (ReflDerivation(prd1.type2), prd1)
        case (ArrowDerivation(ArrowType(t11, t12), ArrowType(t21, t22), prd11, prd12), ArrowDerivation(ArrowType(t31, t32), ArrowType(t41, t42), prd21, prd22)) =>
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (ArrowDerivation(ArrowType(dP11.type1, dP21.type1), ArrowType(dP11.type2, dP21.type2), dP11, dP21), ArrowDerivation(ArrowType(dP12.type1, dP22.type1), ArrowType(dP12.type2, dP22.type2), dP12, dP22))
        case (AbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd11), AbsDerivation(AbsType(k3, b3), AbsType(k4, b4), prd12)) =>
          val (dP1, dP2) = diamondProperty(prd11, prd12)
          (AbsDerivation(AbsType(k2, dP1.type1), AbsType(k2, dP1.type2), dP1), AbsDerivation(AbsType(k2, dP2.type1), AbsType(k2, dP2.type2), dP2))
        case (AppDerivation(AppType(t11, t12), AppType(t21, t22), prd11, prd12), AppDerivation(AppType(t31, t32), AppType(t41, t42), prd21, prd22)) =>
          val (dP11, dP12) = diamondProperty(prd11, prd21)
          val (dP21, dP22) = diamondProperty(prd12, prd22)
          (AppDerivation(AppType(dP11.type1, dP21.type1), AppType(dP11.type2, dP21.type2), dP11, dP21), AppDerivation(AppType(dP12.type1, dP22.type1), AppType(dP12.type2, dP22.type2), dP12, dP22))
        
        
        case _ => (ReflDerivation(prd1.type2), ReflDerivation(prd2.type2))
  }.ensuring(res => res._1.type1 == prd1.type2 &&
                    res._2.type1 == prd2.type2 &&
                    res._1.type2 == res._2.type2 &&
                    res._1.isParallelReduction && res._2.isParallelReduction)
  // sealed trait MultiStepParallelReduction{
  //   def type1: Type = {
  //     this match{
  //       case SimpleStepDerivation(ssr) => ssr.type1
  //       case TransitiveStepDerivation(t1, _, _, _) => t1
  //     }
  //   }

  //   def type2: Type = {
  //     this match{
  //       case SimpleStepDerivation(ssr) => ssr.type2
  //       case TransitiveStepDerivation(_, t2, _, _) => t2
  //     }
  //   }

  //   def isValid: Boolean = {
  //     this match{
  //       case SimpleStepDerivation(strd) => strd.isValid
  //       case TransitiveStepDerivation(t1, t2, strd1, strd2) => 
  //         t1 == strd1.type1 && t2 == strd2.type2 && strd1.type2 == strd2.type1 &&
  //         strd1.isValid && strd2.isValid
  //     }
  //   }

  // }
  // case class SimpleStepDerivation(prd: TypeToTypeDerivation) extends MultiStepParallelReduction
  // case class TransitiveStepDerivation(t1: Type, t2: Type, strd1: MultiStepParallelReduction, strd2: MultiStepParallelReduction) extends MultiStepParallelReduction
  
  sealed trait DetReductionDerivation{
    def type1: Type = {
      this match{
        case DetArrow1Derivation(t1, _, _) => t1
        case DetArrow2Derivation(t1, _, _) => t1
        case DetApp1Derivation(t1, _, _) => t1
        case DetApp2Derivation(t1, _, _) => t1
        case DetBetaDerivation(t1, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case DetArrow1Derivation(_, t2, _) => t2
        case DetArrow2Derivation(_, t2, _) => t2
        case DetApp1Derivation(_, t2, _) => t2
        case DetApp2Derivation(_, t2, _) => t2
        case DetBetaDerivation(_, t2) => t2
      }
    }

    def isValid: Boolean = {
      this match {
        case DetArrow1Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1) =>
          prd1.isValid && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetArrow2Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd2) =>
          prd2.isValid && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
        case DetApp1Derivation(AppType(t11, t12), AppType(t21, t22), prd1) =>
          prd1.isValid && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetApp2Derivation(AppType(t11, t12), AppType(t21, t22), prd2) =>
          prd2.isValid && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
        case DetBetaDerivation(AppType(AbsType(argK, body), t12), t3) => t3 == absSubstitution(body, t12) 
        case _ => false
      }
    }
  }
  case class DetArrow1Derivation(t1: ArrowType, t2: ArrowType, prd1: DetReductionDerivation) extends DetReductionDerivation
  case class DetArrow2Derivation(t1: ArrowType, t2: ArrowType, prd2: DetReductionDerivation) extends DetReductionDerivation
  case class DetApp1Derivation(t1: AppType, t2: AppType, prd1: DetReductionDerivation) extends DetReductionDerivation
  case class DetApp2Derivation(t1: AppType, t2: AppType, prd2: DetReductionDerivation) extends DetReductionDerivation
  case class DetBetaDerivation(t1: AppType, t2: Type) extends DetReductionDerivation

  def detReducesTo(t1: Type, t2: Type): Option[DetReductionDerivation] = {
    decreases(t1.size + t2.size)
    (t1, t2) match{
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => Some(DetArrow1Derivation(at1, at2, prd1))
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => Some(DetArrow2Derivation(at1, at2, prd2))
              case _ => None()
            }
        }
      case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => Some(DetBetaDerivation(at1, t3))
      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => Some(DetApp1Derivation(at1, at2, prd1))
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => Some(DetApp2Derivation(at1, at2, prd2))
              case _ => None()
            }
        }
      case (_, _) => None()
      }
    }
  
  def detReduce(t: Type): Option[DetReductionDerivation] = {
    t match{
      case at@ArrowType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => Some(DetArrow1Derivation(at, ArrowType(prd1.type2, t12), prd1))
          case _ => detReduce(t12) match{
            case Some(prd2) => Some(DetArrow2Derivation(at, ArrowType(t11, prd2.type2), prd2))
            case _ => None()
          }
        }
      case (at@AppType(t11, t12)) =>
        detReduce(t11) match {
          case Some(prd1) => Some(DetApp1Derivation(at, AppType(prd1.type2, t12), prd1))
          case _ => detReduce(t12) match {
            case Some(prd2) => Some(DetApp2Derivation(at, AppType(t11, prd2.type2), prd2))
            case _ => t11 match {
              case AbsType(argK, body) => Some(DetBetaDerivation(at, absSubstitution(body, t12)))
              case _ => None()
            }
          }
        }
      case _ => None()
    }
  }

  def detReducesToSoundness(t1: Type, t2: Type): Unit = {
    require(detReducesTo(t1, t2).isDefined)
    decreases(t1.size + t2.size)
    (t1, t2) match{
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => detReducesToSoundness(t11, t21)
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => detReducesToSoundness(t12, t22)
              case _ => ()
            }
        }
      case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => ()
      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) =>
        detReducesTo(t11, t21) match {
          case Some(prd1) if t12 == t22 => detReducesToSoundness(t11, t21)
          case _ => 
            detReducesTo(t12, t22) match {
              case Some(prd2) if t11 == t21 => detReducesToSoundness(t12, t22)
              case _ => ()
            }
        }
      case (_, _) => ()
    }
  }.ensuring(_ => detReducesTo(t1, t2).get.isValid)

  def detReducesToCompleteness(drd: DetReductionDerivation): Unit = {
    require(drd.isValid)
    drd match {
      case DetArrow1Derivation(ArrowType(t11, t12), ArrowType(t21, t22), drd1) =>
        detReducesToCompleteness(drd1)
      case DetArrow2Derivation(ArrowType(t11, t12), ArrowType(t21, t22), drd2) =>
        detReducesToCompleteness(drd2)
      case DetApp1Derivation(AppType(t11, t12), AppType(t21, t22), drd1) =>
        detReducesToCompleteness(drd1)
      case DetApp2Derivation(AppType(t11, t12), AppType(t21, t22), drd2) =>
        detReducesToCompleteness(drd2)
      case DetBetaDerivation(AppType(AbsType(argK, body), t12), t3) => ()
      case _ => ()
    }
  }.ensuring(_ => detReducesTo(drd.type1, drd.type2).isDefined)

  def detReduceSoundness(t: Type): Unit = {
    require(detReduce(t).isDefined)
    t match{
      case at@ArrowType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReduceSoundness(t11)
          case _ => detReduce(t12) match{
            case Some(prd2) => detReduceSoundness(t12)
            case None() => ()
          }
        }
      case at@AppType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReduceSoundness(t11)
          case _ => detReduce(t12) match {
            case Some(prd2) => detReduceSoundness(t12)
            case _ => t11 match {
              case AbsType(argK, body) => ()
              case _ => ()
            }
          }
        }
      case _ => ()
      }
  }.ensuring(_ => detReduce(t).get.isValid)

  def detReducesToReduce(t: Type): Unit = {
    require(detReduce(t).isDefined)
    t match{
      case at@ArrowType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReducesToReduce(t11)
          case _ => detReduce(t12) match{
            case Some(prd2) => 
              detReducesToReduce(t12)
            case None() => () 
          }
        }
      case at@AppType(t11, t12) =>
        detReduce(t11) match {
          case Some(prd1) => detReducesToReduce(t11)
          case _ => detReduce(t12) match {
            case Some(prd2) => detReducesToReduce(t12)
            case _ => t11 match {
                case AbsType(argK, body) => ()
                case _ => ()
            }
          }
        }
      case _ => ()
      }
  }.ensuring(_ => detReducesTo(t, detReduce(t).get.type2).isDefined)

  // def reduceSubst(td: TypeToTypeDerivation, j: BigInt, sd: TypeToTypeDerivation): TypeToTypeDerivation = {
  //   require(td.isParallelReduction)
  //   require(sd.isParallelReduction)
    
  //   td match
  //     case ReflDerivation(t) =>


  //   td.type1 match
  //     case bt@BasicType(_) => ReflDerivation(bt)
  //     case AbsType(k, body) => 
  //       val bodyDeriv = reduceSubst()
  //       AbsDerivation(AbsType(k, substitute(body, j, sd.type1)), )
  //     case _ => ReflDerivation(td.type1)

  // }.ensuring(res =>
  //   res.isParallelReduction &&
  //   res.type1 == substitute(td.type1, j, sd.type1)
  //   res.type2 == substitute(td.type2, j, sd.type2))


  // def properNormalFormsAreEquivalent(eq: TypeToTypeDerivation){
  //   require(eq.isValid)
  //   require(deriveKind(eq).isDefined)
  //   require(deriveKind().isDefined)
  // }

  sealed trait DetMultiStepReductionDerivation{

    def type1: Type = {
      this match{
        case DetReflDerivation(t) => t
        case DetSingleStepDerivation(rd) => rd.type1
        case DetTransDerivation(t1, _, _, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case DetReflDerivation(t) => t
        case DetSingleStepDerivation(rd) => rd.type2
        case DetTransDerivation(_, t2, _, _) => t2
      }
    }

    def isValid: Boolean = {
      this match{
        case DetReflDerivation(_) => true
        case DetSingleStepDerivation(rd) => rd.isValid
        case DetTransDerivation(t1, t2, rd1, rd2) => 
          t1 == rd1.type1 && t2 == rd2.type2 && rd1.type2 == rd2.type1 &&
          rd1.isValid && rd2.isValid
      }
    }

  }

  case class DetReflDerivation(t: Type) extends DetMultiStepReductionDerivation
  case class DetSingleStepDerivation(rd: DetReductionDerivation) extends DetMultiStepReductionDerivation
  case class DetTransDerivation(t1: Type, t2: Type, rd1: DetMultiStepReductionDerivation, rd2: DetMultiStepReductionDerivation) extends DetMultiStepReductionDerivation

  // def detMultiStepReduce(t: Type): DetMultiStepReductionDerivation = {
  //   detReduce(t) match {
  //     case Some(ssd) => 
  //       val msd = detMultiStepReduce(ssd.type2)
  //       DetTransDerivation(ssd.type1, msd.type2, DetSingleStepDerivation(ssd), msd) 
  //     case None() => DetReflDerivation(t)
  //   }
  // }

  // def detMultiStepReduceSoundness(t: Type): Unit = {
  //   detReduce(t) match {
  //     case Some(ssd) => detMultiStepReduceSoundness(ssd.type2)
  //     case None() => ()
  //   }
  // }.ensuring(detMultiStepReduce(t).isValid)


  }
