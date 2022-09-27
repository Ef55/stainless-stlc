import stainless.lang._
import stainless.collection._
import stainless.annotation._
import LambdaOmega._
import Transformations.Types._

object TypeEquivalence{



  sealed trait EquivalenceDerivation{
    def type1: Type = {
      this match{
        case ReflEqDerivation(t) => t 
        case SymmEqDerivation(t1, _, _) => t1
        case TransEqDerivation(t1, _, _, _) => t1
        case ArrowEqDerivation(t1, _, _, _) => t1
        case AbsEqDerivation(t1, _, _) => t1
        case AppEqDerivation(t1, _, _, _) => t1
        case AppAbsEqDerivation(t1, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case ReflEqDerivation(t) => t 
        case SymmEqDerivation(_, t2, _) => t2
        case TransEqDerivation(_, t2, _, _) => t2
        case ArrowEqDerivation(_, t2, _, _) => t2
        case AbsEqDerivation(_, t2, _) => t2
        case AppEqDerivation(_, t2, _, _) => t2
        case AppAbsEqDerivation(_, t2) => t2
      }
    }

    def isValid: Boolean = {
      this match {
        case ReflEqDerivation(_) => true
        case SymmEqDerivation(t1, t2, ed) => ed.isValid && ed.type1 == t2 && ed.type2 == t1
        case TransEqDerivation(t1, t2, ed1, ed2) => 
          ed1.isValid && ed2.isValid && ed1.type1 == t1 &&
          ed2.type2 == t2 && ed1.type2 == ed2.type1
        case ArrowEqDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ed1, ed2) =>
          ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
          ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
        case AbsEqDerivation(AbsType(k1, b1), AbsType(k2, b2), ed) => 
          ed.isValid && ed.type1 == b1 && ed.type2 == b2 && k1 == k2
        case AppEqDerivation(AppType(t11, t12), AppType(t21, t22), ed1, ed2) =>
          ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
          ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
        case AppAbsEqDerivation(AppType(AbsType(argK, body), t2), t3) =>
          t3 == absSubstitution(body, t2) 
        case AppAbsEqDerivation(_, _) => false
      }
    }

 
  }
  case class ReflEqDerivation(t: Type) extends EquivalenceDerivation
  case class SymmEqDerivation(t1: Type, t2: Type, ed: EquivalenceDerivation) extends EquivalenceDerivation
  case class TransEqDerivation(t1: Type, t2: Type, ed1: EquivalenceDerivation, ed2: EquivalenceDerivation) extends EquivalenceDerivation
  case class ArrowEqDerivation(t1: ArrowType, t2: ArrowType, ed1: EquivalenceDerivation, ed2: EquivalenceDerivation) extends EquivalenceDerivation
  case class AbsEqDerivation(t1: AbsType, t2: AbsType, ed: EquivalenceDerivation) extends EquivalenceDerivation
  case class AppEqDerivation(t1: AppType, t2: AppType, ed: EquivalenceDerivation, ed2: EquivalenceDerivation) extends EquivalenceDerivation
  case class AppAbsEqDerivation(t1: AppType, t2: Type) extends EquivalenceDerivation

//   sealed trait EquivalenceWithoutTransDerivation{
//     def type1: Type = {
//       this match{
//         case ReflEqWTDerivation(t) => t 
//         case SymmEqWTDerivation(t1, _, _) => t1
//         case ArrowEqWTDerivation(t1, _, _, _) => t1
//         case AbsEqWTDerivation(t1, _, _) => t1
//         case AppEqWTDerivation(t1, _, _, _) => t1
//         case AppAbsEqWTDerivation(t1, _) => t1
//       }
//     }

//     def type2: Type = {
//       this match{
//         case ReflEqWTDerivation(t) => t 
//         case SymmEqWTDerivation(_, t2, _) => t2
//         case ArrowEqWTDerivation(_, t2, _, _) => t2
//         case AbsEqWTDerivation(_, t2, _) => t2
//         case AppEqWTDerivation(_, t2, _, _) => t2
//         case AppAbsEqWTDerivation(_, t2) => t2
//       }
//     }

//     def isValid: Boolean = {
//       this match {
//         case ReflEqWTDerivation(_) => true
//         case SymmEqWTDerivation(t1, t2, ed) => ed.isValid && ed.type1 == t2 && ed.type2 == t1
//         case ArrowEqWTDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ed1, ed2) =>
//           ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
//           ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
//         case AbsEqWTDerivation(AbsType(k1, b1), AbsType(k2, b2), ed) => 
//           ed.isValid && ed.type1 == b1 && ed.type2 == b2 && k1 == k2
//         case AppEqWTDerivation(AppType(t11, t12), AppType(t21, t22), ed1, ed2) =>
//           ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
//           ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
//         case AppAbsEqWTDerivation(AppType(AbsType(argK, body), t2), t3) =>
//           t3 == absSubstitution(body, t2) 
//         case AppAbsEqWTDerivation(_, _) => false
//       }
//     }
//   }
//   case class ReflEqWTDerivation(t: Type) extends EquivalenceWithoutTransDerivation
//   case class SymmEqWTDerivation(t1: Type, t2: Type, ed: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class ArrowEqWTDerivation(t1: ArrowType, t2: ArrowType, ed1: EquivalenceWithoutTransDerivation, ed2: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class AbsEqWTDerivation(t1: AbsType, t2: AbsType, ed: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class AppEqWTDerivation(t1: AppType, t2: AppType, ed: EquivalenceWithoutTransDerivation, ed2: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class AppAbsEqWTDerivation(t1: AppType, t2: Type) extends EquivalenceWithoutTransDerivation

//   sealed trait EquivalenceTransUpDerivation{
//     def type1: Type = {
//       this match{
//         case SimpleEqDerivation(ed) => ed.type1
//         case TransUpEqDerivation(t1, _, _, _) => t1
//       }
//     }

//     def type2: Type = {
//       this match{
//         case SimpleEqDerivation(ed) => ed.type2
//         case TransUpEqDerivation(_, t2, _, _) => t2
//       }
//     }

//     def isValid: Boolean = {
//       this match{
//         case SimpleEqDerivation(ed) => ed.isValid
//         case TransUpEqDerivation(t1, t2, ed1, ed2) => 
//           t1 == ed1.type1 && t2 == ed2.type2 && ed1.type2 == ed2.type1 &&
//           ed1.isValid && ed2.isValid
//       }
//     }

//   }
//   case class SimpleEqDerivation(ed: EquivalenceWithoutTransDerivation) extends EquivalenceTransUpDerivation
//   case class TransUpEqDerivation(t1: Type, t2: Type, ed1: EquivalenceTransUpDerivation, ed2: EquivalenceTransUpDerivation) extends EquivalenceTransUpDerivation

 }

object TypeReduction{

  sealed trait ParallelReductionDerivation{
    def type1: Type = {
      this match{
        case ReflDerivation(t) => t 
        case ArrowDerivation(t1, _, _, _) => t1
        case AbsDerivation(t1, _, _) => t1
        case AppDerivation(t1, _, _, _) => t1
        case AppAbsDerivation(t1, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case ReflDerivation(t) => t 
        case ArrowDerivation(_, t2, _, _) => t2
        case AbsDerivation(_, t2, _) => t2
        case AppDerivation(_, t2, _, _) => t2
        case AppAbsDerivation(_, t2) => t2
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
        case AppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => t3 == absSubstitution(body, t12) 
        case _ => false
      }
    }
  }
  case class ReflDerivation(t: Type) extends ParallelReductionDerivation
  case class ArrowDerivation(t1: ArrowType, t2: ArrowType, prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AbsDerivation(t1: AbsType, t2: AbsType, prd: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppDerivation(t1: AppType, t2: AppType, prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppAbsDerivation(t1: AppType, t2: Type) extends ParallelReductionDerivation

  def reducesTo(t1: Type, t2: Type): Option[ParallelReductionDerivation] = {
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
    }.ensuring(_ => reducesTo(t1, t2).get.isValid)

    def reducesToCompleteness(prd: ParallelReductionDerivation): Unit = {
      require(prd.isValid)
      prd match{
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
      }
    }.ensuring(_ => reducesTo(prd.type1, prd.type2).isDefined)

    sealed trait MultiStepParallelReduction{
      def type1: Type = {
        this match{
          case SimpleStepDerivation(ssr) => ssr.type1
          case TransitiveStepDerivation(t1, _, _, _) => t1
        }
      }

      def type2: Type = {
        this match{
          case SimpleStepDerivation(ssr) => ssr.type2
          case TransitiveStepDerivation(_, t2, _, _) => t2
        }
      }

      def isValid: Boolean = {
        this match{
          case SimpleStepDerivation(strd) => strd.isValid
          case TransitiveStepDerivation(t1, t2, strd1, strd2) => 
            t1 == strd1.type1 && t2 == strd2.type2 && strd1.type2 == strd2.type1 &&
            strd1.isValid && strd2.isValid
        }
      }

    }
    case class SimpleStepDerivation(prd: ParallelReductionDerivation) extends MultiStepParallelReduction
    case class TransitiveStepDerivation(t1: Type, t2: Type, strd1: MultiStepParallelReduction, strd2: MultiStepParallelReduction) extends MultiStepParallelReduction
  
sealed trait DetReductionDerivation{
    def type1: Type = {
      this match{
        case DetArrow1Derivation(t1, _, _) => t1
        case DetArrow2Derivation(t1, _, _) => t1
        case DetAbsDerivation(t1, _, _) => t1
        case DetApp1Derivation(t1, _, _) => t1
        case DetApp2Derivation(t1, _, _) => t1
        case DetAppAbsDerivation(t1, _) => t1
      }
    }

    def type2: Type = {
      this match{
        case DetArrow1Derivation(_, t2, _) => t2
        case DetArrow2Derivation(_, t2, _) => t2
        case DetAbsDerivation(_, t2, _) => t2
        case DetApp1Derivation(_, t2, _) => t2
        case DetApp2Derivation(_, t2, _) => t2
        case DetAppAbsDerivation(_, t2) => t2
      }
    }

    def isValid: Boolean = {
      this match {
        case DetArrow1Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1) =>
          prd1.isValid && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetArrow2Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd2) =>
          prd2.isValid && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
        case DetAbsDerivation(AbsType(k1, b1), AbsType(k2, b2), prd) => 
          prd.isValid && prd.type1 == b1 && prd.type2 == b2 && k1 == k2
        case DetApp1Derivation(AppType(t11, t12), AppType(t21, t22), prd1) =>
          prd1.isValid && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetApp2Derivation(AppType(t11, t12), AppType(t21, t22), prd2) =>
          prd2.isValid && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
        case DetAppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => t3 == absSubstitution(body, t12) 
        case _ => false
      }
    }
  }
  case class DetArrow1Derivation(t1: ArrowType, t2: ArrowType, prd1: DetReductionDerivation) extends DetReductionDerivation
  case class DetArrow2Derivation(t1: ArrowType, t2: ArrowType, prd2: DetReductionDerivation) extends DetReductionDerivation
  case class DetAbsDerivation(t1: AbsType, t2: AbsType, prd: DetReductionDerivation) extends DetReductionDerivation
  case class DetApp1Derivation(t1: AppType, t2: AppType, prd1: DetReductionDerivation) extends DetReductionDerivation
  case class DetApp2Derivation(t1: AppType, t2: AppType, prd2: DetReductionDerivation) extends DetReductionDerivation
  case class DetAppAbsDerivation(t1: AppType, t2: Type) extends DetReductionDerivation

  def detReducesTo(t1: Type, t2: Type): Option[DetReductionDerivation] = {
    decreases(t1.size + t2.size)
    (t1, t2) match{
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) if t12 == t22 =>
        detReducesTo(t11, t21) match {
          case Some(prd1) => Some(DetArrow1Derivation(at1, at2, prd1))
          case _ => None()
        }
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) if t11 == t21 =>
        detReducesTo(t12, t22) match {
          case Some(prd2) => Some(DetArrow2Derivation(at1, at2, prd2))
          case _ => None()
        }
      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) if t12 == t22 =>
        detReducesTo(t11, t21) match {
          case Some(prd1) => Some(DetApp1Derivation(at1, at2, prd1))
          case _ => None()
        }
      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) if t11 == t21 =>
        detReducesTo(t12, t22) match {
          case Some(prd2) => Some(DetApp2Derivation(at1, at2, prd2))
          case _ => None()
        }
      case (at1@AbsType(k1, body1), at2@AbsType(k2, body2)) if k1 == k2 =>
          detReducesTo(body1, body2) match {
            case Some(prd) => Some(DetAbsDerivation(at1, at2, prd))
            case _ => None()
          }
      case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => Some(DetAppAbsDerivation(at1, t3))
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
            case _ => None()
          }
        }
      case (at@AbsType(k1, body1)) =>
        detReduce(body1) match {
          case Some(prd) => Some(DetAbsDerivation(at, AbsType(k1, prd.type2), prd))
          case _ => None()
        }
      case at@AppType(AbsType(argK, body), t12) => Some(DetAppAbsDerivation(at, absSubstitution(body, t12)))
      case _ => None()
    }
  }

  def detReducesToSoundness(t1: Type, t2: Type): Unit = {
    require(detReducesTo(t1, t2).isDefined)
    decreases(t1.size + t2.size)
    (t1, t2) match{
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) if t12 == t22 =>
        detReducesToSoundness(t11, t21)
      case (at1@ArrowType(t11, t12), at2@ArrowType(t21, t22)) if t11 == t21 =>
        detReducesToSoundness(t12, t22) 

      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) if t12 == t22 =>
        detReducesToSoundness(t11, t21) 
      case (at1@AppType(t11, t12), at2@AppType(t21, t22)) if t11 == t21 =>
        detReducesToSoundness(t12, t22) 
      case (at1@AbsType(k1, body1), at2@AbsType(k2, body2)) if k1 == k2 =>
        detReducesToSoundness(body1, body2) 
      case (at1@AppType(AbsType(argK, body), t12), t3) if t3 == absSubstitution(body, t12) => ()
      case (_, _) => ()
    }
  }.ensuring(_ => detReducesTo(t1, t2).get.isValid)

  // def detReducesToCompleteness(prd: ParallelReductionDerivation): Unit = {
  //   require(prd.isValid)
  //   prd match{
  //     case ReflDerivation(t) => ()
  //     case ArrowDerivation(ArrowType(_, _), ArrowType(_, _), prd1, prd2) =>
  //       detReducesToCompleteness(prd1)
  //       detReducesToCompleteness(prd2)
  //     case AbsDerivation(AbsType(_, _), AbsType(_, _), prd1) =>
  //       detReducesToCompleteness(prd1)
  //     case AppDerivation(AppType(_, _), AppType(_, _), prd1, prd2) =>
  //       reducesToCompleteness(prd1)
  //       reducesToCompleteness(prd2)
  //     case AppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => 
  //       assert(t3 == absSubstitution(body, t12))
  //       ()
  //     case _ => ()
  //   }
  // }.ensuring(_ => reducesTo(prd.type1, prd.type2).isDefined)

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
            case _ => ()
          }
        }
      case at@AbsType(k1, body1) =>
        detReduce(body1) match {
          case Some(prd) => detReduceSoundness(body1)
          case _ => ()
        }
      case AppType(AbsType(argK, body), t12) => ()
      case _ => ()
      }
  }.ensuring(_ => detReduce(t).get.isValid)

  def detReducesToCompleteness(prd: DetReductionDerivation): Unit = {
    require(prd.isValid)
    prd match{
      case ReflDerivation(t) => ()
      case ArrowDerivation(ArrowType(_, _), ArrowType(_, _), prd1, prd2) =>
        detReducesToCompleteness(prd1)
        detReducesToCompleteness(prd2)
      case AbsDerivation(AbsType(_, _), AbsType(_, _), prd1) =>
        detReducesToCompleteness(prd1)
      case AppDerivation(AppType(_, _), AppType(_, _), prd1, prd2) =>
        reducesToCompleteness(prd1)
        reducesToCompleteness(prd2)
      case AppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => 
        assert(t3 == absSubstitution(body, t12))
        ()
      case _ => ()
    }
  }.ensuring(_ => detReduce())

  // def reducesToCompleteness(prd: ParallelReductionDerivation): Unit = {
  //   require(prd.isValid)
  //   prd match{
  //     case ReflDerivation(t) => ()
  //     case ArrowDerivation(ArrowType(_, _), ArrowType(_, _), prd1, prd2) =>
  //       reducesToCompleteness(prd1)
  //       reducesToCompleteness(prd2)
  //     case AbsDerivation(AbsType(_, _), AbsType(_, _), prd1) =>
  //       reducesToCompleteness(prd1)
  //     case AppDerivation(AppType(_, _), AppType(_, _), prd1, prd2) =>
  //       reducesToCompleteness(prd1)
  //       reducesToCompleteness(prd2)
  //     case AppAbsDerivation(AppType(AbsType(argK, body), t12), t3) => 
  //       assert(t3 == absSubstitution(body, t12))
  //       ()
  //     case _ => ()
  //   }
  // }.ensuring(_ => reducesTo(prd.type1, prd.type2).isDefined)

  }
