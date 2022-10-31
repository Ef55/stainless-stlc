

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

    def isSound: Boolean = {
      this match {
        case DetArrow1Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd1) =>
          prd1.isSound && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetArrow2Derivation(ArrowType(t11, t12), ArrowType(t21, t22), prd2) =>
          prd2.isSound && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
        case DetApp1Derivation(AppType(t11, t12), AppType(t21, t22), prd1) =>
          prd1.isSound && prd1.type1 == t11 && prd1.type2 == t21 && t12 == t22
        case DetApp2Derivation(AppType(t11, t12), AppType(t21, t22), prd2) =>
          prd2.isSound && prd2.type1 == t12 && prd2.type2 == t22 && t11 == t21
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
  }.ensuring(_ => detReducesTo(t1, t2).get.isSound)

  @opaque @pure
  def detReducesToCompleteness(drd: DetReductionDerivation): Unit = {
    require(drd.isSound)
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

  @opaque @pure
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
  }.ensuring(_ => detReduce(t).get.isSound)

  @opaque @pure
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

  // def reduceSubst(td: ParallelReductionDerivation, j: BigInt, sd: ParallelReductionDerivation): ParallelReductionDerivation = {
  //   require(td.isSound)
  //   require(sd.isSound)
    
  //   td match
  //     case ReflDerivation(t) =>


  //   td.type1 match
  //     case bt@BasicType(_) => ReflDerivation(bt)
  //     case AbsType(k, body) => 
  //       val bodyDeriv = reduceSubst()
  //       AbsDerivation(AbsType(k, substitute(body, j, sd.type1)), )
  //     case _ => ReflDerivation(td.type1)

  // }.ensuring(res =>
  //   res.isSound &&
  //   res.type1 == substitute(td.type1, j, sd.type1)
  //   res.type2 == substitute(td.type2, j, sd.type2))


  // def properNormalFormsAreEquivalent(eq: ParallelReductionDerivation){
  //   require(eq.isSound)
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

    def isSound: Boolean = {
      this match{
        case DetReflDerivation(_) => true
        case DetSingleStepDerivation(rd) => rd.isSound
        case DetTransDerivation(t1, t2, rd1, rd2) => 
          t1 == rd1.type1 && t2 == rd2.type2 && rd1.type2 == rd2.type1 &&
          rd1.isSound && rd2.isSound
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
  // }.ensuring(detMultiStepReduce(t).isSound)


  }
