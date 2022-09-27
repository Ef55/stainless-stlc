import stainless.lang._
import stainless.collection._
import stainless.annotation._

object LambdaOmega {

  sealed trait Type{
    def size: BigInt = {
      this match{
        case BasicType(_) => BigInt(1)
        case AppType(t1, t2) => t1.size + t2.size
      }
    }.ensuring(_ > BigInt(0))
  }
  case class BasicType(s: String) extends Type
  case class AppType(t1: Type, t2: Type) extends Type


  sealed trait ParallelReductionDerivation{

    def isValid: Boolean = {
      this match {
        case ReflDerivation(_) => true
        case AppDerivation(AppType(t11, t12), AppType(t21, t22), prd1, prd2) =>
          prd1.isValid && prd2.isValid && t12.size == BigInt(1)
        case AppAbsDerivation(t11, t3) => t11.t2.size == BigInt(1)
        case _ => false
      }
    }
  }
  case class ReflDerivation(t: Type) extends ParallelReductionDerivation
  case class AppDerivation(t1: AppType, t2: AppType, prd1: ParallelReductionDerivation, prd2: ParallelReductionDerivation) extends ParallelReductionDerivation
  case class AppAbsDerivation(t1: AppType, t2: Type) extends ParallelReductionDerivation

    def reducesToCompleteness(prd: ParallelReductionDerivation): Unit = {
      require(prd.isValid)
      prd match{
        case ReflDerivation(t) => ()
        case AppDerivation(AppType(_, t12), AppType(_, _), prd1, prd2) =>
          assert(t12.size == BigInt(1))
          reducesToCompleteness(prd1)
          reducesToCompleteness(prd2)
        case AppAbsDerivation(t11, t3) => assert(t11.t2.size == BigInt(1))
        case _ => ()
      }
    }.ensuring(_ => false)

  }