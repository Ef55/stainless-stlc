import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Reduction {
  import STLC._
  import Transformations._
  import TransformationsProperties._

  // ↑⁻¹( [0 -> ↑¹(arg)]body )
  def absSubsitution(body: Term, arg: Term): Term = {
    assert(!arg.hasFreeVariablesIn(0, 0))
    boundRangeShift(arg, 1, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    boundRangeShiftBackLemma(substitute(body, 0, shift(arg, 1, 0)), 1, 0)
    shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
  }

  // ↑⁻¹( [0 -> ↑¹(arg)]body )
  def absSubstitution(body: Type, arg: Type): Type = {
    assert(!arg.hasFreeVariablesIn(0, 0))
    boundRangeShift(arg, 1, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    boundRangeShiftBackLemma(substitute(body, 0, shift(arg, 1, 0)), 1, 0)
    shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
  }

  def tabsSubstitution(body: Term, arg: Type): Term = {
    assert(!arg.hasFreeVariablesIn(0, 0))
    boundRangeShift(arg, 1, 0, 0)
    boundTypeRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    boundTypeRangeShiftBackLemma(substitute(body, 0, shift(arg, 1, 0)), 1, 0)
    typesShift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
  }

  /// General lambda calculus evaluation

  // [t -> t']
  def reducesTo(t: Term, tp: Term): Boolean = {
    t match {
      case Var(_) => false
      case Abs(_, _) => false
      case App(t1, t2) => {
        (tp match {
          case App(t1p, t2p) if reducesTo(t1, t1p) && t2 == t2p  => true
          case App(t1p, t2p) if t1 == t1p && reducesTo(t2, t2p) => true
          case _ => false
        }) || (t1 match {
          case Abs(_, body) => absSubsitution(body, t2) == tp
          case _ => false
        })
      }
      case Fix(f) => {
        (tp match {
          case Fix(fp) => reducesTo(f, fp)
          case _ => false
        }) || (f match {
          case Abs(_, body) => absSubsitution(body, t) == tp
          case _ => false
        })
      }
      case TAbs(body) => false
      case TApp(term, typ) => {
        (tp match {
          case TApp(termp, typp) => reducesTo(term, termp) && typ == typp
          case _ => false
        }) || (term match {
          case TAbs(body) => tabsSubstitution(body, typ) == tp
          case _ => false
        })
      }
    }
  }

  // { t' | t -> t' }
  def reduceAll(t: Term): Set[Term] = {
    t match {
      case Var(_) => Set[Term]()
      case Abs(_, _) => Set[Term]()
      case App(t1, t2) => {
        reduceAll(t1).map[Term](t1p => App(t1p, t2)) ++ 
          reduceAll(t2).map[Term](t2p => App(t1, t2p)) ++ 
          (t1 match {
            case Abs(_, body) => Set[Term](absSubsitution(body, t2))
            case _ => Set[Term]()
          })
      }
      case Fix(f) => {
        f match {
          case Abs(_, body) => reduceAll(f).map[Term](Fix(_)) + absSubsitution(body, t)
          case _ => reduceAll(f).map(Fix(_))
        }
      }
      case TAbs(body) => Set[Term]()
      case TApp(term, typ) => {
        reduceAll(term).map[Term](TApp(_, typ)) ++
          (term match {
            case TAbs(body) => Set[Term](tabsSubstitution(body, typ))
            case _ => Set[Term]()
          })
      }
    }
  }

  /// Call-by-value lambda calculus evaluation

  def reduceCallByValue(t: Term): Option[Term] = {
    t match {
      case Var(_) => None[Term]()
      case Abs(_, _) => None[Term]()
      case App(t1, t2) => {
        if(!t1.isValue) {
          reduceCallByValue(t1).map(t1p => App(t1p, t2))
        }
        else if(!t2.isValue) {
          reduceCallByValue(t2).map(t2p => App(t1, t2p))
        }
        else {
          t1 match {
            case Abs(_, body) => {
              Some(absSubsitution(body, t2))
            }
            case _ => None[Term]()
          }
        }
      }
      case Fix(f) => {
        if(!f.isValue) {
          reduceCallByValue(f).map(Fix(_))
        }
        else {
          f match {
            case Abs(_, body) => {
              Some(absSubsitution(body, t))
            }
            case _ => None[Term]()
          }
        }
      }
      case TAbs(body) => None[Term]()
      case TApp(term, typ) => {
        if(!term.isValue) {
          reduceCallByValue(term).map[Term](TApp(_, typ))
        }
        else {
          term match {
            case TAbs(body) => Some(tabsSubstitution(body, typ))
            case _ => None[Term]()
          }
        }
      }
    }
  }

}

object ReductionProperties {
  import STLC._
  import Reduction._

  /// ReduceAll correctness

  @opaque @pure
  def reduceAllCompleteness(t: Term, tp: Term): Unit = {
    require(reducesTo(t, tp))

    t match {
      case Var(_) => assert(reduceAll(t).contains(tp))
      case Abs(_, _) => assert(reduceAll(t).contains(tp))
      case App(t1, t2) => {
        tp match {
          case App(t1p, t2p) if reducesTo(t1, t1p) && t2 == t2p  => {
            reduceAllCompleteness(t1, t1p)
            reduceAll(t1).mapPost1[Term](t1p => App(t1p, t2))(t1p)
          }
          case App(t1p, t2p) if t1 == t1p && reducesTo(t2, t2p) => {
            reduceAllCompleteness(t2, t2p)
            reduceAll(t2).mapPost1[Term](t2p => App(t1, t2p))(t2p)
          }
          case _ => assert(reduceAll(t).contains(tp))
        }
      }
      case Fix(f) => {
        tp match {
          case Fix(fp) if reducesTo(f, fp) => {
            reduceAllCompleteness(f, fp)
            reduceAll(f).mapPost1[Term](Fix(_))(fp)
          }
          case _ => assert(reduceAll(t).contains(tp))
        }
      }
      case TAbs(body) => assert(reducesTo(t, tp))
      case TApp(term, typ) => {
        tp match {
          case TApp(termp, typp) if reducesTo(term, termp) && typ == typp => {
            reduceAllCompleteness(term, termp)
            reduceAll(term).mapPost1[Term](TApp(_, typ))(termp)
          }
          case _ => assert(reduceAll(t).contains(tp))
        }
      }
    }
  }.ensuring(reduceAll(t).contains(tp))

  @opaque @pure
  def reduceAllSoundness(t: Term, tp: Term): Unit = {
    require(reduceAll(t).contains(tp))
    t match {
      case Var(_) => assert(reducesTo(t, tp))
      case Abs(_, _) => assert(reducesTo(t, tp))
      case App(t1, t2) => {
        if(reduceAll(t1).map[Term](t1p => App(t1p, t2)).contains(tp)) {
          val App(t1p, t2p) = tp
          reduceAll(t1).mapPost2[Term](t1p => App(t1p, t2))(tp)
          reduceAllSoundness(t1, t1p)
        }
        else if(reduceAll(t2).map[Term](t2p => App(t1, t2p)).contains(tp)) {
          val App(t1p, t2p) = tp
          reduceAll(t2).mapPost2[Term](t2p => App(t1, t2p))(tp)
          reduceAllSoundness(t2, t2p)
        }
        else {
          assert(reducesTo(t, tp))
        }
      }
      case Fix(f) => {
        if(reduceAll(f).map[Term](Fix(_)).contains(tp)) {
          val Fix(fp) = tp
          reduceAll(f).mapPost2[Term](Fix(_))(tp)
          reduceAllSoundness(f, fp)
        }
        else {
          assert(reducesTo(t, tp))
        }
      }
      case TAbs(body) => assert(reducesTo(t, tp))
      case TApp(term, typ) => {
        if(reduceAll(term).map[Term](TApp(_, typ)).contains(tp)) {
          val TApp(termp, typp) = tp
          reduceAll(term).mapPost2[Term](TApp(_, typ))(tp)
          reduceAllSoundness(term, termp)
        }
        else {
          assert(reducesTo(t, tp))
        }
      }
    }
  }.ensuring(reducesTo(t, tp))

  /// Call-by-value soudness

  @opaque @pure
  def reduceCallByValueSoundness(t: Term): Unit = {
    require(reduceCallByValue(t).isDefined)
    val tp = reduceCallByValue(t).get

    t match {
      case Var(_) => assert(false)
      case Abs(_, _) => assert(false)
      case App(t1, t2) => {
        if(!t1.isValue) {
          reduceCallByValueSoundness(t1)
        }
        else if(!t2.isValue) {
          reduceCallByValueSoundness(t2)
        }
        else {
          assert(reducesTo(t, tp))
        }
      }
      case Fix(f) => {
        if(!f.isValue) {
          reduceCallByValueSoundness(f)
        }
        else {
          assert(reducesTo(t, tp))
        }
      }
      case TAbs(_) => assert(false)
      case TApp(term, typ) => {
        if(!term.isValue) {
          reduceCallByValueSoundness(term)
        }
        else {
          assert(reducesTo(t, tp))
        }
      }
    }

  }.ensuring(reducesTo(t, reduceCallByValue(t).get))
}