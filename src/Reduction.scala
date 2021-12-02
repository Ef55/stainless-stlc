import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Reduction {

  import STLC._
  import ReductionProperties._

  /// Transformations on terms

  def negativeShiftValidity(t: Term, d: BigInt, c: BigInt): Boolean = {
    require(d < 0)
    t match {
      case Var(k)         => (k < c) || (k+d >= 0)
      case Abs(_, body)   => negativeShiftValidity(body, d, c+1)
      case App(t1, t2)    => negativeShiftValidity(t1, d, c) && negativeShiftValidity(t2, d, c)
      case Fix(f)         => negativeShiftValidity(f, d, c)
      case TAbs(body)     => negativeShiftValidity(body, d, c)
      case TApp(t, _)     => negativeShiftValidity(t, d, c)
    }
  }

  // ↑ᵈ_c(t)
  def shift(t: Term, d: BigInt, c: BigInt): Term = {
    require(d >= 0 || negativeShiftValidity(t, d, c))
    require(c >= 0)
    t match {
      case Var(k)    => if (k < c) Var(k) else Var(k + d)
      case Abs(typ, body) => Abs(typ, shift(body, d, c+1))
      case App(t1, t2)    => App(shift(t1, d, c), shift(t2, d, c))
      case Fix(f)         => Fix(shift(f, d, c))
      case TAbs(body)     => TAbs(shift(body, d, c))
      case TApp(t, typ)   => TApp(shift(t, d, c), typ)
    }
  }

  // [j -> s]t
  def substitute(t: Term, j: BigInt, s: Term): Term = {
    t match {
      case Var(k) => if (k == j) s else t 
      case Abs(typ, body) => Abs(typ, substitute(body, j+1, shift(s, 1, 0)))
      case App(t1, t2) => App(substitute(t1, j, s), substitute(t2, j, s))
      case Fix(f) => Fix(substitute(f, j, s))
      case TAbs(body) => TAbs(substitute(body, j, s))
      case TApp(t, typ) => TApp(substitute(t, j, s), typ)
    }
  }

  // ↑⁻¹( [0 -> ↑¹(arg)]body )
  def absSubsitution(body: Term, arg: Term): Term = {
    assert(!arg.hasFreeVariablesIn(0, 0))
    boundRangeShift(arg, 1, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    boundRangeShiftBackLemma(substitute(body, 0, shift(arg, 1, 0)), 1, 0)
    shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
  }

  /// Tranformations on types

  def negativeShiftValidity(t: Type, d: BigInt, c: BigInt): Boolean = {
    require(d < 0)
    t match {
      case BasicType(_) => true
      case ArrowType(t1, t2) =>  negativeShiftValidity(t1, d, c) && negativeShiftValidity(t2, d, c)
      case VariableType(k) => (k < c) || (k+d >= 0)
      case UniversalType(body) => negativeShiftValidity(body, d, c+1)
    }
  }

  def shift(t: Type, d: BigInt, c: BigInt): Type = {
    require(d >= 0 || negativeShiftValidity(t, d, c))
    require(c >= 0)
    t match {
      case BasicType(_) => t
      case ArrowType(t1, t2) => ArrowType(shift(t1, d, c), shift(t2, d, c))
      case VariableType(k) => if (k < c) VariableType(k) else VariableType(k + d)
      case UniversalType(body) => UniversalType(shift(body, d, c + 1))
    }
  }

  def substitute(t: Type, j: BigInt, s: Type): Type = {
    t match {
      case BasicType(_) => t
      case ArrowType(t1, t2) => ArrowType(substitute(t1, j, s), substitute(t2, j, s))
      case VariableType(k) => if(j == k) s else t  
      case UniversalType(b) => UniversalType(substitute(b, j + 1, shift(s, 1, 0)))
    }
  }

    // ↑⁻¹( [0 -> ↑¹(arg)]body )
  def absSubstitution(body: Type, arg: Type): Type = {
    assert(!arg.hasFreeVariablesIn(0, 0))
    boundRangeShift(arg, 1, 0, 0)
    boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
    boundRangeShiftBackLemma(substitute(body, 0, shift(arg, 1, 0)), 1, 0)
    shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
  }

  /// General lambda calculus evaluation

  // // [t -> t']
  // def reducesTo(t: Term, tp: Term): Boolean = {
  //   t match {
  //     case Var(_) => false
  //     case Abs(_, _) => false
  //     case App(t1, t2) => {
  //       (tp match {
  //         case App(t1p, t2p) if reducesTo(t1, t1p) && t2 == t2p  => true
  //         case App(t1p, t2p) if t1 == t1p && reducesTo(t2, t2p) => true
  //         case _ => false
  //       }) || (t1 match {
  //         case Abs(_, body) => absSubsitution(body, t2) == tp
  //         case _ => false
  //       })
  //     }
  //     case Fix(f) => {
  //       (tp match {
  //         case Fix(fp) => reducesTo(f, fp)
  //         case _ => false
  //       }) || (f match {
  //         case Abs(_, body) => absSubsitution(body, t) == tp
  //         case _ => false
  //       })
  //     }
  //   }
  // }

  // // { t' | t -> t' }
  // def reduceAll(t: Term): Set[Term] = {
  //   t match {
  //     case Var(_) => Set[Term]()
  //     case Abs(_, _) => Set[Term]()
  //     case App(t1, t2) => {
  //       reduceAll(t1).map[Term](t1p => App(t1p, t2)) ++ 
  //         reduceAll(t2).map[Term](t2p => App(t1, t2p)) ++ 
  //         (t1 match {
  //           case Abs(_, body) => Set[Term](absSubsitution(body, t2))
  //           case _ => Set[Term]()
  //         })
  //     }
  //     case Fix(f) => {
  //       f match {
  //         case Abs(_, body) => reduceAll(f).map[Term](Fix(_)) + absSubsitution(body, t)
  //         case _ => reduceAll(f).map(Fix(_))
  //       }
        
  //     }
  //   }
  // }

  // /// Call-by-value lambda calculus evaluation

  // def reduceCallByValue(t: Term): Option[Term] = {
  //   t match {
  //     case Var(_) => None[Term]()
  //     case Abs(_, _) => None[Term]()
  //     case App(t1, t2) => {
  //       if(!t1.isValue) {
  //         reduceCallByValue(t1).map(t1p => App(t1p, t2))
  //       }
  //       else if(!t2.isValue) {
  //         reduceCallByValue(t2).map(t2p => App(t1, t2p))
  //       }
  //       else {
  //         t1 match {
  //           case Abs(_, body) => {
  //             Some(absSubsitution(body, t2))
  //           }
  //           case _ => None[Term]()
  //         }
  //       }
  //     }
  //     case Fix(f) => {
  //       if(!f.isValue) {
  //         reduceCallByValue(f).map(Fix(_))
  //       }
  //       else {
  //         f match {
  //           case Abs(_, body) => {
  //             Some(absSubsitution(body, t))
  //           }
  //         }
  //       }
  //     }
  //   }
  // }

}

object ReductionProperties {
  import STLC._
  import Reduction._
  import STLCProperties._

  // Substitution & shifting lemmas on terms

  @opaque @pure
  def boundRangeShiftComposition(t: Term, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    require(a >= 0)
    require(c >= 0)
    require(d >= 0)
    require(d <= c + a)
    require(if(d < c) !t.hasFreeVariablesIn(d, c - d) else !t.hasFreeVariablesIn(c, d - c))
    require((b >= 0) || (-b <= a))


    if (d < c){
      boundRangeShift(t, a, c, 0)
      boundRangeShiftBelowCutoff(t, a, c, d, c - d)
      boundRangeConcatenation(shift(t, a, c), d, c - d, a)
      boundRangeDecrease(shift(t, a, c), d, c - d + a, a)
    }
    else{
      boundRangeShift(t, a, c, d - c)
      boundRangeIncreaseCutoff(shift(t, a, c), c, d, a + d - c)
    }

    assert(!shift(t, a, c).hasFreeVariablesIn(d, a))
    if(b < 0){
      boundRangeDecrease(shift(t, a, c), d, a, -b)
      boundRangeShiftBackLemma(shift(t, a, c), -b, d)        
    }
    else{
      ()
    }


    t match {
      case Var(k) => ()
      case Abs(targ, body) => {
        boundRangeShiftComposition(body, a, b, c + 1, d + 1)
      }
      case App(t1, t2) => {
        boundRangeShiftComposition(t1, a, b, c, d)
        boundRangeShiftComposition(t2, a, b, c, d)
      }
      case Fix(f) => {
        boundRangeShiftComposition(f, a, b, c, d)
      }
      case TAbs(body)     => {
        boundRangeShiftComposition(body, a, b, c, d)
      }
      case TApp(t, _)     => {
        boundRangeShiftComposition(t, a, b, c, d)
      }
    }
  }.ensuring(shift(shift(t, a, c), b, d) == shift(t, a + b, c))

  @opaque @pure
  def boundRangeShift(t: Term, d: BigInt, c: BigInt, b: BigInt): Unit = {
    require(c >= 0)
    require(d >= 0)
    require(b >= 0)
    require(!t.hasFreeVariablesIn(c, b))

    t match {
      case Var(_)    => assert(!shift(t, d, c).hasFreeVariablesIn(c, d+b))
      case Abs(_, body)   => {
        boundRangeShift(body, d, c+1, b)
        assert(!shift(t, d, c).hasFreeVariablesIn(c, d+b))
      }
      case App(t1, t2)    => {
        boundRangeShift(t1, d, c, b)
        boundRangeShift(t2, d, c, b)
        assert(!shift(t, d, c).hasFreeVariablesIn(c, d+b))
      }
      case Fix(f) => boundRangeShift(f, d, c, b)
      case TAbs(body)     => boundRangeShift(body, d, c, b)
      case TApp(t, _)     => boundRangeShift(t, d, c, b)
    }

  }.ensuring(!shift(t, d, c).hasFreeVariablesIn(c, d+b))

  @opaque @pure
  def boundRangeShiftBelowCutoff(t: Term, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
    require(d >= 0)
    require(c >= 0)
    require(a >= 0)
    require(b >= 0)
    require(a + b <= c)
    require(!t.hasFreeVariablesIn(a, b))
    t match {
      case Var(k) => ()
      case Abs(targ, body) => 
        boundRangeShiftBelowCutoff(body, d, c + 1, a + 1, b)
      case App(t1, t2) => {
        boundRangeShiftBelowCutoff(t1, d, c, a, b)
        boundRangeShiftBelowCutoff(t2, d, c, a, b)
      }
      case Fix(f) => boundRangeShiftBelowCutoff(f, d, c, a, b)
      case TAbs(body) => boundRangeShiftBelowCutoff(body, d, c, a, b)
      case TApp(t, _) => boundRangeShiftBelowCutoff(t, d, c, a, b)
    }
  }.ensuring(!shift(t, d, c).hasFreeVariablesIn(a, b))

  @opaque @pure
  def boundRangeSubstitutionLemma(t: Term, j: BigInt, s: Term): Unit = {
    require(j >= 0)
    require(!s.hasFreeVariablesIn(0, j+1))

    t match {
      case Var(k) => {
        boundRangeSinglize(s, 0, j+1, j)
      }
      case Abs(_, body) => {
        boundRangeShift(s, 1, 0, j+1)
        boundRangeSinglize(shift(s, 1, 0), 0, j+2, j+1)
        boundRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
      }
      case App(t1, t2) => {
        boundRangeSubstitutionLemma(t1, j, s)
        boundRangeSubstitutionLemma(t2, j, s)
      }
      case Fix(f) => {
        boundRangeSubstitutionLemma(f, j, s)
      }
      case TAbs(body) => {
        boundRangeSubstitutionLemma(body, j, s)
      }
      case TApp(t, _) => {
        boundRangeSubstitutionLemma(t, j, s)
      }
    }
  }.ensuring(!substitute(t, j, s).hasFreeVariable(j))

  @opaque @pure
  def boundRangeShiftBackLemma(t: Term, d: BigInt, c: BigInt): Unit = {
    require(c >= 0)
    require(d > 0)
    require(!t.hasFreeVariablesIn(c, d))

    t match {
      case Var(k) => assert(negativeShiftValidity(t, -d, c))
      case Abs(_, body) => {
        boundRangeShiftBackLemma(body, d, c+1)
        assert(negativeShiftValidity(t, -d, c))
      }
      case App(t1, t2) => {
        boundRangeShiftBackLemma(t1, d, c)
        boundRangeShiftBackLemma(t2, d, c)
        assert(negativeShiftValidity(t, -d, c))
      }
      case Fix(f) => boundRangeShiftBackLemma(f, d, c)
      case TAbs(body)     => boundRangeShiftBackLemma(body, d, c)
      case TApp(t, _)     => boundRangeShiftBackLemma(t, d, c)
    }
  }.ensuring(negativeShiftValidity(t, -d, c))

  /// Substitution & shifting lemmas on types

  def boundRangeShiftComposition(t: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    require(a >= 0)
    require(c >= 0)
    require(d >= 0)
    require(d <= c + a)
    require(if(d < c) !t.hasFreeVariablesIn(d, c - d) else !t.hasFreeVariablesIn(c, d - c))
    require((b >= 0) || (-b <= a))


    if (d < c){
      boundRangeShift(t, a, c, 0)
      boundRangeShiftBelowCutoff(t, a, c, d, c - d)
      boundRangeConcatenation(shift(t, a, c), d, c - d, a)
      boundRangeDecrease(shift(t, a, c), d, c - d + a, a)
    }
    else{
      boundRangeShift(t, a, c, d - c)
      boundRangeIncreaseCutoff(shift(t, a, c), c, d, a + d - c)
    }

    assert(!shift(t, a, c).hasFreeVariablesIn(d, a))
    if(b < 0){
      boundRangeDecrease(shift(t, a, c), d, a, -b)
      boundRangeShiftBackLemma(shift(t, a, c), -b, d)        
    }
    else{
      ()
    }

    t match {
      case VariableType(_) => ()
      case BasicType(_) => ()
      case UniversalType(body) => {
        boundRangeShiftComposition(body, a, b, c + 1, d + 1)
      }
      case ArrowType(t1, t2) => {
        boundRangeShiftComposition(t1, a, b, c, d)
        boundRangeShiftComposition(t2, a, b, c, d)
      }
    }
  }.ensuring(shift(shift(t, a, c), b, d) == shift(t, a + b, c))

  def boundRangeShift(t: Type, d: BigInt, c: BigInt, b: BigInt): Unit = {
    require(c >= 0)
    require(d >= 0)
    require(b >= 0)
    require(!t.hasFreeVariablesIn(c, b))

    t match {
      case BasicType(_) => ()
      case VariableType(_)    => assert(!shift(t, d, c).hasFreeVariablesIn(c, d+b))
      case UniversalType(body)   => {
        boundRangeShift(body, d, c+1, b)
        assert(!shift(t, d, c).hasFreeVariablesIn(c, d+b))
      }
      case ArrowType(t1, t2)    => {
        boundRangeShift(t1, d, c, b)
        boundRangeShift(t2, d, c, b)
        assert(!shift(t, d, c).hasFreeVariablesIn(c, d+b))
      }
    }

  }.ensuring(!shift(t, d, c).hasFreeVariablesIn(c, d+b))

  def boundRangeShiftBelowCutoff(t: Type, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
    require(d >= 0)
    require(c >= 0)
    require(a >= 0)
    require(b >= 0)
    require(a + b <= c)
    require(!t.hasFreeVariablesIn(a, b))
    t match {
      case BasicType(_) => ()
      case VariableType(_) => ()
      case UniversalType(body) => 
        boundRangeShiftBelowCutoff(body, d, c + 1, a + 1, b)
      case ArrowType(t1, t2) => {
        boundRangeShiftBelowCutoff(t1, d, c, a, b)
        boundRangeShiftBelowCutoff(t2, d, c, a, b)
      }
    }
  }.ensuring(!shift(t, d, c).hasFreeVariablesIn(a, b))

  def boundRangeSubstitutionLemma(t: Type, j: BigInt, s: Type): Unit = {
    require(j >= 0)
    require(!s.hasFreeVariablesIn(0, j+1))

    t match {
      case BasicType(_) => 
      case VariableType(v) => {
        boundRangeSinglize(s, 0, j+1, j)
      }
      case UniversalType(body) => {
        boundRangeShift(s, 1, 0, j+1)
        boundRangeSinglize(shift(s, 1, 0), 0, j+2, j+1)
        boundRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
      }
      case ArrowType(t1, t2) => {
        boundRangeSubstitutionLemma(t1, j, s)
        boundRangeSubstitutionLemma(t2, j, s)
      }
    }
  }.ensuring(!substitute(t, j, s).hasFreeVariable(j))

  def boundRangeShiftBackLemma(t: Type, d: BigInt, c: BigInt): Unit = {
    require(c >= 0)
    require(d > 0)
    require(!t.hasFreeVariablesIn(c, d))

    t match {
      case BasicType(_) => 
      case VariableType(_) => assert(negativeShiftValidity(t, -d, c))
      case UniversalType(body) => {
        boundRangeShiftBackLemma(body, d, c+1)
        assert(negativeShiftValidity(t, -d, c))
      }
      case ArrowType(t1, t2) => {
        boundRangeShiftBackLemma(t1, d, c)
        boundRangeShiftBackLemma(t2, d, c)
        assert(negativeShiftValidity(t, -d, c))
      }
    }
  }.ensuring(negativeShiftValidity(t, -d, c))

  /// ReduceAll correctness

  // @opaque @pure
  // def reduceAllCompleteness(t: Term, tp: Term): Unit = {
  //   require(reducesTo(t, tp))

  //   t match {
  //     case Var(_) => assert(reduceAll(t).contains(tp))
  //     case Abs(_, _) => assert(reduceAll(t).contains(tp))
  //     case App(t1, t2) => {
  //       (tp match {
  //         case App(t1p, t2p) if reducesTo(t1, t1p) && t2 == t2p  => {
  //           reduceAllCompleteness(t1, t1p)
  //           reduceAll(t1).mapPost1[Term](t1p => App(t1p, t2))(t1p)
  //         }
  //         case App(t1p, t2p) if t1 == t1p && reducesTo(t2, t2p) => {
  //           reduceAllCompleteness(t2, t2p)
  //           reduceAll(t2).mapPost1[Term](t2p => App(t1, t2p))(t2p)
  //         }
  //         case _ => assert(reduceAll(t).contains(tp))
  //       })
  //     }
  //     case Fix(f) => {
  //       (tp match {
  //         case Fix(fp) if reducesTo(f, fp) => {
  //           reduceAllCompleteness(f, fp)
  //           reduceAll(f).mapPost1[Term](Fix(_))(fp)
  //         }
  //         case _ => assert(reduceAll(t).contains(tp))
  //       })
  //     }
  //   }
  // }.ensuring(reduceAll(t).contains(tp))

  // @opaque @pure
  // def reduceAllSoundness(t: Term, tp: Term): Unit = {
  //   require(reduceAll(t).contains(tp))
  //   t match {
  //     case Var(_) => assert(reducesTo(t, tp))
  //     case Abs(_, _) => assert(reducesTo(t, tp))
  //     case App(t1, t2) => {
  //       if(reduceAll(t1).map[Term](t1p => App(t1p, t2)).contains(tp)) {
  //         val App(t1p, t2p) = tp
  //         reduceAll(t1).mapPost2[Term](t1p => App(t1p, t2))(tp)
  //         reduceAllSoundness(t1, t1p)
  //       }
  //       else if(reduceAll(t2).map[Term](t2p => App(t1, t2p)).contains(tp)) {
  //         val App(t1p, t2p) = tp
  //         reduceAll(t2).mapPost2[Term](t2p => App(t1, t2p))(tp)
  //         reduceAllSoundness(t2, t2p)
  //       }
  //       else {
  //         assert(reducesTo(t, tp))
  //       }
  //     }
  //     case Fix(f) => {
  //       if(reduceAll(f).map[Term](Fix(_)).contains(tp)) {
  //         val Fix(fp) = tp
  //         reduceAll(f).mapPost2[Term](Fix(_))(tp)
  //         reduceAllSoundness(f, fp)
  //       }
  //       else {
  //         assert(reducesTo(t, tp))
  //       }
  //     }
  //   }
  // }.ensuring(reducesTo(t, tp))

  // Call-by-value soudness

  // @opaque @pure
  // def reduceCallByValueSoundness(t: Term): Unit = {
  //   require(reduceCallByValue(t).isDefined)
  //   val tp = reduceCallByValue(t).get

  //   t match {
  //     case Var(_) => assert(false)
  //     case Abs(_, _) => assert(false)
  //     case App(t1, t2) => {
  //       if(!t1.isValue) {
  //         reduceCallByValueSoundness(t1)
  //       }
  //       else if(!t2.isValue) {
  //         reduceCallByValueSoundness(t2)
  //       }
  //       else {
  //         assert(reducesTo(t, tp))
  //       }
  //     }
  //     case Fix(f) => {
  //       if(!f.isValue) {
  //         reduceCallByValueSoundness(f)
  //       }
  //       else {
  //         assert(reducesTo(t, tp))
  //       }
  //     }
  //   }

  // }.ensuring(reducesTo(t, reduceCallByValue(t).get))
}