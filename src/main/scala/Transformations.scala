import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Transformations {
  import SystemF._

  object Terms {
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
  }

  object Types {
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

    def negativeShiftValidity(t: Term, d: BigInt, c: BigInt): Boolean = {
      require(d < 0)
      t match {
        case Var(k) => true
        case Abs(typ, body) => negativeShiftValidity(typ, d, c) && negativeShiftValidity(body, d, c)
        case App(t1, t2) => negativeShiftValidity(t1, d, c) && negativeShiftValidity(t2, d, c)
        case Fix(f) => negativeShiftValidity(f, d, c)
        case TAbs(body) => negativeShiftValidity(body, d, c+1)
        case TApp(t, typ) => negativeShiftValidity(t, d, c) && negativeShiftValidity(typ, d, c)
      }
    }

    def shift(t: Term, d: BigInt, c: BigInt): Term = {
      require(d >= 0 || negativeShiftValidity(t, d, c))
      require(c >= 0)
      t match {
        case Var(k) => t
        case Abs(typ, body) => Abs(shift(typ, d, c), shift(body, d, c))
        case App(t1, t2) => App(shift(t1, d, c), shift(t2, d, c))
        case Fix(f) => Fix(shift(f, d, c))
        case TAbs(body) => TAbs(shift(body, d, c+1))
        case TApp(t, typ) => TApp(shift(t, d, c), shift(typ, d, c))
      }
    }

    def substitute(t: Term, v: BigInt, s: Type): Term = {
      t match {
        case Var(k) => t
        case Abs(typ, body) => Abs(substitute(typ, v, s), substitute(body, v, s))
        case App(t1, t2) => App(substitute(t1, v, s), substitute(t2, v, s))
        case Fix(f) => Fix(substitute(f, v, s))
        case TAbs(body) => TAbs(substitute(body, v+1, shift(s, 1, 0)))
        case TApp(t, typ) => TApp(substitute(t, v, s), substitute(typ, v, s))
      }
    }
  }

}

object TransformationsProperties {
  import SystemF._

  object Terms {
    import SystemFProperties.Terms._
    import Transformations.Terms._

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
  }

  object Types {
    import SystemFProperties.Types._
    import Transformations.Types._

    @opaque @pure
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

    @opaque @pure
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

    @opaque @pure
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

    @opaque @pure
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

    @opaque @pure
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

    /// Types in terms 

    @opaque @pure
    def boundRangeShift(t: Term, d: BigInt, c: BigInt, b: BigInt): Unit = {
      require(c >= 0)
      require(d >= 0)
      require(b >= 0)
      require(!t.hasFreeTypeVariablesIn(c, b))

      t match {
        case Var(k) => ()
        case Abs(targ, body) => {
          boundRangeShift(targ, d, c, b)
          boundRangeShift(body, d, c, b)
        }
        case App(t1, t2) => {
          boundRangeShift(t1, d, c, b)
          boundRangeShift(t2, d, c, b)
        }
        case Fix(f) => boundRangeShift(f, d, c, b)
        case TAbs(body) => {
          boundRangeShift(body, d, c, b)
        }
        case TApp(term, typ) => {
          boundRangeShift(term, d, c, b)
          boundRangeShift(typ, d, c, b)
        }
      }
    }.ensuring(!shift(t, d, c).hasFreeTypeVariablesIn(c, d+b))

    @opaque @pure
    def boundRangeSubstitutionLemma(t: Term, j: BigInt, s: Type): Unit = {
      require(j >= 0)
      require(!s.hasFreeVariablesIn(0, j+1))

      t match {
        case Var(k) => assert(!substitute(t, j, s).hasFreeTypeVariable(j))
        case Abs(targ, body) => {
          boundRangeSubstitutionLemma(targ, j, s)
          boundRangeSubstitutionLemma(body, j, s)
          assert(!substitute(t, j, s).hasFreeTypeVariable(j))
        }
        case App(t1, t2) => {
          boundRangeSubstitutionLemma(t1, j, s)
          boundRangeSubstitutionLemma(t2, j, s)
          assert(!substitute(t, j, s).hasFreeTypeVariable(j))
        }
        case Fix(f) => boundRangeSubstitutionLemma(f, j, s)
        case TAbs(body) => {
          boundRangeShift(s, 1, 0, j+1)
          boundRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
        }
        case TApp(term, typ) => {
          boundRangeSubstitutionLemma(term, j, s)
          boundRangeSubstitutionLemma(typ, j, s)
        }
      }
    }.ensuring(!substitute(t, j, s).hasFreeTypeVariable(j))

    @opaque @pure
    def boundRangeShiftBackLemma(t: Term, d: BigInt, c: BigInt): Unit = {
      require(c >= 0)
      require(d > 0)
      require(!t.hasFreeTypeVariablesIn(c, d))

      t match {
        case Var(k) => assert(negativeShiftValidity(t, -d, c))
        case Abs(targ, body) => {
          boundRangeShiftBackLemma(targ, d, c)
          boundRangeShiftBackLemma(body, d, c)
          assert(negativeShiftValidity(t, -d, c))
        }
        case App(t1, t2) => {
          boundRangeShiftBackLemma(t1, d, c)
          boundRangeShiftBackLemma(t2, d, c)
          assert(negativeShiftValidity(t, -d, c))
        }
        case Fix(f) => boundRangeShiftBackLemma(f, d, c)
        case TAbs(body) => boundRangeShiftBackLemma(body, d, c+1)
        case TApp(term, typ) => {
          boundRangeShiftBackLemma(term, d, c)
          boundRangeShiftBackLemma(typ, d, c)
        }
      }
    }.ensuring(negativeShiftValidity(t, -d, c))
  }

}