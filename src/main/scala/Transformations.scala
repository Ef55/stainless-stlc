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
        case TAbs(body) => TAbs(substitute(body, j, Types.shift(s, 1, 0)))
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

    def negativeShiftValidity(env: Environment, d: BigInt, c: BigInt): Boolean = {
      require(d < 0)

      env match {
        case Nil() => true
        case Cons(h, t) => negativeShiftValidity(h, d, c) && negativeShiftValidity(t, d, c)
      }
    }

    def shift(env: Environment, d: BigInt, c: BigInt): Environment = {
      require(d >= 0 || negativeShiftValidity(env, d, c))
      require(c >= 0)

      env match {
        case Nil() => Nil[Type]()
        case Cons(h, t) => {
          if(d < 0) {
            assert(negativeShiftValidity(env, d, c))
            assert(negativeShiftValidity(h, d, c))
          }
          Cons(shift(h, d, c), shift(t, d, c))
        }
      }
    }.ensuring(res => res.length == env.length)

    def substitute(env: Environment, d: BigInt, typ: Type): Environment = {
      env.map(Transformations.Types.substitute(_, d, typ))
    }
  }

}

object TransformationsProperties {
  import SystemF._

  object Terms {
    import SystemFProperties.Terms._
    import Transformations.Terms._

    @opaque @pure
    def boundRangeTypeShiftIdentity(t: Term, s: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
      require(a >= 0)
      require(b >= 0)
      require(s >= 0 || Transformations.Types.negativeShiftValidity(t, s, c))
      require(c >= 0)

      t match {
        case Var(_) => {
          assert(
            t.hasFreeVariablesIn(a, b) 
            == 
            Transformations.Types.shift(t, s, c).hasFreeVariablesIn(a, b)
          )
        }
        case Abs(_, body) => {
          boundRangeTypeShiftIdentity(body, s, c, a+1, b)
        }
        case App(t1, t2) => {
          boundRangeTypeShiftIdentity(t1, s, c, a, b)
          boundRangeTypeShiftIdentity(t2, s, c, a, b)
        }
        case Fix(f) => {
          boundRangeTypeShiftIdentity(f, s, c, a, b)
        }
        case TAbs(body) => {
          boundRangeTypeShiftIdentity(body, s, c+1, a, b)
        }
        case TApp(body, _) => {
          boundRangeTypeShiftIdentity(body, s, c, a, b)
        }
      }
    }.ensuring(
      t.hasFreeVariablesIn(a, b) 
      == 
      Transformations.Types.shift(t, s, c).hasFreeVariablesIn(a, b)
    )

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
          boundRangeTypeShiftIdentity(s, 1, 0, 0, j+1)
          boundRangeSubstitutionLemma(body, j, Transformations.Types.shift(s, 1, 0))
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
    def boundRangeSubstitutionIdentity(t: Type, j: BigInt, typ: Type): Unit = {
      require(j >= 0)
      require(!t.hasFreeVariablesIn(j, 1))

      t match {
        case VariableType(k) => {
          assert(k != j)
          assert(substitute(t, j, typ) == t)
        }
        case BasicType(_) => {
          assert(substitute(t, j, typ) == t)
        }
        case UniversalType(body) => {
          boundRangeSubstitutionIdentity(body, j+1, shift(typ, 1 ,0))
        }
        case ArrowType(t1, t2) => {
          boundRangeSubstitutionIdentity(t1, j, typ)
          boundRangeSubstitutionIdentity(t2, j, typ)
        }
      }

    }.ensuring(
      substitute(t, j, typ) == t
    )

    @opaque @pure
    def shift0Identity(t: Type, c: BigInt): Unit = {
      require(c >= 0)
      t match {
        case VariableType(k) => {
          assert(shift(t, 0, c) == t)
        }
        case BasicType(_) => {
          assert(shift(t, 0, c) == t)
        }
        case UniversalType(body) => {
          shift0Identity(body, c+1)
        }
        case ArrowType(t1, t2) => {
          shift0Identity(t1, c)
          shift0Identity(t2, c)
        }
      }
    }.ensuring(shift(t, 0, c) == t)

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
    }.ensuring(
      (b >= 0 || negativeShiftValidity(shift(t, a, c), b, d)) &&
      shift(shift(t, a, c), b, d) == shift(t, a + b, c)
    )

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
    def boundRangeShiftCutoff(t: Type, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
      require(c >= 0)
      require(d >= 0)
      require(b >= 0)
      require(a >= 0)
      require(!t.hasFreeVariablesIn(a, b))
      require(c < a)

      t match {
        case BasicType(_) => ()
        case VariableType(_) => ()
        case UniversalType(body)   => {
          boundRangeShiftCutoff(body, d, c+1, a+1, b)
        }
        case ArrowType(t1, t2)    => {
          boundRangeShiftCutoff(t1, d, c, a, b)
          boundRangeShiftCutoff(t2, d, c, a, b)
        }
      }

    }.ensuring(!shift(t, d, c).hasFreeVariablesIn(a + d, b))

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

    @opaque @pure
    def negativeShiftableForwardShift(t: Type, sf: BigInt, sb: BigInt, cf: BigInt, cb: BigInt): Unit = {
      require(sf >= 0)
      require(sb < 0)
      require(cf >= 0 && cb >= 0)
      require(negativeShiftValidity(t, sb, cb))

      t match {
        case VariableType(_) => {
          assert(negativeShiftValidity(shift(t, sf, cf), sb, cb+sf))
        }
        case BasicType(_) => {
          assert(negativeShiftValidity(shift(t, sf, cf), sb, cb+sf))
        }
        case ArrowType(t1, t2) => {
          negativeShiftableForwardShift(t1, sf, sb, cf, cb)
          negativeShiftableForwardShift(t2, sf, sb, cf, cb)
        }
        case UniversalType(body) => {
          negativeShiftableForwardShift(body, sf, sb, cf+1, cb+1)
        }
      }
    }.ensuring(
      negativeShiftValidity(shift(t, sf, cf), sb, cb+sf)
    )

    @opaque @pure
    def negativeShiftableForwardShiftStableCutoff(t: Type, sf: BigInt, sb: BigInt, c: BigInt): Unit = {
      require(sf >= 0)
      require(sb < 0)
      require(c >= 0)
      require(negativeShiftValidity(t, sb, c))

      t match {
        case VariableType(_) => {
          assert(negativeShiftValidity(shift(t, sf, c), sb, c))
        }
        case BasicType(_) => {
          assert(negativeShiftValidity(shift(t, sf, c), sb, c))
        }
        case ArrowType(t1, t2) => {
          negativeShiftableForwardShiftStableCutoff(t1, sf, sb, c)
          negativeShiftableForwardShiftStableCutoff(t2, sf, sb, c)
        }
        case UniversalType(body) => {
          negativeShiftableForwardShiftStableCutoff(body, sf, sb, c+1)
        }
      }
    }.ensuring(
      negativeShiftValidity(shift(t, sf, c), sb, c)
    )

    @opaque @pure
    def negativeShiftableCutoffTransitivity(t: Type, d: BigInt, c: BigInt, cp: BigInt): Unit = {
      require(d < 0 && c >= 0)
      require(negativeShiftValidity(t, d, c))
      require(cp >= c)

      t match {
        case VariableType(_) => {
          assert(negativeShiftValidity(t, d, cp))
        }
        case BasicType(_) => {
          assert(negativeShiftValidity(t, d, cp))
        }
        case ArrowType(t1, t2) => {
          negativeShiftableCutoffTransitivity(t1, d, c, cp)
          negativeShiftableCutoffTransitivity(t2, d, c, cp)
        }
        case UniversalType(body) => {
          negativeShiftableCutoffTransitivity(body, d, c+1, cp+1)
        }
      }
    }.ensuring(
      negativeShiftValidity(t, d, cp)
    )
  @opaque @pure
  def shiftCommutativity(subs: Type, c: BigInt, d: BigInt, a: BigInt, b: BigInt) : Unit ={
    require(c >= 0)
    require(d >= 0)
    require(b >= 0)
    require(a >= 0)
    require(d <= c)
    subs match{
      case BasicType(_) => ()
      case ArrowType(t1, t2) => 
        shiftCommutativity(t1, c, d, a, b)
        shiftCommutativity(t2, c, d, a, b)
      case VariableType(v) =>
        if(v < c){
          assert(shift(VariableType(v), b, c) == VariableType(v))
          if(v < d){
            assert(shift(shift(VariableType(v), b, c), b, d) == VariableType(v))
            assert(shift(VariableType(v), b, d) == VariableType(v))
            assert(shift(shift(VariableType(v), b, d), b, c + 1) == VariableType(v))
          }
          else{
            assert(shift(shift(VariableType(v), b, c), b, d) == VariableType(v + b))
            assert(shift(VariableType(v), b, d) == VariableType(v + b))
            assert(shift(shift(VariableType(v), b, d), b, c + b) == VariableType(v + b))
          }
        }
        else{
          assert(shift(VariableType(v), b, c) == VariableType(v + b))
          if(v + b < d){
            assert(shift(shift(VariableType(v), b, c), b, d) == VariableType(v + b))
            assert(shift(VariableType(v), b, d) == VariableType(v))
            assert(shift(shift(VariableType(v), b, d), 1, c + b) == shift(VariableType(v), b, c + b))
            if(v < c + b){ //TODO: V == [C - C + B[
              assert(shift(VariableType(v), 1, c + b) == VariableType(v))
            }
            else{
              assert(shift(VariableType(v), 1, c + b) == VariableType(v + b))
            }
            
          }
          else{ // v + b >= d <=> v >= d - b
            assert(shift(shift(VariableType(v), b, c), b, d) == VariableType(v + b + b))
            if(v >= d){
              assert(shift(VariableType(v), b, d) == VariableType(v + b))
              assert(shift(shift(VariableType(v), b, d), b, c + b) == VariableType(v + b + b))
            }
            else{ // TODO: V == D - 1
              assert(shift(VariableType(v), b, d) == VariableType(v))
              if(v < c + b){ //TODO V == C
                assert(shift(shift(VariableType(v), b, d), b, c + b) == VariableType(v))
              }
              else{
                assert(shift(shift(VariableType(v), b, d), b, c + b) == VariableType(v + b))
              }
              
            }
          }
        }
        assert(shift(shift(VariableType(v), 1, c), 1, d) == shift(shift(VariableType(v), 1, d), 1, c + 1))
        assert(shift(shift(subs, 1, c), 1, d) == shift(shift(subs, 1, d), 1, c + 1))
      case UniversalType(t) =>
        shiftCommutativity(t, c + 1, d + 1, a, b) 
        assert(shift(shift(t, b, c + 1), a, d + 1) == shift(shift(t, a, d + 1), b, c + a + 1))
        assert(UniversalType(shift(shift(t, b, c + 1), a, d + 1)) == UniversalType(shift(shift(t, a, d + 1), b, c + a + 1)))
        assert(shift(shift(UniversalType(t), b, c), a, d) == shift(shift(UniversalType(t), a, d), b, c + a))
        assert(shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a))
    }
  }.ensuring(shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a))
  
  @opaque @pure
  def shiftSubstitutionCommutativityType(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    require(s >= 0)
    require(c >= 0 && c <= k)

    typ match {
      case BasicType(_) => {
        assert(shift(substitute(typ, k, subs), s, c) == typ)
        assert(substitute(shift(typ, s, c), k+s, shift(subs, s, c)) == typ)
      }
      case ArrowType(t1, t2) => {
        shiftSubstitutionCommutativityType(t1, s, c, k, subs)
        shiftSubstitutionCommutativityType(t2, s, c, k, subs)
      }
      case VariableType(v) => {
        if(v == k) {
          assert(shift(substitute(typ, k, subs), s, c) == shift(subs, s, c))
          assert(substitute(shift(typ, s, c), k+s, shift(subs, s, c)) == shift(subs, s, c))
        }
        else {
          assert(shift(substitute(typ, k, subs), s, c) == shift(typ, s, c))
          assert(substitute(shift(typ, s, c), k+s, shift(subs, s, c)) == shift(typ, s, c))
        }
      }
      case UniversalType(t) => {
        shiftCommutativity(subs, c, 0, 1, s)
        assert(
          shift(shift(subs, s, c), 1, 0)
          ==
          shift(shift(subs, 1, 0), s, c+1)
        )
        shiftSubstitutionCommutativityType(t, s, c+1, k+1, shift(subs, 1, 0))
        assert(
          shift(substitute(t, k+1, shift(subs, 1, 0)), s, c+1)
          ==
          substitute(shift(t, s, c+1), k+1+s, shift(shift(subs, 1, 0), s, c+1))
        )
        assert(
          UniversalType(shift(substitute(t, k+1, shift(subs, 1, 0)), s, c+1))
          ==
          UniversalType(substitute(shift(t, s, c+1), k+1+s, shift(shift(subs, 1, 0), s, c+1)) )
        )
        assert(
          UniversalType(shift(substitute(t, k+1, shift(subs, 1, 0)), s, c+1)  ) 
          == 
          UniversalType(substitute(shift(t, s, c + 1), k + s + 1, shift(shift(subs, s, c), 1, 0)))
        )
        assert(
          shift(substitute(UniversalType(t), k, subs), s, c) 
          == 
          substitute(shift(UniversalType(t), s, c), k+s, shift(subs, s, c))
        )
      }
    }
  }.ensuring(
    shift(substitute(typ, k, subs), s, c) 
    == 
    substitute(shift(typ, s, c), k+s, shift(subs, s, c))
  )

  @opaque @pure
  def shiftSubstitutionCommutativityTypeNeg(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    require(c >= 0 && c <= k)
    require(s > 0)
    require(!typ.hasFreeVariablesIn(c, s))

    boundRangeShiftBackLemma(typ, s, c)
    boundRangeShift(subs, s, c, 0)
    boundRangeTypeSubstitutionLemma1(typ, k + s, shift(subs, s, c), s, s, c, c)
    boundRangeShiftBackLemma(substitute(typ, k + s, shift(subs, s, c)), s, c)


    typ match {
      case BasicType(_) => {}
      case ArrowType(t1, t2) => {
        shiftSubstitutionCommutativityTypeNeg(t1, s, c, k, subs)
        shiftSubstitutionCommutativityTypeNeg(t2, s, c, k, subs)
      }
      case VariableType(v) => {
        boundRangeShiftComposition(subs, s, -s, c, c)
        if (v >= c && k == v - s){
            boundRangeShiftComposition(subs, s, -s, c, c)
            shift0Identity(subs, c)          

        }
      }
      case UniversalType(t) => {
        shiftSubstitutionCommutativityTypeNeg(t, s, c + 1, k + 1, shift(subs, 1, 0))
        shiftCommutativity(subs, c, 0, 1, s)
      }
    }
  }.ensuring(
    shift(substitute(typ, k + s, shift(subs, s, c)), -s, c) 
    == 
    substitute(shift(typ, -s, c), k, subs)
  )

//     def shiftSubstitutionCommutativityTypeNeg2(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
//     require(c >= 0 && c <= k - s)
//     require(s > 0)
//     require(k >= s)
//     require(!typ.hasFreeVariablesIn(c, s))
//     require(!subs.hasFreeVariablesIn(c, s))

//     boundRangeShiftBackLemma(typ, s, c)
//     boundRangeShiftBackLemma(subs, s, c)
//     shiftSubstitutionCommutativityTypeNeg(typ, s, c, k - s, shift(subs, -s, c))
//     boundRangeTypeSubstitutionLemma1(typ, k, subs, s, s, c, c)
    
// //    boundRangeShift(subs, s, c, 0)
//     boundRangeShiftBackLemma(substitute(typ, k, subs), s, c)
//     boundRangeShiftComposition(subs, s, -s, c, c)
//     shift0Identity(subs, c)
//     assert(shift(shift(subs, -s, c), s, c) == subs)


//     // typ match {
//     //   case BasicType(_) => {}
//     //   case ArrowType(t1, t2) => {
//     //     shiftSubstitutionCommutativityTypeNeg2(t1, s, c, k, subs)
//     //     shiftSubstitutionCommutativityTypeNeg2(t2, s, c, k, subs)
//     //   }
//     //   case VariableType(v) => {
//     //     boundRangeShiftComposition(subs, s, -s, c, c)
//     //     if (v >= c && k == v - s){
//     //         boundRangeShiftComposition(subs, s, -s, c, c)
//     //         shift0Identity(subs, c)          

//     //     }
//     //   }
//     //   case UniversalType(t) => {
//     //     shiftSubstitutionCommutativityTypeNeg2(t, s, c + 1, k + 1, shift(subs, 1, 0))
//     //     shiftCommutativity(subs, c, 0, 1, s)
//     //   }
//     // }
//   }.ensuring(
//     shift(substitute(typ, k, subs), -s, c) 
//     == 
//     substitute(shift(typ, -s, c), k - s, shift(subs, -s, c))
//   )



    @opaque @pure
    def boundRangeTypeSubstitutionLemma1(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
      require(j >= 0)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(d >= 0)
      require(!s.hasFreeVariablesIn(c, a))
      require(!t.hasFreeVariablesIn(d, b))
      require(c + a >= d + b)
      require(c <= d)

      t match {
        case BasicType(_) => 
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))
        case ArrowType(t1, t2) => 
          boundRangeTypeSubstitutionLemma1(t1, j, s, a, b, c, d)
          boundRangeTypeSubstitutionLemma1(t2, j, s, a, b, c, d)
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))
        case VariableType(v) => 
          boundRangeIncreaseCutoff(s, c, d, a)
          boundRangeDecrease(s, d, a - (d - c), b)
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))
        case UniversalType(body) =>
          if(c > 0){
            boundRangeShiftCutoff(s, 1, 0, c, a)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
          }
          else{
            assert(!s.hasFreeVariablesIn(0, a))
            boundRangeShift(s, 1, 0, a)
            boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
          }
          boundRangeTypeSubstitutionLemma1(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)

          assert(!substitute(body, j + 1, shift(s, 1, 0)).hasFreeVariablesIn(d + 1, b))
          assert(!UniversalType(substitute(body, j + 1, shift(s, 1, 0))).hasFreeVariablesIn(d, b))
          assert(!substitute(UniversalType(body), j, s).hasFreeVariablesIn(d, b))
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))

      }
    }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(d, b))

        @opaque @pure
    def boundRangeTypeSubstitutionLemma2(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
      require(j >= 0)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(d >= 0)
      require(!s.hasFreeVariablesIn(c, a))
      require(!t.hasFreeVariablesIn(d, b))
      require(c + a <= d + b)
      require(c >= d)

      t match {
        case BasicType(_) => 
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, a))
        case ArrowType(t1, t2) => 
          boundRangeTypeSubstitutionLemma2(t1, j, s, a, b, c, d)
          boundRangeTypeSubstitutionLemma2(t2, j, s, a, b, c, d)
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, a))
        case VariableType(v) => 
          boundRangeIncreaseCutoff(t, d, c, b)
          boundRangeDecrease(t, c, b - (c - d), a)
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, a))
        case UniversalType(body) =>
          if(c > 0){
            boundRangeShiftCutoff(s, 1, 0, c, a)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
          }
          else{
            assert(!s.hasFreeVariablesIn(0, a))
            boundRangeShift(s, 1, 0, a)
            boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
          }
          boundRangeTypeSubstitutionLemma2(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)

          assert(!substitute(body, j + 1, shift(s, 1, 0)).hasFreeVariablesIn(c + 1, a))
          assert(!UniversalType(substitute(body, j + 1, shift(s, 1, 0))).hasFreeVariablesIn(c, a))
          assert(!substitute(UniversalType(body), j, s).hasFreeVariablesIn(c, a))
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, a))

      }
    }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(c, a))

        @opaque @pure
    def boundRangeTypeSubstitutionLemma3(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
      require(j >= 0)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(d >= 0)
      require(!s.hasFreeVariablesIn(c, a))
      require(!t.hasFreeVariablesIn(d, b))
      require(c <= d + b)
      require(c + a >= d + b)
      require(c >= d)

      t match {
        case BasicType(_) => 
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))
        case ArrowType(t1, t2) => 
          boundRangeTypeSubstitutionLemma3(t1, j, s, a, b, c, d)
          boundRangeTypeSubstitutionLemma3(t2, j, s, a, b, c, d)
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))
        case VariableType(v) => 
          boundRangeDecrease(s, c, a, b - (c - d))
          boundRangeIncreaseCutoff(t, d, c, b)
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))
        case UniversalType(body) =>
          if(c > 0){
            boundRangeShiftCutoff(s, 1, 0, c, a)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
          }
          else{
            assert(!s.hasFreeVariablesIn(0, a))
            boundRangeShift(s, 1, 0, a)
            boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
          }
          boundRangeTypeSubstitutionLemma3(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)
          assert(!substitute(body, j + 1, shift(s, 1, 0)).hasFreeVariablesIn(c + 1, b - (c - d)))
          assert(!UniversalType(substitute(body, j + 1, shift(s, 1, 0))).hasFreeVariablesIn(c, b - (c - d)))
          assert(!substitute(UniversalType(body), j, s).hasFreeVariablesIn(c, b - (c - d)))
          assert(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))

      }
    }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))

        @opaque @pure
    def boundRangeTypeSubstitutionLemma4(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
      require(j >= 0)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(d >= 0)
      require(!s.hasFreeVariablesIn(c, a))
      require(!t.hasFreeVariablesIn(d, b))
      require(c + a >= d)
      require(c + a <= d + b)
      require(c <= d)

      t match {
        case BasicType(_) => 
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))
        case ArrowType(t1, t2) => 
          boundRangeTypeSubstitutionLemma4(t1, j, s, a, b, c, d)
          boundRangeTypeSubstitutionLemma4(t2, j, s, a, b, c, d)
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))
        case VariableType(v) => 
          boundRangeDecrease(t, d, b, a - (d - c))
          boundRangeIncreaseCutoff(s, c, d, a)
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))
        case UniversalType(body) =>
          if(c > 0){
            boundRangeShiftCutoff(s, 1, 0, c, a)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
          }
          else{
            assert(!s.hasFreeVariablesIn(0, a))
            boundRangeShift(s, 1, 0, a)
            boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
            assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
          }
          boundRangeTypeSubstitutionLemma4(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)
          assert(!substitute(body, j + 1, shift(s, 1, 0)).hasFreeVariablesIn(d + 1, a - (d - c)))
          assert(!UniversalType(substitute(body, j + 1, shift(s, 1, 0))).hasFreeVariablesIn(d, a - (d - c)))
          assert(!substitute(UniversalType(body), j, s).hasFreeVariablesIn(d, a - (d - c)))
          assert(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))

      }
    }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))


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
          boundRangeShift(body, d, c+1, b)
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

    @opaque @pure
    def negativeShiftableForwardShift(t: Term, sf: BigInt, sb: BigInt, cf: BigInt, cb: BigInt): Unit = {
      require(sf >= 0)
      require(sb < 0)
      require(cf >= 0 && cb >= 0)
      require(negativeShiftValidity(t, sb, cb))

      t match {
        case Var(k) => assert(negativeShiftValidity(shift(t, sf, cf), sb, cb+sf))
        case Abs(targ, body) => {
          negativeShiftableForwardShift(targ, sf, sb, cf, cb)
          negativeShiftableForwardShift(body, sf, sb, cf, cb)
        }
        case App(t1, t2) => {
          negativeShiftableForwardShift(t1, sf, sb, cf, cb)
          negativeShiftableForwardShift(t2, sf, sb, cf, cb)
        }
        case Fix(f) => negativeShiftableForwardShift(f, sf, sb, cf, cb)
        case TAbs(body) => negativeShiftableForwardShift(body, sf, sb, cf+1, cb+1)
        case TApp(term, typ) => {
          negativeShiftableForwardShift(term, sf, sb, cf, cb)
          negativeShiftableForwardShift(typ, sf, sb, cf, cb)
        }
      }
    }.ensuring(
      negativeShiftValidity(shift(t, sf, cf), sb, cb+sf)
    )

    @opaque @pure
    def negativeShiftableForwardShiftStableCutoff(t: Term, sf: BigInt, sb: BigInt, c: BigInt): Unit = {
      require(sf >= 0)
      require(sb < 0)
      require(c >= 0)
      require(negativeShiftValidity(t, sb, c))

      t match {
        case Var(k) => assert(negativeShiftValidity(shift(t, sf, c), sb, c))
        case Abs(targ, body) => {
          negativeShiftableForwardShiftStableCutoff(targ, sf, sb, c)
          negativeShiftableForwardShiftStableCutoff(body, sf, sb, c)
        }
        case App(t1, t2) => {
          negativeShiftableForwardShiftStableCutoff(t1, sf, sb, c)
          negativeShiftableForwardShiftStableCutoff(t2, sf, sb, c)
        }
        case Fix(f) => negativeShiftableForwardShiftStableCutoff(f, sf, sb, c)
        case TAbs(body) => negativeShiftableForwardShiftStableCutoff(body, sf, sb, c+1)
        case TApp(term, typ) => {
          negativeShiftableForwardShiftStableCutoff(term, sf, sb, c)
          negativeShiftableForwardShiftStableCutoff(typ, sf, sb, c)
        }
      }
    }.ensuring(
      negativeShiftValidity(shift(t, sf, c), sb, c)
    )

    /// Types in environments

    @opaque @pure
    def boundRangeSubstitutionIdentity(env: Environment, j: BigInt, typ: Type): Unit = {
      require(j >= 0)
      require(!hasFreeVariablesIn(env, j, 1))

      env match {
        case Nil() => {
          assert(substitute(env, j, typ) == env)
        }
        case Cons(h, t) => {
          boundRangeSubstitutionIdentity(h, j, typ)
          boundRangeSubstitutionIdentity(t, j, typ)
        }
      }

    }.ensuring(
      substitute(env, j, typ) == env
    )

    @opaque @pure
    def shift0Identity(env: Environment, c: BigInt): Unit = {
      require(c >= 0)
      env match {
        case Nil() => assert(shift(env, 0, c) == env)
        case Cons(h, t) => {
          shift0Identity(h, c)
          shift0Identity(t, c)
        }
      }
    }.ensuring(shift(env, 0, c) == env)

    @opaque @pure
    def boundRangeShiftComposition(env: Environment, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
      require(a >= 0)
      require(c >= 0)
      require(d >= 0)
      require(d <= c + a)
      require(if(d < c) !hasFreeVariablesIn(env, d, c - d) else !hasFreeVariablesIn(env, c, d - c))
      require((b >= 0) || (-b <= a))

      env match {
        case Nil() => {
          assert(shift(shift(env, a, c), b, d) == shift(env, a + b, c))
        }
        case Cons(h, t) => {
          boundRangeShiftComposition(h, a, b, c, d)
          boundRangeShiftComposition(t, a, b, c, d)
        }
      }

    }.ensuring(
      (b >= 0 || negativeShiftValidity(shift(env, a, c), b, d)) &&
      shift(shift(env, a, c), b, d) == shift(env, a + b, c)
    )

    @opaque @pure
    def boundRangeShift(env: Environment, d: BigInt, c: BigInt, b: BigInt): Unit = {
      require(c >= 0)
      require(d >= 0)
      require(b >= 0)
      require(!hasFreeVariablesIn(env, c, b))

      env match {
        case Nil() => {
          assert(!hasFreeVariablesIn(shift(env, d, c), c, d+b))
        }
        case Cons(h, t) => {
          boundRangeShift(h, d, c, b)
          boundRangeShift(t, d, c ,b)
        }
      }

    }.ensuring(!hasFreeVariablesIn(shift(env, d, c), c, d+b))

    @opaque @pure
    def boundRangeShiftBackLemma(env: Environment, d: BigInt, c: BigInt): Unit = {
      require(c >= 0)
      require(d > 0)
      require(!hasFreeVariablesIn(env, c, d))

      env match {
        case Nil() => {
          assert(negativeShiftValidity(env, -d, c))
        }
        case Cons(h, t) => {
          boundRangeShiftBackLemma(h, d, c)
          boundRangeShiftBackLemma(t, d, c)
        }
      }
    }.ensuring(negativeShiftValidity(env, -d, c))

    @opaque @pure
    def negativeShiftableForwardShift(env: Environment, sf: BigInt, sb: BigInt, cf: BigInt, cb: BigInt): Unit = {
      require(sf >= 0)
      require(sb < 0)
      require(cf >= 0 && cb >= 0)
      require(negativeShiftValidity(env, sb, cb))

      env match {
        case Nil() => {
          assert(negativeShiftValidity(shift(env, sf, cf), sb, cb+sf))
        }
        case Cons(h, t) => {
          negativeShiftableForwardShift(h, sf, sb, cf, cb)
          negativeShiftableForwardShift(t, sf, sb, cf, cb)
        }
      }
    }.ensuring(
      negativeShiftValidity(shift(env, sf, cf), sb, cb+sf)
    )

    @extern
    def negativeShiftableForwardShiftStableCutoff(env: Environment, sf: BigInt, sb: BigInt, c: BigInt): Unit = {
      require(sf >= 0)
      require(sb < 0)
      require(c >= 0)
      require(negativeShiftValidity(env, sb, c))

    }.ensuring(
      negativeShiftValidity(shift(env, sf, c), sb, c)
    )

    @opaque @pure
    def negativeShiftableCutoffTransitivity(env: Environment, d: BigInt, c: BigInt, cp: BigInt): Unit = {
      require(d < 0 && c >= 0)
      require(negativeShiftValidity(env, d, c))
      require(cp >= c)

      env match {
        case Nil() => {
          assert(negativeShiftValidity(env, d, cp))
        }
        case Cons(h, t) => {
          negativeShiftableCutoffTransitivity(h, d, c, cp)
          negativeShiftableCutoffTransitivity(t, d, c, cp)
        }
      }
    }.ensuring(
      negativeShiftValidity(env, d, cp)
    )

    /// Environment shift is map-like

    @opaque @pure
    def shiftIndexing(env: Environment, d: BigInt, c: BigInt, j: BigInt): Unit = {
      require(d >= 0 || negativeShiftValidity(env, d, c))
      require(c >= 0)
      require(0 <= j && j < env.length)

      val Cons(h, t) = env

      if(j == 0) {
        if(d < 0) {
          assert(negativeShiftValidity(env, d, c))
          assert(negativeShiftValidity(h, d, c))
        }
      }
      else {
        shiftIndexing(t, d, c, j-1)
      }
    }.ensuring(
      ( d >= 0 || negativeShiftValidity(env(j), d, c) ) &&
      ( shift(env, d, c)(j) == shift(env(j), d, c) )
    )

    @opaque @pure
    def shiftConcat(@induct env1: Environment, env2: Environment, d: BigInt, c: BigInt): Unit = {
      require(c >= 0)
      require(d >= 0 || negativeShiftValidity(env1, d, c))
      require(d >= 0 || negativeShiftValidity(env2, d, c))

    }.ensuring(
      (d >= 0 || negativeShiftValidity(env1 ++ env2, d, c)) && 
      ( shift(env1 ++ env2, d, c) == (shift(env1, d, c) ++ shift(env2, d, c)) )
    )
  }

}