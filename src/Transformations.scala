import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Transformations {

  import LambdaOmega._
  import TransformationsProperties.{Terms => TermsProp, Types => TypesProp}

  object Terms {
    // ↑ᵈ_c(t)
    def shift(t: Term, d: BigInt, c: BigInt): Term = {
      require(c >= 0)
      require(if(d < 0){!t.hasFreeVariablesIn(c, -d)} else{true})
      t match {
        case Var(k)         => if (k < c) Var(k) else Var(k + d)
        case Abs(typ, body) => Abs(typ, shift(body, d, c+1))
        case App(t1, t2)    => App(shift(t1, d, c), shift(t2, d, c))
        case Fix(f)         => Fix(shift(f, d, c))
      }
    }

    // [j -> s]t
    def substitute(t: Term, j: BigInt, s: Term): Term = {
      t match {
        case Var(k) => if (k == j) s else t 
        case Abs(typ, body) => Abs(typ, substitute(body, j+1, shift(s, 1, 0)))
        case App(t1, t2) => App(substitute(t1, j, s), substitute(t2, j, s))
        case Fix(f) => Fix(substitute(f, j, s))
      }
    }

    // ↑⁻¹( [0 -> ↑¹(arg)]body )
    def absSubstitution(body: Term, arg: Term): Term = {
      assert(!arg.hasFreeVariablesIn(0, 0))
      TermsProp.boundRangeShift(arg, 1, 0, 0, 0)
      TermsProp.boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
      shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
    }

  }

  object Types{

    def shift(t: Type, d: BigInt, c: BigInt): Type = {
      require(c >= 0)
      require(if(d < 0){!t.hasFreeVariablesIn(c, -d)} else true)
      t match {
        case BasicType(_) => t
        case ArrowType(t1, t2) => ArrowType(shift(t1, d, c), shift(t2, d, c))
        case VariableType(k) => if (k < c) VariableType(k) else VariableType(k + d)
        case AbsType(arg, body) => AbsType(arg, shift(body, d, c + 1))
        case AppType(t1, t2) => AppType(shift(t1, d, c), shift(t2, d, c))
      }
    }.ensuring(_.size == t.size)

    def substitute(t: Type, j: BigInt, s: Type): Type = {
      t match {
        case BasicType(_) => t
        case ArrowType(t1, t2) => ArrowType(substitute(t1, j, s), substitute(t2, j, s))
        case VariableType(k) => if(j == k) s else t  
        case AbsType(k, b) => AbsType(k, substitute(b, j + 1, shift(s, 1, 0)))
        case AppType(t1, t2) => AppType(substitute(t1, j, s), substitute(t2, j, s))
      }
    }

    // ↑⁻¹( [0 -> ↑¹(arg)]body )
    def absSubstitution(body: Type, arg: Type): Type = {
      assert(!arg.hasFreeVariablesIn(0, 0))
      TypesProp.boundRangeShift(arg, 1, 0, 0, 0)
      TypesProp.boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
      shift(substitute(body, 0, shift(arg, 1, 0)), -1, 0)
    }

    def shift(env: TypeEnvironment, d: BigInt, c: BigInt): TypeEnvironment = {
      require(c >= 0)
      require(if(d < 0) !hasFreeVariablesIn(env, c, -d) else true)
      
      env match {
        case Nil() => Nil[Type]()
        case Cons(h, t) => {
          Cons(shift(h, d, c), shift(t, d, c))
        }
      }
    }.ensuring(res => res.length == env.length)

    def substitute(env: TypeEnvironment, d: BigInt, typ: Type): TypeEnvironment = {
      env.map(Transformations.Types.substitute(_, d, typ))
    }
  }
}

object TransformationsProperties {
  import LambdaOmega._

  // Substitution & shifting lemmas

  object Terms {
    import LambdaOmegaProperties.Terms._
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
        boundRangeShift(t, a, c, c, 0)
        boundRangeShift(t, a, c, d, c - d)
        boundRangeConcatenation(shift(t, a, c), d, c - d, a)
        boundRangeDecrease(shift(t, a, c), d, c - d + a, a)
      }
      else{
        boundRangeShift(t, a, c, c, d - c)
        boundRangeIncreaseCutoff(shift(t, a, c), c, d, a + d - c)
      }

      assert(!shift(t, a, c).hasFreeVariablesIn(d, a))
      if(b < 0){
        boundRangeDecrease(shift(t, a, c), d, a, -b)       
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
      }
    }.ensuring(shift(shift(t, a, c), b, d) == shift(t, a + b, c))

    @opaque @pure
    def boundRangeShift(t: Term, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
      require(c >= 0)
      require(a >= 0)
      require(b >= 0)
      require(!t.hasFreeVariablesIn(a, b))
      require(if(d < 0){!t.hasFreeVariablesIn(c, -d)} else true)
      t match {
        case Var(k) => ()
        case Abs(_, body) => boundRangeShift(body, d, c + 1, a + 1, b)
        case App(t1, t2) => {
          boundRangeShift(t1, d, c, a, b)
          boundRangeShift(t2, d, c, a, b)
        }
        case Fix(f) => boundRangeShift(f, d, c, a, b)
      }
    }.ensuring(
      if(d >= 0){
        (if(c >= a && c <= a + b)           {!shift(t, d, c).hasFreeVariablesIn(a, b + d)} else {true}) &&
        (if(c <= a + b)                     {!shift(t, d, c).hasFreeVariablesIn(a + d, b)} else {true}) &&
        (if(c >= a)                         {!shift(t, d, c).hasFreeVariablesIn(a, b)} else {true})
      }
      else{
        (if(a + b <= c)                     {!shift(t, d, c).hasFreeVariablesIn(a, b)} else true) &&
        (if(a + b >= c && a <= c)           {!shift(t, d, c).hasFreeVariablesIn(a, c - a)} else true) &&
        (if(a + b >= -d + c && a <= -d + c) {!shift(t, d, c).hasFreeVariablesIn(c, a + b + d - c)} else true) &&
        (if(a >= -d + c)                    {!shift(t, d, c).hasFreeVariablesIn(a + d, b)} else true) 
      })

    def boundRangeSubstitutionLemma(t: Term, j: BigInt, s: Term): Unit = {
      require(j >= 0)
      require(!s.hasFreeVariablesIn(0, j+1))

      t match {
        case Var(k) => {
          boundRangeIncreaseCutoff(s, 0, j, j+1)
        }
        case Abs(_, body) => {
          boundRangeShift(s, 1, 0, 0, j+1)
          boundRangeIncreaseCutoff(shift(s, 1, 0), 0, j + 1, j+2)
          boundRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
        }
        case App(t1, t2) => {
          boundRangeSubstitutionLemma(t1, j, s)
          boundRangeSubstitutionLemma(t2, j, s)
        }
        case Fix(f) => {
          boundRangeSubstitutionLemma(f, j, s)
        }
      }
    }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(j, 1))
  }

  object Types{

    import LambdaOmegaProperties.Types._
    import Transformations.Types._

    // @opaque @pure
    // def boundRangeSubstitutionIdentity(t: Type, j: BigInt, typ: Type): Unit = {
    //   require(j >= 0)
    //   require(!t.hasFreeVariablesIn(j, 1))

    //   t match {
    //     case VariableType(k) => ()
    //     case BasicType(_) =>  ()
    //     case AbsType(_, body) => {
    //       boundRangeSubstitutionIdentity(body, j+1, shift(typ, 1 ,0))
    //     }
    //     case ArrowType(t1, t2) => {
    //       boundRangeSubstitutionIdentity(t1, j, typ)
    //       boundRangeSubstitutionIdentity(t2, j, typ)
    //     }
    //     case AppType(t1, t2) => {
    //       boundRangeSubstitutionIdentity(t1, j, typ)
    //       boundRangeSubstitutionIdentity(t2, j, typ)
    //     }
    //   }

    // }.ensuring(
    //   substitute(t, j, typ) == t
    // )

    // @opaque @pure
    // def shift0Identity(t: Type, c: BigInt): Unit = {
    //   require(c >= 0)
    //   t match {
    //     case VariableType(k) => ()
    //     case BasicType(_) => ()
    //     case AbsType(_, body) => {
    //       shift0Identity(body, c+1)
    //     }
    //     case ArrowType(t1, t2) => {
    //       shift0Identity(t1, c)
    //       shift0Identity(t2, c)
    //     }
    //     case AppType(t1, t2) => {
    //       shift0Identity(t1, c)
    //       shift0Identity(t2, c)
    //     }
    //   }
    // }.ensuring(shift(t, 0, c) == t)

    @opaque @pure
    def boundRangeShiftComposition(t: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
      require(a >= 0)
      require(c >= 0)
      require(d >= 0)
      require(d <= c + a)
      require(if(d < c) !t.hasFreeVariablesIn(d, c - d) else !t.hasFreeVariablesIn(c, d - c))
      require((b >= 0) || (-b <= a))


      if (d < c){
        boundRangeShift(t, a, c, c, 0)
        boundRangeShift(t, a, c, d, c - d)
        boundRangeConcatenation(shift(t, a, c), d, c - d, a)
        boundRangeDecrease(shift(t, a, c), d, c - d + a, a)
      }
      else{
        boundRangeShift(t, a, c, c, d - c)
        boundRangeIncreaseCutoff(shift(t, a, c), c, d, a + d - c)
      }

      assert(!shift(t, a, c).hasFreeVariablesIn(d, a))
      if(b < 0){
        boundRangeDecrease(shift(t, a, c), d, a, -b)      
      }
      else{
        ()
      }

      t match {
        case VariableType(_) => ()
        case BasicType(_) => ()
        case AbsType(_, body) => {
          boundRangeShiftComposition(body, a, b, c + 1, d + 1)
        }
        case ArrowType(t1, t2) => {
          boundRangeShiftComposition(t1, a, b, c, d)
          boundRangeShiftComposition(t2, a, b, c, d)
        }
        case AppType(t1, t2) => {
          boundRangeShiftComposition(t1, a, b, c, d)
          boundRangeShiftComposition(t2, a, b, c, d)
        }
      }
    }.ensuring(
      (if(b < 0){!shift(t, a, c).hasFreeVariablesIn(d, -b)} else true) &&
      shift(shift(t, a, c), b, d) == shift(t, a + b, c)
    )

    @opaque @pure
    def boundRangeShift(t: Type, d: BigInt, c: BigInt, a: BigInt, b: BigInt): Unit = {
      require(c >= 0)
      require(b >= 0)
      require(a >= 0)
      require(!t.hasFreeVariablesIn(a, b))
      require(if(d < 0){!t.hasFreeVariablesIn(c, -d)} else true)

      t match {
        case BasicType(_) => ()
        case VariableType(_) => ()
        case AbsType(_, body)   => {
          boundRangeShift(body, d, c+1, a + 1, b)
        }
        case ArrowType(t1, t2)    => {
          boundRangeShift(t1, d, c, a, b)
          boundRangeShift(t2, d, c, a, b)
        }
        case AppType(t1, t2)    => {
          boundRangeShift(t1, d, c, a, b)
          boundRangeShift(t2, d, c, a, b)
        }
      }

    }.ensuring(
      if(d >= 0){
        (if(c >= a && c <= a + b)           {!shift(t, d, c).hasFreeVariablesIn(a, b + d)} else {true}) &&
        (if(c <= a + b)                     {!shift(t, d, c).hasFreeVariablesIn(a + d, b)} else {true}) &&
        (if(c >= a)                         {!shift(t, d, c).hasFreeVariablesIn(a, b)} else {true})
      }
      else{
        (if(a + b <= c)                     {!shift(t, d, c).hasFreeVariablesIn(a, b)} else true) &&
        (if(a + b >= c && a <= c)           {!shift(t, d, c).hasFreeVariablesIn(a, c - a)} else true) &&
        (if(a + b >= -d + c && a <= -d + c) {!shift(t, d, c).hasFreeVariablesIn(c, a + b + d - c)} else true) &&
        (if(a >= -d + c)                    {!shift(t, d, c).hasFreeVariablesIn(a + d, b)} else true) 
      })

    def boundRangeSubstitutionLemma(t: Type, j: BigInt, s: Type): Unit = {
      require(j >= 0)
      require(!s.hasFreeVariablesIn(0, j+1))

      t match {
        case BasicType(_) => ()
        case VariableType(k) => {
          boundRangeIncreaseCutoff(s, 0, j, j+1)
        }
        case AbsType(_, body) => {
          boundRangeShift(s, 1, 0, 0, j+1)
          boundRangeIncreaseCutoff(shift(s, 1, 0), 0, j + 1, j+2)
          boundRangeSubstitutionLemma(body, j+1, shift(s, 1, 0))
        }
        case ArrowType(t1, t2) => {
          boundRangeSubstitutionLemma(t1, j, s)
          boundRangeSubstitutionLemma(t2, j, s)
        }
        case AppType(t1, t2) => {
          boundRangeSubstitutionLemma(t1, j, s)
          boundRangeSubstitutionLemma(t2, j, s)
        }
      }
    }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(j, 1))
  }

}