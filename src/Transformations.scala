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
      } 
      == 
      !t.hasFreeVariablesIn(a, b))

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


    @opaque @pure
    def shiftCommutativity(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
      require(c >= 0)
      require(d >= 0)
      require(if a >= 0 then
                if b < 0 then 
                  if d >= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) else 
                  if d <= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) else
                  true
                else true
              else
                if b >= 0 then
                  if d >= c && b >= d - c  then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(c, -a) else
                  if b <= d - c            then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d - b, -a) else
                  if -a <= c - d           then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d, -a) else
                  if d <= c && -a >= c - d then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) else
                  true
              //   else
              //     if d >= c && d - a <= c - b then 
              //       !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
              //       !shift(subs, a, d).hasFreeVariablesIn(c, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) else
              //     if d >= c && d - a >= c - b then
              //       !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
              //       !shift(subs, a, d).hasFreeVariablesIn(d - a + b, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a)
              //     else true
                else true) 
        // if d <= c && c + b >= d then !subs.hasFreeVariablesIn(d, -a) && !shift(subs, b, c).hasFreeVariablesIn(d, - a) else

      subs match {
        case BasicType(_) => ()
        case ArrowType(t1, t2) =>
          shiftCommutativity(t1, b, c, a, d)
          shiftCommutativity(t2, b, c, a, d)
        case AppType(t1, t2) => 
          shiftCommutativity(t1, b, c, a, d)
          shiftCommutativity(t2, b, c, a, d)
        case VariableType(v) => ()
        case AbsType(_, t) => shiftCommutativity(t, b, c+1, a, d+1) 
        
      }
    }.ensuring(
      if a >= 0 then
        if b >= 0 then
          if d <= c                then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
          if d - b >= c            then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
          if d >= c && d - b <= c  then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, c), b, c) else
          true
        else
          if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) && 
                                        shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
          if d <= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) && 
                                        shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
          true //in this case shifts do not trivially commute
      else 
        if b >= 0 then
          if d >= c && b >= d - c  then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(c, -a) &&
                                       shift(shift(subs, b, c), a, d) == shift(shift(subs, a, c), b, c)
          if b <= d - c            then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d - b, -a) &&
                                       shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c)
          if -a <= c - d           then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) &&
                                       shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a)
          if d <= c && -a >= c - d then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) &&
                                       shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, d)
          else true
      //   else
      //     if d >= c && d - a <= c - b then 
      //       !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
      //       !shift(subs, a, d).hasFreeVariablesIn(c, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
      //       shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c) else
      //     if d >= c && d - a >= c - b then
      //       !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
      //       !shift(subs, a, d).hasFreeVariablesIn(d - a + b, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
      //       shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, d - a + b)
          else true)

    

    // @opaque @pure
    // def shiftCommutativity4(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
    //   require(c >= 0)
    //   require(d >= 0)
    //   require(b < 0)
    //   require(a < 0)
    //   require(d <= c+a)
    //   require(!subs.hasFreeVariablesIn(c, -b))
    //   require(!subs.hasFreeVariablesIn(d, -a))
    //   require(!shift(subs, b, c).hasFreeVariablesIn(d, -a))

    //   subs match {
    //     case BasicType(_) => ()
    //     case ArrowType(t1, t2) => {
    //       shiftCommutativity4(t1, b, c, a, d)
    //       shiftCommutativity4(t2, b, c, a, d)
    //     }
    //     case AppType(t1, t2) => {
    //       shiftCommutativity4(t1, b, c, a, d)
    //       shiftCommutativity4(t2, b, c, a, d)
    //     }
    //     case VariableType(v) => {
    //       ()
    //     }
    //     case AbsType(_, t) => {
    //       shiftCommutativity4(t, b, c+1, a, d+1) 
    //     }
    //   }
    // }.ensuring(
    //   !shift(subs, a, d).hasFreeVariablesIn(c+a, -b) &&
    //   shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c+a)
    // )


    // @opaque @pure
    // def shiftCommutativity4(subs: Type, d: BigInt, c: BigInt, a0: BigInt, a: BigInt) : Unit ={
    //   require(c >= 0)
    //   require(a >= 0)
    //   require(d < 0)
    //   require(a0 < 0)
    //   require(a <= c+a0)
    //   require(!subs.hasFreeVariablesIn(c, -d))
    //   require(!subs.hasFreeVariablesIn(a, -a0))
    //   require(!shift(subs, d, c).hasFreeVariablesIn(a, -a0))

    //   subs match {
    //     case BasicType(_) => ()
    //     case ArrowType(t1, t2) => {
    //       shiftCommutativity4(t1, d, c, a0, a)
    //       shiftCommutativity4(t2, d, c, a0, a)
    //     }
    //     case AppType(t1, t2) => {
    //       shiftCommutativity4(t1, d, c, a0, a)
    //       shiftCommutativity4(t2, d, c, a0, a)
    //     }
    //     case VariableType(v) => {
    //       ()
    //     }
    //     case AbsType(_, t) => {
    //       shiftCommutativity4(t, d, c+1, a0, a+1) 
    //     }
    //   }
    // }.ensuring(
    //   !shift(subs, a0, a).hasFreeVariablesIn(c+a0, -d) &&
    //   shift(shift(subs, d, c), a0, a) == shift(shift(subs, a0, a), d, c+a0)
    // )

    // @opaque @pure
    // def shiftSubstitutionCommutativityType(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    //   require(s >= 0)
    //   require(c >= 0 && c <= k)

    //   typ match {
    //     case BasicType(_) => ()
    //     case ArrowType(t1, t2) => {
    //       shiftSubstitutionCommutativityType(t1, s, c, k, subs)
    //       shiftSubstitutionCommutativityType(t2, s, c, k, subs)
    //     }
    //     case VariableType(v) => ()
    //     case UniversalType(t) => {
    //       shiftCommutativity(subs, c, 0, 1, s)
    //       shiftSubstitutionCommutativityType(t, s, c+1, k+1, shift(subs, 1, 0))
    //     }
    //   }
    // }.ensuring(
    //   shift(substitute(typ, k, subs), s, c) 
    //   == 
    //   substitute(shift(typ, s, c), k+s, shift(subs, s, c))
    // )

    // @opaque @pure
    // def shiftSubstitutionCommutativityType2(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    //   require(c > k)
    //   require(k >= 0)
    //   require(if (s < 0) {!subs.hasFreeVariablesIn(c, -s) && !typ.hasFreeVariablesIn(c, -s)} else {true})

    //   if(s < 0){
    //     boundRangeSubstitutionLemma1(typ, k, subs, -s, -s, c, c)
    //   }

    //   typ match {
    //     case BasicType(_) => {}
    //     case ArrowType(t1, t2) => {
    //       shiftSubstitutionCommutativityType2(t1, s, c, k, subs)
    //       shiftSubstitutionCommutativityType2(t2, s, c, k, subs)
    //     }
    //     case VariableType(v) => {}
    //     case UniversalType(t) => {
    //       if(s >= 0){
    //         shiftCommutativity(subs, c, 0, 1, s)
    //       }
    //       else{
    //         boundRangeShift(subs, 1, 0, c, -s)
    //         shiftCommutativity2(subs, s, c, 1, 0)
    //       }
    //       shiftSubstitutionCommutativityType2(t, s, c+1, k+1, shift(subs, 1, 0))
    //     }
    //   }
    // }.ensuring(
    //     (if(s < 0){ (
    //       !substitute(typ, k, subs).hasFreeVariablesIn(c, -s) 
    //     )} else true) &&
    //   (
    //     shift(substitute(typ, k, subs), s, c) 
    //     == 
    //     substitute(shift(typ, s, c), k, shift(subs, s, c))
    //   )
    // )

    // @opaque @pure
    // def shiftSubstitutionCommutativityTypeNeg(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
    //   require(c >= 0 && c <= k)
    //   require(s > 0)
    //   require(!typ.hasFreeVariablesIn(c, s))

    //   boundRangeShift(subs, s, c, c, 0)
    //   boundRangeSubstitutionLemma1(typ, k + s, shift(subs, s, c), s, s, c, c)


    //   typ match {
    //     case BasicType(_) => {}
    //     case ArrowType(t1, t2) => {
    //       shiftSubstitutionCommutativityTypeNeg(t1, s, c, k, subs)
    //       shiftSubstitutionCommutativityTypeNeg(t2, s, c, k, subs)
    //     }
    //     case VariableType(v) => {
    //       boundRangeShiftComposition(subs, s, -s, c, c)
    //       if (v >= c && k == v - s){
    //           boundRangeShiftComposition(subs, s, -s, c, c)
    //           shift0Identity(subs, c)          

    //       }
    //     }
    //     case UniversalType(t) => {
    //       shiftSubstitutionCommutativityTypeNeg(t, s, c + 1, k + 1, shift(subs, 1, 0))
    //       shiftCommutativity(subs, c, 0, 1, s)
    //     }
    //   }
    // }.ensuring(
    //   !substitute(typ, k + s, shift(subs, s, c)).hasFreeVariablesIn(c, s) &&
    //   (
    //     shift(substitute(typ, k + s, shift(subs, s, c)), -s, c) 
    //     == 
    //     substitute(shift(typ, -s, c), k, subs)
    //   )
    // )

    // @opaque @pure
    // def boundRangeSubstitutionLemma1(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    //   require(j >= 0)
    //   require(a >= 0)
    //   require(b >= 0)
    //   require(c >= 0)
    //   require(d >= 0)
    //   require(!s.hasFreeVariablesIn(c, a))
    //   require(!t.hasFreeVariablesIn(d, b))
    //   require(c + a >= d + b)
    //   require(c <= d)

    //   t match {
    //     case BasicType(_) => 
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))
    //     case ArrowType(t1, t2) => 
    //       boundRangeSubstitutionLemma1(t1, j, s, a, b, c, d)
    //       boundRangeSubstitutionLemma1(t2, j, s, a, b, c, d)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))
    //     case VariableType(v) => 
    //       boundRangeIncreaseCutoff(s, c, d, a)
    //       boundRangeDecrease(s, d, a - (d - c), b)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))
    //     case UniversalType(body) =>
    //       if(c > 0){
    //         boundRangeShift(s, 1, 0, c, a)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
    //       }
    //       else{
    //         assert(!s.hasFreeVariablesIn(0, a))
    //         boundRangeShift(s, 1, 0, 0, a)
    //         boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
    //       }
    //       boundRangeSubstitutionLemma1(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)

    //       assert(!substitute(body, j + 1, shift(s, 1, 0)).hasFreeVariablesIn(d + 1, b))
    //       assert(!UniversalType(substitute(body, j + 1, shift(s, 1, 0))).hasFreeVariablesIn(d, b))
    //       assert(!substitute(UniversalType(body), j, s).hasFreeVariablesIn(d, b))
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(d, b))

    //   }
    // }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(d, b))

    // @opaque @pure
    // def boundRangeSubstitutionLemma2(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    //   require(j >= 0)
    //   require(a >= 0)
    //   require(b >= 0)
    //   require(c >= 0)
    //   require(d >= 0)
    //   require(!s.hasFreeVariablesIn(c, a))
    //   require(!t.hasFreeVariablesIn(d, b))
    //   require(c + a <= d + b)
    //   require(c >= d)

    //   t match {
    //     case BasicType(_) => 
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(c, a))
    //     case ArrowType(t1, t2) => 
    //       boundRangeSubstitutionLemma2(t1, j, s, a, b, c, d)
    //       boundRangeSubstitutionLemma2(t2, j, s, a, b, c, d)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(c, a))
    //     case VariableType(v) => 
    //       boundRangeIncreaseCutoff(t, d, c, b)
    //       boundRangeDecrease(t, c, b - (c - d), a)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(c, a))
    //     case UniversalType(body) =>
    //       if(c > 0){
    //         boundRangeShift(s, 1, 0, c, a)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
    //       }
    //       else{
    //         assert(!s.hasFreeVariablesIn(0, a))
    //         boundRangeShift(s, 1, 0, 0, a)
    //         boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
    //       }
    //       boundRangeSubstitutionLemma2(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)

    //   }
    // }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(c, a))

    // @opaque @pure
    // def boundRangeSubstitutionLemma3(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    //   require(j >= 0)
    //   require(a >= 0)
    //   require(b >= 0)
    //   require(c >= 0)
    //   require(d >= 0)
    //   require(!s.hasFreeVariablesIn(c, a))
    //   require(!t.hasFreeVariablesIn(d, b))
    //   require(c <= d + b)
    //   require(c + a >= d + b)
    //   require(c >= d)

    //   t match {
    //     case BasicType(_) => 
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))
    //     case ArrowType(t1, t2) => 
    //       boundRangeSubstitutionLemma3(t1, j, s, a, b, c, d)
    //       boundRangeSubstitutionLemma3(t2, j, s, a, b, c, d)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))
    //     case VariableType(v) => 
    //       boundRangeDecrease(s, c, a, b - (c - d))
    //       boundRangeIncreaseCutoff(t, d, c, b)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))
    //     case UniversalType(body) =>
    //       if(c > 0){
    //         boundRangeShift(s, 1, 0, c, a)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
    //       }
    //       else{
    //         assert(!s.hasFreeVariablesIn(0, a))
    //         boundRangeShift(s, 1, 0, 0, a)
    //         boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
    //       }
    //       boundRangeSubstitutionLemma3(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)

    //   }
    // }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d)))

    // @opaque @pure
    // def boundRangeSubstitutionLemma4(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
    //   require(j >= 0)
    //   require(a >= 0)
    //   require(b >= 0)
    //   require(c >= 0)
    //   require(d >= 0)
    //   require(!s.hasFreeVariablesIn(c, a))
    //   require(!t.hasFreeVariablesIn(d, b))
    //   require(c + a >= d)
    //   require(c + a <= d + b)
    //   require(c <= d)

    //   t match {
    //     case BasicType(_) => 
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))
    //     case ArrowType(t1, t2) => 
    //       boundRangeSubstitutionLemma4(t1, j, s, a, b, c, d)
    //       boundRangeSubstitutionLemma4(t2, j, s, a, b, c, d)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))
    //     case VariableType(v) => 
    //       boundRangeDecrease(t, d, b, a - (d - c))
    //       boundRangeIncreaseCutoff(s, c, d, a)
    //       assert(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))
    //     case UniversalType(body) =>
    //       if(c > 0){
    //         boundRangeShift(s, 1, 0, c, a)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(c + 1, a))
    //       }
    //       else{
    //         assert(!s.hasFreeVariablesIn(0, a))
    //         boundRangeShift(s, 1, 0, 0, a)
    //         boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
    //         assert(!shift(s, 1, 0).hasFreeVariablesIn(1, a))
    //       }
    //       boundRangeSubstitutionLemma4(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)

    //   }
    // }.ensuring(!substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c)))

    // @opaque @pure
    // def substitutionCommutativity(t: Type, j: BigInt, s: Type, k: BigInt, u: Type): Unit = {
    //   require(j >= 0 && k >= 0)
    //   require(j != k)
    //   require(!u.hasFreeVariablesIn(j, 1))

    //   t match {
    //     case VariableType(i) => {
    //       if(i == k) {
    //         boundRangeSubstitutionIdentity(u, j, substitute(s, k, u))
    //       }
    //     }
    //     case BasicType(_) => ()
    //     case ArrowType(t1, t2) => {
    //       substitutionCommutativity(t1, j, s, k, u)
    //       substitutionCommutativity(t2, j, s, k, u)
    //     }
    //     case UniversalType(b) => {
    //       shiftSubstitutionCommutativityType(s, 1, 0, k, u)
    //       boundRangeShift(u, 1, 0, j, 1)
    //       substitutionCommutativity(b, j+1, shift(s, 1, 0), k+1, shift(u, 1, 0))
    //     }
    //   }
    // }.ensuring(
    //   substitute(substitute(t, j, s), k, u)
    //   ==
    //   substitute(substitute(t, k, u), j, substitute(s, k, u))
    // )    
  }

}