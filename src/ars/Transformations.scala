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

    @opaque @pure
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

    @opaque @pure
    def boundRangeSubstitutionIdentity(t: Type, j: BigInt, typ: Type): Unit = {
      require(j >= 0)
      require(!t.hasFreeVariablesIn(j, 1))

      t match {
        case VariableType(k) => ()
        case BasicType(_) =>  ()
        case AbsType(_, body) => {
          boundRangeSubstitutionIdentity(body, j+1, shift(typ, 1 ,0))
        }
        case ArrowType(t1, t2) => {
          boundRangeSubstitutionIdentity(t1, j, typ)
          boundRangeSubstitutionIdentity(t2, j, typ)
        }
        case AppType(t1, t2) => {
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
        case VariableType(k) => ()
        case BasicType(_) => ()
        case AbsType(_, body) => {
          shift0Identity(body, c+1)
        }
        case ArrowType(t1, t2) => {
          shift0Identity(t1, c)
          shift0Identity(t2, c)
        }
        case AppType(t1, t2) => {
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
      require(!t.hasFreeVariablesIn(a, b))

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
      )

    @opaque @pure
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
    def shiftCommutativityPosPos(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(d >= 0)
    
      subs match {
        case BasicType(_) => ()
        case ArrowType(t1, t2) =>
          shiftCommutativityPosPos(t1, b, c, a, d)
          shiftCommutativityPosPos(t2, b, c, a, d)
        case AppType(t1, t2) => 
          shiftCommutativityPosPos(t1, b, c, a, d)
          shiftCommutativityPosPos(t2, b, c, a, d)
        case VariableType(v) => ()
        case AbsType(_, t) => shiftCommutativityPosPos(t, b, c+1, a, d+1) 
        
      }
    }.ensuring(
      if d <= c                then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
      if d - b >= c            then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
      if d >= c && d - b <= c  then shift(shift(subs, b, c), a, d) == shift(shift(subs, a, c), b, c) else
      true)

    @opaque @pure
    def shiftCommutativityPosNeg(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
      require(c >= 0)
      require(d >= 0)
      require(b >= 0)
      require(a < 0)
      require(if d >= c && b >= d - c  then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(c, -a) else
              if b <= d - c            then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d - b, -a) else
              if -a <= c - d           then !shift(subs, b, c).hasFreeVariablesIn(d, -a) || !subs.hasFreeVariablesIn(d, -a) else
              if d <= c && -a >= c - d then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) else
              true) 

      subs match {
        case BasicType(_) => ()
        case ArrowType(t1, t2) =>
          shiftCommutativityPosNeg(t1, b, c, a, d)
          shiftCommutativityPosNeg(t2, b, c, a, d)
        case AppType(t1, t2) => 
          shiftCommutativityPosNeg(t1, b, c, a, d)
          shiftCommutativityPosNeg(t2, b, c, a, d)
        case VariableType(v) => ()
        case AbsType(_, t) => shiftCommutativityPosNeg(t, b, c+1, a, d+1) 
        
      }
    }.ensuring(
      if d >= c && b >= d - c  then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(c, -a) &&
                                    shift(shift(subs, b, c), a, d) == shift(shift(subs, a, c), b, c) else
      if b <= d - c            then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d - b, -a) &&
                                    shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
      if -a <= c - d           then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) &&
                                    shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
      if d <= c && -a >= c - d then !shift(subs, b, c).hasFreeVariablesIn(d, -a) && !subs.hasFreeVariablesIn(d, -a) &&
                                    shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, d)
      else true)

    @opaque @pure
    def shiftCommutativityNegPos(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
      require(c >= 0)
      require(d >= 0)
      require(b < 0)
      require(a >= 0)
      require(!subs.hasFreeVariablesIn(c, -b))
      
      //Weaker but more complex precond
      // require(if d >= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) else 
      //         if d <= c                then !subs.hasFreeVariablesIn(c, -b) || !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) else
      //         true) 

      subs match {
        case BasicType(_) => ()
        case ArrowType(t1, t2) =>
          shiftCommutativityNegPos(t1, b, c, a, d)
          shiftCommutativityNegPos(t2, b, c, a, d)
        case AppType(t1, t2) => 
          shiftCommutativityNegPos(t1, b, c, a, d)
          shiftCommutativityNegPos(t2, b, c, a, d)
        case VariableType(v) => ()
        case AbsType(_, t) => shiftCommutativityNegPos(t, b, c+1, a, d+1) 
        
      }
    }.ensuring(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d - b).hasFreeVariablesIn(c, - b) && 
                                        shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
               if d <= c                then !subs.hasFreeVariablesIn(c, -b) && !shift(subs, a, d).hasFreeVariablesIn(c + a, - b) && 
                                        shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
               true)


    @opaque @pure
    def shiftCommutativityNegNeg(subs: Type, b: BigInt, c: BigInt, a: BigInt, d: BigInt) : Unit ={
      require(c >= 0)
      require(d >= 0)
      require(a < 0)
      require(b < 0)
      require(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d - b, -a) else
              if d <= c && -a <= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) else 
              if d <= c && -a >= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
                                                              !shift(subs, b, c).hasFreeVariablesIn(d, -a) else
              true) 

      subs match {
        case BasicType(_) => ()
        case ArrowType(t1, t2) =>
          shiftCommutativityNegNeg(t1, b, c, a, d)
          shiftCommutativityNegNeg(t2, b, c, a, d)
        case AppType(t1, t2) => 
          shiftCommutativityNegNeg(t1, b, c, a, d)
          shiftCommutativityNegNeg(t2, b, c, a, d)
        case VariableType(v) => ()
        case AbsType(_, t) => shiftCommutativityNegNeg(t, b, c+1, a, d+1) 
        
      }
    }.ensuring(if d >= c                then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d - b, -a) && 
                                             !shift(subs, a, d - b).hasFreeVariablesIn(c, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
                                             shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d - b), b, c) else
               if d <= c && -a <= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
                                             !shift(subs, a, d).hasFreeVariablesIn(c + a, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
                                             shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, c + a) else
               if d <= c && -a >= c - d then !subs.hasFreeVariablesIn(c, -b) && !subs.hasFreeVariablesIn(d, -a) && 
                                             !shift(subs, a, d).hasFreeVariablesIn(d, -b) && !shift(subs, b, c).hasFreeVariablesIn(d, -a) &&
                                             shift(shift(subs, b, c), a, d) == shift(shift(subs, a, d), b, d) else
               true)

  

    @opaque @pure
    def shiftSubstitutionCommutativityType(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
      require(k >= 0)
      require(c >= 0)
      require(
        if s < 0 then 
          !typ.hasFreeVariablesIn(c, -s) && !subs.hasFreeVariablesIn(c, -s)
        else true)

      typ match {
        case BasicType(_) => ()
        case ArrowType(t1, t2) => {
          shiftSubstitutionCommutativityType(t1, s, c, k, subs)
          shiftSubstitutionCommutativityType(t2, s, c, k, subs)
        }
        case AppType(t1, t2) => {
          shiftSubstitutionCommutativityType(t1, s, c, k, subs)
          shiftSubstitutionCommutativityType(t2, s, c, k, subs)
        }
        case VariableType(v) => 
          if c >= 0 && c <= k && s < 0 then
            boundRangeShiftComposition(subs, -s, s, c, c)
            if (v >= c && k == v + s){
                boundRangeShiftComposition(subs, -s, s, c, c)
                shift0Identity(subs, c)          
            }
          else ()
        case AbsType(argK, t) => {
          if s >= 0 then
            shiftCommutativityPosPos(subs, s, c, 1, 0)
          else
            boundRangeShift(subs, 1, 0, c, -s)
            if c > k then
              shiftCommutativityNegPos(subs, s, c, 1, 0)
            else
              shiftCommutativityPosPos(subs, -s, c, 1, 0)
          shiftSubstitutionCommutativityType(t, s, c+1, k+1, shift(subs, 1, 0))
        }
      }
    }.ensuring(
      if s >= 0 then
        if c >= 0 && c <= k then shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k+s, shift(subs, s, c))
                            else shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k, shift(subs, s, c))
      else if c >= 0 && c <= k 
        then !substitute(typ, k - s, shift(subs, -s, c)).hasFreeVariablesIn(c, -s) && 
             shift(substitute(typ, k - s, shift(subs, -s, c)), s, c) == substitute(shift(typ, s, c), k, subs)
        else !substitute(typ, k, subs).hasFreeVariablesIn(c, -s) && 
             shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k, shift(subs, s, c))
    )





    @opaque @pure
    def boundRangeSubstitutionLemma(t: Type, j: BigInt, s: Type, a: BigInt, b: BigInt, c: BigInt, d: BigInt): Unit = {
      require(j >= 0)
      require(a >= 0)
      require(b >= 0)
      require(c >= 0)
      require(d >= 0)
      require(!s.hasFreeVariablesIn(c, a))
      require(!t.hasFreeVariablesIn(d, b))

      t match 
        case BasicType(_) =>  ()
        case ArrowType(t1, t2) => 
          boundRangeSubstitutionLemma(t1, j, s, a, b, c, d)
          boundRangeSubstitutionLemma(t2, j, s, a, b, c, d)
        case AppType(t1, t2) => 
          boundRangeSubstitutionLemma(t1, j, s, a, b, c, d)
          boundRangeSubstitutionLemma(t2, j, s, a, b, c, d)
        case VariableType(v) => 
          if c <= d then
            if c + a >= d + b then
              boundRangeIncreaseCutoff(s, c, d, a)
              boundRangeDecrease(s, d, a - (d - c), b) 
            else if c + a <= d + b && c + a >= d then
              boundRangeDecrease(t, d, b, a - (d - c))
              boundRangeIncreaseCutoff(s, c, d, a)
            else ()
          else 
            if c + a <= d + b then
              boundRangeIncreaseCutoff(t, d, c, b)
              boundRangeDecrease(t, c, b - (c - d), a)
            else if c + a >= d + b && c <= d + b then
              boundRangeDecrease(s, c, a, b - (c - d))
              boundRangeIncreaseCutoff(t, d, c, b)
            else ()
        case AbsType(_, body) =>
          if c > 0 then
            boundRangeShift(s, 1, 0, c, a)
          else
            boundRangeShift(s, 1, 0, 0, a)
            boundRangeIncreaseCutoff(shift(s, 1, 0), 0, 1 , a + 1)
          boundRangeSubstitutionLemma(body, j + 1, shift(s, 1, 0), a, b, c + 1, d + 1)
    }.ensuring(
      if c <= d then
        if c + a >= d + b               then !substitute(t, j, s).hasFreeVariablesIn(d, b) else
        if c + a <= d + b && c + a >= d then !substitute(t, j, s).hasFreeVariablesIn(d, a - (d - c))
        else true /*non trivial range*/
      else
        if c + a <= d + b               then !substitute(t, j, s).hasFreeVariablesIn(c, a) else
        if c + a >= d + b && c <= d + b then !substitute(t, j, s).hasFreeVariablesIn(c, b - (c - d))
        else true /*non trivial range*/)




    
    @opaque @pure
    def substitutionCommutativity(t: Type, j: BigInt, s: Type, k: BigInt, u: Type): Unit = {
      require(j >= 0)
      require(k >= 0)
      require(j != k)
      require(!u.hasFreeVariablesIn(j, 1))

      t match 
        case VariableType(i) => 
          if(i == k) {
            boundRangeSubstitutionIdentity(u, j, substitute(s, k, u))
          }
        
        case BasicType(_) => ()
        case ArrowType(t1, t2) => 
          substitutionCommutativity(t1, j, s, k, u)
          substitutionCommutativity(t2, j, s, k, u)
        
        case AppType(t1, t2) => 
          substitutionCommutativity(t1, j, s, k, u)
          substitutionCommutativity(t2, j, s, k, u)
        
        case AbsType(_, b) => 
          shiftSubstitutionCommutativityType(s, 1, 0, k, u)
          boundRangeShift(u, 1, 0, j, 1)
          substitutionCommutativity(b, j+1, shift(s, 1, 0), k+1, shift(u, 1, 0))
    }.ensuring(
      substitute(substitute(t, j, s), k, u)
      ==
      substitute(substitute(t, k, u), j, substitute(s, k, u))
    )

    //absSubst

    @opaque @pure
    def boundRangeAbsSubst(body: Type, arg: Type, c: BigInt, d: BigInt) = {
      require(c >= 0)
      require(d >= 0)
      require(!arg.hasFreeVariablesIn(c, d))
      require(!body.hasFreeVariablesIn(c + 1, d))

      boundRangeShift(arg, 1, 0, c, d)
      boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0), d, d, c + 1, c + 1)
      boundRangeShift(arg, 1, 0, 0, 0)
      boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
      boundRangeShift(substitute(body, 0, shift(arg, 1, 0)), -1, 0, c + 1, d)
    }.ensuring(!absSubstitution(body, arg).hasFreeVariablesIn(c, d))

    @opaque @pure
    def shiftAbsSubstitutionCommutativity(body: Type, arg: Type, d: BigInt, c: BigInt) = {
      require(c >= 0)
      require(if d < 0 then !arg.hasFreeVariablesIn(c, -d) && !body.hasFreeVariablesIn(c + 1, -d) else true)

      boundRangeShift(arg, 1, 0, 0, 0)
      boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))

      if d < 0 then
        boundRangeShift(arg, 1, 0, c, -d)
        boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0), -d, -d, c + 1, c + 1)
        boundRangeShift(substitute(body, 0, shift(arg, 1, 0)), -1, 0, c + 1, -d)
        shiftCommutativityNegNeg(substitute(body, 0, shift(arg, 1, 0)), -1, 0, d, c)
        shiftSubstitutionCommutativityType(body, d, c + 1, 0, shift(arg, 1, 0))
        shiftCommutativityPosNeg(arg, 1, 0, d, c + 1)
      else
        shiftCommutativityNegPos(substitute(body, 0, shift(arg, 1, 0)), -1, 0, d, c)
        shiftSubstitutionCommutativityType(body, d, c + 1, 0, shift(arg, 1, 0))
        shiftCommutativityPosPos(arg, d, c, 1, 0)
    }.ensuring(_ => shift(absSubstitution(body, arg), d, c) == absSubstitution(shift(body, d, c + 1), shift(arg, d, c)))

    @opaque @pure
    def absSubstSubstCommutativity(body: Type, arg: Type, j: BigInt, s: Type): Unit = {
      require(j >= 0)
      require(!s.hasFreeVariablesIn(0, 1))

      boundRangeShift(arg, 1, 0, 0, 0)
      boundRangeSubstitutionLemma(body, 0, shift(arg, 1, 0))
      shiftSubstitutionCommutativityType(substitute(body, 0, shift(arg, 1, 0)), -1, 0, j, s)
      boundRangeShift(s, 1, 0, 0, 0)
      substitutionCommutativity(body, 0, shift(arg, 1, 0), j + 1, shift(s, 1, 0))
      shiftSubstitutionCommutativityType(arg, 1, 0, j, s)

    }.ensuring(
      substitute(absSubstitution(body, arg), j, s)
      ==
      absSubstitution(substitute(body, j + 1, shift(s, 1, 0)), substitute(arg, j, s))
    )    
  }

    // @opaque @pure
  // def shiftSubstitutionCommutativityTypeNeg(typ: Type, s: BigInt, c: BigInt, k: BigInt, subs: Type): Unit = {
  //   require(c >= 0 && c <= k)
  //   require(s < 0)
  //   require(!typ.hasFreeVariablesIn(c, -s))
  //   require(!subs.hasFreeVariablesIn(c, -s))
  //   require(k + s >= 0) 
  //   // boundRangeShift(subs, -s, c, c, 0)
  //   // boundRangeSubstitutionLemma(typ, k - s, shift(subs, -s, c), -s, -s, c, c)


  //   typ match
  //     case BasicType(_) => ()
  //     case ArrowType(t1, t2) => 
  //       shiftSubstitutionCommutativityTypeNeg(t1, s, c, k, subs)
  //       shiftSubstitutionCommutativityTypeNeg(t2, s, c, k, subs)
  //     case AppType(t1, t2) => 
  //       shiftSubstitutionCommutativityTypeNeg(t1, s, c, k, subs)
  //       shiftSubstitutionCommutativityTypeNeg(t2, s, c, k, subs)

  //     case VariableType(v) => 
  //       assert(!substitute(typ, k, subs).hasFreeVariablesIn(c, -s))
  //       assert(shift(substitute(VariableType(BigInt("8856")), BigInt("11296"), BasicType("")), BigInt("-2440"), BigInt("8859"))
  //           == VariableType(BigInt("8856")))
  //       assert(substitute(shift(typ, s, c), k+s, BasicType("")))
  //       assert(shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k+s, shift(subs, s, c)))
        
        
  //       // boundRangeShiftComposition(subs, -s, s, c, c)
  //       // if (v >= c && k == v + s){
  //       //     boundRangeShiftComposition(subs, -s, s, c, c)
  //       //     shift0Identity(subs, c)          
  //       // }
  //     case AbsType(argK, t) => 
  //       boundRangeShift(subs, 1, 0, c, -s)
  //       shiftSubstitutionCommutativityTypeNeg(t, s, c + 1, k + 1, shift(subs, 1, 0))
  //       // shiftCommutativityPosPos(subs, -s, c, 1, 0)          
  // }.ensuring(
  //   !substitute(typ, k, subs).hasFreeVariablesIn(c, -s) &&
  //   (shift(substitute(typ, k, subs), s, c) == substitute(shift(typ, s, c), k+s, shift(subs, s, c)))
  // )

}