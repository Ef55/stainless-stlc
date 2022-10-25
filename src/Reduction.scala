// import stainless.lang._
// import stainless.collection._
// import stainless.annotation._

// object Reduction {
//   import STLC._

//   import Transformations._
//   import TransformationsProperties.{Terms => TermsProp}

//   sealed trait ReductionRule
//   sealed trait AppRule extends ReductionRule
//   case object App1Congruence extends AppRule
//   case object App2Congruence extends AppRule
//   case object AbsAppReduction extends AppRule
//   sealed trait FixRule extends ReductionRule
//   case object FixCongruence extends FixRule
//   case object AbsFixReduction extends FixRule
//   sealed trait AbsRule extends ReductionRule
//   case object AbsCongruence extends AbsRule


//   // ↑⁻¹( [0 -> ↑¹(arg)]body )
//   def absSubstitution(body: Term, arg: Term): Term = {
//     assert(!arg.hasFreeVariablesIn(0, 0))
//     TermsProp.boundRangeShift(arg, 1, 0, 0, 0)
//     TermsProp.boundRangeSubstitutionLemma(body, 0, Terms.shift(arg, 1, 0))
//     Terms.shift(Terms.substitute(body, 0, Terms.shift(arg, 1, 0)), -1, 0)
//   }

//   // [t -> t']
//   def reducesTo(t: Term, tp: Term): Option[ReductionRule] = {
//     t match {
//       case Var(_) => None[ReductionRule]()
//       case Abs(argTyp, body) =>{
//         tp match {
//           case Abs(argTypp, bodyp) if argTyp == argTypp && reducesTo(body, bodyp).isDefined => Some[ReductionRule](AbsCongruence)
//           case _ => None[ReductionRule]()
//         }
//       }
//       case App(t1, t2) => {
//         (tp match {
//           case App(t1p, t2p) if reducesTo(t1, t1p).isDefined && t2 == t2p  => Some[ReductionRule](App1Congruence)
//           case App(t1p, t2p) if t1 == t1p && reducesTo(t2, t2p).isDefined => Some[ReductionRule](App2Congruence)
//           case _ => None[ReductionRule]()
//         }) orElse (t1 match {
//           case Abs(_, body) if absSubstitution(body, t2) == tp => Some[ReductionRule](AbsAppReduction)
//           case _ => None[ReductionRule]()
//         })
//       }
//       case Fix(f) => {
//         (tp match {
//           case Fix(fp) if reducesTo(f, fp).isDefined => Some[ReductionRule](FixCongruence)
//           case _ => None[ReductionRule]()
//         }) orElse (f match {
//           case Abs(_, body) if absSubstitution(body, t) == tp => Some[ReductionRule](AbsFixReduction)
//           case _ => None[ReductionRule]()
//         })
//       }
//     }
//   }

//   /// Call-by-value lambda calculus evaluation

//   def reduceCallByValue(t: Term): Option[Term] = {
//     t match {
//       case Var(_) => None[Term]()
//       case Abs(_, _) => None[Term]()
//       case App(t1, t2) => {
//         if(!t1.isValue) {
//           reduceCallByValue(t1).map(t1p => App(t1p, t2))
//         }
//         else if(!t2.isValue) {
//           reduceCallByValue(t2).map(t2p => App(t1, t2p))
//         }
//         else {
//           t1 match {
//             case Abs(_, body) => {
//               Some(absSubstitution(body, t2))
//             }
//             case _ => None[Term]()
//           }
//         }
//       }
//       case Fix(f) => {
//         if(!f.isValue) {
//           reduceCallByValue(f).map(Fix(_))
//         }
//         else {
//           f match {
//             case Abs(_, body) => {
//               Some(absSubstitution(body, t))
//             }
//             case _ => None[Term]()
//           }
//         }
//       }
//     }
//   }

// }

// object ReductionProperties {
//   import STLC._
//   import Reduction._

//   /// ReducesTo semantics & inversion

//   def appReducesToSoundness(app: App, tp: Term): Unit = {
//     require(reducesTo(app, tp).isDefined)
//   }.ensuring(reducesTo(app, tp).get.isInstanceOf[AppRule])

//   def app1CongruenceInversion(t: Term, tp: Term): Unit = {
//     require(reducesTo(t, tp).isDefined)
//     require(reducesTo(t, tp).get == App1Congruence)

//     assert(t.isInstanceOf[App])
//   }.ensuring(
//     t.isInstanceOf[App] && tp.isInstanceOf[App] &&
//     (t.asInstanceOf[App].t2 == tp.asInstanceOf[App].t2) &&
//     reducesTo(t.asInstanceOf[App].t1, tp.asInstanceOf[App].t1).isDefined
//   )

//   def app2CongruenceInversion(t: Term, tp: Term): Unit = {
//     require(reducesTo(t, tp).isDefined)
//     require(reducesTo(t, tp).get == App2Congruence)

//     assert(t.isInstanceOf[App])
//   }.ensuring(
//     t.isInstanceOf[App] && tp.isInstanceOf[App] &&
//     (t.asInstanceOf[App].t1 == tp.asInstanceOf[App].t1) &&
//     reducesTo(t.asInstanceOf[App].t2, tp.asInstanceOf[App].t2).isDefined
//   )

//   def absAppReductionInversion(t: Term, tp: Term): Unit = {
//     require(reducesTo(t, tp).isDefined)
//     require(reducesTo(t, tp).get == AbsAppReduction)

//     assert(t.isInstanceOf[App])
//     val App(t1, _) = t
//     assert(t1.isInstanceOf[Abs])
//   }.ensuring(
//     t.isInstanceOf[App] && t.asInstanceOf[App].t1.isInstanceOf[Abs] &&
//     ( 
//       tp 
//       == 
//       absSubstitution(t.asInstanceOf[App].t1.asInstanceOf[Abs].body, t.asInstanceOf[App].t2) 
//     )
//   )

//   def fixReducesToSoundness(fix: Fix, tp: Term): Unit = {
//     require(reducesTo(fix, tp).isDefined)
//   }.ensuring(reducesTo(fix, tp).get.isInstanceOf[FixRule])

//   def fixCongruenceInversion(t: Term, tp: Term): Unit = {
//     require(reducesTo(t, tp).isDefined)
//     require(reducesTo(t, tp).get == FixCongruence)

//     assert(t.isInstanceOf[Fix])
//   }.ensuring(
//     t.isInstanceOf[Fix] && tp.isInstanceOf[Fix] &&
//     reducesTo(t.asInstanceOf[Fix].t, tp.asInstanceOf[Fix].t).isDefined
//   )

//   def absFixReductionInversion(t: Term, tp: Term): Unit = {
//     require(reducesTo(t, tp).isDefined)
//     require(reducesTo(t, tp).get == AbsFixReduction)

//     assert(t.isInstanceOf[Fix])
//     val Fix(f) = t
//     assert(f.isInstanceOf[Abs])
//   }.ensuring(
//     t.isInstanceOf[Fix] && t.asInstanceOf[Fix].t.isInstanceOf[Abs] &&
//     ( 
//       tp 
//       == 
//       absSubstitution(t.asInstanceOf[Fix].t.asInstanceOf[Abs].body, t) 
//     )
//   )

//   def absReducesToSoundness(abs: Abs, tp: Term): Unit = {
//     require(reducesTo(abs, tp).isDefined)
//   }.ensuring(reducesTo(abs, tp).get.isInstanceOf[AbsRule])

//   def absCongruenceInversion(t: Term, tp: Term): Unit = {
//     require(reducesTo(t, tp).isDefined)
//     require(reducesTo(t, tp).get == AbsCongruence)
//   }.ensuring(
//     t.isInstanceOf[Abs] && tp.isInstanceOf[Abs] &&
//     ( t.asInstanceOf[Abs].argType == tp.asInstanceOf[Abs].argType ) &&
//     reducesTo(t.asInstanceOf[Abs].body, tp.asInstanceOf[Abs].body).isDefined
//   )

//   /// Call-by-value soudness

//   @opaque @pure
//   def reduceCallByValueSoundness(t: Term): ReductionRule = {
//     require(reduceCallByValue(t).isDefined)
//     val tp = reduceCallByValue(t).get

//     t match {
//       case Var(_) => assert(false)
//       case Abs(_, _) => assert(false)
//       case App(t1, t2) => {
//         if(!t1.isValue) {
//           reduceCallByValueSoundness(t1)
//         }
//         else if(!t2.isValue) {
//           reduceCallByValueSoundness(t2)
//         }
//         else {
//           assert(reducesTo(t, tp).isDefined)
//         }
//       }
//       case Fix(f) => {
//         if(!f.isValue) {
//           reduceCallByValueSoundness(f)
//         }
//         else {
//           assert(reducesTo(t, tp).isDefined)
//         }
//       }
//     }

//     assert(reducesTo(t, reduceCallByValue(t).get).isDefined)
//     reducesTo(t, reduceCallByValue(t).get).get
//   }.ensuring(res =>
//     reducesTo(t, reduceCallByValue(t).get).isDefined &&
//     ( res == reducesTo(t, reduceCallByValue(t).get).get )
//   )
// }