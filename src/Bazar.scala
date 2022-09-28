//   sealed trait EquivalenceWithoutTransDerivation{
//     def type1: Type = {
//       this match{
//         case ReflEqWTDerivation(t) => t 
//         case SymmEqWTDerivation(t1, _, _) => t1
//         case ArrowEqWTDerivation(t1, _, _, _) => t1
//         case AbsEqWTDerivation(t1, _, _) => t1
//         case AppEqWTDerivation(t1, _, _, _) => t1
//         case AppAbsEqWTDerivation(t1, _) => t1
//       }
//     }

//     def type2: Type = {
//       this match{
//         case ReflEqWTDerivation(t) => t 
//         case SymmEqWTDerivation(_, t2, _) => t2
//         case ArrowEqWTDerivation(_, t2, _, _) => t2
//         case AbsEqWTDerivation(_, t2, _) => t2
//         case AppEqWTDerivation(_, t2, _, _) => t2
//         case AppAbsEqWTDerivation(_, t2) => t2
//       }
//     }

//     def isValid: Boolean = {
//       this match {
//         case ReflEqWTDerivation(_) => true
//         case SymmEqWTDerivation(t1, t2, ed) => ed.isValid && ed.type1 == t2 && ed.type2 == t1
//         case ArrowEqWTDerivation(ArrowType(t11, t12), ArrowType(t21, t22), ed1, ed2) =>
//           ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
//           ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
//         case AbsEqWTDerivation(AbsType(k1, b1), AbsType(k2, b2), ed) => 
//           ed.isValid && ed.type1 == b1 && ed.type2 == b2 && k1 == k2
//         case AppEqWTDerivation(AppType(t11, t12), AppType(t21, t22), ed1, ed2) =>
//           ed1.isValid && ed2.isValid && ed1.type1 == t11 &&
//           ed1.type2 == t21 && ed2.type1 == t12 && ed2.type2 == t22
//         case AppAbsEqWTDerivation(AppType(AbsType(argK, body), t2), t3) =>
//           t3 == absSubstitution(body, t2) 
//         case AppAbsEqWTDerivation(_, _) => false
//       }
//     }
//   }
//   case class ReflEqWTDerivation(t: Type) extends EquivalenceWithoutTransDerivation
//   case class SymmEqWTDerivation(t1: Type, t2: Type, ed: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class ArrowEqWTDerivation(t1: ArrowType, t2: ArrowType, ed1: EquivalenceWithoutTransDerivation, ed2: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class AbsEqWTDerivation(t1: AbsType, t2: AbsType, ed: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class AppEqWTDerivation(t1: AppType, t2: AppType, ed: EquivalenceWithoutTransDerivation, ed2: EquivalenceWithoutTransDerivation) extends EquivalenceWithoutTransDerivation
//   case class AppAbsEqWTDerivation(t1: AppType, t2: Type) extends EquivalenceWithoutTransDerivation

//   sealed trait EquivalenceTransUpDerivation{
//     def type1: Type = {
//       this match{
//         case SimpleEqDerivation(ed) => ed.type1
//         case TransUpEqDerivation(t1, _, _, _) => t1
//       }
//     }

//     def type2: Type = {
//       this match{
//         case SimpleEqDerivation(ed) => ed.type2
//         case TransUpEqDerivation(_, t2, _, _) => t2
//       }
//     }

//     def isValid: Boolean = {
//       this match{
//         case SimpleEqDerivation(ed) => ed.isValid
//         case TransUpEqDerivation(t1, t2, ed1, ed2) => 
//           t1 == ed1.type1 && t2 == ed2.type2 && ed1.type2 == ed2.type1 &&
//           ed1.isValid && ed2.isValid
//       }
//     }

//   }
//   case class SimpleEqDerivation(ed: EquivalenceWithoutTransDerivation) extends EquivalenceTransUpDerivation
//   case class TransUpEqDerivation(t1: Type, t2: Type, ed1: EquivalenceTransUpDerivation, ed2: EquivalenceTransUpDerivation) extends EquivalenceTransUpDerivation
