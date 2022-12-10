// /**
//   *  References: 
//   *    - [TAPL] Types and Programming Languages, Benjamin C. Pierce, 2002, The MIT Press
//   * 
//   *  This file defines the basic bloc of simply typed lambda calculus with type operators (TAPL Chap 29)
//   *  Kind, term, types and environments are defined
//   * 
//   * 
//   */


// import stainless.lang._
// import stainless.collection._
// import stainless.annotation._

// object IdealARS {

//   trait ReductionStep[T]{
//     def term1: T
//     def term2: T
//     def isSound: Boolean
//   }

//   trait ARS[T, R <: ReductionStep[T]] {
//     def term1: T =
//       this match
//         case NilRed(t) => t
//         case ConsRed(h, _) => h.term1
      
//     def term2: T =
//       this match
//         case NilRed(t) => t
//         case ConsRed(_, t) => t.term2

//     def isSound: Boolean =
//       this match
//         case NilRed(t) => true
//         case ConsRed(h, t) => h.term2 == t.term1 && h.isSound && t.isSound

//     def size: BigInt =
//       this match
//         case NilRed(_) => 0
//         case ConsRed(_, t) => t.size + 1
//   }

//   case class NilRed[T, R <: ReductionStep[T]](t: T) extends ARS[T, R]
//   case class ConsRed[T, R <: ReductionStep[T]](head: R, tail: ARS[T, R]) extends ARS[T, R]


// }