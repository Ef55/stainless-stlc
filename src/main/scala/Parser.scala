import verified.SystemF._
import verified.Reduction._
import verified.Typing._

import scala.io.StdIn.readLine

import silex._
import scallion._
import stainless.lang.{Option, Some, None}
import stainless.annotation._

sealed abstract class SystemFToken
case object TermBinder extends SystemFToken
case object TypeBinder extends SystemFToken
case object BodySeparator extends SystemFToken
case object TypeSeparator extends SystemFToken
case object ArrowSymbol extends SystemFToken
case object UniversalSymbol extends SystemFToken
case object FixSymbol extends SystemFToken
case class Identifier(i: Int) extends SystemFToken
case class Name(n: String) extends SystemFToken
case object OpeningParenthesis extends SystemFToken
case object ClosingParenthesis extends SystemFToken
case object OpeningBracket extends SystemFToken
case object ClosingBracket extends SystemFToken
case object WhiteSpace extends SystemFToken

sealed abstract class SystemFKind
case object TermBinderKind extends SystemFKind
case object TypeBinderKind extends SystemFKind
case object BodySeparatorKind extends SystemFKind
case object TypeSeparatorKind extends SystemFKind
case object ArrowSymbolKind extends SystemFKind
case object UniversalSymbolKind extends SystemFKind
case object FixSymbolKind extends SystemFKind
case object IdentifierKind extends SystemFKind
case object NameKind extends SystemFKind
case object OpeningParenthesisKind extends SystemFKind
case object ClosingParenthesisKind extends SystemFKind
case object OpeningBracketKind extends SystemFKind
case object ClosingBracketKind extends SystemFKind

@library
object SystemFLexer extends Lexers with CharLexers {

  type Token = SystemFToken
  type Position = Unit

  val lexer = Lexer(
    elem('\\') | elem('λ') |> TermBinder,
    word("/\\") | elem('Λ') |> TypeBinder,
    elem('.') |> BodySeparator,
    elem(':') |> TypeSeparator,
    word("=>") | elem('⇒') |> ArrowSymbol,
    word("\\/") | elem('∀') |> UniversalSymbol,
    word("Fix") | elem('§') |> FixSymbol,
    many1(digit) |> { cs => Identifier(cs.mkString.toInt) },
    many1(elem(_.isLetter)) |> { cs => Name(cs.mkString) },
    elem('(') |> OpeningParenthesis,
    elem(')') |> ClosingParenthesis,
    elem('[') |> OpeningBracket,
    elem(']') |> ClosingBracket,
    many1(whiteSpace) |> WhiteSpace,
  )

  def apply(str: String): Iterator[Token] = {
    val source = Source.fromString(str, NoPositioner)
    val tokens = lexer.spawn(source)
    tokens.filter(_ != WhiteSpace)
  }
}

@library
object SystemFParser extends Parsers {
  import SafeImplicits._

  type Token = SystemFToken
  type Kind = SystemFKind

  override def getKind(token: Token): Kind = (token: @unchecked) match {
    case TermBinder => TermBinderKind
    case TypeBinder => TypeBinderKind
    case BodySeparator => BodySeparatorKind
    case TypeSeparator => TypeSeparatorKind
    case ArrowSymbol => ArrowSymbolKind
    case UniversalSymbol => UniversalSymbolKind
    case FixSymbol => FixSymbolKind
    case Identifier(_) => IdentifierKind
    case Name(_) => NameKind
    case OpeningParenthesis => OpeningParenthesisKind
    case ClosingParenthesis => ClosingParenthesisKind
    case OpeningBracket => OpeningBracketKind
    case ClosingBracket => ClosingBracketKind
  }

  def drop(k: SystemFKind): Syntax[Unit] = elem(k).map(_ => ())

  val identifier = accept(IdentifierKind) {
    case Identifier(i) => i
  }
  val name = accept(NameKind) {
    case Name(str) => str
  }

  val termBinder = drop(TermBinderKind)
  val typeBinder = drop(TypeBinderKind)
  val bodySeparator = drop(BodySeparatorKind)
  val typeSeparator = drop(TypeSeparatorKind)
  val arrow = drop(ArrowSymbolKind)
  val universal = drop(UniversalSymbolKind)
  val fix = drop(FixSymbolKind)
  val openingParenthesis = drop(OpeningParenthesisKind)
  val closingParenthesis = drop(ClosingParenthesisKind)
  val openingBracket = drop(OpeningBracketKind)
  val closingBracket = drop(ClosingBracketKind)

  lazy val atomicTyp: Syntax[Type] = 
    openingParenthesis ~>~ recursive(typ) ~<~ closingParenthesis |
    name.map(BasicType(_)) |
    identifier.map(VariableType(_))

  lazy val typs: Syntax[Seq[Type]] = rep1sep(atomicTyp, arrow)

  lazy val typ: Syntax[Type] = recursive(
    (universal ~>~ bodySeparator ~>~ typ).map(UniversalType(_): Type) |
    typs.map(ls => ls.reduceRight((t1, t2) => ArrowType(t1, t2)))
  )

  lazy val atomicTerm: Syntax[Term] =
    openingParenthesis ~>~ term ~<~ closingParenthesis |
    identifier.map(Var(_)) 

  lazy val allYouCanEatTerm: Syntax[Term] = 
    ( termBinder ~>~ typ ~ (bodySeparator ~>~ term) ).map{
      case t ~ body => Abs(t, body)
    }.up[Term] |
    ( typeBinder ~>~ bodySeparator ~>~ term ).map{
      case body => TAbs(body)
    }.up[Term]|
    (fix ~>~ term).map(Fix(_)).up[Term]

  lazy val terms: Syntax[Seq[Either[Term, Type]]] = recursive(
    epsilon(Seq[Either[Term, Type]]()) |
    allYouCanEatTerm.map(t => Seq[Either[Term, Type]](Left(t))) |
    ( atomicTerm || openingBracket ~>~ typ ~<~ closingBracket ) +: terms
  )

  lazy val term = recursive(
    allYouCanEatTerm |
    (atomicTerm ~ terms).map{
      case h ~ ls => ls.foldLeft(h)((t1, t2) => t2 match {
        case Left(t) => App(t1, t)
        case Right(t) => TApp(t1, t)
      })
    }
  )

  val parser = Parser(term)

  def apply(it: Iterator[Token]): Option[Term] = parser(it) match {
    case Parsed(value, _) => Some(value)
    case _ => None[Term]()
  }
}

@library
object Main {
  val MAX_ITER = 10

  def par(str: String, p: BigInt, threshold: BigInt): String = {
    if(p > threshold) {
      s"(${str})"
    }
    else {
      str
    }
  }

  def pp(t: Type): String = {
    def rec(t: Type, bind: BigInt): String = t match {
      case BasicType(n) => n
      case VariableType(i) => i.toString
      case ArrowType(t1, t2) => par(s"${rec(t1, 1)}⇒${rec(t2, 0)}", bind, 0)
      case UniversalType(b) => par(s"∀.${rec(b, 0)}", bind, 0)
    }
    rec(t, 0)
  }

  def pp(t: Term): String = {
    def rec(t: Term, bind: BigInt): String = t match {
      case Var(i) => i.toString
      case Abs(typ, body) => par(s"λ${pp(typ)}. ${rec(body, 0)}", bind, 0)
      case App(t1, t2) => par(s"${rec(t1, 1)} ${rec(t2, 0)}", bind, 0)
      case Fix(f) => par(s"§${rec(f, 0)}", bind, 0)
      case TAbs(body) => par(s"Λ.${rec(body, 0)}", bind, 0)
      case TApp(body, arg) => par(s"${rec(body, 1)} [${pp(arg)}]", bind, 0)
    }
    rec(t, 0)
  }

  def reduce(t: Term): Term = {
    var tp = t
    var i = 0
    while(!tp.isValue && i < MAX_ITER) {
      println(s"${pp(tp)} -->")
      tp = reduceCallByValue(tp).get
      i += 1
    }
    tp
  }

  def main(args: Array[String]): Unit = {
    println("Please enter a lambda-term to evaluate:")
    val input = readLine()
    val lexed = SystemFLexer(input)
    val parsed = SystemFParser(lexed)
    parsed match {
      case Some(t) => {
        deriveType(t) match {
          case Some(td) => {
            println(s"⊢ ${pp(t)} : ${pp(td.t)}")
            println("Reduction: ")
            val tp = reduce(t)
            println(s"${pp(tp)} -->${if(tp.isValue) "/" else " ..."}")
          }
          case None() => {
            println(s"`${pp(t)}` is ill-typed!")
          }
        }

      }
      case None() => println("Parsing failed")
    }
  }
}