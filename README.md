# Verified ~~STLC~~ System F in Stainless

Implementation of System F in [Scala](http://scala-lang.org/), formally verified using [Stainless](https://github.com/epfl-lara/stainless).

A few of the proved properties:
- Type judgment uniqueness;
- Preservation;
- Progress for Call-by-Value reduction strategy.

## Verification
The implementation can be verified using stainless:
```
$ cd src/main/scala/verified
$ stainless
```

We strongly recommend using the `--compact` flag as well as a timeout of at least 2 seconds. A Stainless configuration file is [provided](src/main/scala/verified/stainless.conf) with those settings (the timeout is set to 5 seconds for good measure).

## Evaluator
A command-line lambda evaluator can be run using:
```
$ sbt run
```

The evaluator uses [De Bruijn notation](https://en.wikipedia.org/wiki/De_Bruijn_notation) and uses the following symbols:

| Symbol name            | Symbol | ASCII alternative   |
|------------------------|:------:|:-------------------:|
| lambda                 | λ      | `\`                 |
| Lambda                 | Λ      | `/\`                |
| Type arrow             | ⇒      | `=>`                |
| Universal quantifier   | ∀      | `\/`                |
| Fixpoint combinator    | "Fix"  | `§`                 |


The syntax for types is:
| Construct name      | Syntax           |
|---------------------|------------------|
| Type variable       | A number         |
| Ground type         | A string         |
| Function type       | `type ⇒ type`    |
| Universal type      | `∀. type`        |


The syntax for terms is:
| Construct name      | Syntax           |
|---------------------|------------------|
| Var                 | A number         |
| Abs                 | `λtype. term`    |
| App                 | `term term`      |
| Fix                 | `Fix term`       |
| TAbs                | `Λ. term`        |
| TApp                | `term [type]`    |

Example:
```
$ sbt run

Please enter a lambda-term to evaluate:

$ (/\.\0=>0.0)[T]\T.0

⊢ ((Λ.λ0⇒0. 0) [T]) λT. 0 : T⇒T
Reduction: 
((Λ.λ0⇒0. 0) [T]) λT. 0 -->
(λT⇒T. 0) λT. 0 -->
λT. 0 -->/
```

## Examples
A few examples/test cases can be run using:
```
$ sbt test
```