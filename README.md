# Metallic!

Metallic is an experimental, dependently typed, functional programming language with strict evaluation, made mainly as a sandbox to test various ideas that I have about programming language design, and is also
just as a fun personal project of mine. It is currently VERY WIP and not ready for coding even small things in it yet. The language is currently named metallic but like everything in this repo, it is subject to change.
If you want to try it out, first clone the repository and run `cargo test`. Then run the examples using `cargo run .\fib.txt`, and finally try writing your own code :3!

# The ""Philosophy""
The basic philosophy of this language was inspired by [Glivenko's theorem](https://en.wikipedia.org/wiki/Double-negation_translation) which states that for any proposition P which is provable in a classical/nonconstructive manner, the statement `¬¬P` is provable in a constructive manner. For example, the statement `∀P, P ∨ ¬P` a.k.a. the law of excluded middle is impossible to prove constructively because this would correspond to an algorithm which given any proposition, would return either a proof that it is true or a proof that it is false. Such a program is unfortunately impossible to create. However, the statement `∀P, ¬¬(P ∨ ¬P)` IS provable constructively because if we were given a proof that `¬(P ∨ ¬P)`, we could prove that `¬P` by the left part of the disjunction, which then contradicts the fact that `¬¬P` by the right part of the disjunction, i.e. it derives a contradiction. </br>

What I interpret this theorem to mean for theorem provers is that the distinction between `Prop`s and `Type`s is unnecessary. Every dependently-typed language that I know of (except for idris? idk i should probably look into that more) includes a separate type universe `Prop` for types which do not hold any data, which they will then utilize to optimize performance and create proof irrelevance for existence proofs and propositional extentionaity. While this is a useful concept, hearing about this for the first time made me feel somewhat lied to about the curry-howard correspondence. "How can proofs be programs if we have to explicitly avoid the limitations that programs have?" The answer is that, because of Glivenko's theorem, we dont have to do such things! The big plan for including proof data in metallic is treating it as *real, actual data* which just so happens to be stored in the double-negation monad `DN T = (T → Empty) → Empty`. Proof irrelevance is a consequence of function extentionality for functions into the `Empty` type.  </br>

The second part of the philosophy of this language is that it will not include inductive types. It will instead just include basic "enums" as seen in languages like C or Java. In order to recreate most of the same behavior we can instead make a type family over one of these enum types, and then a dependent sum type will be just fine. For example, `Decidable P` would be defined as `(Bool: b) & (if b then P else ¬P)`, and `n ≤ m` would be defined as `(Nat: d) & (n + d = m)`. As seen in the second example, the only "real" inductive type that will be a part of metallic will be the equality type `=`, which has the same rules as in any other type theory. </br></br>
Here is a rundown of almost everything in metallic:
### Syntax
New values are be defined using the syntax 
```
def <Type>: <name> := <value>
```
Note that the type and name are probably swapped compared to most newer languages. Things are highly experimental here though, and this would not be too hard to change right now, so it's fine. </br>
In the same fashion as many other functional languages, function application is performed just by simple concatenation. For example, here is a program that defines a variable `four` by adding two numbers:
```
def Int: four := add 1 3
```
Once some values have been defined, we can run a program using the `eval` keyword:
```
eval add (-17) four   // outputs -13 when interpreted
```
(this part is temporary and will be mostly removed when a system for side effects is implemented.)


### Builtin Values:
Metallic currently has Integer values, Boolean values, Strings, the Unit type, with the single value `()`, and Enums. <br>
On integer values you can currently only add them, or compare if they are equal to eachother. <br>
Booleans are an internally defined enum type with the variants `true` and `false` <br>


### Lambda functions and Let statements
Lambdas are written using the notation `fn <Expr>: <name> do <Expr>`. They represent a computation with an unknown quantity. The type of a lambda that takes an `Int` as input and returns a `Bool` as output is written as `fun Int Bool`.
In metallic, most everything is curried which means that to create a function with multiple arguments we simply write `fn Int: arg1 do  fn Int: arg2 do ...`.

TODO: explain let statements


### Enum types and match statements
A new enum type is created very simply using the notation `enum EnumName variant1 variant2 variant3`. Like C and similar languages, Metallic will not allow you to store data inside each of these variants. 
Instead the idea is that full sum types will be created using a [dependent sum type](https://en.wikipedia.org/wiki/Dependent_type#%CE%A3_type) on a type family over these enum types.

### Dependent Products
Dependent products are best explained through an example:
```
def fun Int Type: ExampleDep := fn Int: n do
  if n <= 0
  then Bool
  else Int

def DepProd Int ExampleDep: val1 := fn Int: n do
  if n <= 0
  then is_even n
  else 19

def DepProd Int ExampleDep: val2 := fn Int: n do
  if n <= 0
  then true
  else -21
```

The basic idea is that if you have a type family `Int -> Type`, which assigns to every element of `Int` an entire type, then you can create a function which takes eveery `Int: n` to a value `ExampleDep n: val1 n`.
For example we can call `ExampleDep 14`, and this will return the type `Bool`. The dependent product allows us to make functions that go into different parts of `ExampleDep`. Like `val1 14` evaluates to `true` which is a bool, but `val1 (-14)` evaluates to 19 which is an integer.

### Pairs
TODO: explain pairs (tuples)

# Important features NOT yet implemented
- Operators (e.g. `+`, `*`, `->`, etc.). Applying functions is currently the only way to do computation.
- Integer comparison operations
- Type Checking. Currently the expressions in the type field are just straight up ignored. It's been a struggle to learn how to do this with dependent types but I now understand to be able to do it once I get to it.
- The `Empty` type, which will be a type that expresses the idea of not returning any value (through either exiting the program or looping forever).
- Dependent sum types.
- if statements
- C code generation. This is eventually going to be a compiled language and not just interpreted. <br>
- Line/column number for errors, along with better error messages
- It's not really not implemented, but I do need to add more tests for everything. (Especially error cases)
