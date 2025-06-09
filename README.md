# Metallic!

Metallic is a dependently typed, functional programming language with strict evaluation, made mainly as a sandbox to test various ideas that I have about programming language design. 
It is currently VERY WIP and not really ready for coding even small things in it yet. The language is currently named metallic but like everything this is subject to change once the language gets more of an identity.
If you want to try it out, first clone the repository and run `cargo test`. Then run the examples using `cargo run .\fib.txt`, and finally try writing your own code :3!

Here is a rundown of almost everything in metallic:
### Syntax
New values are be defined using the syntax 
```
def <Type>: <name> := <Value>
```
In the same fashion as many other functional languages, function application is performed just by simple concatenation. For example, here is a program that defines a variable `four` by adding two numbers:
```
def Int: four := add 1 3
```
Once some values have been defined, we can run a program using the `eval` keyword:
```
eval add (-17) four   // outputs -13 when interpreted
```
(this part is temporary and will be removed when an effects system is implemented.)


### Builtin Values:
Metallic currently only has Integer values, Boolean values, Strings, and the Unit type, with the single value `()`. <br>
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
  if n >= 0   // Note: this specific example uses features that aren't implemented yet
  then Bool
  else Int

def DepProd Int ExampleDep: val1 := fn Int: n do
  if n >= 0
  then is_even n
  else 19

def DepProd Int ExampleDep: val2 := fn Int: n do
  if n >= 0
  then true
  else -21
```

The basic idea is that if you have a type family `Int -> Type`, which assigns to every element of `Int` an entire type, then you can create a function which takes eveery `Int: n` to a value `ExampleDep n: val1 n`.
This feature 

### Pairs
TODO: explain pairs (tuples)

# Important features NOT yet implemented
- Operators (e.g. `+`, `*`, `->`, etc.). Applying functions is currently the only way to do computation.
- Integer comparison operations
- Type Checking. Currently the expressions in the type field are just straight up ignored. It's been a struggle to learn how to do this with dependent types but I now understand to be able to do it once I get to it.
- The `Empty` type, which will be a type that expresses the idea of not returning any value (through either exiting the program or looping forever).
  - I also am currently toying with the idea of a function `((T -> Empty) -> Empty) -> T: dne`, which stands for Double negation elimination. This function would make the logic of metallic's type system a classical logic rather than an intuitionistic one. It would have an immensely inefficient implementation but I believe it's possible, lmk if you want to know more about it.
- Dependent sum types.
- if statements
- Input/Output. The plan for input/output is for it to be a kind of continuation-passing style thing. For example we would have `(String -> IO) -> IO: getln` as the type of a function that reads a line from standard input
- C code generation. This is eventually going to be a compiled language and not just interpreted. This feature will need both type checking and IO to be added before I can start working on it though. <br>
I specifically chose C because I didn't want to have to deal with learning C++ and doing FFI with LLVM or using some other commonly used IR out there that doesn't have very much documentation. And also languages like Haskell and Lean output to C as well.
- Line/column number for errors, along with better error messages
- It's not really not implemented, but I do need to add more tests for everything.
