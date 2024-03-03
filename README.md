This repository contains the supplementary material for the paper
*Beyond Trees: Calculating Graph-Based Compilers*. The material
includes Agda formalisations of all calculations in the paper. In
addition, further examples and calculations are included as well

To typecheck all Agda files, use the included makefile by simply
invoking `make` in this directory. All source files in this directory
have been typechecked using version 2.6.3 of Agda and version 1.7.3 of
the Agda standard library.

# Files

- [Code.agda](Code.agda): Generic definitions of tree-structured code
  (`Code`) and graph-structured code (`Codeᵍ`) together with the
  corresponding definitions of unravelling and bisimilarity. All
  calculations for non-terminating languages (e.g.
  [Repeat.agda](Repeat.agda)) use this module instead of defining
  `Code` and `Codeᵍ` from scratch (since we need bisimilarity).
- [Partial.agda](Partial.agda): Definition of the partiality monad
  `Partial` + proofs of its laws (section 4).

## Compiler calculations from the paper

- [Cond.agda](Cond.agda): Arithmetic expression language with
  conditionals (sections 2 and 3).
- [Repeat.agda](Repeat.agda): Arithmetic expression language with
  simple loops (sections 4).
- [WhileState.agda](WhileState.agda): Arithmetic expression language
  extended with While loops and a reference cell (section 5).

## Additional compiler calculations 

- [While.agda](While.agda): Arithmetic expression language with a
  while loop.
- [Exception.agda](Exception.agda): Arithmetic expression language
  extended with exceptions.
- [Lambda.agda](Lambda.agda): Call-by-value lambda calculus.

## Termination arguments 

In some cases, Agda's termination checker rejects the definition of
the virtual machine `exec`. In these cases, the termination checker is
disabled for `exec` (using the `TERMINATING` pragma) and termination
is proved manually in the following modules:

- [Termination/Exception.agda](Termination/Exception.agda)
- [Termination/Lambda.agda](Termination/Lambda.agda)

## Alternative formalisation using de Bruijn indices

The directory [DeBruijn](DeBruijn/) contains an alternative
formalisation that uses de Bruijn indices instead of parametric
higher-order abstract syntax.

## Calculation of `execG`

[ExecG](ExecG.agda) contains a calculation of the graph-based machine
`execG` from the tree-based machine `exec`.

## Example code

[Examples](Examples.agda) gives some example compilation outputs for
the While language.

# Agda formalisation vs. paper proofs

In the paper, we use an idealised Haskell-like syntax for all
definitions. Here we outline how this idealised syntax is translated
into Agda.

## Sized coinductive types

In the paper, we use the `codata` syntax to distinguish coinductively
defined data types from inductive data types. In particular, we use
this for the coinductive `Partial` type:

```
codata Partial a = Now a | Later (Partial a)
```

In Agda we use coinductive record types to represent coinductive
data types. Moreover, we use sized types to help the termination
checker to recognize productive corecursive function
definitions. Therefore, the `Partial` type has an additional parameter
of type `Size`:

```
data Partial (A : Set) (i : Size) : Set where
  now   : A → Partial A i
  later : ∞Partial A i → Partial A i

record ∞Partial (A : Set) (i : Size) : Set where
  coinductive
  constructor delay
  field
    force : {j : Size< i} → Partial A j
```
## Mutual inductive and coinductive function definitions

The semantic functions `eval` and `exec` are well-defined because
recursive calls take smaller arguments (either structurally or
according to some measure), or are guarded by `Later`. For example, in
the case of the Repeat language, `eval` is applied to the structurally
smaller `x` and `y` in the case of `Add` or is guarded by `Later` in
the case for `Repeat`:

```
eval :: Expr -> Partial Int
eval (Val n)      = return n
eval (Add x y)    = do m <- eval x; n <- eval y; return (m + n)
eval (Repeat x)   = do eval x; Later (eval (Repeat x))
```

This translates to two mutually recursive functions in Agda, one for
recursive calls (applied to smaller arguments) and one for
corecursive calls (guarded by `Later`). We use the prefix `∞` to
distinguish the corecursive function from the recursive function. For
example, for the Repeat language we write an `eval` and an `∞eval`
function:

```
mutual
  eval : ∀ {i} → Expr → Partial ℕ i
  eval (Val x) = return x
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval (Repeat x) = eval x >> later (∞eval (Repeat x))

  ∞eval : ∀ {i} → Expr → ∞Partial ℕ i
  force (∞eval x) = eval x
```


## Mutual inductive and coinductive types

In the paper, we use the `∞` notation to indicate coinductive arguments
in mixed inductive and coinductive type definitions, e.g.:

```
data Code = HALT | REC (∞ Code) | ...
```

Similarly to the translation of function definitions, this `∞`
notation can be translated into a mutual recursive definition of an
inductive type `Code` and a coinductive type `∞Code` in a canonical
way (using sized types as for `Partial`):

```
mutual
  data Code (i : Size) : Set where
    HALT : Code i
    REC' : ∞Code i → Code i
    ...
  
  record ∞Code (i : Size) : Set where
    coinductive
    constructor delay
    field
      force :  {j : Size< i} → Code j
```

## Definition of unravelling

The termination checker is disabled (using the `TERMINATING` pragma)
for the definition of the generic unravelling transformation in
[Code.agda](Code.agda) as Agda does not recognize it as total. We
give an informal argument in [Code.agda](Code.agda) why unravelling
is terminating. Since the argument depends on parametricity we cannot
make this formal in Agda. As an alternative, the [DeBruijn](DeBruijn/)
folder contains a variant of the formalisation that uses de Bruijn
indices instead of parametric higher-order abstract syntax. This
allows us to define unravelling in a way that Agda recognises as total
but at the expense of clarity in the compiler calculations.