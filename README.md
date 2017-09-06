# Simplified Observational Type Theory

This is an implementation
of
[Observational Type Theory](http://strictlypositive.org/obseqnow.pdf). It
is "simplified" because the definitions of equality of types and terms
do not reduce as in the original definition. Instead, the theory
provides ways to construct proofs of equality, and to project out
consequences of an equality (e.g., equal pairs implies the components
are equal). Not reducing equality propositions stops (this source of)
explosion of the sizes of types.

## How to build it

1. Install OCaml and `opam` [https://ocaml.org].
2. `opam install jbuilder cmdliner menhir`
3. `jbuilder build sott-cmdline/sott.exe`

## How to typecheck a file

`./_build/default/sott-cmdline/sott.exe typecheck <file.sott>`

## Examples

1. [test1.sott](test1.sott) Derivation of `transport` from `coerce`;
   and a demonstration that Hofmann's counterexample to canonicity in
   the presence of a functional extensionality axiom fails in OTT.
2. [test1.5.sott](test1.5.sott) Shortened version of [test1.sott].
3. [test2.sott] An equality-proof irrelevance test; transivity and
   symmetry; coherence.
4. [test3.sott](test3.sott) Encoding of sum types via booleans and
   sigma types; demonstration that the counterexample to canonicity
   involving constructors when adding functional extensionality fails
   in OTT [https://coq.inria.fr/cocorico/extensional_equality].
5. [arith.sott](arith.sott) Construction of and some proofs for the
   integers constructed as a quotient of pairs of natural numbers.

## Features

1. Type equalities, written `[A = B]`, where `A` and `B` are proper
   typs. All proofs of the same equality are definitionally equal.

2. Heterogeneous term equality, written `[a : A = b : B]`, where `A`
   and `B` are types. As a shorthand, if `A` is the same as `B`, then
   this can be written as `[a = b : A]`. All proofs of the same
   equality are

3. Reflexivity for both type and term equality, written `refl`.

3. Coercion, written as `coerce(a,A,B,p)`, where `A` and `B` are
   types, `a : A`, and `p : [A = B]`. If `A` and `B` are in normal
   form, then the coercion will compute as appropriate to the
   type. This is how we maintain canonicity even when the equality
   type is arbitrarily extended.

4. Coherence, `coherence(e)` where `e : [A = B]`, has type `[x : A =
   coerce(x,A,B,e) : B]` (the `x` is inferred from the type being
   pushed in).

5. Pi types: `(x : A) -> B`, `\x -> e` and `e1 e2`. Function
   extensionality is witnessed by `funext(x1 x2 x_e. XXX) : [f1 : (x :
   A1) -> B1 = f2 : (x : A2) -> B2]`, where `x1 : A1`, `x2 : A2`,
   `x_e : [x1 : A = x2 : A]` and `XXX : [f1 x1 : B1[x1] = f2 x2 :
   B2[x2]]`.

6. Sigma types `(x : A) * B`, `(x,y)` and `x #fst`, `x #snd`.

7. Booleans: `Bool`, `True`, `False` and `x by_cases for x. T { True
   -> e1; False -> e2 }`.

8. Natural numbers: `Nat`, `Zero`, `Succ n` and `x #recursion for y. T
   { Zero -> e1; Succ n p -> e2 }`.
   
9. A Russell-style universe `Set`, which includes equalities,
   booleans, naturals, Pi, Sigma.
   
10. Quotient types:
    - Formation: `A / R`, where `A` is a type and `R : A -> A -> Set`
    - Introduction: `[a] : A / R`, where `a : A`
    - Elimination: `x #elimq for z. T { [z] -> e1; z1 z2 zr -> e2
      }`. The expression `e1` computes the answer, and `e2` is a proof
      that `e1` doesn't depend on the equivalence class.
    - Propositional equality: `same-class(e) : [[a1] : A/R = [a2] :
      A/R]` when `e : R a1 a2`.

## Bugs/TODO

1. The parser error messages are useless.

2. Not every useful combinator for equalities is present. This is a
   matter of implementing them in the lexer/parser/typechecker.

3. The normaliser is a bit too keen and unfolds all definitions
   whether it needs to or not. This leads to massive terms during type
   checking, and especially in error messages.
   
4. Type error messages don't include the context, and may output names
   that shadow names in the context, leading to incorrect terms.
