Spire
=====

A formally verified dependently typed programming language that
facilitates generic programming.

Generic Programming
-------------------

*Spire* programs can contain generic functions over **all types** in the language.
An eliminator for `Type` allows you to perform case analysis on all types in the
language (at any universe level, in a predicative hierarchy of universes).
Essentially, the entire language is one big Martin-Löf universe.
Actually, the entire language is a super universe, which is a family of successively
larger universes indexed by their level in the universe hierarchy.

Formally Verified
-----------------

A *Haskell* program translates the user-facing *Spire surface language* into the *Spire kernel language*.
This kernel language is formally verified in *Agda*, and proves the following properties:
* Type Safety
* Strong Normalization
* Correctness of Type Checking

The *Haskell* program translates surface syntax into a `PreTerm` value, which is an ordinary non-dependent
type. The `PreTerm` is then passed to the verified type checker via the Agda-Haskell FFI.

Development
-----------

To compile:
`agda -c --compile-dir=. -i src/ -i ~/opt/agda-stdlib/src/ --ghc-flag=-i/Users/larrytheliquid/opt/agda-stdlib/ffi --ghc-flag=-i/Users/larrytheliquid/src/spire/src src/spire.agda`