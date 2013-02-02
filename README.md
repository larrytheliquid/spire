Spire
=====

*Spire* is a dependently typed programming language that supports writing **generic
functions** over all types in the language.
An eliminator for `Type` allows you to perform case analysis on all types in the
language (at any universe level, in a predicative hierarchy of universes).
In essence, the entire language is one big Martin-Löf universe.
Actually, the entire language is a super universe, which is a family of successively
larger universes indexed by their level in the universe hierarchy.

Formally Verified
-----------------

A *Haskell* program translates the *Spire surface language* into the *Spire kernel language*.
This kernel language is formally verified in *Agda*, and proves the following properties:
* type safety
* strong normalization
* correctness of type-checking

The *Haskell* program translates surface syntax into a `PreTerm` value, which is a normal non-dependent
type. The `PreTerm` is then passed to the verified type checker via the the Haskell-Agda FFI.
