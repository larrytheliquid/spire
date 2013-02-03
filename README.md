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
More specifically, the entire language is a super universe: a family of successively
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

Running
-----------

To compile:
```bash
agda -c --compile-dir=. -isrc --ghc-flag=-isrc src/spire.agda
```

To run:
```bash
./spire
```
