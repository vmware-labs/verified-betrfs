
# Existing Tools
## Dafny
### Pros
- We use a lot of its features: https://github.com/splatlab/veribetrfs/blob/master/docs/dafny-features.md
- Emphasis on usability/accessibility
- Existing support team and community
- Automated
- Not constrained by a real, production language

### Cons
- Assumes a C#/Java model fairly deeply
    - E.g., heap is pervasive
    - Class oriented
- Code base shows its age: It's difficult to add new features/experiments
- Missing a standard library
- Custom research language

## Prusti
### Pros
- Works with a real language
- Active support group
- Smaller code files == better organized?
- Rust is designed to be a language for high performance systems

### Cons
- Not enough support for writing functional specs or non-code-based proofs
- Viper is cool, but maybe not a good fit for Rust
    - Viper sits in an awkward spot serving as an "extra middleman" on the path to Z3
    - Viper has this built-in fractional permission logic. Except, this is the wrong abstraction for the Rust, which still has to perform its own borrow-checking, then the Prusti->Viper translation has to convince Viper that everything is kosher with (the moral equivalent of) assume statements.
    - i.e., a Prusti program is already memory-safe by construction (because of the rust borrow checker) so the viper backend is just wasting verification resources checking doing all the fractional permission checks
- We don't always want to be constrained by Rust-style linear type checking

# Wishlist/Questions
Proposed motto (BP): "Easy code is easy to verify; hard code is possible to verify."

We like many of [Dafny's features](https://github.com/splatlab/veribetrfs/blob/master/docs/dafny-features.md)

## Memory model
- Default to a Rust-like type system that discharges most heap-related concerns cheaply
- Escape hatch from the type system
    - Treat the heap as a "second-class citizen", e.g., something that can be passed around explicitly when needed
        - BP: Hopefully with some syntactic sugar?  Dafny's implicit heap and `old` are more pleasant than F*'s explicit heap function signatures
- Default to no GC

## Execution model
- Sequential or concurrent?

## Proof support
- SMT automation
- Ability to write and prove theorems independent of code
- Svelte VCs
    - Generated via Boogie or straight to Z3?  [Chris leans toward Boogie in the short term]
    - Only ask Z3 when it's really necessary, e.g., "program will crash" or "lemma will be unsound"
- Can we incorporate some flavor of the UW "push button" work and/or Ivy?  E.g., can we allow the user, if they choose, to remain within a decidable fragment, or at least warn them when they stray outside it?
- Tactics?
- Options to "turn down" the automation when needed
  - While Dafny has opaque/reveal, they are limited in use. Could imagine a system where any definition could be opaqued or revealed within any scope.
  - Other SMT options per-scope (e.g., `/noNLarith`)
- Are there language/VC design options that would lend themselves to better proof debugging support?
- Interop with Lean?
- How would function/method dichotomy work?
  - I'd want a smoother dichotomy, without having to lose transparency when declaring something a method, but a method cannot, by its nature, be treated as a pure function.
  - Possibility: Rust functions as the base, with attributes that says "proof", "code", "spec".
     - Spec should be very lightweight, classical math (no preconditions)
     - Functions that are both "code" and "spec" could use restricted types for arguments, instead of requires
     - All types are inhabited
- Allow a larger separation between code and proof
  - Don't try to compile ints, forall/exists
    - NOTE(travis): big 'serious' languages usually have bigint libraries though.
  - Default spec maps are infinite, with a finite map implementation available
    - NOTE(travis): I'm not actually convinced (even in proof code) that infinite maps are a better default than finite maps for most use-cases
  - Exploit/emphasize the distinction between code and spec.
- Auto-promotion from machine int to int in proof code
- Fuel: Function from identifier to fuel amount.  Unify opaque and fuel control.  F* version of the fuel axiom plus not passing the fuel parameter to the function definition.
- functions that return multiple values

## Code structure
- Something closer to Clang, with well-defined passes
  - Carefully defined (serializable?) "module interface" format
- What language is it written in?
  - Rust?

## Compilation
- Support for something low level, e.g., C/C++/Rust
- Control over memory layout

## Syntax
- Dafny-like, Rust-like, or something else?
- Maybe two front ends?  One real Rust, and one more toy that both translate to a common AST

## Concurrency features
- library for basic primitives (mutexes, atomics)
- built-in resource support

# Paths Forward

## Hard fork Dafny

## Hard fork Prusti

## Start from Scratch
