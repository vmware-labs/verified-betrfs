
# Features We Use

## Usability
- Good error messages
- UI support
- Verification errors that try to pinpoint the failing clause
- Incremental verification
- Dafny server

## Modularity
- Modules and module refinement
- include
- /proc
- Export sets

## Heap Reasoning
- Linear/Shared
- Dynamic frames for non-linear code
- Syntactic conveniences, like old

## Types
- Basic types
- User-defined datatypes
- Tuples
- Subset types
- Collections: Seq, Array, Set, Map
- Generic types
- Type inference
- Lambdas
- Classes
- (Partial) higher-order functions
- Bitvectors (do we use these?)
- Type synonyms
- Multisets
- Infinite maps

## Statements
- Break?
- Call
- IfThenElse
- While
- Match
- Assert/Assume
- Print
- Reveal
- Forall
- Labeled statements

## Expressions
- Most of them

## Proof Machinery
- Automatic induction
- SMT-back automation
- Lemmas
- Loop invariants
- Semi-automated decreases checks
- Opaque functions
- Calc
- Fuel
- Ghost

## Compilation
- C++


# Features We Don't (Currently) Use

## Types
- Ordinal types
- Type parameter variance
- Multi-dimensional arrays
- Traits
- Co-inductive datatypes 

## Proof Machinery
- Least/Greatest (CoInductive) Predicates and Lemmas
- Co-induction

## Statements
- Yield statements
- "Monad" statements
- Guards
- Binding guards
- Expect
- Skeleton

