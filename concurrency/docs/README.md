We're building a verification framework for verification of concurrent systems (including ‘shared memory’ concurrency) in a language with Rust-inspired ownership semantics.
Currently, the foundation for the framework is Linear-Dafny. The documentation for [ordinary Linear-Dafny can be found here](https://github.com/secure-foundations/dafny/tree/betr/docs/Linear).

In this framework, we bring together several concepts, including an extension to Linear-Dafny called 'ghost linear' (or `glinear`) and some concurrency primitives.
This directory serves as an introduction to those concepts.

## Introduction to concurrent reasoning

[Basic verification with mutexes](MutexIntro.md)

[Introduction to ghost linear](GhostLinearIntro.md)

## Fine-grained locking & sharded state machines

[Introduction: Bank Application](BankIntro.md)

## Implementing your own lock from atomic primitives

## Reader-writer locks
