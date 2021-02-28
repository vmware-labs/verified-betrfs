# Contributing to Verified BetrFS

The Verified BetrFS team welcomes community contributions.
Contributors are encouraged to contact the team early to coordinate
work, as the project is under active development.

## Coding guidelines

Avoid using dynamic frames.  This means avoid classes, traits, and
arrays.  Use the linear type system instead.  We are currently in the
process of removing all classes from the code.

Minimize proofs.  While developing a method, lemma, or function, you
are likely to add many asserts or calc statements as you diagnose the
reason that the code is not verifying.  Once you get the code to
verify, go back and clean up the proof.  Delete any assertions and
comment out (or delete) any intermediate calc steps that are not
actually necessary for dafny to verify the code.

Keep verification times low.  Ideally, all your functions, methods,
and lemmas should verify in less than 20 seconds (under 10 seconds is
even better).  This will improve productivity by keeping things
interactive.  If code is taking too long to verify, you can try to
diagnose the cause by using the profiler (see docs/profiling.txt).
The most common techniques for fixing slow verifications are:
- Break code into smaller chunks (i.e. break a method into smaller
  methods, or into a method and a lemma).
- Mark a function or predicate as opaque.
- Introduce a name for an expression that is causing too many
  quantifier instantiations, so that the name becomes the trigger.
- Use the -noNLarith flag if non-linear arithmetic appears to be the
  cause of the slow verification.

Files with axioms should end in ".s.dfy".  For example, files that
define the top-level correctness specification, or that axiomatize the
behavior of the underlying hardware or OS should end in ".s.dfy".
These files cannot be proven correct by dafny.  Rather, they define
what the software assumes about the environment and what it promises
about its behavior.  In other words, they correspond to the statement
of a theorem about the software.  All other files should be able to be
verified by dafny and should end in ".i.dfy".  (The "s" stands for
"specification" and the "i" stands for "implementation".)  Spec files
(i.e. ".s.dfy" files) can include only other spec files.
Implementation files can include both spec and implementation files.

Avoid introducing trusted code.

Don't use int or nat types in executable code.  The C++ backend does
not support them.  As a general rule, use uint64 for executable code
and nat/int for ghosty code.

Be careful about using function methods.  They can be very convenient
for small expressions but, if you ever have to split a function method
into a separate function and method, then you will have to revisit all
its call sites.  This could require splitting any function methods
that called the function method being split.  So try to use them only
for small expressions that are unlikely to get more complex as the
code evolves, and use them only for leaves of the call graph.

Use dafny's member syntax for types and datatypes, i.e. write
```
datatype Foo == Foo(x: int) {
  function getX() : int { x }
}
```
instead of
```
datatype Foo == Foo(x: int)
function getX(f: Foo) : int { f.x }
```

As a general rule, a file named SomeName.i.dfy should define a module
SomeName.  Be thoughtful about whether you intend users to import your
module opened or not, and name its methods, lemmas, and functions
appropriately.

The closest thing we have to a standard library is in lib/Base.  Make
a reasonable effort to find any elementary lemmas you need in there
before writing a new one.  However, feel free to add new lemmas to the
library when needed.

Our general convention for data structures is to define a
well-formedness predicate `WF()` and an interpretation function `I()`.
The well-formedness predicate defines the basic properties that an
instance of the data structure should satisfy.  The interpretation
function defines the meaning of the data structure.  For example, in a
binary search tree, the `WF()` predicate would assert that no key is
out of place and `I()` would compute a dafny map with the same
key-value pairs as are in the tree.

Datatypes and modules are always capitalized.  PascalCase is the most
common naming convention, but some code uses snake_case.  When we have
to write a function and method version of the same piece of code, we
typically use camelCase for the function and PascalCase for the
method.

Don't bother with excess comments.  Rather, structure your function
and method names and their requires and ensures clauses to be self
documenting.  (Of course high-level comments in a file, or about
anything tricky, are welcome.)
