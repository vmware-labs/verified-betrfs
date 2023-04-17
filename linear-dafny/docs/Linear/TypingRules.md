# The essence of linear Dafny

To clarify the linear Dafny's typechecking rules,
this document formalizes a small language containing essential concepts from linear Dafny.
It starts with just ordinary and `linear` variables,
and then extends the language to support `ghost`, `shared`, and borrowing.

Typing rules are written with assumptions above a horizontal lines and conclusions below the line:

```
assumptions
-----------
conclusions
```

If no assumptions are necessary, the horizontal line is omitted:

```
conclusions
```

## Basic linearity rules

Let `e` denote expressions and `s` denote statements, where `x` stands for variables
and `f` stands for function/method names:

```
u ::= ordinary | linear
expression e ::= x | f(e, e) | e; e | u var x := e; e | if e then e else e
statement s ::= skip | e | x := e | s; s | if e then s else s
```

Each expression can be a variable `x`, a function application, a sequence of expressions,
a variable declaration, or a conditional expression.
For simplicity, every function/method takes exactly two arguments and returns one result.
Statements can be empty (`skip`), an expression `e`, a local variable update `x := e`,
a sequence of statements, or a conditional statement.

Every variable is either ordinary or `linear`, described by a "usage" `u`.
Each function parameter and result has a usage, so that any function `f`
can be summarized with a usage typing `f: (u, u) -> u`.

The type checker uses a set of variables `O` to track ordinary variables
and a set of variables `L` to track linear variables.
For any disjoint sets `X` and `Y`, the notation "`X, Y`" denotes the union of `X` and `Y`.
For simplicity, the type checker assumes that all variables in a program have been renamed to be distinct
before the type checking begins.

For any `O` and `L`, the type checker can check that an expression `e` or a statement `s` is well-typed:
- `O ; L |- e : linear` means that `e` is a well-typed linear expression, consuming all of `L`.
- `O ; L |- e : ordinary` means that `e` is a well-typed ordinary expression, consuming all of `L`.
- `O ; L |- s : L'` means that `s` is a well-typed statement,
consuming some or all of `L`, and leaving any remaining linear variables in `L'`.

When checking subexpressions `e1` and `e2` of an expression `f(e1, e2)`,
linear variables from `L` are split into disjoint `L1` and `L2`,
so that each linear variable is consumed in either `e1` or `e2`,
but not both:

```
f : (u1, u2) -> uf
O ; L1     |-   e1      : u1
O ;     L2 |-       e2  : u2
----------------------------
O ; L1, L2 |- f(e1, e2) : uf
```

Ordinary variables, on the other hand, may be used in both `e1` and `e2`.
Furthermore, linear variables must be used exactly once; they cannot be discarded.
This is enforced by requiring that `L = {x}` when checking the expression `x`
for a linear `x`, and that `L = {}` when checking other atomic expressions:

```
O, {x} ; {}  |- x : ordinary

O      ; {x} |- x : linear
```

The remaining rules for expressions follow the patterns in the rules above:

```
u1 != linear
O ; L1     |- e1     : u1
O ;     L2 |-     e2 : u2
-------------------------
O ; L1, L2 |- e1; e2 : u2

O      ; L1     |-                   e1     : ordinary
O, {x} ;     L2 |-                       e2 : u2
------------------------------------------------------
O      ; L1, L2 |- ordinary var x := e1; e2 : u2

O ; L1          |-                 e1     : linear
O ;     L2, {x} |-                     e2 : u2
--------------------------------------------------
O ; L1, L2      |- linear var x := e1; e2 : u2

O ; L0      |- e0     : ordinary
O ;     L12 |-     e1 : u12
O ;     L12 |-     e2 : u12
------------------------------------------
O ; L0, L12 |- if e0 then e1 else e2 : u12
```

Note that the rule for `if`/`else` shares the linear variables between the `then` and `else` clauses,
since only one of these two clauses will execute at run-time.

Many of the rules shown above nondeterministically split `L` into `L1, L2` when checking subexpressions `e1` and `e2`.
Linear Dafny's type checker implementation computes this split lazily:
it first checks `e1`, and if `e1` consumes a linear variable `x`,
then the type checker knows `x` belongs to `L1`.
If `e2` consumes `x`, then `x` must belong to `L2`.
If neither consume `x`, then the type checker passes `x` to the next enclosing scope
(e.g. `x` might be used by `e3` in `f(f(e1, e2), e3)`.
If linear `x` is never used, the type checker reports a type error.

Because statements may contain assignments `x := e`,
statements can produce `linear` variables as well as consuming `linear` variables.
Therefore, the typing for statements `O; L |- s : L'` tracks both the input linear variables `L`
and the output linear variables `L'`:

```
O ; L |- skip : L

O ; L1 |- e : ordinary
----------------------
O ; L1, L2 |- e : L2

O contains x
O ; L1 |- e : ordinary
-------------------------
O ; L1, L2 |- x := e : L2

O ; L1 |- e : linear
------------------------------
O ; L1, L2 |- x := e : L2, {x}

O ; L0 |- s1 : L1
O ; L1 |- s2 : L2
----------------------
O ; L0 |- s1; s2 |- L2

O ; Le |- e : ordinary
O ; L0 |- s1 : L12
O ; L0 |- s2 : L12
----------------------------------------
O ; Le, L0 |- if e then s1 else s2 : L12
```

## Rules for ghost, shared, and borrowing

This section adds `ghost` and `shared` usages,
as well as supporting `inout` parameters in methods `f`:

```
u ::= ghost | ordinary | shared | linear
io ::= | inout
f: (u io, u io) -> u
expression e ::= x | f(e, e) | e; e | u var x := e; e | if e then e else e
statement s ::= skip | e | x := e | s; s | if e then s else s
```

There is a set of variables for each usage:
`G` for `ghost`, `O` for `ordinary`, `S` for `shared`, and `L` for `linear`.
An additional set `M` tracks `linear` variables that have been mutably borrowed as `inout` arguments to methods:

- `G ; O ; S ; M ; L |- e : u io` means that `e` is well typed, consuming `M` and `L`,
and that `e` has usage `u`, and, if `io` is `inout`,  `e` can be used as an `inout` argument to a method.
- `G ; O ; S ; L |- s : L'` means that `s` is well typed, consuming some or all of `L`,
and producing `L'`.

Note that any kind of variable can be used as a ghost argument to a function/method.
Therefore, *all* variables are placed in `G`, even if they also appear in `O`, `S`, `M`, or `L`.
This emphasizes two important points about linear Dafny's treatment of ghost code:
linear variables can always be used as `ghost`, even after the linear variable has been consumed,
and using a linear variable as `ghost` does not consume the linear variable.

Arguments to a function/method `f` must match the usage and inoutness expected by `f`.
Note that a mutably borrowed variable can only be used for a single `inout` argument,
so the mutably borrowed variables `M` are split between the two arguments as `M1, M2`:

```
f : (u1 io1, u2 io2) -> uf
G ; O ; S ; M1     ; L1     |-   e1      : u1 io1
G ; O ; S ;     M2 ;     L2 |-       e2  : u2 io2
-------------------------------------------------
G ; O ; S ; M1, M2 ; L1, L2 |- f(e1, e2) : uf
```
`ghost` and `shared` variables may be duplicated,
so `G` and `S` are shared between subexpressions `e1` and `e2`.

The typing rules for variables simply read from `G`, `O`, `S`, `M`, or `L`:

```
G, {x} ; O ; S ; {} ; {} |- x : ghost

G ; O, {x} ; S ; {} ; {} |- x : ordinary

G ; O ; S, {x} ; {} ; {} |- x : shared

G ; O ; S      ; {x} ; {} |- x : linear inout

G ; O ; S      ; {} ; {x} |- x : linear
```

Unlike the rule for `f(e1, e2)`, the rule for `e1; e2` allows borrowing:
`e1` can temporarily borrow linear variables from `e2`,
using them as `shared` variables in `e1`.
This exploits the fact that in the run-time evaluation of `e1; e2`,
the expression `e1` is completely evaluated before `e2` begins evaluation,
so that any temporary variable manipulation in `e1` finishes before `e2` has a chance to consume the variables.
(By contrast, the evaluation order of `e1` and `e2` in `f(e1, e2)` is compiler-dependent;
if `e1` tried to borrow `x` from `e2`, the program could crash if the compiler decided to evaluate `e2` first
and `e2` consumed `x`.)

The set `Bs` tracks borrowed immutable variables,
which appear as shared in `S, Bs` when checking `e1`
and then rejoin `Bs, L2` as linear when checking `e2`:

```
u1 != linear
G ; O ; S, Bs ; {} ; L1         |- e1     : u1
G ; O ; S     ; {} ;     Bs, L2 |-     e2 : u2
----------------------------------------------
G ; O ; S     ; {} ; L1, Bs, L2 |- e1; e2 : u2
```

Variable declarations `u var x := e1; e2` also evaluate `e1` before `e2`
and thus allow borrowing inside `e1`.
For conciseness, the following rule covers all 4 cases of `u` = `ghost`, `ordinary`, `shared`, or `linear`,
placing the declared variable in `G`, `O`, `S`, or `L` as appropriate
(and always putting a copy in `G` for ghost usage):

```
Ox = {x} if u1 = ordinary, {} otherwise
Sx = {x} if u1 = shared  , {} otherwise
Lx = {x} if u1 = linear  , {} otherwise
If u1 = shared then Bs = {}
G      ; O     ; S, Bs ; {} ; L1             |-             e1     : u1
G, {x} ; O, Ox ; S, Sx ; {} ;     Bs, L2, Lx |-                 e2 : u2
-----------------------------------------------------------------------
G      ; O     ; S     ; {} ; L1, Bs, L2     |- u1 var x := e1; e2 : u2
```

Note that if `e1` borrows any variables immutably (`Bs != {}`), then `x` and `e1` cannot be `shared` (`u1 != shared`).
This prevents any borrowed variables in `Bs` from escaping `e1` through `x`.
Note that it is still possible to assign a borrowed variable to a `shared` variable,
as long as the borrowing happens outside the scope of the shared variable.
For example, the expression `(shared var y := x; f1(y, y)); f2(x, z)` borrows the linear variable `x`
across the entire subexpression `(shared var y := x; f1(y, y))`,
which is free to assign it to the `shared` variable `y` internally:

```
  {} ; {} ; {x} ; {} ; {}    |- x : shared
  {} ; {} ; {x, y} ; {} ; {} |- f1(y, y) : ...
  ----------------------------------------------------------------- no borrowing happens here: Bs = {}
  {} ; {} ; {x} ; {} ; {}    |- (shared var y := x; f1(y, y)) : ...
  {} ; {} ; {} ; {} ; {x, z} |- f2(x, z) : ...
  --------------------------------------------------------------------------- borrowing happens here: Bs = {x}
  {} ; {} ; {} ; {} ; {x, z} |- (shared var y := x; f1(y, y)); f2(x, z) : ...
```

Linear Dafny's type checker implementation computes the split between `L1`, `Bs`, and `L2` lazily.
If `e1` uses a linear variable `x` as `shared` and `e2` then consumes `x`,
the checker places `x` in `Bs`.
If `e1` tries to borrow `x` but `e2` does not consume `x`,
then the borrowing is lifted to an enclosing scope
(e.g. if `e3` consumes `x` in the expression `((e1; e2); e3)`,
then `(e1; e2)` borrows `x` from `e3`).

`if`/`else` expressions exploit order of evaluation (`e0` precedes `e1` or `e2`) allow borrowing:

```
u0 != linear
G ; O ; S, Bs ; {} ; L0          |- e0     : u0
G ; O ; S     ; {} ;     Bs, L12 |-     e1 : u12
G ; O ; S     ; {} ;     Bs, L12 |-     e2 : u12
---------------------------------------------------------------
G ; O ; S     ; {} ; L0, Bs, L12 |- if e0 then e1 else e2 : u12
```

Typing rules for statements have the same form as the statement typing rules from the previous section,
but also allow borrowing within subexpressions, including mutably borrowed variables for `inout` arguments to methods `f`.
The set `Bm` tracks borrowed mutable variables,
which appear as borrowed mutable when checking `e`
and then rejoin `Bs, Bm, L2` in the linear output:

```
G ; O ; S ; L |- skip : L

u != linear
G ; O ; S, Bs ; Bm ; L1             |- e : u
-----------------------------------------------------
G ; O ; S     ;      L1, Bs, Bm, L2 |- e : Bs, Bm, L2

If u = ghost then G contains x
If u = ordinary then O contains x
If u = shared then S contains x and Bs = {}
u != linear (see rule below for linear)
G ; O ; S, Bs ; Bm ; L1             |-      e : u
----------------------------------------------------------
G ; O ; S     ;      L1, Bs, Bm, L2 |- x := e : Bs, Bm, L2

G ; O ; S, Bs ; Bm ; L1             |-      e : linear
---------------------------------------------------------------
G ; O ; S     ;      L1, Bs, Bm, L2 |- x := e : Bs, Bm, L2, {x}

G ; O ; S ; L0 |- s1 : L1
G ; O ; S ; L1 |- s2 : L2
-----------------------------
G ; O ; S ; L0 |- s1; s2 : L2

G ; O ; S, Bs ; Bm ;    Le |- e : ordinary
G ; O ; S ;     Bs, Bm, L0 |- s1 : L12
G ; O ; S ;     Bs, Bm, L0 |- s2 : L12
--------------------------------------------------------
G ; O ; S ; Le, Bs, Bm, L0 |- if e then s1 else s2 : L12
```

The current implementation of linear Dafny does not support borrowing across statements:
the typing rule for `s1; s2` shown above does not extend `S` when checking `s1`.
For example, suppose `x` is `shared` and `y` is `linear` when checking the statement `x := y; f(x, y)`:

```
G ; O ; S, {x} ; {y} |- x := y; f(x, y) : ...
```

If the `s1; s2` rule allowed `x := y` to borrow `y` from `f(x, y)`,
then `y` would appear in `S` when checking `x := y`,
and the assignment rule for `x := y` would allow the shared `y` to be assigned to the shared `x`.
Then `x` and `y` would hold the same value, which would get passed twice into `f(x, y)`,
which should not happen (the shared `x` should not coexist with the linear `y`).

Note that this is not a problem for the `e1; e2` rule shown earlier, because a Dafny expression `e1`
cannot contain an assignment to a local variable.
(And in linear Dafny, `shared` is *only* used for local variables:
there are no global `shared` variables, `shared` fields in objects or datatypes, or `shared inout` parameters,
so that even if `e1` is a call to method,
the method can't use a side effect to leak the borrowed `x` into a larger scope.)

Although the current for checking `s1; s2` is restrictive,
a future version of linear Dafny could support borrowing across statements by carefully tracking
`shared` variable dataflow, as in the Rust language.

