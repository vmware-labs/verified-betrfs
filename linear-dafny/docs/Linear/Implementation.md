# Implementation of linear Dafny

The implementation of linear Dafny is an extension to the implementation of standard Dafny,
with most changes in the following files:

- Syntax:
  - [DafnyAst.cs](../../Source/Dafny/DafnyAst.cs)
  - [Dafny.atg](../../Source/Dafny/Dafny.atg)
- Type checking:
  - [Resolver.cs](../../Source/Dafny/Resolver.cs)
  - [Linear.cs](../../Source/Dafny/Linear.cs)
- Compilation:
  - [Compiler.cs](../../Source/Dafny/Compiler.cs)

The central definition underlying the syntax, type checking, and compilation changes is the `Usage` type:

```csharp
public enum Usage {
  Ordinary,
  Shared,
  Linear,
  Ghost,
}
```

The `Usage` type generalizes the `IsGhost` property in the standard Dafny syntax,
so that variables can have "usage" of ordinary, `shared`, `linear`, or `ghost`.
For example, linear Dafny extends the standard Dafny `NonglobalVariable` class with a `Usage`
property, and redefines `IsGhost` as a wrapper around `Usage`:

```csharp
  public abstract class NonglobalVariable : IVariable {
    ...
    Usage usage;  // readonly after resolution
    public Usage Usage {
      get {
        return usage;
      }
      set {
        usage = value;
      }
    }
    public bool IsGhost {
      get {
        return Usage == Usage.Ghost;
      }
    }
    public bool IsLinear {
      get {
        return Usage == Usage.Linear;
      }
    }
    public bool IsShared {
      get {
        return Usage == Usage.Shared;
      }
    }
    ...
  }
```

## Type checking

To check linearity, linear Dafny extends the type checker in Resolver.cs
to track each local variable's availability,
described by the enum `Available`:

```csharp
    enum Available {
      Available, // if x is available, it can be borrowed or consumed (A --> B, A --> C, A --> M)
      Borrowed,  // if x is borrowed, it can be borrowed again (but not consumed) (B --> B)
      Consumed,  // if x is consumed, it cannot be consumed or borrowed
      MutablyBorrowed, // if x is mutably borrowed, it cannot be consumed or borrowed
      // Borrowed is used to implement Wadler's "let!(x) y = e1 in e2" expression,
      // in which linear x is borrowed (appears as "shared") inside e1 before being
      // consumed by e2.  (See Wadler, "Linear types can change the world!")
      // We infer "!(x)" rather than asking the user to write it explicitly.
      // If an Available linear variable x is used as "shared" in e1, we change x to Borrowed in e1.
      // If we find that e1 has borrowed x (changed x Available to x Borrowed),
      // then we can introduce "!(x)" if all these conditions hold:
      // - y is not shared (this isn't let!, but simple copying of shared e1 into shared y)
      // - e1 is not shared (for soundness: can't leak shared x into non-shared y)
      // - e2 consumes x (for soundness: this enforces that sharing strictly precedes consumption,
      //   assuming call-by-value evaluation, even if expression evaluation is otherwise unordered)
      // If e2 does not consume x, x stays Borrowed.
      // Borrowed is only meaningful in expressions; it does not propagate across statements.
      // If statement s contains expressions that (mutably) borrow x, x is reset to Available after s is checked.
      // (In other words, if s does not consume x, s can borrow x temporarily, releasing x after s finishes.)
    }
```

The class `UsageContext` holds a mapping of local variables to their current availability:

```csharp
    class UsageContext {
      internal Dictionary<IVariable, Available> available = new Dictionary<IVariable, Available>();
      ...
    }
```

The linearity checking is not done in the central Dafny type checking functions (`ResolveExpression` and `ResolveStatement`),
but instead is done in the ghost/compilable checkers (`CheckIsCompilable` and `ComputeGhostInterest`).
The ghost/compilable checkers are convenient for linearity checking for two reasons.
First, unlike `ResolveExpression` and `ResolveStatement`,
these checkers are aware of which variables are ghost, and this knowledge is necessary for linearity checking
(linear variables can be assigned to ghost variables, but not to ordinary variables).
Second, these checkers traverse only compilable code, skipping over all ghost code,
which is ideal for linearity checking, since linearity only affects compilable code.

The checkers keep a `UsageContext` object that gets updated as variables are used and borrowed:

```csharp
    Usage CheckIsCompilable(Expression expr, UsageContext usageContext, bool inoutUsage = false) {
      ...
    }

    ...

    UsageContext ComputeGhostInterest(Statement stmt, bool mustBeErasable, ICodeContext codeContext, UsageContext usageContext) {
      ...
    }
    class GhostInterest_Visitor
    {
      readonly ICodeContext codeContext;
      readonly Resolver resolver;
      internal UsageContext usageContext;
      ...
      public void Visit(Statement stmt, bool mustBeErasable, bool assumeRhsCompilable = false) {
        ...
      }
      ...
    }
```

The `UsageContext` object is updated in-place as variable availability changes.
This makes checking `if/else` and `while` slightly tricky, requiring saving copies of `UsageContext`.
(In retrospect, this design led to several bugs, so a more functional programming style with an immutable `UsageContext`
might have been a safer design.)

To check borrowing in an expression like "`var x := e1; e2`",
given a `UsageContext` `uc0`,
the type checker performs the following steps:
- Check `e1` in `uc0` to produce a revised `UsageContext` `uc1`.
- Let `borrow` be the list of all variables newly borrowed by `e1`
(i.e. marked Borrowed in `uc1` but not in `uc0`).
Let `uc2` be `uc1` with all variables in `borrow` set to Available
(see `RemoveInnerBorrowed` in Resolver.cs, shown below)
- Check `e2` in `uc2` to produce `uc3`.
- For each `x` in `borrow` (see `MaybeIntroduceLetBang` in Resolver.cs, shown below):
  - if `e2` consumed `x`, then we discharge the borrowing, leaving `x` Available
  - if `e2` did not consume `x`, we broaden the scope of the borrowing, leaving `x` Borrowed

```csharp
    static List<IVariable> RemoveInnerBorrowed(UsageContext outer, UsageContext inner) {
      List<IVariable> borrow = new List<IVariable>();
      if (inner == null) inner = new UsageContext(null, null);
      if (outer == null) outer = new UsageContext(null, null);
      foreach (var k in new List<IVariable>(inner.available.Keys)) {
        if (outer.available[k] == Available.Available && inner.available[k] == Available.Borrowed) {
          inner.available[k] = Available.Available;
          borrow.Add(k);
        }
      }
      return borrow;
    }

    void MaybeIntroduceLetBang(IToken tok, Usage usage, UsageContext usageContext, List<IVariable> borrow) {
      foreach (var x in borrow) {
        if (usageContext.available[x] == Available.Consumed) {
          // If Body consumed x, try to introduce let!(x) here
          if (usage == Usage.Shared) {
            reporter.Error(MessageSource.Resolver, tok, "cannot borrow {0} when assigning to shared variable", x.Name);
          }
        } else {
          // Otherwise, we don't introduce let!(x) here; just propagate the fact that x was Borrowed
          usageContext.available[x] = Available.Borrowed;
        }
      }
    }
```

## Relevant git commits

### Linear and shared

Basics of `linear`:
- [Some initial support for linear variables, with basic linearity checking for some expressions and statements](https://github.com/secure-foundations/dafny/commit/d63cc8ccb7dcdc1aadf15d5cb94d330b4d68f91a)
- [Support function types with linear/shared parameters/returns](https://github.com/secure-foundations/dafny/commit/61d00e0dd417a2f00a6776615f9aac8f62989eef)

Borrowing and `shared`:
- [Add support for shared variables and for borrowing in method calls](https://github.com/secure-foundations/dafny/commit/d8ae52be72022b3d5595a5e17de2dc5c00f3f500)
- [Generalize rules for borrowing and infer let!(x) for borrowing in expressions](https://github.com/secure-foundations/dafny/commit/c0937814ff81c3cfc03afefd0088c63604c8ea01)

Linear datatypes and tuples:
- [Add linear datatypes](https://github.com/secure-foundations/dafny/commit/bfaa4bd27b3d2338ba22e73c0313af182961b3bf)
- [Support ghost/linear/shared arguments to constructors](https://github.com/secure-foundations/dafny/commit/22cbe251b6664cb6f1b8b9f36e14c5c132b959fe)
- [Allow selection from shared expressions](https://github.com/secure-foundations/dafny/commit/915fb69c0ba2ca53f15b19efbb2dd9475cdc08f6)
- [Support tuples with linear and ghost components](https://github.com/secure-foundations/dafny/commit/c51154653ec55b2a08cd3610228f00968250e989)
- [Allow linear/shared "this"](https://github.com/secure-foundations/dafny/commit/afda6a4d2b2a7acbfcd6190b3ed90c736bf104b9)
- [Allow "linear var D() := ...;" to deconstruct empty linear datatype cases](https://github.com/secure-foundations/dafny/commit/dab22ed867d000341588add7a1f2e1ba4b1a49b3)

### Features for libraries of linear abstract types

Inline functions:
- [Add {:inline} attribute to functions, clean up overloading](https://github.com/secure-foundations/dafny/commit/f402331aec0a1a10ae37ade6f6e534eaa333e444)
- [Fix {:inline} bug and support linear/shared in StmtExpr](https://github.com/secure-foundations/dafny/commit/e67adb3e301d0592d2a0cdfc4f954f01190f7dc3)

Operator overloading:
- [Add operator overloading for ghost [], | |, and in](https://github.com/secure-foundations/dafny/commit/3a42ad3b04b177f275e788a3a861705c0251fb1e)
- [Call PartiallyResolveTypeForMemberSelection for overloads.  Seems to break b8.dfy, git-issue196.dfy; not clear why.](https://github.com/secure-foundations/dafny/commit/f4e44c85c20f8dd60ce6a607e3278ab9e835d45f)
- [Use PartiallyResolveTypeForMemberSelection more gently for overloads, so that b8.dfy and git-issue196.dfy work again](https://github.com/secure-foundations/dafny/commit/34867aa1959d5deaa762fef59dc9e77b410ac14d)

Decreases clauses and rank_is_less_than:
- [Add rank_is_less_than function for user-axiomatized collection types](https://github.com/secure-foundations/dafny/commit/a92fdab9963b0a3eb9fd8806433b97db539e001a)
- [Weaken Contract.Assert for rank_is_less_than](https://github.com/secure-foundations/dafny/commit/e96cdfdc9eec87d781d75ef4b0eefe5abe74dbbd)

caller_must_be_pure:
- [Add caller_must_be_pure attribute for BoxedLinear.Borrow](https://github.com/secure-foundations/dafny/commit/02f16ad6fd33d9c0f1396b790a38ebb1b2412ab2)
- [Allow borrowing of caller_must_be_pure results in some method calls](https://github.com/secure-foundations/dafny/commit/aa60a3bac2e3aed375af867c49affcf0519e7840)

### Mutable borrowing and inout

- [Add inout formals and arguments to the parser](https://github.com/secure-foundations/dafny/commit/101050b2951f39f63f227e78bd724da997e8e7a1)
- [Adapt linearity checks to inout formals](https://github.com/secure-foundations/dafny/commit/25c1455d332995ec98370f234d8ebce25dbbdc7c)
- [Disallow borrowing (shared) a linear variable that was already mutably borrowed and viceversa](https://github.com/secure-foundations/dafny/commit/178c0cb31ad79a5f6da15b0ee5637e760b31ccd0)
- [Only permit linear member select expressions as inout arguments](https://github.com/secure-foundations/dafny/commit/9f46834bcceb7443a2f56e8eb6149ec4e2a7cb7c)
- [Transform inout signatures and callsites to vanilla dafny for resolution](https://github.com/secure-foundations/dafny/commit/ff8f0cd7bc18fdbf4215b479c648d8e8d819195e)
- [Fix linearity check for inout arguments](https://github.com/secure-foundations/dafny/commit/903bde822a0c2ca9af9d3caad3e7d08696da2a54)
- [Support inout `this` (`self`) for datatype members](https://github.com/secure-foundations/dafny/commit/0c4268e1f997f73b9f165d6f85d620efd83fd7a9)
- [Support blocks, ifs, match statements](https://github.com/secure-foundations/dafny/commit/6012f6db3e5c563b1a098241bbcf62e54b742041)
- [Fix linearity check for nested MemberSelectExprs, support while statements](https://github.com/secure-foundations/dafny/commit/fe2481dc89ad05332c270a3ef2b67ac40f78bf37)
- [Overhaul inout assign: support inout update stmt, disallow unsound inout ghost argument](https://github.com/secure-foundations/dafny/commit/673ae820146d92289beb986008c321078f03216c)
- [Fix linearity check allowing multiple mutable borrows in the same call](https://github.com/secure-foundations/dafny/commit/cae85db87380ca4614dc572d367fe8dbf89ae983)
- [Undo inout rewriting before compilation](https://github.com/secure-foundations/dafny/commit/25a2fc15842ee0c3f43a9ae8ee1a0af1a4b1ca1e)
- [Undo inout rewriting of methods before compilation](https://github.com/secure-foundations/dafny/commit/e759fe5af504d1b4189af4d0d3f658489918d433)
- [Undo inout rewriting later, to fix resolution errors](https://github.com/secure-foundations/dafny/commit/947536697dbcc3d2ad93f6c8d20ad707240d8b12)
- [Undo inout this rewriting](https://github.com/secure-foundations/dafny/commit/55f164e4702ab2fdc3d592b445b45c21b02bd7ef)
- [New fix for compilation of datatype member functions](https://github.com/secure-foundations/dafny/commit/2928a9004d680af661d2d8279b25c41b3a1003df)
- [Fix for matching on datatypes](https://github.com/secure-foundations/dafny/commit/dae4154594baaad7a819e54f8fca920cc7918f8e)
- [Treat inout parameters as formal parameters](https://github.com/secure-foundations/dafny/commit/b2dbdc86499d2260c898f196bd0812ad48dbf921)
- [attempt to fix compilation for inout arguments/assign](https://github.com/secure-foundations/dafny/commit/fc36b3e0b52d7758b6125206b749591426e894bd)
- [linear inout compilation support for datatype methods](https://github.com/secure-foundations/dafny/commit/01cbe7ddf83a275bad79ad57ae5b13334e0fad9c)
- [attempt to implement missing case in compilation rewriter](https://github.com/secure-foundations/dafny/commit/59e7982975155cee2c8fadc2958ed782cf5c1cf8)
- [attempt to partly fix rewriting for compilation of resolved statements](https://github.com/secure-foundations/dafny/commit/ba9b19d71e78010f64cb249b9b0b01c345c0e76f)
- [rewrite resolved bodies of match statements](https://github.com/secure-foundations/dafny/commit/5c04a6e3d4055192e891245b978cedbc6c7f37cf)
- [inout ghost assignment are ghost](https://github.com/secure-foundations/dafny/commit/d2bbff441fd624cec1f4da298f5eb88483ccc176)

### Compilation

Linear Dafny has support for compiling programs to C++.

- [Start working on some linear compilation tests](https://github.com/secure-foundations/dafny/commit/ea1b9fa78fc05b644c89e8f97f1a7478ce7eebe0)
- [More progress on compiling linear sequence examples](https://github.com/secure-foundations/dafny/commit/c164ae463e1c853bc1a0d7914d913b86fa875f32)
- [Pass along linearity info when declaring a local variable, and in the C++ backend, pass that info along to TypeName](https://github.com/secure-foundations/dafny/commit/31c821b12bad79f8d07aafd538c3e790f20424b4)
- [Basic linear tests compile and run (except for Dafny complaints about missing extern declarations)](https://github.com/secure-foundations/dafny/commit/6d03cc75f90d5f0502eb3e3cffbc6c70837e4342)
- [Linear test compiles cleanly and runs correctly](https://github.com/secure-foundations/dafny/commit/01d2d856d172ae9c62540128f2b696892853c3c6)
- [Grab linearity data from datatype](https://github.com/secure-foundations/dafny/commit/f705a21c061c7d2d25b7bfa7f227511a73f40459)
- [Remove some REVIEW comments, as in each case, the type passed in is already null, so we won't be emitting type information. Instead, at least in C++, we use 'auto'](https://github.com/secure-foundations/dafny/commit/ac80ae6def605150b1e406e37af94616cc7bb532)
- [Pass Usage instead of a isLinear:bool, so that we can also differentiate shared variables](https://github.com/secure-foundations/dafny/commit/31b16bd2ce8324d36e61108dcf4a78f66c6d8fe4)
- [DeclareFormal also needs to take a Usage.  In C++ land, we also pass usage along when declaring return types](https://github.com/secure-foundations/dafny/commit/81c2c294cdc41ad2631cd3b20c5d1cfee55de09d)
- [Default values need to know Usage as well](https://github.com/secure-foundations/dafny/commit/5402824020fe47fbc1a02b806c90fc561a755e9d)
- [Split the declaration and implementation of equality checks for datatypes between the .h and .cpp files](https://github.com/secure-foundations/dafny/commit/b1b646007915cd97611afd8cbd1754aadbbc63ee)
- [Pass additional usage info to various calls to TypeName within the C++ backend](https://github.com/secure-foundations/dafny/commit/900698ba5fad9a1c8dce2299a23a1974409d0e05)
- [Pass in the usage of function result types](https://github.com/secure-foundations/dafny/commit/f9be75b52ad7cacc7c00b075d49042ac0964482d)

