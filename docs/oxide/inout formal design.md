# `inout` design

Syntax extension to linear dafny to support in-place mutation of datatype fields through mutable references. Mutable references can only be constructed as method formals; non-argument variables cannot contain mutable references.

Mutable references can refer to `ordinary` fields of `linear` `datatype`s (`ordinary inout` reference) or to `linear` fields of `linear` `datatype`s (`linear inout` reference). There can be a "path" of `linear` fields of `linear` datatypes to reach the `linear` or `ordinary` field which is mutably referenced; no `ordinary` fields are permitted in the path (except at the end). Support for mutation of `ordinary` fields of `ordinary` datatypes is out of scope for this design (and likely unsound in the general case).

Mutating (transitive) fields of `linear` datatypes is safe as there exists only a single reference to the outer `linear` datatype.



##### example of path of `linear` fields

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">linear</span> datatype Loco = Loco(fuel: nat)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">linear</span> datatype Car = Car(passengers: nat)
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span><span style="color: #008000; font-weight: bold">linear</span> datatype Train = Train(<span style="color: #008000; font-weight: bold">linear</span> loco: Loco, <span style="color: #008000; font-weight: bold">linear</span> car1: Car, <span style="color: #008000; font-weight: bold">linear</span> car2: Car)
</span><span id="lineno-syn-00-4"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">4 </span>
</span><span id="lineno-syn-00-5"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">5 </span><span style="color: #008000; font-weight: bold">method</span> <span style="color: #0000FF">Rail</span>(<span style="color: #008000; font-weight: bold">linear</span> train: Train) {
</span><span id="lineno-syn-00-6"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">6 </span>  <span style="color: #408080; font-style: italic">→ valid path for an `ordinary inout` reference:</span> train.car2.passengers
</span><span id="lineno-syn-00-7"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">7 </span>  <span style="color: #408080; font-style: italic">→ valid path for a `linar inout` reference:</span> train.car2
</span><span id="lineno-syn-00-8"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">8 </span>}
</span></pre></div>



## syntax

### method definition

A `method` parameter takes a mutable reference if it's marked `inout` (`ordinary inout` reference). It can be optionally marked `linear` (`linear inout` reference). A `linear inout` parameter must be of a `linear` `datatype`.

```
method Method([linear] inout param: Type)
```



##### example

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">linear</span> datatype Loco = Loco(fuel: nat)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">linear</span> datatype Car = Car(passengers: nat)
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span>
</span><span id="lineno-syn-00-4"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">4 </span><span style="color: #008000; font-weight: bold">method</span> <span style="color: #0000FF">LoadPassengers</span>(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> self: Car, count: nat)
</span></pre></div>



A `method` that's a member of a `linear` datatype can be marked `linear inout` to take the `datatype` as a `linear inout` mutable reference. This is equivalent to taking `this` as a `linear inout` parameter.

```
linear inout Member()
```



##### example

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">linear</span> datatype Train = Train(<span style="color: #008000; font-weight: bold">linear</span> loco: Loco, <span style="color: #008000; font-weight: bold">linear</span> car1: Car, <span style="color: #008000; font-weight: bold">linear</span> car2: Car)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span>{
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span>  <span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> <span style="color: #008000; font-weight: bold">method</span> <span style="color: #0000FF">LoadFuel</span>(fuel: nat) {
</span><span id="lineno-syn-00-4"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">4 </span>    <span style="color: #408080; font-style: italic">// `this` is `linear inout` here</span>
</span></pre></div>



#### `requires` and `ensures`

A `requires` clause can refer to the value of `param` before the method has executed as `param`. An `ensures` clause can refer to the value of `param` before the method has executed as `old(param)` and it can refer to the value of `param` after execution as `param`. Note that, differently from `old` in dynamic frames dafny, because `param` is linear and doesn't contain pointers, `old(param).fieldname` and `old(param.fieldname)` have identical meaning. To simplify translation, we only permit `old(param)` (no complex expressions within `old`) for `inout` method parameters.



##### example

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> <span style="color: #0000FF">LoadPassengers</span>(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> self: Car, count: nat)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">ensures</span> self.passengers == <span style="color: #008000; font-weight: bold">old</span>(self).passengers + count
</span></pre></div>



### method body

The body of a `method` that takes one or more mutable references as parameters will allow assignment to the `inout` variable. If it's a `linear inout` reference, the variable is treated linearly within the method body (it must be available on `return`). Mutable references can be constructed by passing the `linear inout` variable (or a path with `linear` fields, as described earlier) to a `method` taking an `inout` argument. Assigments and mutations of the `inout` variable affect the datatype from which the mutable reference was constructed.



### call site

A method call can construct a mutable reference by passing (a path of `linear` fields of) a `linear` variable or a `linear inout` argument, prefixed with `[linear] inout`. The variable/argument must be available before the call and remains available after the call. The variable/argument must *not* be otherwise borrowed for the duration of the call.



##### example #1, `ordinary inout` reference

given the trusted library `method Assign` (see "proposed trusted methods")

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> {:<span style="color: #008000; font-weight: bold">extern</span>} Assign&lt;V&gt;(<span style="color: #008000; font-weight: bold">inout</span> v: V, newV: V)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">ensures</span> v == newV
</span></pre></div>

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> <span style="color: #0000FF">LoadPassengers</span>(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> self: Car, count: nat)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">ensures</span> self.passengers == <span style="color: #008000; font-weight: bold">old</span>(self).passengers + count
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span>{
</span><span id="lineno-syn-00-4"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">4 </span>  <span style="color: #B00040">var</span> newCount := self.passengers + count;
</span><span id="lineno-syn-00-5"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">5 </span>  Assign(<span style="color: #008000; font-weight: bold">inout</span> self.passengers, newCount);
</span><span id="lineno-syn-00-6"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">6 </span>}
</span></pre></div>



##### example #2, `linear inout` reference

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">linear</span> <span style="color: #B00040">var</span> train: Train := ...;
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span>LoadPassengers(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> train.car1);
</span></pre></div>

(`car1` is a `linear` field of `Train`)



### ghost code

Similarly to `linear` variables, `[linear] inout` variables (formals) can be used in ghost expressions and assigned to `ghost` variables.



##### example

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> <span style="color: #0000FF">LoadPassengers</span>(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> self: Car, count: nat)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">ensures</span> self.passengers == <span style="color: #008000; font-weight: bold">old</span>(self).passengers + count
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span>{
</span><span id="lineno-syn-00-4"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">4 </span>  <span style="color: #B00040">var</span> newCount := self.passengers + count;
</span><span id="lineno-syn-00-5"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">5 </span>  <span style="color: #008000; font-weight: bold">ghost</span> <span style="color: #B00040">var</span> beforeLoad := self;
</span><span id="lineno-syn-00-6"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">6 </span>  Assign(<span style="color: #008000; font-weight: bold">inout</span> self.passengers, newCount);
</span><span id="lineno-syn-00-7"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">7 </span>  assert beforeLoad == <span style="color: #008000; font-weight: bold">old</span>(self);
</span><span id="lineno-syn-00-8"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">8 </span>  assert beforeLoad.passengers == self.passengers - count;
</span><span id="lineno-syn-00-9"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">9 </span>}
</span></pre></div>



## trusted methods

These are trusted library methods that complement the new syntax.

### `Assign`

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> {:<span style="color: #008000; font-weight: bold">extern</span>} Assign&lt;V&gt;(<span style="color: #008000; font-weight: bold">inout</span> v: V, newV: V)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">ensures</span> v == newV
</span></pre></div>

`Assign` enables changing the value of an `ordinary` field of a `linear` datatype without additional syntax. We can later add syntactic sugar to support regular assignment syntax.



### `Replace`

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> {:<span style="color: #008000; font-weight: bold">extern</span>} Replace&lt;V&gt;(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> v: V, <span style="color: #008000; font-weight: bold">linear</span> newV: V)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span>returns (<span style="color: #008000; font-weight: bold">linear</span> replaced: V)
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span><span style="color: #008000; font-weight: bold">ensures</span> replaced == <span style="color: #008000; font-weight: bold">old</span>(v)
</span><span id="lineno-syn-00-4"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">4 </span><span style="color: #008000; font-weight: bold">ensures</span> v == newV
</span></pre></div>

`Replace` enables updating the value of a `linear` field of a `linear` datatype without additional syntax. We can later add syntactic sugar to support regular assignment syntax.



### `Swap`

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> {:<span style="color: #008000; font-weight: bold">extern</span>} Swap&lt;V&gt;(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> a: V, <span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> b: V)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">ensures</span> b == <span style="color: #008000; font-weight: bold">old</span>(a)
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span><span style="color: #008000; font-weight: bold">ensures</span> a == <span style="color: #008000; font-weight: bold">old</span>(b)
</span></pre></div>

`Swap` enables swapping the values of two `linear` fields of the same type of `linear` datatypes without additional syntax.



## translation (verification conditions) [WIP]

For verification (translation to _Boogie_), the `[linear] inout` parameters are translated to regular dafny as follows:



### method definition

```
method Method([linear] inout param: Type)
  returns (ret1: RetType)
  requires Expr(param)
  ensures Expr(param, after(param))
```

translates to:

```
method Method(param: Type)
  returns (param': Type, ret1: RetType)
  requires Expr(param)
  ensures Expr(/* param -> */ param, /* after(param) */ -> param')
```



### body

Introduce preamble:

```
{
  var param := param;
```

introduce epilogue:

```
	param' := param;
}
```



### call site

For

```
linear var thing;
```



**Case #1**

```
var ret1 := Method(inout thing);
```

translates to:

```
var ret1;
thing, ret1 := Method(thing);
```



**Case #2**

```
var ret1 := Method(inout thing.field);
```

translates to:

```
var _tmp00, ret1 := Method(thing.field);
thing := thing.(field := _tmp00);
```



## design considerations

### alternatives considered

#### `after`

We considered using `after` to refer to the value after execution; unfortunately this breaks the semantics of `old` from within the body.

<div class="highlight" style="font-size:11pt"><pre style="line-height: 125%"><span></span><span id="lineno-syn-00-1"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">1 </span><span style="color: #008000; font-weight: bold">method</span> <span style="color: #0000FF">LoadPassengers</span>(<span style="color: #008000; font-weight: bold">linear</span> <span style="color: #008000; font-weight: bold">inout</span> self: Car, count: nat)
</span><span id="lineno-syn-00-2"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">2 </span><span style="color: #008000; font-weight: bold">ensures</span> <span style="color: #0000FF">after</span>(self).passengers == self.passengers + count
</span><span id="lineno-syn-00-3"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">3 </span>{
</span><span id="lineno-syn-00-4"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">4 </span>  <span style="color: #B00040">var</span> newCount := self.passengers + count;
</span><span id="lineno-syn-00-5"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">5 </span>  <span style="color: #008000; font-weight: bold">ghost</span> <span style="color: #B00040">var</span> beforeLoad := self;
</span><span id="lineno-syn-00-6"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">6 </span>  Assign(<span style="color: #008000; font-weight: bold">inout</span> self.passengers, newCount);
</span><span id="lineno-syn-00-7"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">7 </span>  assert beforeLoad.passengers == self.passengers - count;
</span><span id="lineno-syn-00-8"><span style="background-color: #f0f0f0; padding: 0 5px 0 5px">8 </span>}
</span></pre></div>



### [WIP]



[todo discuss how borrow checking is only useful when you have mutable references]

```
                 linearity
             /              \
      mutable refs          |
            \               |
             -----------\   |
                   borrow checker
```



[discuss alternative compiler optimisation pass for `function method`s]



[todo discuss improvement over `old` and labels in dynamic frames dafny]

```
method (x: Datatype)  (x: Datatype) -> (x': Datatype)

ensures old(x).y == 22  ensures x.y == 22
ensures old(x.y) == 22  ensures x.y == 22

label here:
ghost var x_snapshot := x;

old@here(x.y)

Mutate(x.somefield) // x := x.(somefield := Mutate(x.somefield))
```



[todo: DAG tree??]