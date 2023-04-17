// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

linear datatype lOption<A> = LNone | LSome(linear a:A)
linear datatype nlPair<A, B> = NlPair(a:A, linear b:B)
linear datatype llPair<A, B> = LlPair(linear a:A, linear b:B)
linear datatype nlList<A> = NlNil | NlCons(hd:A, linear tl:nlList<A>)
datatype list<A> = Nil | Cons(hd:int, tl:list)

function method AllocInt(x:int):linear int
function method FreeInt(linear x:int):int
function method GetInt(shared x:int):int
function method ShareInt(shared x:int):shared int

function method LOptionGet<A>(linear o:lOption<A>):linear A
    requires o.LSome?
{
    linear var LSome(a) := o;
    a
}

function method SOptionGet<A>(shared o:lOption<A>):shared A
    requires o.LSome?
{
    o.a
}

function method Length1<A>(shared l:nlList<A>):int
{
    if l.NlNil? then 0
    else 1 + Length1(l.tl)
}

function method Length2<A>(shared l:nlList<A>):int
{
    shared match l
    {
        case NlNil => 0
        case NlCons(_, tl) => 1 + Length2(tl)
    }
}

function method IncrAll1(linear l:nlList<int>):linear nlList<int>
{
    linear match l
    {
        case NlNil => NlNil
        case NlCons(hd, tl) => NlCons(hd + 1, IncrAll1(tl))
    }
}

function method IncrAll2(linear l:nlList<int>):linear nlList<int>
{
    if l.NlNil? then l
    else
    (
        linear var NlCons(hd, tl) := l;
        NlCons(hd + 1, IncrAll2(tl))
    )
}

function method FreeList<A>(linear l:nlList<A>):()
{
    linear match l
    {
        case NlNil => ()
        case NlCons(hd, tl) => FreeList(tl)
    }
}

function method Share1(linear p:nlPair<int, int>):linear nlPair<int, int>
{
    var x:int := p.a + p.a;
    var y:int := (shared var NlPair(sa, sb) := p; sa + GetInt(sb));
    linear var NlPair(_, b) := p;
    NlPair(x, b)
}

function method Share2(linear l:nlList<int>):linear nlList<int>
{
    var x:int := if l.NlNil? then 0 else l.hd + l.hd;
    var y:int := (
        shared match l
        {
            case NlNil => 0
            case NlCons(sa, sb) => sa + Length1(sb)
        }
    );
    linear match l
    {
        case NlNil => NlNil
        case NlCons(_, b) => NlCons(x + y, b)
    }
}

method M(linear l_in:nlList<int>, shared s:nlList<int>, shared nl:nlPair<int, nlPair<int, int>>) returns(linear l:nlList<int>)
{
    l := l_in;
    linear match l
    {
        case NlNil => l := NlCons(10, NlNil);
        case NlCons(hd, tl) => l := NlCons(hd, tl);
    }
    var i := l.hd + l.hd;
    var k:int := (shared var NlCons(si, sy) := l; si + 1);
    var nla := nl.b.a;
    shared var nlb := nl.b.b;
    shared match s
    {
        case NlNil => k := k + 1;
        case NlCons(hd, tl) => k := k + hd + Length1(tl);
    }
    linear var NlCons(a, b) := l;
    l := b;
    if (s.NlCons?)
    {
        shared var NlCons(sa, sb) := s;
        k := k + sa + Length1(sb);
    }
}

method TupleGood(shared x:(int, linear int), y:(int, int, bool), linear l:int) returns(linear q:int)
{
    var i := x.0;
    shared var j := x.1;
    linear var z:(int, linear int) := (i, linear l);
    linear var (a, linear b) := z;
    q := b;
}

type TX
function operator(| |)(tx:TX):nat
datatype dx = DX(tx:TX)
function MX(d:dx):nat
{
    match d { case DX(tx) => |tx| }
}

linear datatype fd = FD(i:int)
{
  linear function method f1():(linear r:fd) {this}
  shared function method f2():int {this.i}
  linear function method f3():(linear r:fd) {this.f1()}
  linear method m1() returns(linear r:fd) {r := this;}
  linear method m2() returns(linear r:fd) {r := m1();}
  linear method m3() returns(linear r:fd) {var i := f2(); r := m1();}
}

linear datatype D0 = D0
linear datatype Dg = Dg(ghost g:int)

method TestD0(linear x:D0)
{
    linear var D0() := x; // note:it's important to allow the "()"; this is *not* the same as "linear var D0 := x;"
}

method TestDg(linear x:Dg)
{
    linear var Dg(g) := x;
}

function method FunD0(linear x:D0):()
{
    linear var D0() := x;
    ()
}

function method FunDg(linear x:Dg):()
{
    linear var Dg(g) := x;
    ()
}

//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//

// ---------- fails ------------------------------------

function method LOptionGet_a<A>(linear o:lOption<A>):A
    requires o.LSome?
{
    var LSome(a) := o;
    a
}

function method LOptionGet_b<A>(linear o:lOption<A>):linear lOption<A>
    requires o.LSome?
{
    shared var LSome(a) := o;
    o
}

function method LOptionGet_c<A>(linear o:lOption<A>):linear lOption<A>
    requires o.LSome?
{
    shared match o
    {
        case LSome(a) => o
    }
}

function method SOptionGet_a<A>(linear o:lOption<A>):linear A
    requires o.LSome?
{
    o.a
}

function method F_a(i:int):nlPair<int, int>
{
    NlPair(i, i)
}

function method F_b(shared i:int):nlPair<int, int>
{
    NlPair(i, i)
}

function method F_c(linear i:int):nlPair<int, int>
{
    NlPair(i, i)
}

function method F_d(i:int):shared nlPair<int, int>
{
    NlPair(i, i)
}

function method F_e(shared i:int):shared nlPair<int, int>
{
    NlPair(i, i)
}

function method F_f(linear i:int):shared nlPair<int, int>
{
    NlPair(i, i)
}

function method F_g(i:int):linear nlPair<int, int>
{
    NlPair(i, i)
}

function method F_h(shared i:int):linear nlPair<int, int>
{
    NlPair(i, i)
}

function method F_i(linear i:int):linear nlPair<int, int>
{
    NlPair(i, i)
}

function method G_a(p:nlPair<int, int>):int
{
    shared var NlPair(a, b) := p; a
}

function method G_b(p:nlPair<int, int>):int
{
    linear var NlPair(a, b) := p; a
}

function method G_c(shared p:nlPair<int, int>):int
{
    var NlPair(a, b) := p; a
}

function method G_d(shared p:nlPair<int, int>):int
{
    linear var NlPair(a, b) := p; a
}

function method G_e(linear p:nlPair<int, int>):int
{
    var NlPair(a, b) := p; a
}

function method G_f(linear p:nlPair<int, int>):linear nlPair<int, int>
{
    shared var NlPair(a, b) := p; p
}

function method H_a(shared p:nlPair<int, int>):int
{
    var NlPair(a, b) := p; b
}

function method H_b(shared p:nlPair<int, int>):shared int
{
    var NlPair(a, b) := p; a
}

function method H_c(linear p:nlPair<int, int>):int
{
    var NlPair(a, b) := p; b
}

function method H_d(shared p:nlPair<int, int>):linear int
{
    var NlPair(a, b) := p; a
}

function method G_a'(p:nlPair<int, int>):int
{
    shared match p {case NlPair(a, b) => a}
}

function method G_b'(p:nlPair<int, int>):int
{
    linear match p {case NlPair(a, b) => a}
}

function method G_c'(shared p:nlPair<int, int>):int
{
    match p {case NlPair(a, b) => a}
}

function method G_d'(shared p:nlPair<int, int>):int
{
    linear match p {case NlPair(a, b) => a}
}

function method G_e'(linear p:nlPair<int, int>):int
{
    match p {case NlPair(a, b) => a}
}

function method G_f'(linear p:nlPair<int, int>):linear nlPair<int, int>
{
    shared match p {case NlPair(a, b) => p}
}

function method H_a'(shared p:nlPair<int, int>):int
{
    match p {case NlPair(a, b) => b}
}

function method H_b'(shared p:nlPair<int, int>):shared int
{
    match p {case NlPair(a, b) => a}
}

function method H_c'(linear p:nlPair<int, int>):int
{
    match p {case NlPair(a, b) => b}
}

function method H_d'(shared p:nlPair<int, int>):linear int
{
    match p {case NlPair(a, b) => a}
}

method G_a''(p:nlPair<int, int>) returns(x:int)
{
    shared var NlPair(a, b) := p; x := a;
}

method G_b''(p:nlPair<int, int>) returns(x:int)
{
    linear var NlPair(a, b) := p; x := a;
}

method G_c''(shared p:nlPair<int, int>) returns(x:int)
{
    var NlPair(a, b) := p; x := a;
}

method G_d''(shared p:nlPair<int, int>) returns(x:int)
{
    linear var NlPair(a, b) := p; x := a;
}

method G_e''(linear p:nlPair<int, int>) returns(x:int)
{
    var NlPair(a, b) := p; x := a;
}

method G_f''(linear p:nlPair<int, int>) returns(linear x:nlPair<int, int>)
{
    shared var NlPair(a, b) := p; x := p;
}

method H_a''(shared p:nlPair<int, int>) returns(x:int)
{
    var NlPair(a, b) := p; x := b;
}

method H_b''(shared p:nlPair<int, int>) returns(shared x:int)
{
    var NlPair(a, b) := p; x := a;
}

method H_c''(linear p:nlPair<int, int>) returns(x:int)
{
    var NlPair(a, b) := p; x := b;
}

method H_d''(shared p:nlPair<int, int>) returns(linear x:int)
{
    var NlPair(a, b) := p; x := a;
}

method G_a'''(p:nlPair<int, int>) returns(x:int)
{
    shared match p {case NlPair(a, b) => x := a;}
}

method G_b'''(p:nlPair<int, int>) returns(x:int)
{
    linear match p {case NlPair(a, b) => x := a;}
}

method G_c'''(shared p:nlPair<int, int>) returns(x:int)
{
    match p {case NlPair(a, b) => x := a;}
}

method G_d'''(shared p:nlPair<int, int>) returns(x:int)
{
    linear match p {case NlPair(a, b) => x := a;}
}

method G_e'''(linear p:nlPair<int, int>) returns(x:int)
{
    match p {case NlPair(a, b) => x := a;}
}

method G_f'''(linear p:nlPair<int, int>) returns(linear x:nlPair<int, int>)
{
    shared match p {case NlPair(a, b) => x := p;}
}

method H_a'''(shared p:nlPair<int, int>) returns(x:int)
{
    match p {case NlPair(a, b) => x := b;}
}

method H_b'''(shared p:nlPair<int, int>) returns(shared x:int)
{
    match p {case NlPair(a, b) => x := a;}
}

method H_c'''(linear p:nlPair<int, int>) returns(x:int)
{
    match p {case NlPair(a, b) => x := b;}
}

method H_d'''(shared p:nlPair<int, int>) returns(linear x:int)
{
    match p {case NlPair(a, b) => x := a;}
}

function method Match_a(linear l:nlList<int>, linear r:nlList<int>):linear nlList<int>
{
    linear match l
    {
        case NlNil => r
        case NlCons(a, b) => b
    }
}

function method Match_b(linear l:nlList<int>, linear r:nlList<int>):linear nlList<int>
{
    linear match l
    {
        case NlCons(a, b) => b
        case NlNil => r
    }
}

method Match_c(linear l:nlList<int>, linear r:nlList<int>) returns(linear x:nlList<int>)
{
    linear match l
    {
        case NlNil => x := r;
        case NlCons(a, b) => x := b;
    }
}

method Match_d(linear l:nlList<int>, linear r:nlList<int>) returns(linear x:nlList<int>)
{
    linear match l
    {
        case NlCons(a, b) => x := b;
        case NlNil => x := r;
    }
}

method Match_e(linear l:nlList<int>) returns(linear x:nlList<int>)
{
    linear match l
    {
        case NlNil => {}
        case NlCons(a, b) => x := b;
    }
}

method Match_f(linear l:nlList<int>) returns(linear x:nlList<int>)
{
    linear match l
    {
        case NlCons(a, b) => x := b;
        case NlNil => {}
    }
}

method Vars_a() returns(linear l:nlList<int>)
{
    l := NlCons(10, NlNil);
    shared var NlCons(si, sy) := l;
}

method Vars_b() returns(linear l:nlList<int>)
{
    l := NlCons(10, NlNil);
    linear var ltl := (shared var NlCons(li, ly) := l; ly);
}

method Vars_c() returns(linear l:nlList<int>)
{
    l := NlCons(10, NlNil);
    shared var ltl := (shared var NlCons(li, ly) := l; ly);
}

function method Leak_a():int
{
    linear var l:nlList<int> := NlNil; 0
}

function method Leak_b():int
{
    linear var NlCons(a, b) := NlCons(10, NlNil); 0
}

function method Leak_c():int
{
    linear match NlCons(10, NlNil) {case NlCons(a, b) => 0}
}

method Leak_a'()
{
    linear var l:nlList<int> := NlNil;
}

method Leak_b'()
{
    linear var NlCons(a, b) := NlCons(10, NlNil);
}

method Leak_c'()
{
    linear match NlCons(10, NlNil) {case NlCons(a, b) => {}}
}

function method id<A>(linear a:A):linear A

method ExpSelect(linear l:nlPair<int, nlPair<int, int>>, shared s:nlPair<int, nlPair<int, int>>)
{
    var x1 := l.b.a; // ok: borrow l
    shared var x2 := l.b.b; // can't smuggle shared value into x2
    shared var x3 := s.b.a; // can't assign ordinary to shared
    var x4 := s.b.b; // can't assign ordinary to shared
    var y1 := id(l).b.a; // can't borrow from non-variable expression id(l)
}

method TupleBad(shared x:(int, linear int), y:(int, int, bool), linear l:int) returns(linear q:int)
{
    shared var i := x.0;
    var j := x.1;
    linear var z:(int, linear int) := (i, linear l);
    linear var (a, linear b) := z;
    q := b;
}

linear datatype fd' = FD'(i:int)
{
  linear function method f1():(linear r:fd') {FD'(this.i)}
  shared function method f2():int {f1().i}
  function method f3():int {f2()}
  linear method m1() returns(linear r:fd') {r := FD'(this.i);}
  method m2() returns(linear r:fd') {r := m1();}
}
