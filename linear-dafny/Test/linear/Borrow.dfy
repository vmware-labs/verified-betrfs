// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

function method AllocInt(x:int):linear int
function method FreeInt(linear x:int):int
function method GetInt(shared x:int):int
function method ShareInt(shared x:int):shared int

method B1(linear x_in:int) returns(linear x:int, j:int)
{
    var i:int := GetInt(x_in) + GetInt(x_in);
    x := x_in;
    j := i + GetInt(x) + GetInt(x);
}

function method F1(linear x:int):linear int
{
    var i:int := GetInt(x) + GetInt(x);
    var j:int := GetInt(x) + GetInt(x);
    x
}

function method F2(linear x:int):linear int
{
    F1(var i:int := GetInt(x) + GetInt(x); x)
}

function method F3(linear x:int):linear int
{
    var i:int := (
      shared var s:int := ShareInt(x);
      GetInt(s)
    );
    x
}

// ---------- fails ------------------------------------

function method F1_a(linear x:int):int
{
    var i:int := GetInt(x) + FreeInt(x);
    i
}

function method F1_b(linear x:int):int
{
    var i:int := GetInt(x) + GetInt(x);
    i
}

function method F1_c(x:int):int
{
    linear var l:int := AllocInt(x);
    x
}

function method F1_d(linear x:int):int
{
    var p := (
      GetInt(x),
      FreeInt(x)
    );
    0
}

function method F1_d'(linear x:int):int
{
    var p := (
      FreeInt(x),
      GetInt(x)
    );
    0
}

function method F1_e(linear x:int):int
{
    var p := (
      (var i:int := GetInt(x); i + 1),
      FreeInt(x)
    );
    0
}

function method F1_e'(linear x:int):int
{
    var p := (
      FreeInt(x),
      (var i:int := GetInt(x); i + 1)
    );
    0
}

function method F3_a(linear x:int):linear int
{
    shared var i:int := ShareInt(x);
    x
}
