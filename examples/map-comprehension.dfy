
module MapComprehension {
  method Main()
  {
    var a := map[2 := (3, 5), 3 := (5, 8)];
    var one := map k | k in a :: k := a[k].0;
    var two := map k | k in a :: a[k].0;
    print one, " =?= ", two;
    assert one == two;
  }
}
