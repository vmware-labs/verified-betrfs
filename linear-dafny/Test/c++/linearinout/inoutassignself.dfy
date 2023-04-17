module Contiguous {

datatype Thing = Thing()

method ChangeThing(thing: Thing) returns (res: Thing) {
  res := Thing();
}

linear datatype Container = Container(thing: Thing) {
  linear inout method DoSomething() {
    inout self.thing := ChangeThing(self.thing);
  }
}

method Main() {
  linear var cnt := Container(Thing());
  inout cnt.DoSomething();
  linear var Container(_) := cnt;
}

}
