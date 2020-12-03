include "StateImpl.i.dfy"
include "CommitterImpl.i.dfy"
include "../lib/Lang/LinearBox.i.dfy"

module FullImpl {
  import opened Options
  import opened StateImpl
  import opened CommitterImpl
  import opened DiskOpImpl
  import StateModel
  import CommitterModel
  import JC = JournalCache
  import opened LinearBox

  class Full {
    var bc: Variables;
    var jc: BoxedLinear<Committer>;
    
    ghost var Repr: set<object>;

    predicate ProtectedReprInv()
    reads this, this.Repr
    {
      && this in Repr
      && this.bc in Repr
      && this.jc in Repr

      // TODO make bc.Repr instaed of bc.Repr()
      // so we don't have to do this nonsense.
      // (jonh) Or wait until linearization gets to the top of the object tree...
      && this.bc.persistentIndirectionTable in Repr
      && this.bc.ephemeralIndirectionTable in Repr
      && (this.bc.frozenIndirectionTable != null ==>
          this.bc.frozenIndirectionTable in Repr)
      && this.bc.lru in Repr
      && this.bc.cache in Repr
      && this.bc.blockAllocator in Repr

      && this.Repr == {this} + this.bc.Repr() + this.jc.Repr
      && this !in this.bc.Repr()
      && this !in this.jc.Repr
      && this.bc.Repr() !! this.jc.Repr
      && this.jc.Inv()
    }

    protected predicate ReprInv()
    reads this, this.Repr
    ensures ReprInv() ==> this in this.Repr
    {
      ProtectedReprInv()
    }

    lemma reveal_ReprInv()
    ensures ReprInv() <==> ProtectedReprInv()
    {
    }

    predicate W()
    reads this, this.Repr
    {
      && ReprInv()
      && this.bc.WF()
      && this.jc.Has()
      && this.jc.Read().WF()
    }

    function I() : StateModel.Variables
    reads this, this.Repr
    requires W()
    {
      StateModel.Variables(this.bc.I(), this.jc.Read().I())
    }

    predicate WF()
    reads this, this.Repr
    {
      && W()
      && this.bc.WF()
      && this.jc.Read().WF()
    }

    predicate Inv()
    reads this, this.Repr
    {
      && W()
      && StateModel.Inv(I())
    }

    constructor()
    ensures Inv()
    ensures fresh(Repr)
    ensures !bc.ready
    ensures jc.Read().I()
        == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[])
    {
      bc := new Variables();
      linear var cm := CommitterImpl.Committer.Constructor();
      jc := new BoxedLinear(cm);

      new;
      Repr := {this} + this.bc.Repr() + this.jc.Repr;

      assert StateModel.Inv(I());
    }
  }
}
