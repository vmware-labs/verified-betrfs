include "StateImpl.i.dfy"
include "CommitterImpl.i.dfy"

module FullImpl {
  import opened Options
  import opened StateImpl
  import opened CommitterImpl
  import opened DiskOpImpl
  import StateModel
  import CommitterModel
  import JC = JournalCache

  class Full {
    var bc: Variables;
    var jc: Committer;
    
    ghost var Repr: set<object>;

    predicate ProtectedReprInv()
    reads this, this.Repr
    {
      && this in Repr
      && this.bc in Repr
      && this.jc in Repr

      // UGH TODO make bc.Repr instaed of bc.Repr()
      // so we don't have to do this crap
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
      && this.bc.W()
      && this.jc.W()
    }

    function I() : StateModel.Variables
    reads this, this.Repr
    requires W()
    {
      StateModel.Variables(this.bc.I(), this.jc.I())
    }

    predicate WF()
    reads this, this.Repr
    {
      && W()
      && this.bc.WF()
      && this.jc.WF()
    }

    predicate Inv(k: ImplConstants)
    reads this, this.Repr
    {
      && W()
      && StateModel.Inv(Ic(k), I())
    }

    constructor(k: ImplConstants)
    ensures Inv(k)
    ensures fresh(Repr)
    ensures !bc.ready
    ensures CommitterModel.I(jc.I())
        == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[])
    {
      bc := new Variables();
      jc := new Committer();

      new;
      Repr := {this} + this.bc.Repr() + this.jc.Repr;

      assert StateModel.Inv(Ic(k), I());
    }
  }
}
