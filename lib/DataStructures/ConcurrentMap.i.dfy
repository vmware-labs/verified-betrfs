include "../Base/sequences.i.dfy"

module ConcurrentMap {
  import opened Sequences

type Key = int
type Value(!new,==)

datatype Slot = Slot(ghost slot: nat)
predicate ValidSlot(elementsLength: nat, slot: Slot)
{
  slot.slot < elementsLength
}

function SlotForKey(elementsLength: nat, key: Key): (result: Slot)
requires 0 < elementsLength
ensures ValidSlot(elementsLength, result)
//  {
//    var h := hash64(key);
//    Slot((h as nat) % elementsLength)
//  }

datatype Item = Empty | Entry(key: Key, value: Value) | Tombstone(key: Key)

datatype ThreadState =
  | Insert(key: Key, value: Value, slot:Slot)
  | Remove(key: Key, slot:Slot)
  | Query(key: Key, slot:Slot)
  | Idle

predicate WFThreadState(elementsLength:nat, t:ThreadState)
{
  match t
    case Insert(_, _, slot) => ValidSlot(elementsLength, slot)
    case Remove(_, slot) => ValidSlot(elementsLength, slot)
    case Query(_, slot) => ValidSlot(elementsLength, slot)
    case Idle => true
}

datatype Variables = Variables(table:seq<Item>, threads:seq<ThreadState>)
predicate ValidThreadId(s:Variables, tid:nat)
{
  tid < |s.threads|
}

predicate WFVariables(s:Variables)
{
  && 0 < |s.table|
  && (forall tid | ValidThreadId(s, tid) :: WFThreadState(|s.table|, s.threads[tid]))
}

predicate InsertInit(s:Variables, s':Variables, tid:nat, key:Key, value:Value) {
  && WFVariables(s)
  && ValidThreadId(s, tid)
  && s.threads[tid].Idle?
  && s' == s.(threads := s.threads[tid := Insert(key, value, SlotForKey(|s.table|, key))])
}

predicate InsertAdvance(s:Variables, s':Variables, tid:nat) {
  && WFVariables(s)
  && ValidThreadId(s, tid)
  && var t := s.threads[tid];
  && t.Insert?
  && !s.table[t.slot.slot].Empty?
  && s.table[t.slot.slot].key != t.key
  && t.slot.slot < |s.table|-1  // Can't roll around end of table
  && s' == s.(threads := s.threads[tid := t.(slot := Slot(t.slot.slot+1))])
}

predicate InsertComplete(s:Variables, s':Variables, tid:nat) {
  && WFVariables(s)
  && ValidThreadId(s, tid)
  && var t := s.threads[tid];
  && t.Insert?
  && (s.table[t.slot.slot].Empty? || s.table[t.slot.slot].key == t.key)
  && s' == s.(threads := s.threads[tid := Idle], table := s.table[t.slot.slot := Entry(t.key, t.value)])
}


predicate QueryInit(s:Variables, s':Variables, tid:nat, key:Key) {
  && WFVariables(s)
  && ValidThreadId(s, tid)
  && s.threads[tid].Idle?
  && s' == s.(threads := s.threads[tid := Query(key, SlotForKey(|s.table|, key))])
}

predicate QueryAdvance(s:Variables, s':Variables, tid:nat) {
  && WFVariables(s)
  && ValidThreadId(s, tid)
  && var t := s.threads[tid];
  && t.Query?
  && !s.table[t.slot.slot].Empty?
  && s.table[t.slot.slot].key != t.key
  && t.slot.slot < |s.table|-1  // Can't roll around end of table TODO
  && s' == s.(threads := s.threads[tid := t.(slot := Slot(t.slot.slot+1))])
}

// TODO Success-only result; need to return None
predicate QueryComplete(s:Variables, s':Variables, tid:nat, value:Value) {
  && WFVariables(s)
  && ValidThreadId(s, tid)
  && var t := s.threads[tid];
  && t.Query?
  && s.table[t.slot.slot] == Entry(t.key, value)
  && s' == s.(threads := s.threads[tid := Idle])
}

predicate Init(s:Variables) {
  && |s.table| >0
  && (forall si | 0<=si<|s.table| :: s.table[si].Empty?)
  && (forall tid | 0 <= tid < |s.threads| :: s.threads[tid].Idle?)
}

datatype Step =
  | InsertInitStep(key:Key, value:Value, tid:nat)
  | InsertAdvanceStep(tid:nat)
  | InsertCompleteStep(tid:nat)
  | QueryInitStep(key:Key, tid:nat)
  | QueryAdvanceStep(tid:nat)
  | QueryCompleteStep(tid:nat, value:Value)

predicate NextStep(s:Variables, s':Variables, step:Step) {
  match step
    case InsertInitStep(key, value, tid) => InsertInit(s, s', tid, key, value)
    case InsertAdvanceStep(tid) => InsertAdvance(s, s', tid)
    case InsertCompleteStep(tid) => InsertComplete(s, s', tid)
    case QueryInitStep(key, tid) => QueryInit(s, s', tid, key)
    case QueryAdvanceStep(tid) => QueryAdvance(s, s', tid)
    case QueryCompleteStep(tid, value) => QueryComplete(s, s', tid, value)
}

predicate Next(s:Variables, s':Variables) {
  exists step:Step :: NextStep(s, s', step)
}

function I(table:seq<Item>) : (m:map<Key,Value>)
  ensures forall slot | ValidSlot(|table|, slot) && table[slot.slot].Entry?  :: table[slot.slot].key in m
{
  if |table|==0
    then map[]
  else
    var last := Last(table);
    if last.Entry?
      then I(DropLast(table))[last.key := last.value]
      else I(DropLast(table))
}

predicate KeySlot(table:seq<Item>, slot:Slot)
{
  && ValidSlot(|table|, slot)
  && !table[slot.slot].Empty?
}

predicate UniqueKeys(table:seq<Item>)
{
  (forall i, j | && KeySlot(table, i) && KeySlot(table, j) && table[i.slot].key == table[j.slot].key
    :: i == j)
}

predicate ReachableForKey(table:seq<Item>, key:Key, end /* exclusive */ :Slot)
{
  && 0<|table|
  && ValidSlot(|table|, end)
  && var start := SlotForKey(|table|, key);
  && start.slot <= end.slot
  && (forall i:Slot | start.slot<=i.slot<end.slot :: !table[i.slot].Empty? && table[i.slot].key!=key)
}

predicate ReachableInv(table:seq<Item>)
{
  (forall i | KeySlot(table, i) :: ReachableForKey(table, table[i.slot].key, i))
}

predicate TableInv(table:seq<Item>)
{
  && UniqueKeys(table)
  && ReachableInv(table)
}

predicate ThreadInv(s:Variables, t:ThreadState)
{
  !t.Idle? ==> ReachableForKey(s.table, t.key, t.slot)
}

predicate Inv(s:Variables)
{
  && TableInv(s.table)
  && (forall tid | ValidThreadId(s, tid) :: ThreadInv(s, s.threads[tid]))
}

lemma InitInv(s:Variables)
requires Init(s)
ensures Inv(s)
{
}

lemma NextInv(s:Variables, s':Variables)
requires Next(s, s')
requires Inv(s)
ensures Inv(s')
{
}

function AValue() : Value

lemma InsertPossible()
{
  var t0 := [Empty];
  var s0 := Variables(t0, [Idle]);
  var v0 := AValue();
  assert Init(s0);

  // InsertInit

  var t1 := [Empty];
  var s1 := Variables(t1, [Insert(5, v0, Slot(0))]);
  assert NextStep(s0, s1, InsertInitStep(5, v0, 0));
  assert Next(s0, s1);

  // InsertComplete

  var t2 := [Entry(5, v0)];
  var s2 := Variables(t1, [Idle]);
  assert NextStep(s1, s2, InsertCompleteStep(0));
  assert Next(s1, s2);
}


}
