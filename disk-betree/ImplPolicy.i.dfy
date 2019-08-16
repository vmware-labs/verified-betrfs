include "ImplFlush.i.dfy"
include "Bounds.i.dfy"

module ImplPolicy {
  import opened Bounds
  import opened NativeTypes

  datatype Action =
    | ActionPageIn(ref: Reference)
    | ActionSplit(ref: Reference)
    | ActionFlush(ref: Reference, slot: uint64)
    | ActionEvict
    | ActionFail

  function WeightBucket(bucket: Bucket) : int
  function WeightBucketList(bucket: BucketList) : int

  function biggestSlot(buckets: BucketList) : (res : (int, int))
  ensures 0 <= res.0 < |buckets|
  {
    if |buckets| == 0 then 0 else (
      var m := biggestSlot(DropLast(buckets));
      var w := m.1;
      var w' := WeightBucket(Last(buckets));
      if w' > w then (
        (|buckets| - 1, w')
      ) else (
        m
      )
    )
  }

  function getActionToPageIn(cache: map<Reference, Node>, ref: Reference)
  {
    if |cache| >= MaxCacheSize() then
      ActionEvict
    else
      ActionPageIn(ref)
  }

  function getActionToFlush(cache: map<Reference, Node>, ref: Reference, counter: int) : Action
  requires forall ref | ref in cache :: BT.WFNode(cache[ref])
  requires counter >= 0
  decreases counter
  {
    if counter == 0 then (
      ActionFail
    ) else if ref in cache then (
      var node := cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() then (
        ActionSplit(ref)
      ) else (
        var biggestSlot := biggestSlot(node.buckets);
        var slot := biggestSlot.0;
        var slotWeight := biggestSlot.1;
        if slotWeight >= FlushTriggerWeight() then (
          var childref := node.children[slot];
          if childref in cache then (
            var child := cache[childref];
            var childTotalWeight := WeightBucketList(child);
            if slotWeight + childTotalWeight <= MaxTotalBucketWeight() then (
              ActionFlush(ref, slot)
            ) else (
              getActionToFlush(cache, childref, counter - 1)
            )
          ) else (
            getActionToPageIn(cache, childref)
          )
        ) else (
          ActionSplit(ref)
        )
      )
    ) else (
      getActionToPageIn(cache, ref)
    )
  }

  method BiggestSlot(buckets: seq<KMTable>)
  returns (slot: uint64, weight: uint64)
  requires |buckets| <= MaxNumChildren()
  requires WeightBucketList(buckets) <= MaxTotalBucketWeight()
  ensures (slot as int, weight as int) == biggestSlot(KMTable.ISeq(buckets))
  {
    
  }
}
