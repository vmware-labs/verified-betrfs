include "ImplFlush.i.dfy"
include "Bounds.i.dfy"

module ImplPolicy {
  import opened Bounds

  datatype Action =
    | ActionPageIn(ref: Reference)
    | ActionSplit(ref: Reference)
    | ActionFlush(ref: Reference, slot: uint64)
    | ActionEvict
    | ActionFail

  function biggestSlot(node: Node) : (slot : int)
  ensures 0 <= slot < |node.buckets|

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
        var slot := biggestSlot(node);
        var slotWeight := WeightBucket(node.buckets[slot]);
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
}
