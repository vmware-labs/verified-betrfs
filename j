diff --git a/Impl/JournalistImpl.i.dfy b/Impl/JournalistImpl.i.dfy
index 67f652ba..37c62d65 100644
--- a/Impl/JournalistImpl.i.dfy
+++ b/Impl/JournalistImpl.i.dfy
@@ -19,34 +19,12 @@ module JournalistImpl {
 
   import JournalistModel
 
-  class Journalist {
-    var journalEntries: array<JournalEntry>;
-    var start: uint64;
-    var len1: uint64;
-    var len2: uint64;
-
-    var replayJournal: seq<JournalEntry>;
-    var replayIdx: uint64;
-
-    var journalFront: Option<seq<JournalBlock>>;
-    var journalBack: Option<seq<JournalBlock>>;
-    
-    var writtenJournalBlocks: uint64;
-    var frozenJournalBlocks: uint64;
-    var inMemoryWeight: uint64;
-
-    ghost var Repr: set<object>;
-
-    protected predicate ReprInv()
-    reads this
-    ensures ReprInv() ==> this in Repr
-    {
-      Repr == {this, this.journalEntries}
-    }
-
-    protected function I() : JournalistModel.JournalistModel
-    reads this, this.Repr
-    requires ReprInv()
+  linear datatype Journalist = Journalist(journalEntries: seq<JournalEntry>, start: uint64,
+    len1: uint64, len2: uint64, replayJournal: seq<JournalEntry>, replayIdx: uint64, 
+    journalFront: Option<seq<JournalBlock>>, journalBack: Option<seq<JournalBlock>>, writtenJournalBlocks: uint64,
+    frozenJournalBlocks: uint64, inMemoryWeight: uint64)
+  {
+    function I() : JournalistModel.JournalistModel
     {
       JournalistModel.JournalistModel(
         this.journalEntries[..],
@@ -63,46 +41,38 @@ module JournalistImpl {
     }
 
     predicate WF()
-    reads this, this.Repr
     {
-      && ReprInv()
       && JournalistModel.WF(I())
     }
 
-    protected predicate Inv()
-    reads this, this.Repr
-    ensures Inv() ==> ReprInv()
+    predicate Inv()
     {
-      && ReprInv()
       && JournalistModel.Inv(I())
     }
 
-    constructor()
-    ensures Inv()
-    ensures fresh(Repr)
-    ensures I() == JournalistModel.JournalistConstructor()
+    static method NewJournal(): (linear j: Journalist)
+    ensures j.Inv()
+    ensures j.I() == JournalistModel.JournalistConstructor()
     {
-      new;
-      this.journalEntries := NativeArrays.newArrayFill(
-          4096,
-          JournalInsert([], []));
-      this.start := 0;
-      this.len1 := 0;
-      this.len2 := 0;
-      this.replayJournal := [];
-      this.replayIdx := 0;
-      this.journalFront := None;
-      this.journalBack := None;
-      this.writtenJournalBlocks := 0;
-      this.frozenJournalBlocks := 0;
-      this.inMemoryWeight := 0;
+      linear var j := Journalist;
+      j.journalEntries := JournalInsert([], []);
+      j.start := 0;
+      j.len1 := 0;
+      j.len2 := 0;
+      j.replayJournal := [];
+      j.replayIdx := 0;
+      j.journalFront := None;
+      j.journalBack := None;
+      j.writtenJournalBlocks := 0;
+      j.frozenJournalBlocks := 0;
+      j.inMemoryWeight := 0;
 
-      Repr := {this, this.journalEntries};
       JournalistModel.reveal_JournalistConstructor();
-      assert I() == JournalistModel.JournalistConstructor();
+      assert j.I() == JournalistModel.JournalistConstructor();
+      return j;
     }
 
-    method hasFrozenJournal() returns (b: bool)
+    shared method hasFrozenJournal() returns (b: bool)
     requires Inv()
     ensures b == JournalistModel.hasFrozenJournal(I())
     {
@@ -110,7 +80,7 @@ module JournalistImpl {
       return this.len1 != 0;
     }
 
-    method hasInMemoryJournal() returns (b: bool)
+    shared method hasInMemoryJournal() returns (b: bool)
     requires Inv()
     ensures b == JournalistModel.hasInMemoryJournal(I())
     {
@@ -177,17 +147,18 @@ module JournalistImpl {
       return this.writtenJournalBlocks;
     }
 
-    method setWrittenJournalLen(len: uint64)
+    linear inout method setWrittenJournalLen(len: uint64):
     requires Inv()
     requires JournalistModel.setWrittenJournalLen.requires(I(), len)
-    modifies Repr
-    ensures Repr == old(Repr)
     ensures Inv()
     ensures I() == JournalistModel.setWrittenJournalLen(old(I()), len)
     {
-      this.writtenJournalBlocks := len;
-      this.frozenJournalBlocks := 0;
-      assert I() == JournalistModel.setWrittenJournalLen(old(I()), len);
+      // this = self 
+      // old(this) = old_self
+
+      inout self.writtenJournalBlocks := len;
+      inout self.frozenJournalBlocks := 0;
+      assert I() == JournalistModel.setWrittenJournalLen(old_self.I(), len);
     }
 
     method updateWrittenJournalLen(len: uint64)
