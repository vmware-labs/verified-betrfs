include "MissingLibrary.dfy"

// A Map that can crash and revert to prior states, but only in
// controlled ways, limited by a sync operation.
abstract module CrashableMap {
import opened MissingLibrary
type Key(!new,==)
type Value(!new,==)
  
datatype Constants = Constants()
type View = imap<Key, Option<Value> >
datatype Variables = Variables(views:seq<View>)
// A bit of philosophy: Note that, even here in the abstract spec, we maintain
// a list of views that haven't yet been committed to disk. Why? Becuase in the
// future, we may commit some prefix of that view. If we've done 10 alternating
// increments to keys A and B, a filesystem crash could expose *any* of the
// outstanding values -- but no other values, and no views in which B is two
// steps ahead of A. (This is a stronger guarantee than many real filesystems
// give; we may well need to relax it later to allow the implementation more
// freedom.)

predicate ViewComplete(view:View)
{
    forall k :: k in view
}

predicate AllViewsComplete(views:seq<View>)
{
    forall i :: 0<=i<|views| ==> ViewComplete(views[i])
}

predicate WF(s:Variables)
{
    && 0 < |s.views|
    && AllViewsComplete(s.views)
}

// Dafny black magic: This name is here to give EmptyMap's forall something to
// trigger on. (Eliminates a /!\ Warning.)
predicate InDomain(k:Key)
{
    true
}

function EmptyMap() : (zmap : imap<Key,Option<Value> >)
    ensures ViewComplete(zmap)
{
    imap k | InDomain(k) :: None
}

predicate Init(k:Constants, s:Variables)
    ensures Init(k, s) ==> WF(s)
{
    s == Variables([EmptyMap()])
}

function EphemeralView(k:Constants, s:Variables) : View
    requires WF(s)
{
    s.views[0]
}

function PersistentView(k:Constants, s:Variables) : View
    requires WF(s)
{
    s.views[|s.views|-1]
}

predicate Query(k:Constants, s:Variables, s':Variables, key:Key, result:Option<Value>)
    requires WF(s)
{
    && result == EphemeralView(k, s)[key]
    && s' == s
}

predicate Write(k:Constants, s:Variables, s':Variables, key:Key, new_value:Option<Value>)
    requires WF(s)
    ensures Write(k, s, s', key, new_value) ==> WF(s')
{
    // Prepend a new ephemeral view, and preserve the committed persistent view.
    && WF(s')
    && EphemeralView(k, s') == EphemeralView(k, s)[key := new_value]
    && PersistentView(k, s') == PersistentView(k, s)

    // You're allowed to drop intermediate views, but if you keep them, they
    // need to maintain the order from earlier writes. (This is all or nothing:
    // keep them all if you're the log, keep nothing if you're the tree. One
    // could imagine allowing selective drop of intermediate views, but we
    // don't need it, so we didn't write it.)
    && (2 < |s'.views| ==> s'.views[1..] == s.views)
}

// Report to the user that the disk is synchronized with the memory.
predicate CompleteSync(k:Constants, s:Variables, s':Variables)
    requires WF(s)
{
    && |s.views| == 1
    && s' == s
}

// Some group of writes gets committed, eliminating stale views from before.
predicate PersistWrites(k:Constants, s:Variables, s':Variables, writesRetired:int)
    requires WF(s)
    ensures PersistWrites(k, s, s', writesRetired) ==> WF(s')
{
    && 0 < writesRetired < |s.views|    // leave a view when you're done!
    && s'.views == s.views[..|s.views|-writesRetired]
}

// Forget all non-persisted data.
predicate SpontaneousCrash(k:Constants, s:Variables, s':Variables)
    requires WF(s)
    ensures SpontaneousCrash(k, s, s') ==> WF(s')
{
    s'.views == [s.views[|s.views|-1]]
}

predicate Stutter(k:Constants, s:Variables, s':Variables)
    requires WF(s)
{
    s' == s
}

datatype Step =
    | QueryStep(key:Key, result:Option<Value>)
    | WriteStep(key:Key, new_value:Option<Value>)
    | CompleteSyncStep
    | PersistWritesStep(writesRetired:int)
    | SpontaneousCrashStep
    | StutterStep

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
    requires WF(s)
{
    && match step {
        case QueryStep(key, result) => Query(k, s, s', key, result)
        case WriteStep(key, new_value) => Write(k, s, s', key, new_value)
        case CompleteSyncStep() => CompleteSync(k, s, s')
        case PersistWritesStep(writesRetired) => PersistWrites(k, s, s', writesRetired)
        case SpontaneousCrashStep() => SpontaneousCrash(k, s, s')
        case StutterStep() => Stutter(k, s, s')
    }
}

predicate Next(k:Constants, s:Variables, s':Variables)
    requires WF(s)
    ensures Next(k, s, s') ==> WF(s')
{
    exists step :: NextStep(k, s, s', step)
}

}
