module AppTypes {

datatype Datum = Datum(key:int, value:int)

function EmptyValue() : int
{
    0
}

}

module AbstractMap {
import opened AppTypes

datatype Constants = Constants()
type View = imap<int, int>
datatype Variables = Variables(views:seq<View>)
// A bit of philosophy: Note that, even here in the abstract spec, we maintain
// a list of views that haven't yet been committed to disk. Why? Becuase in the
// future, we may commit some prefix of that view. If we've done 10 alternating
// increments to keys A and B, a filesystem crash could expose *any* of the
// outstanding values -- but no other values, and no views in which B is two
// steps ahead of A. (This is a stronger guarantee than many real filesystems
// give; we may well need to relax it later to allow the implementation more
// freedom.)

predicate completeMap<K(!new),V>(a:imap<K,V>)
{
    forall k :: k in a
}

predicate WF(s:Variables)
{
    && 0 < |s.views|
    && forall i :: 0<=i<|s.views| ==> completeMap(s.views[i])
}

// Dafny black magic: This name is here to give EmptyMap's forall something to
// trigger on. (Eliminates a /!\ Warning.)
predicate InDomain(k:int)
{
    true
}

function EmptyMap() : (zmap : imap<int,int>)
    ensures completeMap(zmap)
{
    imap k | InDomain(k) :: EmptyValue()
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

predicate Query(k:Constants, s:Variables, s':Variables, datum:Datum)
    requires WF(s)
{
    && datum.value == EphemeralView(k, s)[datum.key]
    && s' == s
}

predicate Write(k:Constants, s:Variables, s':Variables, datum:Datum)
    requires WF(s)
{
    // Prepend a new ephemeral view. Prior view remains on the view
    // stack that's allowed to appear after a crash.
    var newView := EphemeralView(k, s)[datum.key := datum.value];
    s'.views == [newView] + s.views
}

// Report to the user that the disk is synchronized with the memory.
predicate CompleteSync(k:Constants, s:Variables, s':Variables)
    requires WF(s)
{
    && |s.views| == 1
    && s' == s
}

// Some group of writes gets committed, eliminating stale views from before.
predicate PersistWrites(k:Constants, s:Variables, s':Variables, count:int)
    requires WF(s)
    ensures PersistWrites(k, s, s', count) ==> WF(s')
{
    && 0 < count < |s.views|    // leave a view when you're done!
    && s'.views == s.views[..|s.views|-count]
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

datatype Step = Query(datum:Datum) | Write(datum:Datum) | CompleteSync | PersistWritesStep(count:int) | SpontaneousCrash | Stutter

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
    requires WF(s)
{
    match step {
        case Query(datum) => Query(k, s, s', datum)
        case Write(datum) => Write(k, s, s', datum)
        case CompleteSync() => CompleteSync(k, s, s')
        case PersistWritesStep(count) => PersistWrites(k, s, s', count)
        case SpontaneousCrash() => SpontaneousCrash(k, s, s')
        case Stutter() => Stutter(k, s, s')
    }
}

predicate Next(k:Constants, s:Variables, s':Variables)
    requires WF(s)
    ensures Next(k, s, s') ==> WF(s')
{
    exists step :: NextStep(k, s, s', step)
}

}
