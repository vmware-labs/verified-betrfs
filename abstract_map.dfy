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
datatype Variables = Variables(ephemeral:imap<int, int>, persistent:imap<int, int>)

predicate completeMap<K(!new),V>(a:imap<K,V>)
{
    forall k :: k in a
}

predicate WF(s:Variables)
{
    && completeMap(s.ephemeral)
    && completeMap(s.persistent)
}

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
    ensures Init(k, s) ==> WF(s);
{
    s == Variables(EmptyMap(), EmptyMap())
}

predicate Query(k:Constants, s:Variables, s':Variables, datum:Datum)
    requires WF(s);
{
    && datum.value == s.ephemeral[datum.key]
    && s' == s
}

predicate Write(k:Constants, s:Variables, s':Variables, datum:Datum)
    requires WF(s);
{
    && s'.ephemeral == s.ephemeral[datum.key := datum.value]
    && s'.persistent == s.persistent
}

// Report to the user that the disk is synchronized with the memory.
predicate CompleteSync(k:Constants, s:Variables, s':Variables)
    requires WF(s);
{
    && s.persistent == s.ephemeral
    && s' == s
}

// Some group of keys get committed.
predicate PersistKeys(k:Constants, s:Variables, s':Variables, keys:set<int>)
    requires WF(s);
{
    && s'.ephemeral == s.ephemeral
    && WF(s')
    && forall k:int :: s'.persistent[k] == if k in keys then s.ephemeral[k] else s.persistent[k]
}

// Forget all non-persisted data.
predicate SpontaneousCrash(k:Constants, s:Variables, s':Variables)
    requires WF(s);
{
    && s'.ephemeral == s.persistent
    && s'.persistent == s.persistent
}

predicate Stutter(k:Constants, s:Variables, s':Variables)
    requires WF(s);
{
    && s'.ephemeral == s.ephemeral
    && s'.persistent == s.persistent
}

datatype Step = Query(datum:Datum) | Write(datum:Datum) | CompleteSync | PersistKeys(keys:set<int>) | SpontaneousCrash | Stutter

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
    requires WF(s);
{
    match step {
        case Query(datum) => Query(k, s, s', datum)
        case Write(datum) => Write(k, s, s', datum)
        case CompleteSync() => CompleteSync(k, s, s')
        case PersistKeys(keys) => PersistKeys(k, s, s', keys)
        case SpontaneousCrash() => SpontaneousCrash(k, s, s')
        case Stutter() => Stutter(k, s, s')
    }
}

predicate Next(k:Constants, s:Variables, s':Variables)
    requires WF(s);
    ensures Next(k, s, s') ==> WF(s');
{
    exists step :: NextStep(k, s, s', step)
}

}
