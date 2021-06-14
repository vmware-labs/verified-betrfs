include "../Base/KeyType.s.dfy"
include "../Lang/NativeTypes.s.dfy"

// Trusted file for applying translation
// makes assumption that all strings under one prefix existing in the key value store
// can be safely translated into a string with a different prefix within the key length limit
// this is false now, but this assumption will be no longer needed once we remove key length restriction
// or skip squashing unwritable translations
module TranslationApply {
    import opened NativeTypes
    import opened KeyType

    function method changePrefix(oldPrefix: Key, newPrefix: Key, key: Key) : Key
    requires |oldPrefix| <= |key|
    requires key[..|oldPrefix|] == oldPrefix
    {
        assume |newPrefix + key[|oldPrefix|..]| <= KeyType.MaxLen() as int;
        newPrefix + key[|oldPrefix| as uint64 ..]
    }
}