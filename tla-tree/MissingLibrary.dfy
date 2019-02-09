function Last<T>(s:seq<T>) : T  // TODO move to library
    requires 0<|s|
{
    s[|s|-1]
}

