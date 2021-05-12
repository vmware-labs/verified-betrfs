// Some lightweight definitions module suitable for use in
// trusted specification (.s) settings.

module SequencesLite {

  function Last<E>(run: seq<E>) : E
    requires |run| > 0;
  {
    run[|run|-1]
  }

  function DropLast<E>(run: seq<E>) : seq<E>
    requires |run| > 0;
  {
    run[..|run|-1]
  }

}
