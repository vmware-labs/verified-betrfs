/*
 * In this example I use `seq<T>` to refer to a mathematical
 * sequence type. It's assumed to have operations
 * length: s.len()
 * index: s[i]
 * update: s[i := blah]
 * concat: s ++ t
 * slice: s[i..j]
 */


// seq<T> is only allowed in proof code
// so this is a compile error:
fn compiled_seq<T>(s: seq<T>) -> seq<T> {
  s
}

// This is fine:
ghost fn ghost_seq<T>(s: seq<T>) -> seq<T> {
}

fn do_stuff_with_seqs<T>() -> {
  // Valid: Vec<T> type is the same as seq<T>
  // from the verifier's point-of-view
  let vec = Vec::new();
  ghost let s = ghost_seq(vec); 

  // Valid: an array is a seq
  let ar = [0; 3];
  ghost let s = ghost_seq(ar); 

  // slice is a seq
  let slice = &vec[1..2];
  ghost let s = ghost_seq(slice); 

  // this is valid, it's just comparing two seqs
  assert slice == ar;

  // iter is a sequence
  let iter = vec.filter_map(|x| x); 
  ghost let s = ghost_seq(iter); 

  // iter.collect() gives a Vec
  // (which is, again, just a sequence)
  // iterator's 'collect' is just the identity
  assert iter == iter.collect();
}

fn mutate_vec(v: Vec<u8>)
requires v.len() == 2
{
  // Make a 'ghost' copy
  ghost let v_original = v;

  v[0] = 5;

  assert v == original_v[0 := 5];

  v.push(19);

  assert v == original_v[0 := 5] ++ [19];
}

// Let's define our own list type

// By default, an enum would have an interpretation
// as an algebraic datatype.

enum ListImpl<T> {
  EmptyList,
  Cons(head: T, tail: Box<List<T>>),
}

// Let's define a List which uses a private
// ListImpl<T> field but exposes a seq<T>
// interface.

#[implements(seq<T>)]
struct List<T> {
  list: ListImpl,
}

impl List<T> {
  // List<T> was marked as implementing seq<T>, so it has to
  // support the following:

  ghost fn WF(&self) -> bool { true }

  ghost fn I(&self) -> seq<T>
  requires WF()
  {
    match self {
      List::EmptyList => []
      List::Cons(head, tail) => [head] ++ tail.I()
    }
  }

  // Contracts have to be written in terms of self.I()

  pub fn push_to_front(&mut self, new_head: T)
  ensures self.I() == [new_head] ++ old(self.I())
  {
    self.list = ListImpl::Cons(new_head, self.list);
  }

  // List implements .len() which is a feature of seq
  // so we require that it have the same behavior.

  // We add an additional 'requires' clause, though, which must
  // be met if a client wants to call 'len()' in non-ghost code.

  pub fn len(&self) -> (result: u64)
  requires self.I().len() < 0x10000000000000000
  ensures result == self.I().len()
  {
    match self.list {
      ListImpl::EmptyList => 0
      ListImpl::Cons(head, tail) => 1 + tail.len()
    }
  }
}

fn do_stuff_with_list<T>(l: List<T>) {
  // As with vecs, arrays, etc., l is a seq<T>
  ghost let s = ghost_seq(l);

  // Calling 'len' will demand the precondition, l.len() < 2^64
  let the_len = l.len();

  // In this line, 'l' is the mathematical seq<T> so no precondition is needed
  ghost let the_len_ghost = l.len();

  // This line fails, as List didn't define any slice functionality
  let the_slice = &l[0..1];

  // This is fine, 'l' is the mathematical seq<T> here
  ghost let the_slice_ghost = l[0..1];
}
