// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

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
