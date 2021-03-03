// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause


module LogSpec {
  type Element
  type Log = seq<Element>

  datatype Index = Index(idx: int)

  state machine k() s(log: Log) step()

  init
  {
    s == Variables([]) /* == Variables([]) */
  }

  step Query(idx: Index, result: Element)
  {
    && 0 <= idx.idx < |s.log|
    && result == s.log[idx.idx]
    && s' == s
  }

  step Append(element: Element)
  {
    && s'.log == s.log + [element]
  }

  step Stutter()
  {
    && s' == s
  }
}
