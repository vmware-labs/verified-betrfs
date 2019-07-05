
module LogSpec {
  
  type Element

  datatype Constants = Constants()
  type Log = seq<Element>
  datatype Variables = Variables(log: Log)

  datatype Index = Index(idx: int)

  predicate Init(k:Constants, s:Variables)
  {
    s == Variables([])
  }

  predicate Query(k: Constants, s: Variables, s': Variables, idx: Index, result: Element)
  {
    && 0 <= idx.idx < |s.log|
    && result == s.log[idx.idx]
    && s' == s
  }

  predicate Append(k: Constants, s: Variables, s': Variables, element: Element)
  {
    && s'.log == s.log + [element]
  }

  predicate Stutter(k:Constants, s:Variables, s':Variables)
  {
    && s' == s
  }

  datatype Step =
      | QueryStep(idx: Index, result: Element)
      | AppendStep(element: Element)
      | StutterStep

  predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
  {
      match step {
          case QueryStep(idx, result) => Query(k, s, s', idx, result)
          case AppendStep(element) => Append(k, s, s', element)
          case StutterStep() => Stutter(k, s, s')
      }
  }

  predicate Next(k:Constants, s:Variables, s':Variables)
  {
      exists step :: NextStep(k, s, s', step)
  }

}
