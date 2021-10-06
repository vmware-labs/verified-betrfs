include "../../framework/Cells.s.dfy"

module Handle {
  import opened Cells

  type ContentsType(!new)
  type Handle = CellContents<ContentsType>
}
