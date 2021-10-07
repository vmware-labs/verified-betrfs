include "../../framework/Cells.s.dfy"

module Handle {
  import opened LinearCells

  type ContentsType(!new)
  type Handle = LCellContents<ContentsType>
}
