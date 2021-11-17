include "../../framework/Cells.s.dfy"

abstract module ContentsTypeMod {
  type ContentsType(!new)
}

module Handle(typeMod:ContentsTypeMod) {
  import opened LinearCells

  type Handle = LCellContents<typeMod.ContentsType>
}
