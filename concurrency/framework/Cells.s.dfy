module Cells {
  type {:predefined} Cell<V>
  datatype CellContents<V> = CellContents(ghost cell: Cell<V>, v: V)

  method {:extern} new_cell<V>(v: V)
  returns (linear cell: Cell<V>, glinear cellContents: CellContents<V>)
  ensures cellContents == CellContents(cell, v)

  method {:extern} read_cell<V>(shared cell: Cell<V>, gshared cellContents: CellContents<V>)
  returns (v: V)
  requires cell == cellContents.cell
  ensures v == cellContents.v

  method {:extern} write_cell<V>(shared cell: Cell<V>, glinear inout cellContents: CellContents<V>, v: V)
  requires cell == old_cellContents.cell
  ensures cellContents == old_cellContents.(v := v)
}
