include "../../lib/Base/Option.s.dfy"

module {:extern "Cells"} Cells {
  type {:extern "struct"} Cell(!new,00)<V>
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

module {:extern "LinearCells"} LinearCells {
  import opened Options

  type {:extern "struct"} LinearCell(!new,00)<V>
  datatype CellContents<V> = CellContents(ghost lcell: LinearCell<V>, v: Option<V>)

  method {:extern} new_cell<V>()
  returns (linear lcell: LinearCell<V>, glinear cellContents: CellContents<V>)
  ensures cellContents == CellContents(lcell, None)

  method {:extern} read_lcell<V>(shared lcell: LinearCell<V>, gshared cellContents: CellContents<V>)
  returns (shared v: V)
  requires cellContents.lcell == lcell
  requires cellContents.v.Some?
  ensures cellContents.v.value == v

  method {:extern} take_lcell<V>(shared lcell: LinearCell<V>, glinear cellContents: CellContents<V>)
  returns (linear v: V, glinear cellContents': CellContents<V>)
  requires cellContents.lcell == lcell
  requires cellContents.v.Some?
  ensures cellContents.v.value == v
  ensures cellContents'.lcell == lcell
  ensures cellContents'.v == None

  method {:extern} give_lcell<V>(shared lcell: LinearCell<V>, glinear cellContents: CellContents<V>, linear v: V)
  returns (glinear cellContents': CellContents<V>)
  requires cellContents.lcell == lcell
  requires cellContents.v.None?
  ensures cellContents'.lcell == lcell
  ensures cellContents'.v == Some(v)
}
