abstract module CrashTypes {
  datatype CrashableUIOp<UIOp> = 
    | CrashOp
    | NormalOp(uiop: UIOp)
}
