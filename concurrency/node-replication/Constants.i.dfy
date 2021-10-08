include "../../lib/Lang/NativeTypes.s.dfy"

module Constants {
  import opened NativeTypes

  // TODO fill in reasonable constants for these

  const GC_FROM_HEAD: uint64 := 9999;
  const WARN_THRESHOLD: uint64 := 9999;
  const MAX_COMBINED_OPS: uint64 := 9999;

  // Fixed number of replicas (in reference impl, this is variable)
  const NUM_REPLICAS: uint64 := 4;
  const BUFFER_SIZE: uint64 := 9999;

  const MAX_THREADS_PER_REPLICA: uint64 := 32;
}
