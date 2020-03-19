include "../lib/Base/NativeTypes.s.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"

module {:extern} AllocationReport {
  import opened NativeTypes
  import BucketImpl
  method {:extern "AllocationReport_Compile", "start"} start()
  method {:extern "AllocationReport_Compile", "sampleBucket"} sampleBucket(ref: uint64, bucket: BucketImpl.MutBucket)
  method {:extern "AllocationReport_Compile", "stop"} stop()
}
