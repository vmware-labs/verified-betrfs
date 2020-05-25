# Yahoo! Cloud System Benchmark
# Workload A: Update heavy workload
#   Application example: Session store recording recent actions
#                        
#   Read/update ratio: 50/50

workloadname=A

recordcount=10000000
operationcount=10000
workload=com.yahoo.ycsb.workloads.CoreWorkload

readallfields=true
writeallfields=true

readproportion=0.5
updateproportion=0.5
scanproportion=0
insertproportion=0

fieldcount=1
fieldlength=512

requestdistribution=zipfian

#syncintervalms=1000
# Sync based on ops, so we don't create sync-collapse in slow phases.
#syncintervalops=10000
