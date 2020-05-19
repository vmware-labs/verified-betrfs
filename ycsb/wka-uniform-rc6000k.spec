# Yahoo! Cloud System Benchmark
# Workload A: Update heavy workload
#   Application example: Session store recording recent actions
#                        
#   Read/update ratio: 50/50

recordcount=6000000
operationcount=20000000
workload=com.yahoo.ycsb.workloads.CoreWorkload

readallfields=true
writeallfields=true

readproportion=0.5
updateproportion=0.5
scanproportion=0
insertproportion=0

fieldcount=1
fieldlength=512

requestdistribution=uniform

#syncintervalms=1000
syncintervalops=10000
