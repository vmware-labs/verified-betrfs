# Yahoo! Cloud System Benchmark
# Workload C: Read only
#   Application example: user profile cache, where profiles are constructed elsewhere (e.g., Hadoop)
#                        
#   Read/update ratio: 100/0

recordcount=1000000
operationcount=5000000
workload=com.yahoo.ycsb.workloads.CoreWorkload

readallfields=true
writeallfields=true

readproportion=0
updateproportion=1
scanproportion=0
insertproportion=0

fieldcount=1
fieldlength=512

requestdistribution=zipfian

syncintervalms=1000
