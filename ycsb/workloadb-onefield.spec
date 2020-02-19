# Yahoo! Cloud System Benchmark
# Workload B: Read mostly workload
#   Application example: photo tagging; add a tag is an update, but most operations are to read tags
#                        
#   Read/update ratio: 95/5

recordcount=1000000
operationcount=5000000
workload=com.yahoo.ycsb.workloads.CoreWorkload

readallfields=true
writeallfields=true

readproportion=0.95
updateproportion=0.05
scanproportion=0
insertproportion=0

fieldcount=1
fieldlength=512

requestdistribution=zipfian

syncintervalms=1000
