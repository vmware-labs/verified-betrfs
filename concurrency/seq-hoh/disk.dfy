// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause






// trust me, please
method disk_write(addr: int, data: seq<byte>, linear ticket: StateObject)
returns (linear stub: StateObject)
requires ticket == DiskWriteTicket(addr, data)
ensures stub == DiskWriteStub(addr, data)

method disk_read(addr: int, len: int, linear ticket: StateObject)
returns (data: seq<byte>, linear stub: StateObject)
ensures stub == DiskReadStub(addr, data)
