// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module AsyncSectorDiskModelTypes {
  datatype AsyncSectorDiskModelVariables<M,D> = AsyncSectorDiskModelVariables(machine: M, disk: D)
}
