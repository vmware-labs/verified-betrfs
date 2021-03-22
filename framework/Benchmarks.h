// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#pragma once

#include <string>

void RunAllBenchmarks(std::string filename);
void RunBenchmark(std::string filename, std::string const& name, bool skipPrepare);
