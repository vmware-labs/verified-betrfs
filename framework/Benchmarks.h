// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

#pragma once

#include <string>

void RunAllBenchmarks(std::string filename);
void RunBenchmark(std::string filename, std::string const& name, bool skipPrepare);
