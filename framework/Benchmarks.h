#pragma once

#include <string>

void RunAllBenchmarks(std::string filename);
void RunBenchmark(std::string filename, std::string const& name, bool skipPrepare);
