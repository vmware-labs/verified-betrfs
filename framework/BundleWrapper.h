// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

#pragma once
#include <memory>
#include <optional>
#include "Framework.h"

namespace MainHandlers_Compile {
  class HeapState;
}

struct Variables {
  std::shared_ptr<MainHandlers_Compile::HeapState> hs;
};

namespace UI_Compile {
  struct SuccResultList;
  struct RangeStart;
};

Variables handle_InitState();
DafnyMap<uint64, DafnySequence<uint8>> handle_Mkfs();
void handle_EvictEverything(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io);
void handle_CountAmassAllocations(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io);
uint64 handle_PushSync(Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);
std::pair<bool, bool> handle_PopSync(
  Variables,
  std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>,
  uint64,
  bool graphSync);

bool handle_Insert(Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, DafnySequence<uint8>, DafnySequence<uint8>);
std::optional<DafnySequence<uint8>> handle_Query(Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, DafnySequence<uint8>);
std::optional<UI_Compile::SuccResultList> handle_Succ(Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, UI_Compile::RangeStart start, uint64 maxToFind);
void handle_ReadResponse(Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);
void handle_WriteResponse(Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);

uint64 MaxKeyLen();
uint64 MaxValueLen();
