#pragma once
#include <memory>
#include <optional>
#include "Framework.h"

namespace BlockJournalCache_Compile {
  struct Constants;
}
namespace MainHandlers_Compile {
  class HeapState;
}

struct Constants {
  std::shared_ptr<BlockJournalCache_Compile::Constants> k;
};

struct Variables {
  std::shared_ptr<MainHandlers_Compile::HeapState> hs;
};

namespace UI_Compile {
  struct SuccResultList;
  struct RangeStart;
};

std::pair<Constants, Variables> handle_InitState();
DafnyMap<uint64, DafnySequence<uint8>> handle_Mkfs();
void handle_EvictEverything(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io);
void handle_CountAmassAllocations(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io);
uint64 handle_PushSync(Constants, Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);
std::pair<bool, bool> handle_PopSync(
  Constants,
  Variables,
  std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>,
  uint64,
  bool graphSync);

bool handle_Insert(Constants, Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, DafnySequence<uint8>, DafnySequence<uint8>);
std::optional<DafnySequence<uint8>> handle_Query(Constants, Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, DafnySequence<uint8>);
std::optional<UI_Compile::SuccResultList> handle_Succ(Constants, Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, UI_Compile::RangeStart start, uint64 maxToFind);
void handle_ReadResponse(Constants, Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);
void handle_WriteResponse(Constants, Variables, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);

uint64 MaxKeyLen();
uint64 MaxValueLen();
