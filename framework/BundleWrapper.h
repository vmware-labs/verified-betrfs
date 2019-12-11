#pragma once
#include <memory>
#include "Framework.h"

namespace BetreeGraphBlockCache_Compile {
  struct Constants;
}
namespace Handlers_Compile {
  class HeapState;
}

class Constants {
  std::shared_ptr<BetreeGraphBlockCache_Compile::Constants> k;
};

class Variables {
  std::shared_ptr<Handlers_Compile::HeapState> hs;
};

std::pair<Constants, Variables> handle_InitState();
uint64 handle_PushSync(Constants, Variables, shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);
std::pair<bool, bool> handle_PopSync(Constants, Variables, shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, uint64);
bool handle_Insert(Constants, Variables, shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, DafnySequence<uint8>, DafnySequence<uint8>);
std::pair<bool, DafnySequence<uint8>> handle_Query(Constants, Variables, shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>, DafnySequence<uint8>);
void handle_ReadResponse(Constants, Variables, shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);
void handle_WriteResponse(Constants, Variables, shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler>);

uint64 MaxKeyLen();
uint64 MaxValueLen();
