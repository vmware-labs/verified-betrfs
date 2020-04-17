#include "BundleWrapper.h"
#include "Bundle.cpp"

using namespace MainHandlers_Compile;

std::pair<Constants, Variables> handle_InitState()
{
  auto tup2 = __default::InitState();
  Constants k;
  malloc_accounting_set_scope("BundleWrapper::handle_InitState");
  k.k = std::shared_ptr<BlockJournalCache_Compile::Constants>(
      new BlockJournalCache_Compile::Constants(tup2.t0));
  malloc_accounting_default_scope();
  Variables hs;
  hs.hs = tup2.t1;
  return std::make_pair(k, hs);
}

DafnyMap<uint64, DafnySequence<uint8>> handle_Mkfs()
{
  return __default::Mkfs();
}

void handle_EvictEverything(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleEvictEverything(*k.k, hs.hs, io);
}

void handle_CountAmassAllocations(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleCountAmassAllocations(*k.k, hs.hs, io);
}

uint64 handle_PushSync(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  return __default::handlePushSync(*k.k, hs.hs, io);
}

std::pair<bool, bool> handle_PopSync(
  Constants k,
  Variables hs,
  std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io,
  uint64 id,
  bool graphSync)
{
  auto p = __default::handlePopSync(*k.k, hs.hs, io, id, graphSync);
  return std::make_pair(p.t0, p.t1);
}

bool handle_Insert(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, DafnySequence<uint8> key, DafnySequence<uint8> value)
{
  return __default::handleInsert(*k.k, hs.hs, io, key, value);
}

std::optional<DafnySequence<uint8>> handle_Query(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, DafnySequence<uint8> key)
{
  auto p = __default::handleQuery(*k.k, hs.hs, io, key);
  if (p.is_Option_Some()) {
    return std::optional<DafnySequence<uint8>>(p.dtor_value());
  } else {
    return std::nullopt;
  }
}

std::optional<UI_Compile::SuccResultList> handle_Succ(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, UI_Compile::RangeStart start, uint64 maxToFind)
{
  auto p = __default::handleSucc(*k.k, hs.hs, io, start, maxToFind);
  if (p.is_Option_Some()) {
    return std::optional<UI_Compile::SuccResultList>(p.dtor_value());
  } else {
    return std::nullopt;
  }
}

void handle_ReadResponse(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleReadResponse(*k.k, hs.hs, io);
}

void handle_WriteResponse(Constants k, Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleWriteResponse(*k.k, hs.hs, io);
}

uint64 MaxKeyLen()
{
  return KeyType_Compile::__default::MaxLen();
}

uint64 MaxValueLen()
{
  return ValueType_Compile::__default::MaxLen();
}
