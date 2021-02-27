// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

#include "BundleWrapper.h"
#include "Bundle.cpp"

using namespace MainHandlers_Compile;

Variables handle_InitState()
{
  auto heapState = __default::InitState();
  malloc_accounting_set_scope("BundleWrapper::handle_InitState");
  malloc_accounting_default_scope();
  Variables hs;
  hs.hs = heapState;
  return hs;
}

DafnyMap<uint64, DafnySequence<uint8>> handle_Mkfs()
{
  return __default::Mkfs();
}

void handle_EvictEverything(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleEvictEverything(hs.hs, io);
}

void handle_CountAmassAllocations(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleCountAmassAllocations(hs.hs, io);
}

uint64 handle_PushSync(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  return __default::handlePushSync(hs.hs, io);
}

std::pair<bool, bool> handle_PopSync(
  Variables hs,
  std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io,
  uint64 id,
  bool graphSync)
{
  auto p = __default::handlePopSync(hs.hs, io, id, graphSync);
  return std::make_pair(p.t0, p.t1);
}

bool handle_Insert(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, DafnySequence<uint8> key, DafnySequence<uint8> value)
{
  return __default::handleInsert(hs.hs, io, key, value);
}

std::optional<DafnySequence<uint8>> handle_Query(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, DafnySequence<uint8> key)
{
  auto p = __default::handleQuery(hs.hs, io, key);
  if (p.is_Option_Some()) {
    return std::optional<DafnySequence<uint8>>(p.dtor_value());
  } else {
    return std::nullopt;
  }
}

std::optional<UI_Compile::SuccResultList> handle_Succ(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, UI_Compile::RangeStart start, uint64 maxToFind)
{
  auto p = __default::handleSucc(hs.hs, io, start, maxToFind);
  if (p.is_Option_Some()) {
    return std::optional<UI_Compile::SuccResultList>(p.dtor_value());
  } else {
    return std::nullopt;
  }
}

void handle_ReadResponse(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleReadResponse(hs.hs, io);
}

void handle_WriteResponse(Variables hs, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleWriteResponse(hs.hs, io);
}

uint64 MaxKeyLen()
{
  return KeyType_Compile::__default::MaxLen();
}

uint64 MaxValueLen()
{
  return ValueType_Compile::__default::MaxLen();
}
