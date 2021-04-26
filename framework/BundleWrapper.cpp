// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#include "BundleWrapper.h"
#include "Bundle.cpp"

using namespace MainHandlers_Compile;

Variables handle_InitState()
{
  auto full = std::make_shared<FullImpl_Compile::Full>(__default::InitState());
  Variables f;
  f.full = full;

  malloc_accounting_set_scope("BundleWrapper::handle_InitState");
  malloc_accounting_default_scope();
  return f;
}

DafnyMap<uint64, DafnySequence<uint8>> handle_Mkfs()
{
  return __default::Mkfs();
}

void handle_EvictEverything(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleEvictEverything(*f.full, io);
}

void handle_CountAmassAllocations(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleCountAmassAllocations(*f.full, io);
}

uint64 handle_PushSync(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  return __default::handlePushSync(*f.full, io);
}

std::pair<bool, bool> handle_PopSync(
  Variables f,
  std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io,
  uint64 id,
  bool graphSync)
{
  auto p = __default::handlePopSync(*f.full, io, id, graphSync);    
  return std::make_pair(p.get<0>(), p.get<1>());
}

bool handle_Insert(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, DafnySequence<uint8> key, DafnySequence<uint8> value)
{
  return __default::handleInsert(*f.full, io, key, value);
}

std::optional<DafnySequence<uint8>> handle_Query(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, DafnySequence<uint8> key)
{
  auto p = __default::handleQuery(*f.full, io, key);
  if (p.is_Option_Some()) {
    return std::optional<DafnySequence<uint8>>(p.dtor_value());
  } else {
    return std::nullopt;
  }
}

std::optional<UI_Compile::SuccResultList> handle_Succ(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io, UI_Compile::RangeStart start, uint64 maxToFind)
{
  auto p = __default::handleSucc(*f.full, io, start, maxToFind);
  if (p.is_Option_Some()) {
    return std::optional<UI_Compile::SuccResultList>(p.dtor_value());
  } else {
    return std::nullopt;
  }
}

void handle_ReadResponse(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleReadResponse(*f.full, io);
}

void handle_WriteResponse(Variables f, std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io)
{
  __default::handleWriteResponse(*f.full, io);
}

uint64 MaxKeyLen()
{
  return KeyType_Compile::__default::MaxLen();
}

uint64 MaxValueLen()
{
  return ValueType_Compile::__default::MaxLen();
}
