// Dafny program Application.i.dfy compiled into a Cpp header file
#pragma once
#include "DafnyRuntime.h"
namespace _System  {
}// end of namespace _System  declarations
namespace NativeTypes_Compile  {
  class class_sbyte;
  class class_byte;
  class class_int16;
  class class_uint16;
  class class_int32;
  class class_uint32;
  class class_int64;
  class class_uint64;
  class class_nat8;
  class class_nat16;
  class class_nat32;
  class class_nat64;
  class class_uint128;
  class __default;
}// end of namespace NativeTypes_Compile  declarations
namespace Options_Compile  {
  template <typename V>
struct Option;
}// end of namespace Options_Compile  declarations
namespace GlinearOption_Compile  {
  template <typename V>
struct glOption;
  class __default;
}// end of namespace GlinearOption_Compile  declarations
namespace Ptrs  {
  template <typename V>
struct PointsTo;
  template <typename V>
struct PointsToLinear;
  template <typename V>
struct PointsToArray;
  // Extern declaration of Ptr
 struct Ptr;
}// end of namespace Ptrs  declarations
namespace PageSizeConstant_Compile  {
  class __default;
}// end of namespace PageSizeConstant_Compile  declarations
namespace IocbStruct  {
  
struct Iocb;
  // Extern declaration of Iovec
 struct Iovec;
}// end of namespace IocbStruct  declarations
namespace NonlinearLemmas_Compile  {
}// end of namespace NonlinearLemmas_Compile  declarations
namespace Math_Compile  {
}// end of namespace Math_Compile  declarations
namespace Constants_Compile  {
  
struct PreConfig;
  
struct Config;
  class __default;
}// end of namespace Constants_Compile  declarations
namespace MapSum_Compile  {
}// end of namespace MapSum_Compile  declarations
namespace FullMaps_Compile  {
  template <typename K>
struct pre__FullMap;
  template <typename K> using FullMap = FullMaps_Compile::pre__FullMap <K> ;
  template <typename K>
  class class_FullMap;
}// end of namespace FullMaps_Compile  declarations
namespace GhostLoc_Compile  {
  
struct Loc;
}// end of namespace GhostLoc_Compile  declarations
namespace Cells  {
  // Extern declaration of Cell
template <typename V> struct Cell;
  template <typename V>
struct CellContents;
}// end of namespace Cells  declarations
namespace RequestIds_Compile  {
}// end of namespace RequestIds_Compile  declarations
namespace CacheStatusType_Compile  {
  
struct Status;
}// end of namespace CacheStatusType_Compile  declarations
namespace DiskIfc_Compile  {
   using Block = DafnySequence<uint8>;
  class class_Block;
  
struct ReqRead;
  
struct ReqWrite;
  
struct RespRead;
  
struct RespWrite;
  
struct DiskOp;
}// end of namespace DiskIfc_Compile  declarations
namespace CacheIfc_Compile  {
  
struct Input;
  
struct Output;
  
struct Op;
}// end of namespace CacheIfc_Compile  declarations
namespace CacheSSM_Compile  {
  
struct Entry;
  
struct M;
  
struct Step;
}// end of namespace CacheSSM_Compile  declarations
namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile  {
  
struct Token;
}// end of namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile  declarations
namespace DiskSingletonLoc_Compile  {
}// end of namespace DiskSingletonLoc_Compile  declarations
namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile  {
}// end of namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile  declarations
namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile  {
  
struct Token;
}// end of namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile  declarations
namespace DiskToken_ON_CacheIfc_CacheSSM__Compile  {
  
struct Token;
}// end of namespace DiskToken_ON_CacheIfc_CacheSSM__Compile  declarations
namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile  {
  class __default;
}// end of namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile  declarations
namespace CacheResources_Compile  {
  
struct DiskPageMap;
  
struct HavocPermission;
  
struct CacheStatus;
  
struct CacheEmpty;
  
struct CacheReading;
  
struct CacheEntry;
  
struct DiskWriteTicket;
  
struct DiskWriteStub;
  
struct DiskReadTicket;
  
struct DiskReadStub;
  class __default;
}// end of namespace CacheResources_Compile  declarations
namespace CacheHandle_Compile  {
  
struct PageHandle;
  
struct Key;
  
struct Handle;
}// end of namespace CacheHandle_Compile  declarations
namespace RwLock_Compile  {
  
struct Flag;
  
struct SharedState;
  
struct ExcState;
  
struct WritebackState;
  
struct ReadState;
  
struct CentralState;
  
struct M;
}// end of namespace RwLock_Compile  declarations
namespace Rw_PCMWrap_ON_RwLock__Compile  {
  
struct M;
}// end of namespace Rw_PCMWrap_ON_RwLock__Compile  declarations
namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {
  
struct Token;
}// end of namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile  declarations
namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {
   using GToken = Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile::Token;
  class class_GToken;
}// end of namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile  declarations
namespace Rw_PCMExt_ON_RwLock__Compile  {
}// end of namespace Rw_PCMExt_ON_RwLock__Compile  declarations
namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile  {
  
struct Token;
}// end of namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile  declarations
namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile  {
}// end of namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile  declarations
namespace RwTokens_ON_RwLock__Compile  {
   using Token = Tokens_ON_Rw__PCMExt__ON__RwLock____Compile::Token;
  class class_Token;
  class __default;
}// end of namespace RwTokens_ON_RwLock__Compile  declarations
namespace RwLockToken_Compile  {
  
struct CentralToken;
  
struct WritebackObtainedToken;
  
struct SharedPendingToken;
  
struct SharedPending2Token;
  
struct SharedObtainedToken;
  class __default;
}// end of namespace RwLockToken_Compile  declarations
namespace GlinearMap_Compile  {
}// end of namespace GlinearMap_Compile  declarations
namespace CacheAIOParams_Compile  {
  
struct IOSlotAccess;
  
struct ReadG;
  
struct ReadvG;
  
struct WriteG;
  
struct WritevG;
  class __default;
}// end of namespace CacheAIOParams_Compile  declarations
namespace BitOps_Compile  {
  class __default;
}// end of namespace BitOps_Compile  declarations
namespace Atomics  {
}// end of namespace Atomics  declarations
namespace CounterPCM_Compile  {
  
struct M;
}// end of namespace CounterPCM_Compile  declarations
namespace Tokens_ON_CounterPCM__Compile  {
  
struct Token;
}// end of namespace Tokens_ON_CounterPCM__Compile  declarations
namespace ClientCounter_Compile  {
  
struct Client;
  
struct Clients;
  class __default;
}// end of namespace ClientCounter_Compile  declarations
namespace AtomicRefcountImpl_Compile  {
  
struct RG;
  
struct AtomicRefcount;
  class __default;
}// end of namespace AtomicRefcountImpl_Compile  declarations
namespace AtomicIndexLookupImpl_Compile  {
  class __default;
}// end of namespace AtomicIndexLookupImpl_Compile  declarations
namespace AtomicStatusImpl_Compile  {
  
struct G;
  
struct AtomicStatus;
  class __default;
}// end of namespace AtomicStatusImpl_Compile  declarations
namespace BasicLockImpl_Compile  {
  template <typename G>
struct pre__BasicLock;
  template <typename G> using BasicLock = BasicLockImpl_Compile::pre__BasicLock <G> ;
  template <typename G>
  class class_BasicLock;
  class __default;
}// end of namespace BasicLockImpl_Compile  declarations
namespace LinearMaybe  {
}// end of namespace LinearMaybe  declarations
namespace LinearExtern  {
}// end of namespace LinearExtern  declarations
namespace LinearSequence__i_Compile  {
  class __default;
}// end of namespace LinearSequence__i_Compile  declarations
namespace ThreadUtils  {
}// end of namespace ThreadUtils  declarations
namespace MemSplit_Compile  {
  class __default;
}// end of namespace MemSplit_Compile  declarations
namespace InstantiatedDiskInterface  {
  // Extern declaration of IOCtx
 struct IOCtx;
  
struct FinishedReq;
}// end of namespace InstantiatedDiskInterface  declarations
namespace CacheTypes_ON_TheAIO__Compile  {
  
struct NullGhostType;
  
struct StatusIdx;
  
struct Cache;
  
struct LocalState;
  
struct IOSlot;
}// end of namespace CacheTypes_ON_TheAIO__Compile  declarations
namespace CacheIO_ON_TheAIO__Compile  {
  class __default;
}// end of namespace CacheIO_ON_TheAIO__Compile  declarations
namespace CacheWritebackBatch_ON_TheAIO__Compile  {
  class __default;
}// end of namespace CacheWritebackBatch_ON_TheAIO__Compile  declarations
namespace CacheOps_ON_TheAIO__Compile  {
  
struct PageHandleIdx;
  
struct WriteablePageHandle;
  
struct ReadonlyPageHandle;
  
struct ClaimPageHandle;
  class __default;
}// end of namespace CacheOps_ON_TheAIO__Compile  declarations
namespace CacheInit_ON_TheAIO__Compile  {
  class __default;
}// end of namespace CacheInit_ON_TheAIO__Compile  declarations
namespace Application_ON_TheAIO__Compile  {
  class __default;
}// end of namespace Application_ON_TheAIO__Compile  declarations
namespace AsyncDisk_Compile  {
  
struct Variables;
  
struct Step;
  
struct InternalStep;
}// end of namespace AsyncDisk_Compile  declarations
namespace LinearCells  {
  // Extern declaration of LinearCell
template <typename V> struct LinearCell;
  template <typename V>
struct LCellContents;
}// end of namespace LinearCells  declarations
namespace _module  {
}// end of namespace _module  declarations
namespace _System  {
}// end of namespace _System  datatype declarations
namespace NativeTypes_Compile  {
}// end of namespace NativeTypes_Compile  datatype declarations
namespace Options_Compile  {
  template <typename V>
bool operator==(const Option<V> &left, const Option<V> &right); 
  template <typename V>
struct Option_None;
  template <typename V>
bool operator==(const Option_None<V> &left, const Option_None<V> &right); 
  template <typename V>
struct Option_None {
    friend bool operator==<V>(const Option_None &left, const Option_None &right); 
    friend bool operator!=(const Option_None &left, const Option_None &right) { return !(left == right); } 
  };
  template <typename V>
struct Option_Some;
  template <typename V>
bool operator==(const Option_Some<V> &left, const Option_Some<V> &right); 
  template <typename V>
struct Option_Some {
    V value;
    friend bool operator==<V>(const Option_Some &left, const Option_Some &right); 
    friend bool operator!=(const Option_Some &left, const Option_Some &right) { return !(left == right); } 
  };
  template <typename V>
struct Option {
    std::variant<Option_None<V>, Option_Some<V>> v;
    static Option create_None() {
      Option<V> COMPILER_result;
      Option_None<V> COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Option create_Some(V value) {
      Option<V> COMPILER_result;
      Option_Some<V> COMPILER_result_subStruct;
      COMPILER_result_subStruct.value = value;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Option();
    ~Option() {}
    Option(const Option &other) {
      v = other.v;
    }
    Option& operator=(const Option other) {
      v = other.v;
      return *this;
    }
    bool is_Option_None() const { return std::holds_alternative<Option_None<V>>(v); }
    bool is_Option_Some() const { return std::holds_alternative<Option_Some<V>>(v); }
    Option* operator->() { return this; }
    friend bool operator==(const Option &left, const Option &right) { 
    	return left.v == right.v;
}
    V& dtor_value() {
      return std::get<Option_Some<V>>(v).value; 
    }
    friend bool operator!=(const Option &left, const Option &right) { return !(left == right); } 
  };
  template <typename V>
inline bool is_Option_None(const struct Option<V> d);
  template <typename V>
inline bool is_Option_Some(const struct Option<V> d);
}// end of namespace Options_Compile  datatype declarations
namespace GlinearOption_Compile  {
  template <typename V>
bool operator==(const glOption<V> &left, const glOption<V> &right); 
  template <typename V>
struct glOption_glNone;
  template <typename V>
bool operator==(const glOption_glNone<V> &left, const glOption_glNone<V> &right); 
  template <typename V>
struct glOption_glNone {
    friend bool operator==<V>(const glOption_glNone &left, const glOption_glNone &right); 
    friend bool operator!=(const glOption_glNone &left, const glOption_glNone &right) { return !(left == right); } 
  };
  template <typename V>
struct glOption_glSome;
  template <typename V>
bool operator==(const glOption_glSome<V> &left, const glOption_glSome<V> &right); 
  template <typename V>
struct glOption_glSome {
    friend bool operator==<V>(const glOption_glSome &left, const glOption_glSome &right); 
    friend bool operator!=(const glOption_glSome &left, const glOption_glSome &right) { return !(left == right); } 
  };
  template <typename V>
struct glOption {
    std::variant<glOption_glNone<V>, glOption_glSome<V>> v;
    static glOption create_glNone() {
      glOption<V> COMPILER_result;
      glOption_glNone<V> COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static glOption create_glSome() {
      glOption<V> COMPILER_result;
      glOption_glSome<V> COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    glOption();
    ~glOption() {}
    glOption(const glOption &other) {
      v = other.v;
    }
    glOption& operator=(const glOption other) {
      v = other.v;
      return *this;
    }
    bool is_glOption_glNone() const { return std::holds_alternative<glOption_glNone<V>>(v); }
    bool is_glOption_glSome() const { return std::holds_alternative<glOption_glSome<V>>(v); }
    glOption* operator->() { return this; }
    friend bool operator==(const glOption &left, const glOption &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const glOption &left, const glOption &right) { return !(left == right); } 
  };
  template <typename V>
inline bool is_glOption_glNone(const struct glOption<V> d);
  template <typename V>
inline bool is_glOption_glSome(const struct glOption<V> d);
}// end of namespace GlinearOption_Compile  datatype declarations
namespace Ptrs  {
  template <typename V>
bool operator==(const PointsTo<V> &left, const PointsTo<V> &right); 
  template <typename V>
struct PointsTo {
    PointsTo();
    PointsTo* operator->() { return this; }
    friend bool operator==<V>(const PointsTo &left, const PointsTo &right);
    friend bool operator!=(const PointsTo &left, const PointsTo &right) { return !(left == right); } 
  };
  template <typename V>
inline bool is_PointsTo(const struct PointsTo<V> d) { (void) d; return true; }
  template <typename V>
bool operator==(const PointsToLinear<V> &left, const PointsToLinear<V> &right); 
  template <typename V>
struct PointsToLinear_PointsToLinear;
  template <typename V>
bool operator==(const PointsToLinear_PointsToLinear<V> &left, const PointsToLinear_PointsToLinear<V> &right); 
  template <typename V>
struct PointsToLinear_PointsToLinear {
    friend bool operator==<V>(const PointsToLinear_PointsToLinear &left, const PointsToLinear_PointsToLinear &right); 
    friend bool operator!=(const PointsToLinear_PointsToLinear &left, const PointsToLinear_PointsToLinear &right) { return !(left == right); } 
  };
  template <typename V>
struct PointsToLinear_PointsToEmpty;
  template <typename V>
bool operator==(const PointsToLinear_PointsToEmpty<V> &left, const PointsToLinear_PointsToEmpty<V> &right); 
  template <typename V>
struct PointsToLinear_PointsToEmpty {
    friend bool operator==<V>(const PointsToLinear_PointsToEmpty &left, const PointsToLinear_PointsToEmpty &right); 
    friend bool operator!=(const PointsToLinear_PointsToEmpty &left, const PointsToLinear_PointsToEmpty &right) { return !(left == right); } 
  };
  template <typename V>
struct PointsToLinear {
    std::variant<PointsToLinear_PointsToLinear<V>, PointsToLinear_PointsToEmpty<V>> v;
    static PointsToLinear create_PointsToLinear() {
      PointsToLinear<V> COMPILER_result;
      PointsToLinear_PointsToLinear<V> COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static PointsToLinear create_PointsToEmpty() {
      PointsToLinear<V> COMPILER_result;
      PointsToLinear_PointsToEmpty<V> COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    PointsToLinear();
    ~PointsToLinear() {}
    PointsToLinear(const PointsToLinear &other) {
      v = other.v;
    }
    PointsToLinear& operator=(const PointsToLinear other) {
      v = other.v;
      return *this;
    }
    bool is_PointsToLinear_PointsToLinear() const { return std::holds_alternative<PointsToLinear_PointsToLinear<V>>(v); }
    bool is_PointsToLinear_PointsToEmpty() const { return std::holds_alternative<PointsToLinear_PointsToEmpty<V>>(v); }
    PointsToLinear* operator->() { return this; }
    friend bool operator==(const PointsToLinear &left, const PointsToLinear &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const PointsToLinear &left, const PointsToLinear &right) { return !(left == right); } 
  };
  template <typename V>
inline bool is_PointsToLinear_PointsToLinear(const struct PointsToLinear<V> d);
  template <typename V>
inline bool is_PointsToLinear_PointsToEmpty(const struct PointsToLinear<V> d);
  template <typename V>
bool operator==(const PointsToArray<V> &left, const PointsToArray<V> &right); 
  template <typename V>
struct PointsToArray {
    PointsToArray();
    PointsToArray* operator->() { return this; }
    friend bool operator==<V>(const PointsToArray &left, const PointsToArray &right);
    friend bool operator!=(const PointsToArray &left, const PointsToArray &right) { return !(left == right); } 
  };
  template <typename V>
inline bool is_PointsToArray(const struct PointsToArray<V> d) { (void) d; return true; }
}// end of namespace Ptrs  datatype declarations
namespace PageSizeConstant_Compile  {
}// end of namespace PageSizeConstant_Compile  datatype declarations
namespace IocbStruct  {
  
bool operator==(const Iocb &left, const Iocb &right); 
  
struct Iocb_IocbUninitialized;
  
bool operator==(const Iocb_IocbUninitialized &left, const Iocb_IocbUninitialized &right); 
  
struct Iocb_IocbUninitialized {
    friend bool operator==(const Iocb_IocbUninitialized &left, const Iocb_IocbUninitialized &right); 
    friend bool operator!=(const Iocb_IocbUninitialized &left, const Iocb_IocbUninitialized &right) { return !(left == right); } 
  };
  
struct Iocb_IocbRead;
  
bool operator==(const Iocb_IocbRead &left, const Iocb_IocbRead &right); 
  
struct Iocb_IocbRead {
    friend bool operator==(const Iocb_IocbRead &left, const Iocb_IocbRead &right); 
    friend bool operator!=(const Iocb_IocbRead &left, const Iocb_IocbRead &right) { return !(left == right); } 
  };
  
struct Iocb_IocbWrite;
  
bool operator==(const Iocb_IocbWrite &left, const Iocb_IocbWrite &right); 
  
struct Iocb_IocbWrite {
    friend bool operator==(const Iocb_IocbWrite &left, const Iocb_IocbWrite &right); 
    friend bool operator!=(const Iocb_IocbWrite &left, const Iocb_IocbWrite &right) { return !(left == right); } 
  };
  
struct Iocb_IocbReadv;
  
bool operator==(const Iocb_IocbReadv &left, const Iocb_IocbReadv &right); 
  
struct Iocb_IocbReadv {
    friend bool operator==(const Iocb_IocbReadv &left, const Iocb_IocbReadv &right); 
    friend bool operator!=(const Iocb_IocbReadv &left, const Iocb_IocbReadv &right) { return !(left == right); } 
  };
  
struct Iocb_IocbWritev;
  
bool operator==(const Iocb_IocbWritev &left, const Iocb_IocbWritev &right); 
  
struct Iocb_IocbWritev {
    friend bool operator==(const Iocb_IocbWritev &left, const Iocb_IocbWritev &right); 
    friend bool operator!=(const Iocb_IocbWritev &left, const Iocb_IocbWritev &right) { return !(left == right); } 
  };
  
struct Iocb {
    std::variant<Iocb_IocbUninitialized, Iocb_IocbRead, Iocb_IocbWrite, Iocb_IocbReadv, Iocb_IocbWritev> v;
    static Iocb create_IocbUninitialized() {
      Iocb COMPILER_result;
      Iocb_IocbUninitialized COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Iocb create_IocbRead() {
      Iocb COMPILER_result;
      Iocb_IocbRead COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Iocb create_IocbWrite() {
      Iocb COMPILER_result;
      Iocb_IocbWrite COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Iocb create_IocbReadv() {
      Iocb COMPILER_result;
      Iocb_IocbReadv COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Iocb create_IocbWritev() {
      Iocb COMPILER_result;
      Iocb_IocbWritev COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Iocb();
    ~Iocb() {}
    Iocb(const Iocb &other) {
      v = other.v;
    }
    Iocb& operator=(const Iocb other) {
      v = other.v;
      return *this;
    }
    bool is_Iocb_IocbUninitialized() const { return std::holds_alternative<Iocb_IocbUninitialized>(v); }
    bool is_Iocb_IocbRead() const { return std::holds_alternative<Iocb_IocbRead>(v); }
    bool is_Iocb_IocbWrite() const { return std::holds_alternative<Iocb_IocbWrite>(v); }
    bool is_Iocb_IocbReadv() const { return std::holds_alternative<Iocb_IocbReadv>(v); }
    bool is_Iocb_IocbWritev() const { return std::holds_alternative<Iocb_IocbWritev>(v); }
    Iocb* operator->() { return this; }
    friend bool operator==(const Iocb &left, const Iocb &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Iocb &left, const Iocb &right) { return !(left == right); } 
  };
  
inline bool is_Iocb_IocbUninitialized(const struct Iocb d);
  
inline bool is_Iocb_IocbRead(const struct Iocb d);
  
inline bool is_Iocb_IocbWrite(const struct Iocb d);
  
inline bool is_Iocb_IocbReadv(const struct Iocb d);
  
inline bool is_Iocb_IocbWritev(const struct Iocb d);
}// end of namespace IocbStruct  datatype declarations
namespace NonlinearLemmas_Compile  {
}// end of namespace NonlinearLemmas_Compile  datatype declarations
namespace Math_Compile  {
}// end of namespace Math_Compile  datatype declarations
namespace Constants_Compile  {
  
bool operator==(const PreConfig &left, const PreConfig &right); 
  
struct PreConfig {
    uint32 cache__size;
    uint64 num__disk__pages;
    uint64 pages__per__extent;
    uint64 num__io__slots;
    PreConfig(uint32 cache__size, uint64 num__disk__pages, uint64 pages__per__extent, uint64 num__io__slots) : cache__size (cache__size),  num__disk__pages (num__disk__pages),  pages__per__extent (pages__per__extent),  num__io__slots (num__io__slots) {}
    PreConfig();
    PreConfig* operator->() { return this; }
    friend bool operator==(const PreConfig &left, const PreConfig &right);
    friend bool operator!=(const PreConfig &left, const PreConfig &right) { return !(left == right); } 
    bool WF();  };
  
inline bool is_PreConfig(const struct PreConfig d) { (void) d; return true; }
  
bool operator==(const Config &left, const Config &right); 
  
struct Config {
    uint32 cache__size;
    uint64 num__disk__pages;
    uint64 pages__per__extent;
    uint64 num__io__slots;
    uint64 batch__capacity;
    uint64 cacheline__capacity;
    Config(uint32 cache__size, uint64 num__disk__pages, uint64 pages__per__extent, uint64 num__io__slots, uint64 batch__capacity, uint64 cacheline__capacity) : cache__size (cache__size),  num__disk__pages (num__disk__pages),  pages__per__extent (pages__per__extent),  num__io__slots (num__io__slots),  batch__capacity (batch__capacity),  cacheline__capacity (cacheline__capacity) {}
    Config();
    Config* operator->() { return this; }
    friend bool operator==(const Config &left, const Config &right);
    friend bool operator!=(const Config &left, const Config &right) { return !(left == right); } 
  };
  
inline bool is_Config(const struct Config d) { (void) d; return true; }
}// end of namespace Constants_Compile  datatype declarations
namespace MapSum_Compile  {
}// end of namespace MapSum_Compile  datatype declarations
namespace FullMaps_Compile  {
  template <typename K>
bool operator==(const pre__FullMap<K> &left, const pre__FullMap<K> &right); 
  template <typename K>
struct pre__FullMap {
    pre__FullMap();
    pre__FullMap* operator->() { return this; }
    friend bool operator==<K>(const pre__FullMap &left, const pre__FullMap &right);
    friend bool operator!=(const pre__FullMap &left, const pre__FullMap &right) { return !(left == right); } 
  };
  template <typename K>
inline bool is_FullMap(const struct pre__FullMap<K> d) { (void) d; return true; }
}// end of namespace FullMaps_Compile  datatype declarations
namespace GhostLoc_Compile  {
  
struct Loc;
  
bool operator==(const Loc &left, const Loc &right); 
  
struct Loc_BaseLoc;
  
bool operator==(const Loc_BaseLoc &left, const Loc_BaseLoc &right); 
  
struct Loc_BaseLoc {
    friend bool operator==(const Loc_BaseLoc &left, const Loc_BaseLoc &right); 
    friend bool operator!=(const Loc_BaseLoc &left, const Loc_BaseLoc &right) { return !(left == right); } 
  };
  
struct Loc_ExtLoc;
  
bool operator==(const Loc_ExtLoc &left, const Loc_ExtLoc &right); 
  
struct Loc_ExtLoc {
    friend bool operator==(const Loc_ExtLoc &left, const Loc_ExtLoc &right); 
    friend bool operator!=(const Loc_ExtLoc &left, const Loc_ExtLoc &right) { return !(left == right); } 
  };
  
struct Loc {
    std::variant<Loc_BaseLoc, Loc_ExtLoc> v;
    static Loc create_BaseLoc() {
      Loc COMPILER_result;
      Loc_BaseLoc COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Loc create_ExtLoc() {
      Loc COMPILER_result;
      Loc_ExtLoc COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Loc();
    ~Loc() {}
    Loc(const Loc &other) {
      v = other.v;
    }
    Loc& operator=(const Loc other) {
      v = other.v;
      return *this;
    }
    bool is_Loc_BaseLoc() const { return std::holds_alternative<Loc_BaseLoc>(v); }
    bool is_Loc_ExtLoc() const { return std::holds_alternative<Loc_ExtLoc>(v); }
    Loc* operator->() { return this; }
    friend bool operator==(const Loc &left, const Loc &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Loc &left, const Loc &right) { return !(left == right); } 
  };
  
inline bool is_Loc_BaseLoc(const struct Loc d);
  
inline bool is_Loc_ExtLoc(const struct Loc d);
}// end of namespace GhostLoc_Compile  datatype declarations
namespace Cells  {
  template <typename V>
bool operator==(const CellContents<V> &left, const CellContents<V> &right); 
  template <typename V>
struct CellContents {
    V v;
    CellContents(V v) : v (v) {}
    CellContents();
    CellContents* operator->() { return this; }
    friend bool operator==<V>(const CellContents &left, const CellContents &right);
    friend bool operator!=(const CellContents &left, const CellContents &right) { return !(left == right); } 
  };
  template <typename V>
inline bool is_CellContents(const struct CellContents<V> d) { (void) d; return true; }
}// end of namespace Cells  datatype declarations
namespace RequestIds_Compile  {
}// end of namespace RequestIds_Compile  datatype declarations
namespace CacheStatusType_Compile  {
  
bool operator==(const Status &left, const Status &right); 
  
struct Status_Clean;
  
bool operator==(const Status_Clean &left, const Status_Clean &right); 
  
struct Status_Clean {
    friend bool operator==(const Status_Clean &left, const Status_Clean &right); 
    friend bool operator!=(const Status_Clean &left, const Status_Clean &right) { return !(left == right); } 
  };
  
struct Status_Dirty;
  
bool operator==(const Status_Dirty &left, const Status_Dirty &right); 
  
struct Status_Dirty {
    friend bool operator==(const Status_Dirty &left, const Status_Dirty &right); 
    friend bool operator!=(const Status_Dirty &left, const Status_Dirty &right) { return !(left == right); } 
  };
  
struct Status_Writeback;
  
bool operator==(const Status_Writeback &left, const Status_Writeback &right); 
  
struct Status_Writeback {
    friend bool operator==(const Status_Writeback &left, const Status_Writeback &right); 
    friend bool operator!=(const Status_Writeback &left, const Status_Writeback &right) { return !(left == right); } 
  };
  
struct Status {
    std::variant<Status_Clean, Status_Dirty, Status_Writeback> v;
    static Status create_Clean() {
      Status COMPILER_result;
      Status_Clean COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Status create_Dirty() {
      Status COMPILER_result;
      Status_Dirty COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Status create_Writeback() {
      Status COMPILER_result;
      Status_Writeback COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Status();
    ~Status() {}
    Status(const Status &other) {
      v = other.v;
    }
    Status& operator=(const Status other) {
      v = other.v;
      return *this;
    }
    bool is_Status_Clean() const { return std::holds_alternative<Status_Clean>(v); }
    bool is_Status_Dirty() const { return std::holds_alternative<Status_Dirty>(v); }
    bool is_Status_Writeback() const { return std::holds_alternative<Status_Writeback>(v); }
    Status* operator->() { return this; }
    friend bool operator==(const Status &left, const Status &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Status &left, const Status &right) { return !(left == right); } 
  };
  
inline bool is_Status_Clean(const struct Status d);
  
inline bool is_Status_Dirty(const struct Status d);
  
inline bool is_Status_Writeback(const struct Status d);
}// end of namespace CacheStatusType_Compile  datatype declarations
namespace DiskIfc_Compile  {
  
bool operator==(const ReqRead &left, const ReqRead &right); 
  
struct ReqRead {
    ReqRead();
    ReqRead* operator->() { return this; }
    friend bool operator==(const ReqRead &left, const ReqRead &right);
    friend bool operator!=(const ReqRead &left, const ReqRead &right) { return !(left == right); } 
  };
  
inline bool is_ReqRead(const struct ReqRead d) { (void) d; return true; }
  
bool operator==(const ReqWrite &left, const ReqWrite &right); 
  
struct ReqWrite {
    DafnySequence<uint8> data;
    ReqWrite(DafnySequence<uint8> data) : data (data) {}
    ReqWrite();
    ReqWrite* operator->() { return this; }
    friend bool operator==(const ReqWrite &left, const ReqWrite &right);
    friend bool operator!=(const ReqWrite &left, const ReqWrite &right) { return !(left == right); } 
  };
  
inline bool is_ReqWrite(const struct ReqWrite d) { (void) d; return true; }
  
bool operator==(const RespRead &left, const RespRead &right); 
  
struct RespRead {
    DafnySequence<uint8> data;
    RespRead(DafnySequence<uint8> data) : data (data) {}
    RespRead();
    RespRead* operator->() { return this; }
    friend bool operator==(const RespRead &left, const RespRead &right);
    friend bool operator!=(const RespRead &left, const RespRead &right) { return !(left == right); } 
  };
  
inline bool is_RespRead(const struct RespRead d) { (void) d; return true; }
  
bool operator==(const RespWrite &left, const RespWrite &right); 
  
struct RespWrite {
    RespWrite();
    RespWrite* operator->() { return this; }
    friend bool operator==(const RespWrite &left, const RespWrite &right);
    friend bool operator!=(const RespWrite &left, const RespWrite &right) { return !(left == right); } 
  };
  
inline bool is_RespWrite(const struct RespWrite d) { (void) d; return true; }
  
bool operator==(const DiskOp &left, const DiskOp &right); 
  
struct DiskOp_ReqReadOp;
  
bool operator==(const DiskOp_ReqReadOp &left, const DiskOp_ReqReadOp &right); 
  
struct DiskOp_ReqReadOp {
    DiskIfc_Compile::ReqRead reqRead;
    friend bool operator==(const DiskOp_ReqReadOp &left, const DiskOp_ReqReadOp &right); 
    friend bool operator!=(const DiskOp_ReqReadOp &left, const DiskOp_ReqReadOp &right) { return !(left == right); } 
  };
  
struct DiskOp_ReqWriteOp;
  
bool operator==(const DiskOp_ReqWriteOp &left, const DiskOp_ReqWriteOp &right); 
  
struct DiskOp_ReqWriteOp {
    DiskIfc_Compile::ReqWrite reqWrite;
    friend bool operator==(const DiskOp_ReqWriteOp &left, const DiskOp_ReqWriteOp &right); 
    friend bool operator!=(const DiskOp_ReqWriteOp &left, const DiskOp_ReqWriteOp &right) { return !(left == right); } 
  };
  
struct DiskOp_RespReadOp;
  
bool operator==(const DiskOp_RespReadOp &left, const DiskOp_RespReadOp &right); 
  
struct DiskOp_RespReadOp {
    DiskIfc_Compile::RespRead respRead;
    friend bool operator==(const DiskOp_RespReadOp &left, const DiskOp_RespReadOp &right); 
    friend bool operator!=(const DiskOp_RespReadOp &left, const DiskOp_RespReadOp &right) { return !(left == right); } 
  };
  
struct DiskOp_RespWriteOp;
  
bool operator==(const DiskOp_RespWriteOp &left, const DiskOp_RespWriteOp &right); 
  
struct DiskOp_RespWriteOp {
    DiskIfc_Compile::RespWrite respWrite;
    friend bool operator==(const DiskOp_RespWriteOp &left, const DiskOp_RespWriteOp &right); 
    friend bool operator!=(const DiskOp_RespWriteOp &left, const DiskOp_RespWriteOp &right) { return !(left == right); } 
  };
  
struct DiskOp {
    std::variant<DiskOp_ReqReadOp, DiskOp_ReqWriteOp, DiskOp_RespReadOp, DiskOp_RespWriteOp> v;
    static DiskOp create_ReqReadOp(DiskIfc_Compile::ReqRead reqRead) {
      DiskOp COMPILER_result;
      DiskOp_ReqReadOp COMPILER_result_subStruct;
      COMPILER_result_subStruct.reqRead = reqRead;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static DiskOp create_ReqWriteOp(DiskIfc_Compile::ReqWrite reqWrite) {
      DiskOp COMPILER_result;
      DiskOp_ReqWriteOp COMPILER_result_subStruct;
      COMPILER_result_subStruct.reqWrite = reqWrite;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static DiskOp create_RespReadOp(DiskIfc_Compile::RespRead respRead) {
      DiskOp COMPILER_result;
      DiskOp_RespReadOp COMPILER_result_subStruct;
      COMPILER_result_subStruct.respRead = respRead;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static DiskOp create_RespWriteOp(DiskIfc_Compile::RespWrite respWrite) {
      DiskOp COMPILER_result;
      DiskOp_RespWriteOp COMPILER_result_subStruct;
      COMPILER_result_subStruct.respWrite = respWrite;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    DiskOp();
    ~DiskOp() {}
    DiskOp(const DiskOp &other) {
      v = other.v;
    }
    DiskOp& operator=(const DiskOp other) {
      v = other.v;
      return *this;
    }
    bool is_DiskOp_ReqReadOp() const { return std::holds_alternative<DiskOp_ReqReadOp>(v); }
    bool is_DiskOp_ReqWriteOp() const { return std::holds_alternative<DiskOp_ReqWriteOp>(v); }
    bool is_DiskOp_RespReadOp() const { return std::holds_alternative<DiskOp_RespReadOp>(v); }
    bool is_DiskOp_RespWriteOp() const { return std::holds_alternative<DiskOp_RespWriteOp>(v); }
    DiskOp* operator->() { return this; }
    friend bool operator==(const DiskOp &left, const DiskOp &right) { 
    	return left.v == right.v;
}
    DiskIfc_Compile::ReqRead& dtor_reqRead() {
      return std::get<DiskOp_ReqReadOp>(v).reqRead; 
    }
    DiskIfc_Compile::ReqWrite& dtor_reqWrite() {
      return std::get<DiskOp_ReqWriteOp>(v).reqWrite; 
    }
    DiskIfc_Compile::RespRead& dtor_respRead() {
      return std::get<DiskOp_RespReadOp>(v).respRead; 
    }
    DiskIfc_Compile::RespWrite& dtor_respWrite() {
      return std::get<DiskOp_RespWriteOp>(v).respWrite; 
    }
    friend bool operator!=(const DiskOp &left, const DiskOp &right) { return !(left == right); } 
  };
  
inline bool is_DiskOp_ReqReadOp(const struct DiskOp d);
  
inline bool is_DiskOp_ReqWriteOp(const struct DiskOp d);
  
inline bool is_DiskOp_RespReadOp(const struct DiskOp d);
  
inline bool is_DiskOp_RespWriteOp(const struct DiskOp d);
}// end of namespace DiskIfc_Compile  datatype declarations
namespace CacheIfc_Compile  {
  
bool operator==(const Input &left, const Input &right); 
  
struct Input_WriteInput;
  
bool operator==(const Input_WriteInput &left, const Input_WriteInput &right); 
  
struct Input_WriteInput {
    DafnySequence<uint8> data;
    friend bool operator==(const Input_WriteInput &left, const Input_WriteInput &right); 
    friend bool operator!=(const Input_WriteInput &left, const Input_WriteInput &right) { return !(left == right); } 
  };
  
struct Input_ReadInput;
  
bool operator==(const Input_ReadInput &left, const Input_ReadInput &right); 
  
struct Input_ReadInput {
    friend bool operator==(const Input_ReadInput &left, const Input_ReadInput &right); 
    friend bool operator!=(const Input_ReadInput &left, const Input_ReadInput &right) { return !(left == right); } 
  };
  
struct Input_SyncInput;
  
bool operator==(const Input_SyncInput &left, const Input_SyncInput &right); 
  
struct Input_SyncInput {
    friend bool operator==(const Input_SyncInput &left, const Input_SyncInput &right); 
    friend bool operator!=(const Input_SyncInput &left, const Input_SyncInput &right) { return !(left == right); } 
  };
  
struct Input_HavocInput;
  
bool operator==(const Input_HavocInput &left, const Input_HavocInput &right); 
  
struct Input_HavocInput {
    friend bool operator==(const Input_HavocInput &left, const Input_HavocInput &right); 
    friend bool operator!=(const Input_HavocInput &left, const Input_HavocInput &right) { return !(left == right); } 
  };
  
struct Input {
    std::variant<Input_WriteInput, Input_ReadInput, Input_SyncInput, Input_HavocInput> v;
    static Input create_WriteInput(DafnySequence<uint8> data) {
      Input COMPILER_result;
      Input_WriteInput COMPILER_result_subStruct;
      COMPILER_result_subStruct.data = data;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Input create_ReadInput() {
      Input COMPILER_result;
      Input_ReadInput COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Input create_SyncInput() {
      Input COMPILER_result;
      Input_SyncInput COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Input create_HavocInput() {
      Input COMPILER_result;
      Input_HavocInput COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Input();
    ~Input() {}
    Input(const Input &other) {
      v = other.v;
    }
    Input& operator=(const Input other) {
      v = other.v;
      return *this;
    }
    bool is_Input_WriteInput() const { return std::holds_alternative<Input_WriteInput>(v); }
    bool is_Input_ReadInput() const { return std::holds_alternative<Input_ReadInput>(v); }
    bool is_Input_SyncInput() const { return std::holds_alternative<Input_SyncInput>(v); }
    bool is_Input_HavocInput() const { return std::holds_alternative<Input_HavocInput>(v); }
    Input* operator->() { return this; }
    friend bool operator==(const Input &left, const Input &right) { 
    	return left.v == right.v;
}
    DafnySequence<uint8>& dtor_data() {
      return std::get<Input_WriteInput>(v).data; 
    }
    friend bool operator!=(const Input &left, const Input &right) { return !(left == right); } 
  };
  
inline bool is_Input_WriteInput(const struct Input d);
  
inline bool is_Input_ReadInput(const struct Input d);
  
inline bool is_Input_SyncInput(const struct Input d);
  
inline bool is_Input_HavocInput(const struct Input d);
  
bool operator==(const Output &left, const Output &right); 
  
struct Output_WriteOutput;
  
bool operator==(const Output_WriteOutput &left, const Output_WriteOutput &right); 
  
struct Output_WriteOutput {
    friend bool operator==(const Output_WriteOutput &left, const Output_WriteOutput &right); 
    friend bool operator!=(const Output_WriteOutput &left, const Output_WriteOutput &right) { return !(left == right); } 
  };
  
struct Output_ReadOutput;
  
bool operator==(const Output_ReadOutput &left, const Output_ReadOutput &right); 
  
struct Output_ReadOutput {
    friend bool operator==(const Output_ReadOutput &left, const Output_ReadOutput &right); 
    friend bool operator!=(const Output_ReadOutput &left, const Output_ReadOutput &right) { return !(left == right); } 
  };
  
struct Output_SyncOutput;
  
bool operator==(const Output_SyncOutput &left, const Output_SyncOutput &right); 
  
struct Output_SyncOutput {
    friend bool operator==(const Output_SyncOutput &left, const Output_SyncOutput &right); 
    friend bool operator!=(const Output_SyncOutput &left, const Output_SyncOutput &right) { return !(left == right); } 
  };
  
struct Output_HavocOutput;
  
bool operator==(const Output_HavocOutput &left, const Output_HavocOutput &right); 
  
struct Output_HavocOutput {
    friend bool operator==(const Output_HavocOutput &left, const Output_HavocOutput &right); 
    friend bool operator!=(const Output_HavocOutput &left, const Output_HavocOutput &right) { return !(left == right); } 
  };
  
struct Output {
    std::variant<Output_WriteOutput, Output_ReadOutput, Output_SyncOutput, Output_HavocOutput> v;
    static Output create_WriteOutput() {
      Output COMPILER_result;
      Output_WriteOutput COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Output create_ReadOutput() {
      Output COMPILER_result;
      Output_ReadOutput COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Output create_SyncOutput() {
      Output COMPILER_result;
      Output_SyncOutput COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Output create_HavocOutput() {
      Output COMPILER_result;
      Output_HavocOutput COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Output();
    ~Output() {}
    Output(const Output &other) {
      v = other.v;
    }
    Output& operator=(const Output other) {
      v = other.v;
      return *this;
    }
    bool is_Output_WriteOutput() const { return std::holds_alternative<Output_WriteOutput>(v); }
    bool is_Output_ReadOutput() const { return std::holds_alternative<Output_ReadOutput>(v); }
    bool is_Output_SyncOutput() const { return std::holds_alternative<Output_SyncOutput>(v); }
    bool is_Output_HavocOutput() const { return std::holds_alternative<Output_HavocOutput>(v); }
    Output* operator->() { return this; }
    friend bool operator==(const Output &left, const Output &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Output &left, const Output &right) { return !(left == right); } 
  };
  
inline bool is_Output_WriteOutput(const struct Output d);
  
inline bool is_Output_ReadOutput(const struct Output d);
  
inline bool is_Output_SyncOutput(const struct Output d);
  
inline bool is_Output_HavocOutput(const struct Output d);
  
bool operator==(const Op &left, const Op &right); 
  
struct Op {
    CacheIfc_Compile::Input input;
    CacheIfc_Compile::Output output;
    Op(CacheIfc_Compile::Input input, CacheIfc_Compile::Output output) : input (input),  output (output) {}
    Op();
    Op* operator->() { return this; }
    friend bool operator==(const Op &left, const Op &right);
    friend bool operator!=(const Op &left, const Op &right) { return !(left == right); } 
  };
  
inline bool is_Op(const struct Op d) { (void) d; return true; }
}// end of namespace CacheIfc_Compile  datatype declarations
namespace CacheSSM_Compile  {
  
bool operator==(const Entry &left, const Entry &right); 
  
struct Entry_Empty;
  
bool operator==(const Entry_Empty &left, const Entry_Empty &right); 
  
struct Entry_Empty {
    friend bool operator==(const Entry_Empty &left, const Entry_Empty &right); 
    friend bool operator!=(const Entry_Empty &left, const Entry_Empty &right) { return !(left == right); } 
  };
  
struct Entry_Reading;
  
bool operator==(const Entry_Reading &left, const Entry_Reading &right); 
  
struct Entry_Reading {
    friend bool operator==(const Entry_Reading &left, const Entry_Reading &right); 
    friend bool operator!=(const Entry_Reading &left, const Entry_Reading &right) { return !(left == right); } 
  };
  
struct Entry_Entry;
  
bool operator==(const Entry_Entry &left, const Entry_Entry &right); 
  
struct Entry_Entry {
    DafnySequence<uint8> data;
    friend bool operator==(const Entry_Entry &left, const Entry_Entry &right); 
    friend bool operator!=(const Entry_Entry &left, const Entry_Entry &right) { return !(left == right); } 
  };
  
struct Entry {
    std::variant<Entry_Empty, Entry_Reading, Entry_Entry> v;
    static Entry create_Empty() {
      Entry COMPILER_result;
      Entry_Empty COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Entry create_Reading() {
      Entry COMPILER_result;
      Entry_Reading COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Entry create_Entry(DafnySequence<uint8> data) {
      Entry COMPILER_result;
      Entry_Entry COMPILER_result_subStruct;
      COMPILER_result_subStruct.data = data;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Entry();
    ~Entry() {}
    Entry(const Entry &other) {
      v = other.v;
    }
    Entry& operator=(const Entry other) {
      v = other.v;
      return *this;
    }
    bool is_Entry_Empty() const { return std::holds_alternative<Entry_Empty>(v); }
    bool is_Entry_Reading() const { return std::holds_alternative<Entry_Reading>(v); }
    bool is_Entry_Entry() const { return std::holds_alternative<Entry_Entry>(v); }
    Entry* operator->() { return this; }
    friend bool operator==(const Entry &left, const Entry &right) { 
    	return left.v == right.v;
}
    DafnySequence<uint8>& dtor_data() {
      return std::get<Entry_Entry>(v).data; 
    }
    friend bool operator!=(const Entry &left, const Entry &right) { return !(left == right); } 
  };
  
inline bool is_Entry_Empty(const struct Entry d);
  
inline bool is_Entry_Reading(const struct Entry d);
  
inline bool is_Entry_Entry(const struct Entry d);
  
bool operator==(const M &left, const M &right); 
  
struct M_M;
  
bool operator==(const M_M &left, const M_M &right); 
  
struct M_M {
    friend bool operator==(const M_M &left, const M_M &right); 
    friend bool operator!=(const M_M &left, const M_M &right) { return !(left == right); } 
  };
  
struct M_Fail;
  
bool operator==(const M_Fail &left, const M_Fail &right); 
  
struct M_Fail {
    friend bool operator==(const M_Fail &left, const M_Fail &right); 
    friend bool operator!=(const M_Fail &left, const M_Fail &right) { return !(left == right); } 
  };
  
struct M {
    std::variant<M_M, M_Fail> v;
    static M create_M() {
      M COMPILER_result;
      M_M COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static M create_Fail() {
      M COMPILER_result;
      M_Fail COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    M();
    ~M() {}
    M(const M &other) {
      v = other.v;
    }
    M& operator=(const M other) {
      v = other.v;
      return *this;
    }
    bool is_M_M() const { return std::holds_alternative<M_M>(v); }
    bool is_M_Fail() const { return std::holds_alternative<M_Fail>(v); }
    M* operator->() { return this; }
    friend bool operator==(const M &left, const M &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const M &left, const M &right) { return !(left == right); } 
  };
  
inline bool is_M_M(const struct M d);
  
inline bool is_M_Fail(const struct M d);
  
bool operator==(const Step &left, const Step &right); 
  
struct Step_StartReadStep;
  
bool operator==(const Step_StartReadStep &left, const Step_StartReadStep &right); 
  
struct Step_StartReadStep {
    friend bool operator==(const Step_StartReadStep &left, const Step_StartReadStep &right); 
    friend bool operator!=(const Step_StartReadStep &left, const Step_StartReadStep &right) { return !(left == right); } 
  };
  
struct Step_FinishReadStep;
  
bool operator==(const Step_FinishReadStep &left, const Step_FinishReadStep &right); 
  
struct Step_FinishReadStep {
    friend bool operator==(const Step_FinishReadStep &left, const Step_FinishReadStep &right); 
    friend bool operator!=(const Step_FinishReadStep &left, const Step_FinishReadStep &right) { return !(left == right); } 
  };
  
struct Step_StartWritebackStep;
  
bool operator==(const Step_StartWritebackStep &left, const Step_StartWritebackStep &right); 
  
struct Step_StartWritebackStep {
    friend bool operator==(const Step_StartWritebackStep &left, const Step_StartWritebackStep &right); 
    friend bool operator!=(const Step_StartWritebackStep &left, const Step_StartWritebackStep &right) { return !(left == right); } 
  };
  
struct Step_FinishWritebackStep;
  
bool operator==(const Step_FinishWritebackStep &left, const Step_FinishWritebackStep &right); 
  
struct Step_FinishWritebackStep {
    friend bool operator==(const Step_FinishWritebackStep &left, const Step_FinishWritebackStep &right); 
    friend bool operator!=(const Step_FinishWritebackStep &left, const Step_FinishWritebackStep &right) { return !(left == right); } 
  };
  
struct Step_EvictStep;
  
bool operator==(const Step_EvictStep &left, const Step_EvictStep &right); 
  
struct Step_EvictStep {
    friend bool operator==(const Step_EvictStep &left, const Step_EvictStep &right); 
    friend bool operator!=(const Step_EvictStep &left, const Step_EvictStep &right) { return !(left == right); } 
  };
  
struct Step_ObserveCleanForSyncStep;
  
bool operator==(const Step_ObserveCleanForSyncStep &left, const Step_ObserveCleanForSyncStep &right); 
  
struct Step_ObserveCleanForSyncStep {
    friend bool operator==(const Step_ObserveCleanForSyncStep &left, const Step_ObserveCleanForSyncStep &right); 
    friend bool operator!=(const Step_ObserveCleanForSyncStep &left, const Step_ObserveCleanForSyncStep &right) { return !(left == right); } 
  };
  
struct Step_ApplyReadStep;
  
bool operator==(const Step_ApplyReadStep &left, const Step_ApplyReadStep &right); 
  
struct Step_ApplyReadStep {
    friend bool operator==(const Step_ApplyReadStep &left, const Step_ApplyReadStep &right); 
    friend bool operator!=(const Step_ApplyReadStep &left, const Step_ApplyReadStep &right) { return !(left == right); } 
  };
  
struct Step_ApplyWriteStep;
  
bool operator==(const Step_ApplyWriteStep &left, const Step_ApplyWriteStep &right); 
  
struct Step_ApplyWriteStep {
    friend bool operator==(const Step_ApplyWriteStep &left, const Step_ApplyWriteStep &right); 
    friend bool operator!=(const Step_ApplyWriteStep &left, const Step_ApplyWriteStep &right) { return !(left == right); } 
  };
  
struct Step_MarkDirtyStep;
  
bool operator==(const Step_MarkDirtyStep &left, const Step_MarkDirtyStep &right); 
  
struct Step_MarkDirtyStep {
    friend bool operator==(const Step_MarkDirtyStep &left, const Step_MarkDirtyStep &right); 
    friend bool operator!=(const Step_MarkDirtyStep &left, const Step_MarkDirtyStep &right) { return !(left == right); } 
  };
  
struct Step_HavocNewStep;
  
bool operator==(const Step_HavocNewStep &left, const Step_HavocNewStep &right); 
  
struct Step_HavocNewStep {
    friend bool operator==(const Step_HavocNewStep &left, const Step_HavocNewStep &right); 
    friend bool operator!=(const Step_HavocNewStep &left, const Step_HavocNewStep &right) { return !(left == right); } 
  };
  
struct Step_HavocEvictStep;
  
bool operator==(const Step_HavocEvictStep &left, const Step_HavocEvictStep &right); 
  
struct Step_HavocEvictStep {
    friend bool operator==(const Step_HavocEvictStep &left, const Step_HavocEvictStep &right); 
    friend bool operator!=(const Step_HavocEvictStep &left, const Step_HavocEvictStep &right) { return !(left == right); } 
  };
  
struct Step {
    std::variant<Step_StartReadStep, Step_FinishReadStep, Step_StartWritebackStep, Step_FinishWritebackStep, Step_EvictStep, Step_ObserveCleanForSyncStep, Step_ApplyReadStep, Step_ApplyWriteStep, Step_MarkDirtyStep, Step_HavocNewStep, Step_HavocEvictStep> v;
    static Step create_StartReadStep() {
      Step COMPILER_result;
      Step_StartReadStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_FinishReadStep() {
      Step COMPILER_result;
      Step_FinishReadStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_StartWritebackStep() {
      Step COMPILER_result;
      Step_StartWritebackStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_FinishWritebackStep() {
      Step COMPILER_result;
      Step_FinishWritebackStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_EvictStep() {
      Step COMPILER_result;
      Step_EvictStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_ObserveCleanForSyncStep() {
      Step COMPILER_result;
      Step_ObserveCleanForSyncStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_ApplyReadStep() {
      Step COMPILER_result;
      Step_ApplyReadStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_ApplyWriteStep() {
      Step COMPILER_result;
      Step_ApplyWriteStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_MarkDirtyStep() {
      Step COMPILER_result;
      Step_MarkDirtyStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_HavocNewStep() {
      Step COMPILER_result;
      Step_HavocNewStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_HavocEvictStep() {
      Step COMPILER_result;
      Step_HavocEvictStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Step();
    ~Step() {}
    Step(const Step &other) {
      v = other.v;
    }
    Step& operator=(const Step other) {
      v = other.v;
      return *this;
    }
    bool is_Step_StartReadStep() const { return std::holds_alternative<Step_StartReadStep>(v); }
    bool is_Step_FinishReadStep() const { return std::holds_alternative<Step_FinishReadStep>(v); }
    bool is_Step_StartWritebackStep() const { return std::holds_alternative<Step_StartWritebackStep>(v); }
    bool is_Step_FinishWritebackStep() const { return std::holds_alternative<Step_FinishWritebackStep>(v); }
    bool is_Step_EvictStep() const { return std::holds_alternative<Step_EvictStep>(v); }
    bool is_Step_ObserveCleanForSyncStep() const { return std::holds_alternative<Step_ObserveCleanForSyncStep>(v); }
    bool is_Step_ApplyReadStep() const { return std::holds_alternative<Step_ApplyReadStep>(v); }
    bool is_Step_ApplyWriteStep() const { return std::holds_alternative<Step_ApplyWriteStep>(v); }
    bool is_Step_MarkDirtyStep() const { return std::holds_alternative<Step_MarkDirtyStep>(v); }
    bool is_Step_HavocNewStep() const { return std::holds_alternative<Step_HavocNewStep>(v); }
    bool is_Step_HavocEvictStep() const { return std::holds_alternative<Step_HavocEvictStep>(v); }
    Step* operator->() { return this; }
    friend bool operator==(const Step &left, const Step &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Step &left, const Step &right) { return !(left == right); } 
  };
  
inline bool is_Step_StartReadStep(const struct Step d);
  
inline bool is_Step_FinishReadStep(const struct Step d);
  
inline bool is_Step_StartWritebackStep(const struct Step d);
  
inline bool is_Step_FinishWritebackStep(const struct Step d);
  
inline bool is_Step_EvictStep(const struct Step d);
  
inline bool is_Step_ObserveCleanForSyncStep(const struct Step d);
  
inline bool is_Step_ApplyReadStep(const struct Step d);
  
inline bool is_Step_ApplyWriteStep(const struct Step d);
  
inline bool is_Step_MarkDirtyStep(const struct Step d);
  
inline bool is_Step_HavocNewStep(const struct Step d);
  
inline bool is_Step_HavocEvictStep(const struct Step d);
}// end of namespace CacheSSM_Compile  datatype declarations
namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile  {
  
bool operator==(const Token &left, const Token &right); 
  
struct Token {
    Token();
    Token* operator->() { return this; }
    friend bool operator==(const Token &left, const Token &right);
    friend bool operator!=(const Token &left, const Token &right) { return !(left == right); } 
  };
  
inline bool is_Token(const struct Token d) { (void) d; return true; }
}// end of namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile  datatype declarations
namespace DiskSingletonLoc_Compile  {
}// end of namespace DiskSingletonLoc_Compile  datatype declarations
namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile  {
}// end of namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile  datatype declarations
namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile  {
  
bool operator==(const Token &left, const Token &right); 
  
struct Token {
    Token();
    Token* operator->() { return this; }
    friend bool operator==(const Token &left, const Token &right);
    friend bool operator!=(const Token &left, const Token &right) { return !(left == right); } 
  };
  
inline bool is_Token(const struct Token d) { (void) d; return true; }
}// end of namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile  datatype declarations
namespace DiskToken_ON_CacheIfc_CacheSSM__Compile  {
  
bool operator==(const Token &left, const Token &right); 
  
struct Token {
    CacheSSM_Compile::M val;
    Token(CacheSSM_Compile::M val) : val (val) {}
    Token();
    Token* operator->() { return this; }
    friend bool operator==(const Token &left, const Token &right);
    friend bool operator!=(const Token &left, const Token &right) { return !(left == right); } 
  };
  
inline bool is_Token(const struct Token d) { (void) d; return true; }
}// end of namespace DiskToken_ON_CacheIfc_CacheSSM__Compile  datatype declarations
namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile  {
}// end of namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile  datatype declarations
namespace CacheResources_Compile  {
  
bool operator==(const DiskPageMap &left, const DiskPageMap &right); 
  
struct DiskPageMap {
    DiskPageMap();
    DiskPageMap* operator->() { return this; }
    friend bool operator==(const DiskPageMap &left, const DiskPageMap &right);
    friend bool operator!=(const DiskPageMap &left, const DiskPageMap &right) { return !(left == right); } 
  };
  
inline bool is_DiskPageMap(const struct DiskPageMap d) { (void) d; return true; }
  
bool operator==(const HavocPermission &left, const HavocPermission &right); 
  
struct HavocPermission {
    HavocPermission();
    HavocPermission* operator->() { return this; }
    friend bool operator==(const HavocPermission &left, const HavocPermission &right);
    friend bool operator!=(const HavocPermission &left, const HavocPermission &right) { return !(left == right); } 
  };
  
inline bool is_HavocPermission(const struct HavocPermission d) { (void) d; return true; }
  
bool operator==(const CacheStatus &left, const CacheStatus &right); 
  
struct CacheStatus {
    CacheStatus();
    CacheStatus* operator->() { return this; }
    friend bool operator==(const CacheStatus &left, const CacheStatus &right);
    friend bool operator!=(const CacheStatus &left, const CacheStatus &right) { return !(left == right); } 
  };
  
inline bool is_CacheStatus(const struct CacheStatus d) { (void) d; return true; }
  
bool operator==(const CacheEmpty &left, const CacheEmpty &right); 
  
struct CacheEmpty {
    CacheEmpty();
    CacheEmpty* operator->() { return this; }
    friend bool operator==(const CacheEmpty &left, const CacheEmpty &right);
    friend bool operator!=(const CacheEmpty &left, const CacheEmpty &right) { return !(left == right); } 
  };
  
inline bool is_CacheEmpty(const struct CacheEmpty d) { (void) d; return true; }
  
bool operator==(const CacheReading &left, const CacheReading &right); 
  
struct CacheReading {
    CacheReading();
    CacheReading* operator->() { return this; }
    friend bool operator==(const CacheReading &left, const CacheReading &right);
    friend bool operator!=(const CacheReading &left, const CacheReading &right) { return !(left == right); } 
  };
  
inline bool is_CacheReading(const struct CacheReading d) { (void) d; return true; }
  
bool operator==(const CacheEntry &left, const CacheEntry &right); 
  
struct CacheEntry {
    CacheEntry();
    CacheEntry* operator->() { return this; }
    friend bool operator==(const CacheEntry &left, const CacheEntry &right);
    friend bool operator!=(const CacheEntry &left, const CacheEntry &right) { return !(left == right); } 
  };
  
inline bool is_CacheEntry(const struct CacheEntry d) { (void) d; return true; }
  
bool operator==(const DiskWriteTicket &left, const DiskWriteTicket &right); 
  
struct DiskWriteTicket {
    DiskWriteTicket();
    DiskWriteTicket* operator->() { return this; }
    friend bool operator==(const DiskWriteTicket &left, const DiskWriteTicket &right);
    friend bool operator!=(const DiskWriteTicket &left, const DiskWriteTicket &right) { return !(left == right); } 
  };
  
inline bool is_DiskWriteTicket(const struct DiskWriteTicket d) { (void) d; return true; }
  
bool operator==(const DiskWriteStub &left, const DiskWriteStub &right); 
  
struct DiskWriteStub {
    DiskWriteStub();
    DiskWriteStub* operator->() { return this; }
    friend bool operator==(const DiskWriteStub &left, const DiskWriteStub &right);
    friend bool operator!=(const DiskWriteStub &left, const DiskWriteStub &right) { return !(left == right); } 
  };
  
inline bool is_DiskWriteStub(const struct DiskWriteStub d) { (void) d; return true; }
  
bool operator==(const DiskReadTicket &left, const DiskReadTicket &right); 
  
struct DiskReadTicket {
    DiskReadTicket();
    DiskReadTicket* operator->() { return this; }
    friend bool operator==(const DiskReadTicket &left, const DiskReadTicket &right);
    friend bool operator!=(const DiskReadTicket &left, const DiskReadTicket &right) { return !(left == right); } 
  };
  
inline bool is_DiskReadTicket(const struct DiskReadTicket d) { (void) d; return true; }
  
bool operator==(const DiskReadStub &left, const DiskReadStub &right); 
  
struct DiskReadStub {
    DiskReadStub();
    DiskReadStub* operator->() { return this; }
    friend bool operator==(const DiskReadStub &left, const DiskReadStub &right);
    friend bool operator!=(const DiskReadStub &left, const DiskReadStub &right) { return !(left == right); } 
  };
  
inline bool is_DiskReadStub(const struct DiskReadStub d) { (void) d; return true; }
}// end of namespace CacheResources_Compile  datatype declarations
namespace CacheHandle_Compile  {
  
bool operator==(const PageHandle &left, const PageHandle &right); 
  
struct PageHandle {
    Ptrs::Ptr data__ptr;
    int64 disk__addr;
    PageHandle(Ptrs::Ptr data__ptr, int64 disk__addr) : data__ptr (data__ptr),  disk__addr (disk__addr) {}
    PageHandle();
    PageHandle* operator->() { return this; }
    friend bool operator==(const PageHandle &left, const PageHandle &right);
    friend bool operator!=(const PageHandle &left, const PageHandle &right) { return !(left == right); } 
  };
  
inline bool is_PageHandle(const struct PageHandle d) { (void) d; return true; }
  
bool operator==(const Key &left, const Key &right); 
  
struct Key {
    Ptrs::Ptr data__ptr;
    Cells::Cell <CacheHandle_Compile::PageHandle>  idx__cell;
    Key(Ptrs::Ptr data__ptr, Cells::Cell <CacheHandle_Compile::PageHandle>  idx__cell) : data__ptr (data__ptr),  idx__cell (idx__cell) {}
    Key();
    Key* operator->() { return this; }
    friend bool operator==(const Key &left, const Key &right);
    friend bool operator!=(const Key &left, const Key &right) { return !(left == right); } 
  };
  
inline bool is_Key(const struct Key d) { (void) d; return true; }
  
bool operator==(const Handle &left, const Handle &right); 
  
struct Handle_CacheEmptyHandle;
  
bool operator==(const Handle_CacheEmptyHandle &left, const Handle_CacheEmptyHandle &right); 
  
struct Handle_CacheEmptyHandle {
    friend bool operator==(const Handle_CacheEmptyHandle &left, const Handle_CacheEmptyHandle &right); 
    friend bool operator!=(const Handle_CacheEmptyHandle &left, const Handle_CacheEmptyHandle &right) { return !(left == right); } 
  };
  
struct Handle_CacheReadingHandle;
  
bool operator==(const Handle_CacheReadingHandle &left, const Handle_CacheReadingHandle &right); 
  
struct Handle_CacheReadingHandle {
    friend bool operator==(const Handle_CacheReadingHandle &left, const Handle_CacheReadingHandle &right); 
    friend bool operator!=(const Handle_CacheReadingHandle &left, const Handle_CacheReadingHandle &right) { return !(left == right); } 
  };
  
struct Handle_CacheEntryHandle;
  
bool operator==(const Handle_CacheEntryHandle &left, const Handle_CacheEntryHandle &right); 
  
struct Handle_CacheEntryHandle {
    friend bool operator==(const Handle_CacheEntryHandle &left, const Handle_CacheEntryHandle &right); 
    friend bool operator!=(const Handle_CacheEntryHandle &left, const Handle_CacheEntryHandle &right) { return !(left == right); } 
  };
  
struct Handle {
    std::variant<Handle_CacheEmptyHandle, Handle_CacheReadingHandle, Handle_CacheEntryHandle> v;
    static Handle create_CacheEmptyHandle() {
      Handle COMPILER_result;
      Handle_CacheEmptyHandle COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Handle create_CacheReadingHandle() {
      Handle COMPILER_result;
      Handle_CacheReadingHandle COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Handle create_CacheEntryHandle() {
      Handle COMPILER_result;
      Handle_CacheEntryHandle COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Handle();
    ~Handle() {}
    Handle(const Handle &other) {
      v = other.v;
    }
    Handle& operator=(const Handle other) {
      v = other.v;
      return *this;
    }
    bool is_Handle_CacheEmptyHandle() const { return std::holds_alternative<Handle_CacheEmptyHandle>(v); }
    bool is_Handle_CacheReadingHandle() const { return std::holds_alternative<Handle_CacheReadingHandle>(v); }
    bool is_Handle_CacheEntryHandle() const { return std::holds_alternative<Handle_CacheEntryHandle>(v); }
    Handle* operator->() { return this; }
    friend bool operator==(const Handle &left, const Handle &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Handle &left, const Handle &right) { return !(left == right); } 
  };
  
inline bool is_Handle_CacheEmptyHandle(const struct Handle d);
  
inline bool is_Handle_CacheReadingHandle(const struct Handle d);
  
inline bool is_Handle_CacheEntryHandle(const struct Handle d);
}// end of namespace CacheHandle_Compile  datatype declarations
namespace RwLock_Compile  {
  
bool operator==(const Flag &left, const Flag &right); 
  
struct Flag_Unmapped;
  
bool operator==(const Flag_Unmapped &left, const Flag_Unmapped &right); 
  
struct Flag_Unmapped {
    friend bool operator==(const Flag_Unmapped &left, const Flag_Unmapped &right); 
    friend bool operator!=(const Flag_Unmapped &left, const Flag_Unmapped &right) { return !(left == right); } 
  };
  
struct Flag_Reading;
  
bool operator==(const Flag_Reading &left, const Flag_Reading &right); 
  
struct Flag_Reading {
    friend bool operator==(const Flag_Reading &left, const Flag_Reading &right); 
    friend bool operator!=(const Flag_Reading &left, const Flag_Reading &right) { return !(left == right); } 
  };
  
struct Flag_Reading__ExcLock;
  
bool operator==(const Flag_Reading__ExcLock &left, const Flag_Reading__ExcLock &right); 
  
struct Flag_Reading__ExcLock {
    friend bool operator==(const Flag_Reading__ExcLock &left, const Flag_Reading__ExcLock &right); 
    friend bool operator!=(const Flag_Reading__ExcLock &left, const Flag_Reading__ExcLock &right) { return !(left == right); } 
  };
  
struct Flag_Available;
  
bool operator==(const Flag_Available &left, const Flag_Available &right); 
  
struct Flag_Available {
    friend bool operator==(const Flag_Available &left, const Flag_Available &right); 
    friend bool operator!=(const Flag_Available &left, const Flag_Available &right) { return !(left == right); } 
  };
  
struct Flag_Claimed;
  
bool operator==(const Flag_Claimed &left, const Flag_Claimed &right); 
  
struct Flag_Claimed {
    friend bool operator==(const Flag_Claimed &left, const Flag_Claimed &right); 
    friend bool operator!=(const Flag_Claimed &left, const Flag_Claimed &right) { return !(left == right); } 
  };
  
struct Flag_Writeback;
  
bool operator==(const Flag_Writeback &left, const Flag_Writeback &right); 
  
struct Flag_Writeback {
    friend bool operator==(const Flag_Writeback &left, const Flag_Writeback &right); 
    friend bool operator!=(const Flag_Writeback &left, const Flag_Writeback &right) { return !(left == right); } 
  };
  
struct Flag_Writeback__Claimed;
  
bool operator==(const Flag_Writeback__Claimed &left, const Flag_Writeback__Claimed &right); 
  
struct Flag_Writeback__Claimed {
    friend bool operator==(const Flag_Writeback__Claimed &left, const Flag_Writeback__Claimed &right); 
    friend bool operator!=(const Flag_Writeback__Claimed &left, const Flag_Writeback__Claimed &right) { return !(left == right); } 
  };
  
struct Flag_Writeback__PendingExcLock;
  
bool operator==(const Flag_Writeback__PendingExcLock &left, const Flag_Writeback__PendingExcLock &right); 
  
struct Flag_Writeback__PendingExcLock {
    friend bool operator==(const Flag_Writeback__PendingExcLock &left, const Flag_Writeback__PendingExcLock &right); 
    friend bool operator!=(const Flag_Writeback__PendingExcLock &left, const Flag_Writeback__PendingExcLock &right) { return !(left == right); } 
  };
  
struct Flag_PendingExcLock;
  
bool operator==(const Flag_PendingExcLock &left, const Flag_PendingExcLock &right); 
  
struct Flag_PendingExcLock {
    friend bool operator==(const Flag_PendingExcLock &left, const Flag_PendingExcLock &right); 
    friend bool operator!=(const Flag_PendingExcLock &left, const Flag_PendingExcLock &right) { return !(left == right); } 
  };
  
struct Flag_ExcLock__Clean;
  
bool operator==(const Flag_ExcLock__Clean &left, const Flag_ExcLock__Clean &right); 
  
struct Flag_ExcLock__Clean {
    friend bool operator==(const Flag_ExcLock__Clean &left, const Flag_ExcLock__Clean &right); 
    friend bool operator!=(const Flag_ExcLock__Clean &left, const Flag_ExcLock__Clean &right) { return !(left == right); } 
  };
  
struct Flag_ExcLock__Dirty;
  
bool operator==(const Flag_ExcLock__Dirty &left, const Flag_ExcLock__Dirty &right); 
  
struct Flag_ExcLock__Dirty {
    friend bool operator==(const Flag_ExcLock__Dirty &left, const Flag_ExcLock__Dirty &right); 
    friend bool operator!=(const Flag_ExcLock__Dirty &left, const Flag_ExcLock__Dirty &right) { return !(left == right); } 
  };
  
struct Flag {
    std::variant<Flag_Unmapped, Flag_Reading, Flag_Reading__ExcLock, Flag_Available, Flag_Claimed, Flag_Writeback, Flag_Writeback__Claimed, Flag_Writeback__PendingExcLock, Flag_PendingExcLock, Flag_ExcLock__Clean, Flag_ExcLock__Dirty> v;
    static Flag create_Unmapped() {
      Flag COMPILER_result;
      Flag_Unmapped COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_Reading() {
      Flag COMPILER_result;
      Flag_Reading COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_Reading__ExcLock() {
      Flag COMPILER_result;
      Flag_Reading__ExcLock COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_Available() {
      Flag COMPILER_result;
      Flag_Available COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_Claimed() {
      Flag COMPILER_result;
      Flag_Claimed COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_Writeback() {
      Flag COMPILER_result;
      Flag_Writeback COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_Writeback__Claimed() {
      Flag COMPILER_result;
      Flag_Writeback__Claimed COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_Writeback__PendingExcLock() {
      Flag COMPILER_result;
      Flag_Writeback__PendingExcLock COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_PendingExcLock() {
      Flag COMPILER_result;
      Flag_PendingExcLock COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_ExcLock__Clean() {
      Flag COMPILER_result;
      Flag_ExcLock__Clean COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Flag create_ExcLock__Dirty() {
      Flag COMPILER_result;
      Flag_ExcLock__Dirty COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Flag();
    ~Flag() {}
    Flag(const Flag &other) {
      v = other.v;
    }
    Flag& operator=(const Flag other) {
      v = other.v;
      return *this;
    }
    bool is_Flag_Unmapped() const { return std::holds_alternative<Flag_Unmapped>(v); }
    bool is_Flag_Reading() const { return std::holds_alternative<Flag_Reading>(v); }
    bool is_Flag_Reading__ExcLock() const { return std::holds_alternative<Flag_Reading__ExcLock>(v); }
    bool is_Flag_Available() const { return std::holds_alternative<Flag_Available>(v); }
    bool is_Flag_Claimed() const { return std::holds_alternative<Flag_Claimed>(v); }
    bool is_Flag_Writeback() const { return std::holds_alternative<Flag_Writeback>(v); }
    bool is_Flag_Writeback__Claimed() const { return std::holds_alternative<Flag_Writeback__Claimed>(v); }
    bool is_Flag_Writeback__PendingExcLock() const { return std::holds_alternative<Flag_Writeback__PendingExcLock>(v); }
    bool is_Flag_PendingExcLock() const { return std::holds_alternative<Flag_PendingExcLock>(v); }
    bool is_Flag_ExcLock__Clean() const { return std::holds_alternative<Flag_ExcLock__Clean>(v); }
    bool is_Flag_ExcLock__Dirty() const { return std::holds_alternative<Flag_ExcLock__Dirty>(v); }
    Flag* operator->() { return this; }
    friend bool operator==(const Flag &left, const Flag &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Flag &left, const Flag &right) { return !(left == right); } 
  };
  
inline bool is_Flag_Unmapped(const struct Flag d);
  
inline bool is_Flag_Reading(const struct Flag d);
  
inline bool is_Flag_Reading__ExcLock(const struct Flag d);
  
inline bool is_Flag_Available(const struct Flag d);
  
inline bool is_Flag_Claimed(const struct Flag d);
  
inline bool is_Flag_Writeback(const struct Flag d);
  
inline bool is_Flag_Writeback__Claimed(const struct Flag d);
  
inline bool is_Flag_Writeback__PendingExcLock(const struct Flag d);
  
inline bool is_Flag_PendingExcLock(const struct Flag d);
  
inline bool is_Flag_ExcLock__Clean(const struct Flag d);
  
inline bool is_Flag_ExcLock__Dirty(const struct Flag d);
  
bool operator==(const SharedState &left, const SharedState &right); 
  
struct SharedState_SharedPending;
  
bool operator==(const SharedState_SharedPending &left, const SharedState_SharedPending &right); 
  
struct SharedState_SharedPending {
    friend bool operator==(const SharedState_SharedPending &left, const SharedState_SharedPending &right); 
    friend bool operator!=(const SharedState_SharedPending &left, const SharedState_SharedPending &right) { return !(left == right); } 
  };
  
struct SharedState_SharedPending2;
  
bool operator==(const SharedState_SharedPending2 &left, const SharedState_SharedPending2 &right); 
  
struct SharedState_SharedPending2 {
    friend bool operator==(const SharedState_SharedPending2 &left, const SharedState_SharedPending2 &right); 
    friend bool operator!=(const SharedState_SharedPending2 &left, const SharedState_SharedPending2 &right) { return !(left == right); } 
  };
  
struct SharedState_SharedObtained;
  
bool operator==(const SharedState_SharedObtained &left, const SharedState_SharedObtained &right); 
  
struct SharedState_SharedObtained {
    CacheHandle_Compile::Handle b;
    friend bool operator==(const SharedState_SharedObtained &left, const SharedState_SharedObtained &right); 
    friend bool operator!=(const SharedState_SharedObtained &left, const SharedState_SharedObtained &right) { return !(left == right); } 
  };
  
struct SharedState {
    std::variant<SharedState_SharedPending, SharedState_SharedPending2, SharedState_SharedObtained> v;
    static SharedState create_SharedPending() {
      SharedState COMPILER_result;
      SharedState_SharedPending COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static SharedState create_SharedPending2() {
      SharedState COMPILER_result;
      SharedState_SharedPending2 COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static SharedState create_SharedObtained(CacheHandle_Compile::Handle b) {
      SharedState COMPILER_result;
      SharedState_SharedObtained COMPILER_result_subStruct;
      COMPILER_result_subStruct.b = b;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    SharedState();
    ~SharedState() {}
    SharedState(const SharedState &other) {
      v = other.v;
    }
    SharedState& operator=(const SharedState other) {
      v = other.v;
      return *this;
    }
    bool is_SharedState_SharedPending() const { return std::holds_alternative<SharedState_SharedPending>(v); }
    bool is_SharedState_SharedPending2() const { return std::holds_alternative<SharedState_SharedPending2>(v); }
    bool is_SharedState_SharedObtained() const { return std::holds_alternative<SharedState_SharedObtained>(v); }
    SharedState* operator->() { return this; }
    friend bool operator==(const SharedState &left, const SharedState &right) { 
    	return left.v == right.v;
}
    CacheHandle_Compile::Handle& dtor_b() {
      return std::get<SharedState_SharedObtained>(v).b; 
    }
    friend bool operator!=(const SharedState &left, const SharedState &right) { return !(left == right); } 
  };
  
inline bool is_SharedState_SharedPending(const struct SharedState d);
  
inline bool is_SharedState_SharedPending2(const struct SharedState d);
  
inline bool is_SharedState_SharedObtained(const struct SharedState d);
  
bool operator==(const ExcState &left, const ExcState &right); 
  
struct ExcState_ExcNone;
  
bool operator==(const ExcState_ExcNone &left, const ExcState_ExcNone &right); 
  
struct ExcState_ExcNone {
    friend bool operator==(const ExcState_ExcNone &left, const ExcState_ExcNone &right); 
    friend bool operator!=(const ExcState_ExcNone &left, const ExcState_ExcNone &right) { return !(left == right); } 
  };
  
struct ExcState_ExcClaim;
  
bool operator==(const ExcState_ExcClaim &left, const ExcState_ExcClaim &right); 
  
struct ExcState_ExcClaim {
    CacheHandle_Compile::Handle b;
    friend bool operator==(const ExcState_ExcClaim &left, const ExcState_ExcClaim &right); 
    friend bool operator!=(const ExcState_ExcClaim &left, const ExcState_ExcClaim &right) { return !(left == right); } 
  };
  
struct ExcState_ExcPendingAwaitWriteback;
  
bool operator==(const ExcState_ExcPendingAwaitWriteback &left, const ExcState_ExcPendingAwaitWriteback &right); 
  
struct ExcState_ExcPendingAwaitWriteback {
    CacheHandle_Compile::Handle b;
    friend bool operator==(const ExcState_ExcPendingAwaitWriteback &left, const ExcState_ExcPendingAwaitWriteback &right); 
    friend bool operator!=(const ExcState_ExcPendingAwaitWriteback &left, const ExcState_ExcPendingAwaitWriteback &right) { return !(left == right); } 
  };
  
struct ExcState_ExcPending;
  
bool operator==(const ExcState_ExcPending &left, const ExcState_ExcPending &right); 
  
struct ExcState_ExcPending {
    bool clean;
    CacheHandle_Compile::Handle b;
    friend bool operator==(const ExcState_ExcPending &left, const ExcState_ExcPending &right); 
    friend bool operator!=(const ExcState_ExcPending &left, const ExcState_ExcPending &right) { return !(left == right); } 
  };
  
struct ExcState_ExcObtained;
  
bool operator==(const ExcState_ExcObtained &left, const ExcState_ExcObtained &right); 
  
struct ExcState_ExcObtained {
    bool clean;
    friend bool operator==(const ExcState_ExcObtained &left, const ExcState_ExcObtained &right); 
    friend bool operator!=(const ExcState_ExcObtained &left, const ExcState_ExcObtained &right) { return !(left == right); } 
  };
  
struct ExcState {
    std::variant<ExcState_ExcNone, ExcState_ExcClaim, ExcState_ExcPendingAwaitWriteback, ExcState_ExcPending, ExcState_ExcObtained> v;
    static ExcState create_ExcNone() {
      ExcState COMPILER_result;
      ExcState_ExcNone COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static ExcState create_ExcClaim(CacheHandle_Compile::Handle b) {
      ExcState COMPILER_result;
      ExcState_ExcClaim COMPILER_result_subStruct;
      COMPILER_result_subStruct.b = b;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static ExcState create_ExcPendingAwaitWriteback(CacheHandle_Compile::Handle b) {
      ExcState COMPILER_result;
      ExcState_ExcPendingAwaitWriteback COMPILER_result_subStruct;
      COMPILER_result_subStruct.b = b;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static ExcState create_ExcPending(bool clean, CacheHandle_Compile::Handle b) {
      ExcState COMPILER_result;
      ExcState_ExcPending COMPILER_result_subStruct;
      COMPILER_result_subStruct.clean = clean;
      COMPILER_result_subStruct.b = b;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static ExcState create_ExcObtained(bool clean) {
      ExcState COMPILER_result;
      ExcState_ExcObtained COMPILER_result_subStruct;
      COMPILER_result_subStruct.clean = clean;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    ExcState();
    ~ExcState() {}
    ExcState(const ExcState &other) {
      v = other.v;
    }
    ExcState& operator=(const ExcState other) {
      v = other.v;
      return *this;
    }
    bool is_ExcState_ExcNone() const { return std::holds_alternative<ExcState_ExcNone>(v); }
    bool is_ExcState_ExcClaim() const { return std::holds_alternative<ExcState_ExcClaim>(v); }
    bool is_ExcState_ExcPendingAwaitWriteback() const { return std::holds_alternative<ExcState_ExcPendingAwaitWriteback>(v); }
    bool is_ExcState_ExcPending() const { return std::holds_alternative<ExcState_ExcPending>(v); }
    bool is_ExcState_ExcObtained() const { return std::holds_alternative<ExcState_ExcObtained>(v); }
    ExcState* operator->() { return this; }
    friend bool operator==(const ExcState &left, const ExcState &right) { 
    	return left.v == right.v;
}
    CacheHandle_Compile::Handle& dtor_b() {
      if (is_ExcState_ExcClaim()) { return std::get<ExcState_ExcClaim>(v).b; }
      if (is_ExcState_ExcPendingAwaitWriteback()) { return std::get<ExcState_ExcPendingAwaitWriteback>(v).b; }
      return std::get<ExcState_ExcPending>(v).b; 
    }
    bool& dtor_clean() {
      if (is_ExcState_ExcPending()) { return std::get<ExcState_ExcPending>(v).clean; }
      return std::get<ExcState_ExcObtained>(v).clean; 
    }
    friend bool operator!=(const ExcState &left, const ExcState &right) { return !(left == right); } 
  };
  
inline bool is_ExcState_ExcNone(const struct ExcState d);
  
inline bool is_ExcState_ExcClaim(const struct ExcState d);
  
inline bool is_ExcState_ExcPendingAwaitWriteback(const struct ExcState d);
  
inline bool is_ExcState_ExcPending(const struct ExcState d);
  
inline bool is_ExcState_ExcObtained(const struct ExcState d);
  
bool operator==(const WritebackState &left, const WritebackState &right); 
  
struct WritebackState_WritebackNone;
  
bool operator==(const WritebackState_WritebackNone &left, const WritebackState_WritebackNone &right); 
  
struct WritebackState_WritebackNone {
    friend bool operator==(const WritebackState_WritebackNone &left, const WritebackState_WritebackNone &right); 
    friend bool operator!=(const WritebackState_WritebackNone &left, const WritebackState_WritebackNone &right) { return !(left == right); } 
  };
  
struct WritebackState_WritebackObtained;
  
bool operator==(const WritebackState_WritebackObtained &left, const WritebackState_WritebackObtained &right); 
  
struct WritebackState_WritebackObtained {
    CacheHandle_Compile::Handle b;
    friend bool operator==(const WritebackState_WritebackObtained &left, const WritebackState_WritebackObtained &right); 
    friend bool operator!=(const WritebackState_WritebackObtained &left, const WritebackState_WritebackObtained &right) { return !(left == right); } 
  };
  
struct WritebackState {
    std::variant<WritebackState_WritebackNone, WritebackState_WritebackObtained> v;
    static WritebackState create_WritebackNone() {
      WritebackState COMPILER_result;
      WritebackState_WritebackNone COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static WritebackState create_WritebackObtained(CacheHandle_Compile::Handle b) {
      WritebackState COMPILER_result;
      WritebackState_WritebackObtained COMPILER_result_subStruct;
      COMPILER_result_subStruct.b = b;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    WritebackState();
    ~WritebackState() {}
    WritebackState(const WritebackState &other) {
      v = other.v;
    }
    WritebackState& operator=(const WritebackState other) {
      v = other.v;
      return *this;
    }
    bool is_WritebackState_WritebackNone() const { return std::holds_alternative<WritebackState_WritebackNone>(v); }
    bool is_WritebackState_WritebackObtained() const { return std::holds_alternative<WritebackState_WritebackObtained>(v); }
    WritebackState* operator->() { return this; }
    friend bool operator==(const WritebackState &left, const WritebackState &right) { 
    	return left.v == right.v;
}
    CacheHandle_Compile::Handle& dtor_b() {
      return std::get<WritebackState_WritebackObtained>(v).b; 
    }
    friend bool operator!=(const WritebackState &left, const WritebackState &right) { return !(left == right); } 
  };
  
inline bool is_WritebackState_WritebackNone(const struct WritebackState d);
  
inline bool is_WritebackState_WritebackObtained(const struct WritebackState d);
  
bool operator==(const ReadState &left, const ReadState &right); 
  
struct ReadState_ReadNone;
  
bool operator==(const ReadState_ReadNone &left, const ReadState_ReadNone &right); 
  
struct ReadState_ReadNone {
    friend bool operator==(const ReadState_ReadNone &left, const ReadState_ReadNone &right); 
    friend bool operator!=(const ReadState_ReadNone &left, const ReadState_ReadNone &right) { return !(left == right); } 
  };
  
struct ReadState_ReadPending;
  
bool operator==(const ReadState_ReadPending &left, const ReadState_ReadPending &right); 
  
struct ReadState_ReadPending {
    friend bool operator==(const ReadState_ReadPending &left, const ReadState_ReadPending &right); 
    friend bool operator!=(const ReadState_ReadPending &left, const ReadState_ReadPending &right) { return !(left == right); } 
  };
  
struct ReadState_ReadPendingCounted;
  
bool operator==(const ReadState_ReadPendingCounted &left, const ReadState_ReadPendingCounted &right); 
  
struct ReadState_ReadPendingCounted {
    friend bool operator==(const ReadState_ReadPendingCounted &left, const ReadState_ReadPendingCounted &right); 
    friend bool operator!=(const ReadState_ReadPendingCounted &left, const ReadState_ReadPendingCounted &right) { return !(left == right); } 
  };
  
struct ReadState_ReadObtained;
  
bool operator==(const ReadState_ReadObtained &left, const ReadState_ReadObtained &right); 
  
struct ReadState_ReadObtained {
    friend bool operator==(const ReadState_ReadObtained &left, const ReadState_ReadObtained &right); 
    friend bool operator!=(const ReadState_ReadObtained &left, const ReadState_ReadObtained &right) { return !(left == right); } 
  };
  
struct ReadState {
    std::variant<ReadState_ReadNone, ReadState_ReadPending, ReadState_ReadPendingCounted, ReadState_ReadObtained> v;
    static ReadState create_ReadNone() {
      ReadState COMPILER_result;
      ReadState_ReadNone COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static ReadState create_ReadPending() {
      ReadState COMPILER_result;
      ReadState_ReadPending COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static ReadState create_ReadPendingCounted() {
      ReadState COMPILER_result;
      ReadState_ReadPendingCounted COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static ReadState create_ReadObtained() {
      ReadState COMPILER_result;
      ReadState_ReadObtained COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    ReadState();
    ~ReadState() {}
    ReadState(const ReadState &other) {
      v = other.v;
    }
    ReadState& operator=(const ReadState other) {
      v = other.v;
      return *this;
    }
    bool is_ReadState_ReadNone() const { return std::holds_alternative<ReadState_ReadNone>(v); }
    bool is_ReadState_ReadPending() const { return std::holds_alternative<ReadState_ReadPending>(v); }
    bool is_ReadState_ReadPendingCounted() const { return std::holds_alternative<ReadState_ReadPendingCounted>(v); }
    bool is_ReadState_ReadObtained() const { return std::holds_alternative<ReadState_ReadObtained>(v); }
    ReadState* operator->() { return this; }
    friend bool operator==(const ReadState &left, const ReadState &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const ReadState &left, const ReadState &right) { return !(left == right); } 
  };
  
inline bool is_ReadState_ReadNone(const struct ReadState d);
  
inline bool is_ReadState_ReadPending(const struct ReadState d);
  
inline bool is_ReadState_ReadPendingCounted(const struct ReadState d);
  
inline bool is_ReadState_ReadObtained(const struct ReadState d);
  
bool operator==(const CentralState &left, const CentralState &right); 
  
struct CentralState_CentralNone;
  
bool operator==(const CentralState_CentralNone &left, const CentralState_CentralNone &right); 
  
struct CentralState_CentralNone {
    friend bool operator==(const CentralState_CentralNone &left, const CentralState_CentralNone &right); 
    friend bool operator!=(const CentralState_CentralNone &left, const CentralState_CentralNone &right) { return !(left == right); } 
  };
  
struct CentralState_CentralState;
  
bool operator==(const CentralState_CentralState &left, const CentralState_CentralState &right); 
  
struct CentralState_CentralState {
    RwLock_Compile::Flag flag;
    CacheHandle_Compile::Handle stored__value;
    friend bool operator==(const CentralState_CentralState &left, const CentralState_CentralState &right); 
    friend bool operator!=(const CentralState_CentralState &left, const CentralState_CentralState &right) { return !(left == right); } 
  };
  
struct CentralState {
    std::variant<CentralState_CentralNone, CentralState_CentralState> v;
    static CentralState create_CentralNone() {
      CentralState COMPILER_result;
      CentralState_CentralNone COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static CentralState create_CentralState(RwLock_Compile::Flag flag, CacheHandle_Compile::Handle stored__value) {
      CentralState COMPILER_result;
      CentralState_CentralState COMPILER_result_subStruct;
      COMPILER_result_subStruct.flag = flag;
      COMPILER_result_subStruct.stored__value = stored__value;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    CentralState();
    ~CentralState() {}
    CentralState(const CentralState &other) {
      v = other.v;
    }
    CentralState& operator=(const CentralState other) {
      v = other.v;
      return *this;
    }
    bool is_CentralState_CentralNone() const { return std::holds_alternative<CentralState_CentralNone>(v); }
    bool is_CentralState_CentralState() const { return std::holds_alternative<CentralState_CentralState>(v); }
    CentralState* operator->() { return this; }
    friend bool operator==(const CentralState &left, const CentralState &right) { 
    	return left.v == right.v;
}
    RwLock_Compile::Flag& dtor_flag() {
      return std::get<CentralState_CentralState>(v).flag; 
    }
    CacheHandle_Compile::Handle& dtor_stored__value() {
      return std::get<CentralState_CentralState>(v).stored__value; 
    }
    friend bool operator!=(const CentralState &left, const CentralState &right) { return !(left == right); } 
  };
  
inline bool is_CentralState_CentralNone(const struct CentralState d);
  
inline bool is_CentralState_CentralState(const struct CentralState d);
  
bool operator==(const M &left, const M &right); 
  
struct M_M;
  
bool operator==(const M_M &left, const M_M &right); 
  
struct M_M {
    RwLock_Compile::CentralState central;
    RwLock_Compile::ExcState exc;
    RwLock_Compile::ReadState read;
    RwLock_Compile::WritebackState writeback;
    friend bool operator==(const M_M &left, const M_M &right); 
    friend bool operator!=(const M_M &left, const M_M &right) { return !(left == right); } 
  };
  
struct M_Fail;
  
bool operator==(const M_Fail &left, const M_Fail &right); 
  
struct M_Fail {
    friend bool operator==(const M_Fail &left, const M_Fail &right); 
    friend bool operator!=(const M_Fail &left, const M_Fail &right) { return !(left == right); } 
  };
  
struct M {
    std::variant<M_M, M_Fail> v;
    static M create_M(RwLock_Compile::CentralState central, RwLock_Compile::ExcState exc, RwLock_Compile::ReadState read, RwLock_Compile::WritebackState writeback) {
      M COMPILER_result;
      M_M COMPILER_result_subStruct;
      COMPILER_result_subStruct.central = central;
      COMPILER_result_subStruct.exc = exc;
      COMPILER_result_subStruct.read = read;
      COMPILER_result_subStruct.writeback = writeback;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static M create_Fail() {
      M COMPILER_result;
      M_Fail COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    M();
    ~M() {}
    M(const M &other) {
      v = other.v;
    }
    M& operator=(const M other) {
      v = other.v;
      return *this;
    }
    bool is_M_M() const { return std::holds_alternative<M_M>(v); }
    bool is_M_Fail() const { return std::holds_alternative<M_Fail>(v); }
    M* operator->() { return this; }
    friend bool operator==(const M &left, const M &right) { 
    	return left.v == right.v;
}
    RwLock_Compile::CentralState& dtor_central() {
      return std::get<M_M>(v).central; 
    }
    RwLock_Compile::ExcState& dtor_exc() {
      return std::get<M_M>(v).exc; 
    }
    RwLock_Compile::ReadState& dtor_read() {
      return std::get<M_M>(v).read; 
    }
    RwLock_Compile::WritebackState& dtor_writeback() {
      return std::get<M_M>(v).writeback; 
    }
    friend bool operator!=(const M &left, const M &right) { return !(left == right); } 
  };
  
inline bool is_M_M(const struct M d);
  
inline bool is_M_Fail(const struct M d);
}// end of namespace RwLock_Compile  datatype declarations
namespace Rw_PCMWrap_ON_RwLock__Compile  {
  
bool operator==(const M &left, const M &right); 
  
struct M {
    M();
    M* operator->() { return this; }
    friend bool operator==(const M &left, const M &right);
    friend bool operator!=(const M &left, const M &right) { return !(left == right); } 
  };
  
inline bool is_M(const struct M d) { (void) d; return true; }
}// end of namespace Rw_PCMWrap_ON_RwLock__Compile  datatype declarations
namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {
  
bool operator==(const Token &left, const Token &right); 
  
struct Token {
    Token();
    Token* operator->() { return this; }
    friend bool operator==(const Token &left, const Token &right);
    friend bool operator!=(const Token &left, const Token &right) { return !(left == right); } 
  };
  
inline bool is_Token(const struct Token d) { (void) d; return true; }
}// end of namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile  datatype declarations
namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {
}// end of namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile  datatype declarations
namespace Rw_PCMExt_ON_RwLock__Compile  {
}// end of namespace Rw_PCMExt_ON_RwLock__Compile  datatype declarations
namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile  {
  
bool operator==(const Token &left, const Token &right); 
  
struct Token {
    Token();
    Token* operator->() { return this; }
    friend bool operator==(const Token &left, const Token &right);
    friend bool operator!=(const Token &left, const Token &right) { return !(left == right); } 
  };
  
inline bool is_Token(const struct Token d) { (void) d; return true; }
}// end of namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile  datatype declarations
namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile  {
}// end of namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile  datatype declarations
namespace RwTokens_ON_RwLock__Compile  {
}// end of namespace RwTokens_ON_RwLock__Compile  datatype declarations
namespace RwLockToken_Compile  {
  
bool operator==(const CentralToken &left, const CentralToken &right); 
  
struct CentralToken {
    CentralToken();
    CentralToken* operator->() { return this; }
    friend bool operator==(const CentralToken &left, const CentralToken &right);
    friend bool operator!=(const CentralToken &left, const CentralToken &right) { return !(left == right); } 
  };
  
inline bool is_CentralToken(const struct CentralToken d) { (void) d; return true; }
  
bool operator==(const WritebackObtainedToken &left, const WritebackObtainedToken &right); 
  
struct WritebackObtainedToken {
    WritebackObtainedToken();
    WritebackObtainedToken* operator->() { return this; }
    friend bool operator==(const WritebackObtainedToken &left, const WritebackObtainedToken &right);
    friend bool operator!=(const WritebackObtainedToken &left, const WritebackObtainedToken &right) { return !(left == right); } 
  };
  
inline bool is_WritebackObtainedToken(const struct WritebackObtainedToken d) { (void) d; return true; }
  
bool operator==(const SharedPendingToken &left, const SharedPendingToken &right); 
  
struct SharedPendingToken {
    SharedPendingToken();
    SharedPendingToken* operator->() { return this; }
    friend bool operator==(const SharedPendingToken &left, const SharedPendingToken &right);
    friend bool operator!=(const SharedPendingToken &left, const SharedPendingToken &right) { return !(left == right); } 
  };
  
inline bool is_SharedToken(const struct SharedPendingToken d) { (void) d; return true; }
  
bool operator==(const SharedPending2Token &left, const SharedPending2Token &right); 
  
struct SharedPending2Token {
    SharedPending2Token();
    SharedPending2Token* operator->() { return this; }
    friend bool operator==(const SharedPending2Token &left, const SharedPending2Token &right);
    friend bool operator!=(const SharedPending2Token &left, const SharedPending2Token &right) { return !(left == right); } 
  };
  
inline bool is_SharedToken(const struct SharedPending2Token d) { (void) d; return true; }
  
bool operator==(const SharedObtainedToken &left, const SharedObtainedToken &right); 
  
struct SharedObtainedToken {
    SharedObtainedToken();
    SharedObtainedToken* operator->() { return this; }
    friend bool operator==(const SharedObtainedToken &left, const SharedObtainedToken &right);
    friend bool operator!=(const SharedObtainedToken &left, const SharedObtainedToken &right) { return !(left == right); } 
  };
  
inline bool is_SharedObtainedToken(const struct SharedObtainedToken d) { (void) d; return true; }
}// end of namespace RwLockToken_Compile  datatype declarations
namespace GlinearMap_Compile  {
}// end of namespace GlinearMap_Compile  datatype declarations
namespace CacheAIOParams_Compile  {
  
bool operator==(const IOSlotAccess &left, const IOSlotAccess &right); 
  
struct IOSlotAccess {
    IOSlotAccess();
    IOSlotAccess* operator->() { return this; }
    friend bool operator==(const IOSlotAccess &left, const IOSlotAccess &right);
    friend bool operator!=(const IOSlotAccess &left, const IOSlotAccess &right) { return !(left == right); } 
  };
  
inline bool is_IOSlotAccess(const struct IOSlotAccess d) { (void) d; return true; }
  
bool operator==(const ReadG &left, const ReadG &right); 
  
struct ReadG {
    ReadG();
    ReadG* operator->() { return this; }
    friend bool operator==(const ReadG &left, const ReadG &right);
    friend bool operator!=(const ReadG &left, const ReadG &right) { return !(left == right); } 
  };
  
inline bool is_ReadG(const struct ReadG d) { (void) d; return true; }
  
bool operator==(const ReadvG &left, const ReadvG &right); 
  
struct ReadvG {
    ReadvG();
    ReadvG* operator->() { return this; }
    friend bool operator==(const ReadvG &left, const ReadvG &right);
    friend bool operator!=(const ReadvG &left, const ReadvG &right) { return !(left == right); } 
  };
  
inline bool is_ReadvG(const struct ReadvG d) { (void) d; return true; }
  
bool operator==(const WriteG &left, const WriteG &right); 
  
struct WriteG {
    WriteG();
    WriteG* operator->() { return this; }
    friend bool operator==(const WriteG &left, const WriteG &right);
    friend bool operator!=(const WriteG &left, const WriteG &right) { return !(left == right); } 
  };
  
inline bool is_WriteG(const struct WriteG d) { (void) d; return true; }
  
bool operator==(const WritevG &left, const WritevG &right); 
  
struct WritevG {
    WritevG();
    WritevG* operator->() { return this; }
    friend bool operator==(const WritevG &left, const WritevG &right);
    friend bool operator!=(const WritevG &left, const WritevG &right) { return !(left == right); } 
  };
  
inline bool is_WritevG(const struct WritevG d) { (void) d; return true; }
}// end of namespace CacheAIOParams_Compile  datatype declarations
namespace BitOps_Compile  {
}// end of namespace BitOps_Compile  datatype declarations
namespace Atomics  {
}// end of namespace Atomics  datatype declarations
namespace CounterPCM_Compile  {
  
bool operator==(const M &left, const M &right); 
  
struct M {
    M();
    M* operator->() { return this; }
    friend bool operator==(const M &left, const M &right);
    friend bool operator!=(const M &left, const M &right) { return !(left == right); } 
  };
  
inline bool is_Counter(const struct M d) { (void) d; return true; }
}// end of namespace CounterPCM_Compile  datatype declarations
namespace Tokens_ON_CounterPCM__Compile  {
  
bool operator==(const Token &left, const Token &right); 
  
struct Token {
    Token();
    Token* operator->() { return this; }
    friend bool operator==(const Token &left, const Token &right);
    friend bool operator!=(const Token &left, const Token &right) { return !(left == right); } 
  };
  
inline bool is_Token(const struct Token d) { (void) d; return true; }
}// end of namespace Tokens_ON_CounterPCM__Compile  datatype declarations
namespace ClientCounter_Compile  {
  
bool operator==(const Client &left, const Client &right); 
  
struct Client {
    Client();
    Client* operator->() { return this; }
    friend bool operator==(const Client &left, const Client &right);
    friend bool operator!=(const Client &left, const Client &right) { return !(left == right); } 
  };
  
inline bool is_Client(const struct Client d) { (void) d; return true; }
  
bool operator==(const Clients &left, const Clients &right); 
  
struct Clients {
    Clients();
    Clients* operator->() { return this; }
    friend bool operator==(const Clients &left, const Clients &right);
    friend bool operator!=(const Clients &left, const Clients &right) { return !(left == right); } 
  };
  
inline bool is_Clients(const struct Clients d) { (void) d; return true; }
}// end of namespace ClientCounter_Compile  datatype declarations
namespace AtomicRefcountImpl_Compile  {
  
bool operator==(const RG &left, const RG &right); 
  
struct RG {
    RG();
    RG* operator->() { return this; }
    friend bool operator==(const RG &left, const RG &right);
    friend bool operator!=(const RG &left, const RG &right) { return !(left == right); } 
  };
  
inline bool is_RG(const struct RG d) { (void) d; return true; }
  
bool operator==(const AtomicRefcount &left, const AtomicRefcount &right); 
  
struct AtomicRefcount {
    Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG>  a;
    AtomicRefcount(Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG>  a) : a (a) {}
    AtomicRefcount();
    AtomicRefcount* operator->() { return this; }
    friend bool operator==(const AtomicRefcount &left, const AtomicRefcount &right);
    friend bool operator!=(const AtomicRefcount &left, const AtomicRefcount &right) { return !(left == right); } 
  };
  
inline bool is_AtomicRefcount(const struct AtomicRefcount d) { (void) d; return true; }
}// end of namespace AtomicRefcountImpl_Compile  datatype declarations
namespace AtomicIndexLookupImpl_Compile  {
}// end of namespace AtomicIndexLookupImpl_Compile  datatype declarations
namespace AtomicStatusImpl_Compile  {
  
bool operator==(const G &left, const G &right); 
  
struct G {
    G();
    G* operator->() { return this; }
    friend bool operator==(const G &left, const G &right);
    friend bool operator!=(const G &left, const G &right) { return !(left == right); } 
  };
  
inline bool is_G(const struct G d) { (void) d; return true; }
  
bool operator==(const AtomicStatus &left, const AtomicStatus &right); 
  
struct AtomicStatus {
    Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G>  atomic;
    AtomicStatus(Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G>  atomic) : atomic (atomic) {}
    AtomicStatus();
    AtomicStatus* operator->() { return this; }
    friend bool operator==(const AtomicStatus &left, const AtomicStatus &right);
    friend bool operator!=(const AtomicStatus &left, const AtomicStatus &right) { return !(left == right); } 
    bool try__acquire__writeback(bool with__access);
    void release__writeback();
    struct Tuple<bool, bool> try__check__writeback__isnt__set();
    bool try__alloc();
    void clear__exc__bit__during__load__phase();
    void load__phase__finish();
    void load__phase__finish__threadless();
    bool quicktest__is__exc__locked();
    struct Tuple<bool, bool, bool> is__exc__locked__or__free();
    void mark__accessed();
    void clear__accessed();
    bool is__reading();
    bool take__exc__if__eq__clean();
    void set__to__free();
    void set__to__free2();
    void abandon__exc();
    void abandon__reading__pending();
    void mark__dirty();
    bool try__set__claim();
    void unset__claim();
    void set__exc();
    void unset__exc();
    void read2exc__noop();
  };
  
inline bool is_AtomicStatus(const struct AtomicStatus d) { (void) d; return true; }
}// end of namespace AtomicStatusImpl_Compile  datatype declarations
namespace BasicLockImpl_Compile  {
  template <typename G>
bool operator==(const pre__BasicLock<G> &left, const pre__BasicLock<G> &right); 
  template <typename G>
struct pre__BasicLock {
    Atomics::Atomic <bool, GlinearOption_Compile::glOption <G> >  a;
    pre__BasicLock(Atomics::Atomic <bool, GlinearOption_Compile::glOption <G> >  a) : a (a) {}
    pre__BasicLock();
    pre__BasicLock* operator->() { return this; }
    friend bool operator==<G>(const pre__BasicLock &left, const pre__BasicLock &right);
    friend bool operator!=(const pre__BasicLock &left, const pre__BasicLock &right) { return !(left == right); } 
  };
  template <typename G>
inline bool is_BasicLock(const struct pre__BasicLock<G> d) { (void) d; return true; }
}// end of namespace BasicLockImpl_Compile  datatype declarations
namespace LinearMaybe  {
}// end of namespace LinearMaybe  datatype declarations
namespace LinearExtern  {
}// end of namespace LinearExtern  datatype declarations
namespace LinearSequence__i_Compile  {
}// end of namespace LinearSequence__i_Compile  datatype declarations
namespace ThreadUtils  {
}// end of namespace ThreadUtils  datatype declarations
namespace MemSplit_Compile  {
}// end of namespace MemSplit_Compile  datatype declarations
namespace InstantiatedDiskInterface  {
  
bool operator==(const FinishedReq &left, const FinishedReq &right); 
  
struct FinishedReq_FRNone;
  
bool operator==(const FinishedReq_FRNone &left, const FinishedReq_FRNone &right); 
  
struct FinishedReq_FRNone {
    friend bool operator==(const FinishedReq_FRNone &left, const FinishedReq_FRNone &right); 
    friend bool operator!=(const FinishedReq_FRNone &left, const FinishedReq_FRNone &right) { return !(left == right); } 
  };
  
struct FinishedReq_FRWrite;
  
bool operator==(const FinishedReq_FRWrite &left, const FinishedReq_FRWrite &right); 
  
struct FinishedReq_FRWrite {
    friend bool operator==(const FinishedReq_FRWrite &left, const FinishedReq_FRWrite &right); 
    friend bool operator!=(const FinishedReq_FRWrite &left, const FinishedReq_FRWrite &right) { return !(left == right); } 
  };
  
struct FinishedReq_FRWritev;
  
bool operator==(const FinishedReq_FRWritev &left, const FinishedReq_FRWritev &right); 
  
struct FinishedReq_FRWritev {
    friend bool operator==(const FinishedReq_FRWritev &left, const FinishedReq_FRWritev &right); 
    friend bool operator!=(const FinishedReq_FRWritev &left, const FinishedReq_FRWritev &right) { return !(left == right); } 
  };
  
struct FinishedReq_FRRead;
  
bool operator==(const FinishedReq_FRRead &left, const FinishedReq_FRRead &right); 
  
struct FinishedReq_FRRead {
    friend bool operator==(const FinishedReq_FRRead &left, const FinishedReq_FRRead &right); 
    friend bool operator!=(const FinishedReq_FRRead &left, const FinishedReq_FRRead &right) { return !(left == right); } 
  };
  
struct FinishedReq_FRReadv;
  
bool operator==(const FinishedReq_FRReadv &left, const FinishedReq_FRReadv &right); 
  
struct FinishedReq_FRReadv {
    friend bool operator==(const FinishedReq_FRReadv &left, const FinishedReq_FRReadv &right); 
    friend bool operator!=(const FinishedReq_FRReadv &left, const FinishedReq_FRReadv &right) { return !(left == right); } 
  };
  
struct FinishedReq {
    std::variant<FinishedReq_FRNone, FinishedReq_FRWrite, FinishedReq_FRWritev, FinishedReq_FRRead, FinishedReq_FRReadv> v;
    static FinishedReq create_FRNone() {
      FinishedReq COMPILER_result;
      FinishedReq_FRNone COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static FinishedReq create_FRWrite() {
      FinishedReq COMPILER_result;
      FinishedReq_FRWrite COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static FinishedReq create_FRWritev() {
      FinishedReq COMPILER_result;
      FinishedReq_FRWritev COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static FinishedReq create_FRRead() {
      FinishedReq COMPILER_result;
      FinishedReq_FRRead COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static FinishedReq create_FRReadv() {
      FinishedReq COMPILER_result;
      FinishedReq_FRReadv COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    FinishedReq();
    ~FinishedReq() {}
    FinishedReq(const FinishedReq &other) {
      v = other.v;
    }
    FinishedReq& operator=(const FinishedReq other) {
      v = other.v;
      return *this;
    }
    bool is_FinishedReq_FRNone() const { return std::holds_alternative<FinishedReq_FRNone>(v); }
    bool is_FinishedReq_FRWrite() const { return std::holds_alternative<FinishedReq_FRWrite>(v); }
    bool is_FinishedReq_FRWritev() const { return std::holds_alternative<FinishedReq_FRWritev>(v); }
    bool is_FinishedReq_FRRead() const { return std::holds_alternative<FinishedReq_FRRead>(v); }
    bool is_FinishedReq_FRReadv() const { return std::holds_alternative<FinishedReq_FRReadv>(v); }
    FinishedReq* operator->() { return this; }
    friend bool operator==(const FinishedReq &left, const FinishedReq &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const FinishedReq &left, const FinishedReq &right) { return !(left == right); } 
  };
  
inline bool is_FinishedReq_FRNone(const struct FinishedReq d);
  
inline bool is_FinishedReq_FRWrite(const struct FinishedReq d);
  
inline bool is_FinishedReq_FRWritev(const struct FinishedReq d);
  
inline bool is_FinishedReq_FRRead(const struct FinishedReq d);
  
inline bool is_FinishedReq_FRReadv(const struct FinishedReq d);
}// end of namespace InstantiatedDiskInterface  datatype declarations
namespace CacheTypes_ON_TheAIO__Compile  {
  
bool operator==(const NullGhostType &left, const NullGhostType &right); 
  
struct NullGhostType {
    NullGhostType();
    NullGhostType* operator->() { return this; }
    friend bool operator==(const NullGhostType &left, const NullGhostType &right);
    friend bool operator!=(const NullGhostType &left, const NullGhostType &right) { return !(left == right); } 
  };
  
inline bool is_NullGhostType(const struct NullGhostType d) { (void) d; return true; }
  
bool operator==(const StatusIdx &left, const StatusIdx &right); 
  
struct StatusIdx {
    AtomicStatusImpl_Compile::AtomicStatus status;
    Cells::Cell <CacheHandle_Compile::PageHandle>  page__handle;
    StatusIdx(AtomicStatusImpl_Compile::AtomicStatus status, Cells::Cell <CacheHandle_Compile::PageHandle>  page__handle) : status (status),  page__handle (page__handle) {}
    StatusIdx();
    StatusIdx* operator->() { return this; }
    friend bool operator==(const StatusIdx &left, const StatusIdx &right);
    friend bool operator!=(const StatusIdx &left, const StatusIdx &right) { return !(left == right); } 
  };
  
inline bool is_StatusIdx(const struct StatusIdx d) { (void) d; return true; }
  
bool operator==(const Cache &left, const Cache &right); 
  
struct Cache {
    Constants_Compile::Config config;
    Ptrs::Ptr data__base__ptr;
    Ptrs::Ptr iocb__base__ptr;
    LinearExtern::lseq <AtomicRefcountImpl_Compile::AtomicRefcount>  read__refcounts__array;
    LinearExtern::lseq <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> >  cache__idx__of__page__array;
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::StatusIdx>  status__idx__array;
    Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  global__clockpointer;
    Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  req__hand__base;
    LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  batch__busy;
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot>  io__slots;
    InstantiatedDiskInterface::IOCtx ioctx;
    Cache(Constants_Compile::Config config, Ptrs::Ptr data__base__ptr, Ptrs::Ptr iocb__base__ptr, LinearExtern::lseq <AtomicRefcountImpl_Compile::AtomicRefcount>  read__refcounts__array, LinearExtern::lseq <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> >  cache__idx__of__page__array, LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::StatusIdx>  status__idx__array, Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  global__clockpointer, Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  req__hand__base, LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  batch__busy, LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot>  io__slots, InstantiatedDiskInterface::IOCtx ioctx) : config (config),  data__base__ptr (data__base__ptr),  iocb__base__ptr (iocb__base__ptr),  read__refcounts__array (read__refcounts__array),  cache__idx__of__page__array (cache__idx__of__page__array),  status__idx__array (status__idx__array),  global__clockpointer (global__clockpointer),  req__hand__base (req__hand__base),  batch__busy (batch__busy),  io__slots (io__slots),  ioctx (ioctx) {}
    Cache();
    Cache* operator->() { return this; }
    friend bool operator==(const Cache &left, const Cache &right);
    friend bool operator!=(const Cache &left, const Cache &right) { return !(left == right); } 
    Ptrs::Ptr data__ptr(uint32 i);AtomicStatusImpl_Compile::AtomicStatus* status__atomic(uint32 i);Cells::Cell <CacheHandle_Compile::PageHandle> * page__handle__ptr(uint32 i);AtomicRefcountImpl_Compile::AtomicRefcount* read__refcount__atomic(uint64 j, uint32 i);Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * cache__idx__of__page__atomic(uint64 i);  };
  
inline bool is_Cache(const struct Cache d) { (void) d; return true; }
  
bool operator==(const LocalState &left, const LocalState &right); 
  
struct LocalState {
    uint64 t;
    uint64 free__hand;
    uint64 io__slot__hand;
    LocalState(uint64 t, uint64 free__hand, uint64 io__slot__hand) : t (t),  free__hand (free__hand),  io__slot__hand (io__slot__hand) {}
    LocalState();
    LocalState* operator->() { return this; }
    friend bool operator==(const LocalState &left, const LocalState &right);
    friend bool operator!=(const LocalState &left, const LocalState &right) { return !(left == right); } 
  };
  
inline bool is_LocalState(const struct LocalState d) { (void) d; return true; }
  
bool operator==(const IOSlot &left, const IOSlot &right); 
  
struct IOSlot {
    Ptrs::Ptr iocb__ptr;
    Ptrs::Ptr iovec__ptr;
    BasicLockImpl_Compile::pre__BasicLock <CacheAIOParams_Compile::IOSlotAccess>  lock;
    IOSlot(Ptrs::Ptr iocb__ptr, Ptrs::Ptr iovec__ptr, BasicLockImpl_Compile::pre__BasicLock <CacheAIOParams_Compile::IOSlotAccess>  lock) : iocb__ptr (iocb__ptr),  iovec__ptr (iovec__ptr),  lock (lock) {}
    IOSlot();
    IOSlot* operator->() { return this; }
    friend bool operator==(const IOSlot &left, const IOSlot &right);
    friend bool operator!=(const IOSlot &left, const IOSlot &right) { return !(left == right); } 
  };
  
inline bool is_IOSlot(const struct IOSlot d) { (void) d; return true; }
}// end of namespace CacheTypes_ON_TheAIO__Compile  datatype declarations
namespace CacheIO_ON_TheAIO__Compile  {
}// end of namespace CacheIO_ON_TheAIO__Compile  datatype declarations
namespace CacheWritebackBatch_ON_TheAIO__Compile  {
}// end of namespace CacheWritebackBatch_ON_TheAIO__Compile  datatype declarations
namespace CacheOps_ON_TheAIO__Compile  {
  
bool operator==(const PageHandleIdx &left, const PageHandleIdx &right); 
  
struct PageHandleIdx {
    uint32 cache__idx;
    PageHandleIdx(uint32 cache__idx) : cache__idx (cache__idx) {}
    PageHandleIdx();
    PageHandleIdx* operator->() { return this; }
    friend bool operator==(const PageHandleIdx &left, const PageHandleIdx &right);
    friend bool operator!=(const PageHandleIdx &left, const PageHandleIdx &right) { return !(left == right); } 
  };
  
inline bool is_PageHandleIdx(const struct PageHandleIdx d) { (void) d; return true; }
  
bool operator==(const WriteablePageHandle &left, const WriteablePageHandle &right); 
  
struct WriteablePageHandle {
    WriteablePageHandle();
    WriteablePageHandle* operator->() { return this; }
    friend bool operator==(const WriteablePageHandle &left, const WriteablePageHandle &right);
    friend bool operator!=(const WriteablePageHandle &left, const WriteablePageHandle &right) { return !(left == right); } 
  };
  
inline bool is_WriteablePageHandle(const struct WriteablePageHandle d) { (void) d; return true; }
  
bool operator==(const ReadonlyPageHandle &left, const ReadonlyPageHandle &right); 
  
struct ReadonlyPageHandle {
    ReadonlyPageHandle();
    ReadonlyPageHandle* operator->() { return this; }
    friend bool operator==(const ReadonlyPageHandle &left, const ReadonlyPageHandle &right);
    friend bool operator!=(const ReadonlyPageHandle &left, const ReadonlyPageHandle &right) { return !(left == right); } 
  };
  
inline bool is_ReadonlyPageHandle(const struct ReadonlyPageHandle d) { (void) d; return true; }
  
bool operator==(const ClaimPageHandle &left, const ClaimPageHandle &right); 
  
struct ClaimPageHandle {
    ClaimPageHandle();
    ClaimPageHandle* operator->() { return this; }
    friend bool operator==(const ClaimPageHandle &left, const ClaimPageHandle &right);
    friend bool operator!=(const ClaimPageHandle &left, const ClaimPageHandle &right) { return !(left == right); } 
  };
  
inline bool is_ClaimPageHandle(const struct ClaimPageHandle d) { (void) d; return true; }
}// end of namespace CacheOps_ON_TheAIO__Compile  datatype declarations
namespace CacheInit_ON_TheAIO__Compile  {
}// end of namespace CacheInit_ON_TheAIO__Compile  datatype declarations
namespace Application_ON_TheAIO__Compile  {
}// end of namespace Application_ON_TheAIO__Compile  datatype declarations
namespace AsyncDisk_Compile  {
  
bool operator==(const Variables &left, const Variables &right); 
  
struct Variables {
    Variables();
    Variables* operator->() { return this; }
    friend bool operator==(const Variables &left, const Variables &right);
    friend bool operator!=(const Variables &left, const Variables &right) { return !(left == right); } 
  };
  
inline bool is_Variables(const struct Variables d) { (void) d; return true; }
  
bool operator==(const Step &left, const Step &right); 
  
struct Step_RecvReadStep;
  
bool operator==(const Step_RecvReadStep &left, const Step_RecvReadStep &right); 
  
struct Step_RecvReadStep {
    friend bool operator==(const Step_RecvReadStep &left, const Step_RecvReadStep &right); 
    friend bool operator!=(const Step_RecvReadStep &left, const Step_RecvReadStep &right) { return !(left == right); } 
  };
  
struct Step_RecvWriteStep;
  
bool operator==(const Step_RecvWriteStep &left, const Step_RecvWriteStep &right); 
  
struct Step_RecvWriteStep {
    friend bool operator==(const Step_RecvWriteStep &left, const Step_RecvWriteStep &right); 
    friend bool operator!=(const Step_RecvWriteStep &left, const Step_RecvWriteStep &right) { return !(left == right); } 
  };
  
struct Step_AckReadStep;
  
bool operator==(const Step_AckReadStep &left, const Step_AckReadStep &right); 
  
struct Step_AckReadStep {
    friend bool operator==(const Step_AckReadStep &left, const Step_AckReadStep &right); 
    friend bool operator!=(const Step_AckReadStep &left, const Step_AckReadStep &right) { return !(left == right); } 
  };
  
struct Step_AckWriteStep;
  
bool operator==(const Step_AckWriteStep &left, const Step_AckWriteStep &right); 
  
struct Step_AckWriteStep {
    friend bool operator==(const Step_AckWriteStep &left, const Step_AckWriteStep &right); 
    friend bool operator!=(const Step_AckWriteStep &left, const Step_AckWriteStep &right) { return !(left == right); } 
  };
  
struct Step {
    std::variant<Step_RecvReadStep, Step_RecvWriteStep, Step_AckReadStep, Step_AckWriteStep> v;
    static Step create_RecvReadStep() {
      Step COMPILER_result;
      Step_RecvReadStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_RecvWriteStep() {
      Step COMPILER_result;
      Step_RecvWriteStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_AckReadStep() {
      Step COMPILER_result;
      Step_AckReadStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static Step create_AckWriteStep() {
      Step COMPILER_result;
      Step_AckWriteStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    Step();
    ~Step() {}
    Step(const Step &other) {
      v = other.v;
    }
    Step& operator=(const Step other) {
      v = other.v;
      return *this;
    }
    bool is_Step_RecvReadStep() const { return std::holds_alternative<Step_RecvReadStep>(v); }
    bool is_Step_RecvWriteStep() const { return std::holds_alternative<Step_RecvWriteStep>(v); }
    bool is_Step_AckReadStep() const { return std::holds_alternative<Step_AckReadStep>(v); }
    bool is_Step_AckWriteStep() const { return std::holds_alternative<Step_AckWriteStep>(v); }
    Step* operator->() { return this; }
    friend bool operator==(const Step &left, const Step &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const Step &left, const Step &right) { return !(left == right); } 
  };
  
inline bool is_Step_RecvReadStep(const struct Step d);
  
inline bool is_Step_RecvWriteStep(const struct Step d);
  
inline bool is_Step_AckReadStep(const struct Step d);
  
inline bool is_Step_AckWriteStep(const struct Step d);
  
bool operator==(const InternalStep &left, const InternalStep &right); 
  
struct InternalStep_ProcessReadStep;
  
bool operator==(const InternalStep_ProcessReadStep &left, const InternalStep_ProcessReadStep &right); 
  
struct InternalStep_ProcessReadStep {
    friend bool operator==(const InternalStep_ProcessReadStep &left, const InternalStep_ProcessReadStep &right); 
    friend bool operator!=(const InternalStep_ProcessReadStep &left, const InternalStep_ProcessReadStep &right) { return !(left == right); } 
  };
  
struct InternalStep_ProcessWriteStep;
  
bool operator==(const InternalStep_ProcessWriteStep &left, const InternalStep_ProcessWriteStep &right); 
  
struct InternalStep_ProcessWriteStep {
    friend bool operator==(const InternalStep_ProcessWriteStep &left, const InternalStep_ProcessWriteStep &right); 
    friend bool operator!=(const InternalStep_ProcessWriteStep &left, const InternalStep_ProcessWriteStep &right) { return !(left == right); } 
  };
  
struct InternalStep_HavocConflictingWritesStep;
  
bool operator==(const InternalStep_HavocConflictingWritesStep &left, const InternalStep_HavocConflictingWritesStep &right); 
  
struct InternalStep_HavocConflictingWritesStep {
    friend bool operator==(const InternalStep_HavocConflictingWritesStep &left, const InternalStep_HavocConflictingWritesStep &right); 
    friend bool operator!=(const InternalStep_HavocConflictingWritesStep &left, const InternalStep_HavocConflictingWritesStep &right) { return !(left == right); } 
  };
  
struct InternalStep_HavocConflictingWriteReadStep;
  
bool operator==(const InternalStep_HavocConflictingWriteReadStep &left, const InternalStep_HavocConflictingWriteReadStep &right); 
  
struct InternalStep_HavocConflictingWriteReadStep {
    friend bool operator==(const InternalStep_HavocConflictingWriteReadStep &left, const InternalStep_HavocConflictingWriteReadStep &right); 
    friend bool operator!=(const InternalStep_HavocConflictingWriteReadStep &left, const InternalStep_HavocConflictingWriteReadStep &right) { return !(left == right); } 
  };
  
struct InternalStep {
    std::variant<InternalStep_ProcessReadStep, InternalStep_ProcessWriteStep, InternalStep_HavocConflictingWritesStep, InternalStep_HavocConflictingWriteReadStep> v;
    static InternalStep create_ProcessReadStep() {
      InternalStep COMPILER_result;
      InternalStep_ProcessReadStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static InternalStep create_ProcessWriteStep() {
      InternalStep COMPILER_result;
      InternalStep_ProcessWriteStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static InternalStep create_HavocConflictingWritesStep() {
      InternalStep COMPILER_result;
      InternalStep_HavocConflictingWritesStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    static InternalStep create_HavocConflictingWriteReadStep() {
      InternalStep COMPILER_result;
      InternalStep_HavocConflictingWriteReadStep COMPILER_result_subStruct;
      COMPILER_result.v = COMPILER_result_subStruct;
      return COMPILER_result;
    }
    InternalStep();
    ~InternalStep() {}
    InternalStep(const InternalStep &other) {
      v = other.v;
    }
    InternalStep& operator=(const InternalStep other) {
      v = other.v;
      return *this;
    }
    bool is_InternalStep_ProcessReadStep() const { return std::holds_alternative<InternalStep_ProcessReadStep>(v); }
    bool is_InternalStep_ProcessWriteStep() const { return std::holds_alternative<InternalStep_ProcessWriteStep>(v); }
    bool is_InternalStep_HavocConflictingWritesStep() const { return std::holds_alternative<InternalStep_HavocConflictingWritesStep>(v); }
    bool is_InternalStep_HavocConflictingWriteReadStep() const { return std::holds_alternative<InternalStep_HavocConflictingWriteReadStep>(v); }
    InternalStep* operator->() { return this; }
    friend bool operator==(const InternalStep &left, const InternalStep &right) { 
    	return left.v == right.v;
}
    friend bool operator!=(const InternalStep &left, const InternalStep &right) { return !(left == right); } 
  };
  
inline bool is_InternalStep_ProcessReadStep(const struct InternalStep d);
  
inline bool is_InternalStep_ProcessWriteStep(const struct InternalStep d);
  
inline bool is_InternalStep_HavocConflictingWritesStep(const struct InternalStep d);
  
inline bool is_InternalStep_HavocConflictingWriteReadStep(const struct InternalStep d);
}// end of namespace AsyncDisk_Compile  datatype declarations
namespace LinearCells  {
  template <typename V>
bool operator==(const LCellContents<V> &left, const LCellContents<V> &right); 
  template <typename V>
struct LCellContents {
    Options_Compile::Option <V>  v;
    LCellContents(Options_Compile::Option <V>  v) : v (v) {}
    LCellContents();
    LCellContents* operator->() { return this; }
    friend bool operator==<V>(const LCellContents &left, const LCellContents &right);
    friend bool operator!=(const LCellContents &left, const LCellContents &right) { return !(left == right); } 
  };
  template <typename V>
inline bool is_LCellContents(const struct LCellContents<V> d) { (void) d; return true; }
}// end of namespace LinearCells  datatype declarations
namespace _module  {
}// end of namespace _module  datatype declarations
namespace _System  {
}// end of namespace _System  class declarations
namespace NativeTypes_Compile  {
  class class_sbyte {
    public:
    // Default constructor
    class_sbyte() {}
    static int8 get_Default() {
      return 0;
    }
  };
  class class_byte {
    public:
    // Default constructor
    class_byte() {}
    static uint8 get_Default() {
      return 0;
    }
  };
  class class_int16 {
    public:
    // Default constructor
    class_int16() {}
    static int16 get_Default() {
      return 0;
    }
  };
  class class_uint16 {
    public:
    // Default constructor
    class_uint16() {}
    static uint16 get_Default() {
      return 0;
    }
  };
  class class_int32 {
    public:
    // Default constructor
    class_int32() {}
    static int32 get_Default() {
      return 0;
    }
  };
  class class_uint32 {
    public:
    // Default constructor
    class_uint32() {}
    static uint32 get_Default() {
      return 0;
    }
  };
  class class_int64 {
    public:
    // Default constructor
    class_int64() {}
    static int64 get_Default() {
      return 0;
    }
  };
  class class_uint64 {
    public:
    // Default constructor
    class_uint64() {}
    static uint64 get_Default() {
      return 0;
    }
  };
  class class_nat8 {
    public:
    // Default constructor
    class_nat8() {}
    static int8 get_Default() {
      return 0;
    }
  };
  class class_nat16 {
    public:
    // Default constructor
    class_nat16() {}
    static int16 get_Default() {
      return 0;
    }
  };
  class class_nat32 {
    public:
    // Default constructor
    class_nat32() {}
    static int32 get_Default() {
      return 0;
    }
  };
  class class_nat64 {
    public:
    // Default constructor
    class_nat64() {}
    static int64 get_Default() {
      return 0;
    }
  };
  class class_uint128 {
    public:
    // Default constructor
    class_uint128() {}
    static __m128i get_Default() {
      return _mm_setr_epi32(0,0,0,0);
    }
  };
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint64 Uint64Size();static uint64 Uint32Size();static uint64 Uint16Size();  };
}// end of namespace NativeTypes_Compile  class declarations
namespace Options_Compile  {
}// end of namespace Options_Compile  class declarations
namespace GlinearOption_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace GlinearOption_Compile  class declarations
namespace Ptrs  {
}// end of namespace Ptrs  class declarations
namespace PageSizeConstant_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint64 PageSize64();  };
}// end of namespace PageSizeConstant_Compile  class declarations
namespace IocbStruct  {
}// end of namespace IocbStruct  class declarations
namespace NonlinearLemmas_Compile  {
}// end of namespace NonlinearLemmas_Compile  class declarations
namespace Math_Compile  {
}// end of namespace Math_Compile  class declarations
namespace Constants_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint64 PLATFORM__CACHELINE__SIZE__64();static uint32 ENTRIES__PER__BATCH__32();static Constants_Compile::Config fromPreConfig(Constants_Compile::PreConfig pre);
    static uint32 CHUNK__SIZE__32();static uint64 AIO__HAND__BATCH__SIZE__64();static uint64 DEFAULT__MAX__IO__EVENTS__64();static uint64 RC__WIDTH__64();static uint64 CLEAN__AHEAD__64();static uint32 ref__internal(uint32 i);static uint64 rc__index(Constants_Compile::Config config, uint64 j, uint32 i);  };
}// end of namespace Constants_Compile  class declarations
namespace MapSum_Compile  {
}// end of namespace MapSum_Compile  class declarations
namespace FullMaps_Compile  {
  template <typename K>
  class class_FullMap {
    public:
    // Default constructor
    class_FullMap() {}
    static FullMap<K> get_Default() {
      return FullMaps_Compile::pre__FullMap<K>();
    }
  };
}// end of namespace FullMaps_Compile  class declarations
namespace GhostLoc_Compile  {
}// end of namespace GhostLoc_Compile  class declarations
namespace Cells  {
}// end of namespace Cells  class declarations
namespace RequestIds_Compile  {
}// end of namespace RequestIds_Compile  class declarations
namespace CacheStatusType_Compile  {
}// end of namespace CacheStatusType_Compile  class declarations
namespace DiskIfc_Compile  {
  class class_Block {
    public:
    // Default constructor
    class_Block() {}
    static Block get_Default() {
      return DafnySequence<uint8>();
    }
  };
}// end of namespace DiskIfc_Compile  class declarations
namespace CacheIfc_Compile  {
}// end of namespace CacheIfc_Compile  class declarations
namespace CacheSSM_Compile  {
}// end of namespace CacheSSM_Compile  class declarations
namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile  {
}// end of namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile  class declarations
namespace DiskSingletonLoc_Compile  {
}// end of namespace DiskSingletonLoc_Compile  class declarations
namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile  {
}// end of namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile  class declarations
namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile  {
}// end of namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile  class declarations
namespace DiskToken_ON_CacheIfc_CacheSSM__Compile  {
}// end of namespace DiskToken_ON_CacheIfc_CacheSSM__Compile  class declarations
namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile  class declarations
namespace CacheResources_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace CacheResources_Compile  class declarations
namespace CacheHandle_Compile  {
}// end of namespace CacheHandle_Compile  class declarations
namespace RwLock_Compile  {
}// end of namespace RwLock_Compile  class declarations
namespace Rw_PCMWrap_ON_RwLock__Compile  {
}// end of namespace Rw_PCMWrap_ON_RwLock__Compile  class declarations
namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {
}// end of namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile  class declarations
namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {
  class class_GToken {
    public:
    // Default constructor
    class_GToken() {}
    static GToken get_Default() {
      return Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile::Token();
    }
  };
}// end of namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile  class declarations
namespace Rw_PCMExt_ON_RwLock__Compile  {
}// end of namespace Rw_PCMExt_ON_RwLock__Compile  class declarations
namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile  {
}// end of namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile  class declarations
namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile  {
}// end of namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile  class declarations
namespace RwTokens_ON_RwLock__Compile  {
  class class_Token {
    public:
    // Default constructor
    class_Token() {}
    static Token get_Default() {
      return Tokens_ON_Rw__PCMExt__ON__RwLock____Compile::Token();
    }
  };
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace RwTokens_ON_RwLock__Compile  class declarations
namespace RwLockToken_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace RwLockToken_Compile  class declarations
namespace GlinearMap_Compile  {
}// end of namespace GlinearMap_Compile  class declarations
namespace CacheAIOParams_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace CacheAIOParams_Compile  class declarations
namespace BitOps_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint8 bit__or__uint8(uint8 a, uint8 b);static uint8 bit__and__uint8(uint8 a, uint8 b);static uint8 bit__xor__uint8(uint8 a, uint8 b);static uint64 bit__or__uint64(uint64 a, uint64 b);static uint64 bit__and__uint64(uint64 a, uint64 b);static uint64 bit__xor__uint64(uint64 a, uint64 b);  };
}// end of namespace BitOps_Compile  class declarations
namespace Atomics  {
}// end of namespace Atomics  class declarations
namespace CounterPCM_Compile  {
}// end of namespace CounterPCM_Compile  class declarations
namespace Tokens_ON_CounterPCM__Compile  {
}// end of namespace Tokens_ON_CounterPCM__Compile  class declarations
namespace ClientCounter_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace ClientCounter_Compile  class declarations
namespace AtomicRefcountImpl_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static bool is__refcount__eq(AtomicRefcountImpl_Compile::AtomicRefcount& a, uint8 val);
    static void inc__refcount__for__reading(AtomicRefcountImpl_Compile::AtomicRefcount& a);
    static void inc__refcount__for__shared(AtomicRefcountImpl_Compile::AtomicRefcount& a);
    static void inc__refcount__for__exc(AtomicRefcountImpl_Compile::AtomicRefcount& a);
    static void dec__refcount__for__shared__pending(AtomicRefcountImpl_Compile::AtomicRefcount& a);
    static void dec__refcount__for__shared__obtained(AtomicRefcountImpl_Compile::AtomicRefcount& a);
  };
}// end of namespace AtomicRefcountImpl_Compile  class declarations
namespace AtomicIndexLookupImpl_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint32 read__known__cache__idx(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a);
    static uint32 atomic__index__lookup__read(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a);
    static void atomic__index__lookup__clear__mapping(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a);
    static void atomic__index__lookup__clear__mapping__havoc(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a);
    static bool atomic__index__lookup__add__mapping(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a, uint64 disk__idx, uint32 cache__idx);
    static bool atomic__index__lookup__add__mapping__instant(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a, uint64 disk__idx, uint32 cache__idx);
    static uint32 init__NOT__MAPPED() {
      return (uint32)4294967295;
    }
    static uint32 NOT__MAPPED;
  };
}// end of namespace AtomicIndexLookupImpl_Compile  class declarations
namespace AtomicStatusImpl_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint8 flag__writeback();static uint8 flag__exc();static uint8 flag__accessed();static uint8 flag__unmapped();static uint8 flag__reading();static uint8 flag__clean();static uint8 flag__claim();  };
}// end of namespace AtomicStatusImpl_Compile  class declarations
namespace BasicLockImpl_Compile  {
  template <typename G>
  class class_BasicLock {
    public:
    // Default constructor
    class_BasicLock() {}
    static BasicLock<G> get_Default() {
      return BasicLockImpl_Compile::pre__BasicLock<G>();
    }
  };
  class __default {
    public:
    // Default constructor
    __default() {}
    template <typename __G>
    static bool try__acquire(BasicLockImpl_Compile::pre__BasicLock <__G> & l);
    template <typename __G>
    static void release(BasicLockImpl_Compile::pre__BasicLock <__G> & l);
    template <typename __G>
    static bool is__locked(BasicLockImpl_Compile::pre__BasicLock <__G> & l);
    template <typename __G>
    static BasicLockImpl_Compile::pre__BasicLock <__G>  new__basic__lock();
  };
}// end of namespace BasicLockImpl_Compile  class declarations
namespace LinearMaybe  {
}// end of namespace LinearMaybe  class declarations
namespace LinearExtern  {
}// end of namespace LinearExtern  class declarations
namespace LinearSequence__i_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    template <typename __A>
    static LinearExtern::linear_seq<__A> seq__alloc__init(uint64 length, __A a);template <typename __A>
    static uint64 lseq__length__as__uint64(LinearExtern::lseq <__A> & s);template <typename __A>
    static uint64 lseq__length__uint64(LinearExtern::lseq <__A> & s);
    template <typename __A>
    static __A* lseq__peek(LinearExtern::lseq <__A> & s, uint64 i);template <typename __A>
    static LinearExtern::lseq <__A>  lseq__alloc(uint64 length);
    template <typename __A>
    static LinearExtern::lseq <__A>  lseq__alloc__hugetables(uint64 length);
    template <typename __A>
    static void lseq__free(LinearExtern::lseq <__A>  s);
    template <typename __A>
    static Tuple0 lseq__free__fun(LinearExtern::lseq <__A>  s);template <typename __A>
    static struct Tuple<LinearExtern::lseq <__A> , __A> lseq__swap(LinearExtern::lseq <__A>  s1, uint64 i, __A a1);
    template <typename __A>
    static __A lseq__swap__inout(LinearExtern::lseq <__A> & s, uint64 i, __A a1);
    template <typename __A>
    static struct Tuple<LinearExtern::lseq <__A> , __A> lseq__take(LinearExtern::lseq <__A>  s1, uint64 i);
    template <typename __A>
    static __A lseq__take__inout(LinearExtern::lseq <__A> & s, uint64 i);
    template <typename __A>
    static Tuple <LinearExtern::lseq <__A> , __A>  lseq__take__fun(LinearExtern::lseq <__A>  s1, uint64 i);template <typename __A>
    static LinearExtern::lseq <__A>  lseq__give(LinearExtern::lseq <__A>  s1, uint64 i, __A a);
    template <typename __A>
    static void lseq__give__inout(LinearExtern::lseq <__A> & s1, uint64 i, __A a);
    template <typename __A>
    static void SeqCopy(LinearExtern::shared_seq<__A>& source, LinearExtern::linear_seq<__A>& dest, uint64 start, uint64 end, uint64 dest__start);
    template <typename __A>
    static LinearExtern::linear_seq<__A> AllocAndCopy(LinearExtern::shared_seq<__A>& source, uint64 from, uint64 to);
    template <typename __A>
    static struct Tuple<LinearExtern::lseq <__A> , LinearExtern::lseq <__A> > AllocAndMoveLseq(LinearExtern::lseq <__A>  source, uint64 from, uint64 to);
    template <typename __A>
    static LinearExtern::linear_seq<__A> SeqResize(LinearExtern::linear_seq<__A> s, uint64 newlen, __A a);
    template <typename __A>
    static void SeqResizeMut(LinearExtern::linear_seq<__A>& s, uint64 newlen, __A a);
    template <typename __A>
    static LinearExtern::linear_seq<__A> InsertSeq(LinearExtern::linear_seq<__A> s, __A a, uint64 pos);
    template <typename __A>
    static LinearExtern::lseq <__A>  InsertLSeq(LinearExtern::lseq <__A>  s, __A a, uint64 pos);
    template <typename __A>
    static struct Tuple<LinearExtern::lseq <__A> , __A> Replace1With2Lseq(LinearExtern::lseq <__A>  s, __A l, __A r, uint64 pos);
    template <typename __A>
    static __A Replace1With2Lseq__inout(LinearExtern::lseq <__A> & s, __A l, __A r, uint64 pos);
    template <typename __A>
    static void mut__seq__set(LinearExtern::linear_seq<__A>& s, uint64 i, __A a);
  };
}// end of namespace LinearSequence__i_Compile  class declarations
namespace ThreadUtils  {
}// end of namespace ThreadUtils  class declarations
namespace MemSplit_Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
  };
}// end of namespace MemSplit_Compile  class declarations
namespace InstantiatedDiskInterface  {
}// end of namespace InstantiatedDiskInterface  class declarations
namespace CacheTypes_ON_TheAIO__Compile  {
}// end of namespace CacheTypes_ON_TheAIO__Compile  class declarations
namespace CacheIO_ON_TheAIO__Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint64 get__free__io__slot(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local);
    static void disk__writeback__async(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__idx, uint32 cache__idx);
    static void disk__read__async(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__idx, uint32 cache__idx, Ptrs::Ptr ptr);
    static void disk__read__sync(uint64 disk__idx, Ptrs::Ptr ptr);
    static void disk__writeback__sync(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 disk__idx, Ptrs::Ptr ptr);
    static void disk__read__callback(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx);
    static void disk__writeback__callback(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx);
    static void disk__writeback__callback__vec(CacheTypes_ON_TheAIO__Compile::Cache& cache, Ptrs::Ptr iovec__ptr, uint64 iovec__len);
    static void disk__read__callback__vec(CacheTypes_ON_TheAIO__Compile::Cache& cache, Ptrs::Ptr iovec__ptr, uint64 iovec__len);
    static void io__cleanup(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 max__io__events);
    static void io__cleanup__all(CacheTypes_ON_TheAIO__Compile::Cache& cache);
    static uint32 cache__idx__of__data__ptr(CacheTypes_ON_TheAIO__Compile::Cache& cache, Ptrs::Ptr data__ptr);
    static bool io__cleanup__1(CacheTypes_ON_TheAIO__Compile::Cache& cache);
  };
}// end of namespace CacheIO_ON_TheAIO__Compile  class declarations
namespace CacheWritebackBatch_ON_TheAIO__Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static bool pages__share__extent(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 a, uint64 b);static uint64 walk__forward(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__addr, bool is__urgent);
    static uint64 walk__backward(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__addr, bool is__urgent);
    static void vec__writeback__async(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 start__addr, uint64 end__addr);
    static void batch__start__writeback(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint32 batch__idx, bool is__urgent);
  };
}// end of namespace CacheWritebackBatch_ON_TheAIO__Compile  class declarations
namespace CacheOps_ON_TheAIO__Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static uint8 try__get__read(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState);
    static void platform__sleep(uint64 ns);
    static uint8 get__read(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState);
    static bool try__take__read__lock__on__cache__entry(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, int64 expected__disk__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState);
    static void move__hand(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, bool is__urgent);
    static bool check__all__refcounts__dont__wait(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx);
    static void check__all__refcounts__with__t__block(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 t, uint32 cache__idx);
    static void try__evict__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx);
    static void evict__batch(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 chunk);
    static uint32 get__free__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState);
    static int64 try__take__read__lock__disk__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 disk__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState);
    static CacheOps_ON_TheAIO__Compile::PageHandleIdx get(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx);
    static void unget(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static bool claim(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static void unclaim(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static void lock(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static void unlock(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static CacheOps_ON_TheAIO__Compile::PageHandleIdx get__claim__lock(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx);
    static void mark__dirty(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static void page__sync__nonblocking(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static void page__sync__blocking(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph);
    static void evict__all(CacheTypes_ON_TheAIO__Compile::Cache& cache);
    static void flush(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local);
    static bool try__get__read__and__release(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState);
    static void prefetch__io(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 pages__in__req, uint64 addr, uint64 slot__idx, Ptrs::Ptr iovec__ptr);
    static void prefetch(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 base__addr);
    static struct Tuple<bool, CacheOps_ON_TheAIO__Compile::PageHandleIdx> alloc(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx);
    static void try__dealloc__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx);
    static void wait(CacheTypes_ON_TheAIO__Compile::Cache& cache);
  };
}// end of namespace CacheOps_ON_TheAIO__Compile  class declarations
namespace CacheInit_ON_TheAIO__Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  init__batch__busy(Constants_Compile::Config config);
    static struct Tuple<Ptrs::Ptr, LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot> > init__ioslots(Constants_Compile::Config config);
    static CacheTypes_ON_TheAIO__Compile::Cache init__cache(Constants_Compile::PreConfig preConfig);
    static CacheTypes_ON_TheAIO__Compile::LocalState init__thread__local__state(uint64 t);
  };
}// end of namespace CacheInit_ON_TheAIO__Compile  class declarations
namespace Application_ON_TheAIO__Compile  {
  class __default {
    public:
    // Default constructor
    __default() {}
    static DafnySequence<uint8> copy__seq__out(Ptrs::Ptr ptr);
    static void copy__seq__in(Ptrs::Ptr ptr, DafnySequence<uint8> data);
    static CacheTypes_ON_TheAIO__Compile::Cache init(Constants_Compile::PreConfig preConfig);
    static CacheTypes_ON_TheAIO__Compile::LocalState init__thread__local__state(uint64 t);
    static DafnySequence<uint8> read__block(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx);
    static void write__block(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx, DafnySequence<uint8> data);
  };
}// end of namespace Application_ON_TheAIO__Compile  class declarations
namespace AsyncDisk_Compile  {
}// end of namespace AsyncDisk_Compile  class declarations
namespace LinearCells  {
}// end of namespace LinearCells  class declarations
namespace _module  {
}// end of namespace _module  class declarations
template <typename V>
struct std::hash<Options_Compile::Option_None<V>> {
  std::size_t operator()(const Options_Compile::Option_None<V>& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <typename V>
struct std::hash<Options_Compile::Option_Some<V>> {
  std::size_t operator()(const Options_Compile::Option_Some<V>& x) const {
    size_t seed = 0;
    hash_combine<V>(seed, x.value);
    return seed;
  }
};
template <typename V>
struct std::hash<Options_Compile::Option<V>> {
  std::size_t operator()(const Options_Compile::Option<V>& x) const {
    size_t seed = 0;
    if (x.is_Option_None()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct Options_Compile::Option_None<V>>(seed, std::get<Options_Compile::Option_None<V>>(x.v));
    }
    if (x.is_Option_Some()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct Options_Compile::Option_Some<V>>(seed, std::get<Options_Compile::Option_Some<V>>(x.v));
    }
    return seed;
  }
};
template <typename V>
struct std::hash<GlinearOption_Compile::glOption_glNone<V>> {
  std::size_t operator()(const GlinearOption_Compile::glOption_glNone<V>& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <typename V>
struct std::hash<GlinearOption_Compile::glOption_glSome<V>> {
  std::size_t operator()(const GlinearOption_Compile::glOption_glSome<V>& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <typename V>
struct std::hash<GlinearOption_Compile::glOption<V>> {
  std::size_t operator()(const GlinearOption_Compile::glOption<V>& x) const {
    size_t seed = 0;
    if (x.is_glOption_glNone()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct GlinearOption_Compile::glOption_glNone<V>>(seed, std::get<GlinearOption_Compile::glOption_glNone<V>>(x.v));
    }
    if (x.is_glOption_glSome()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct GlinearOption_Compile::glOption_glSome<V>>(seed, std::get<GlinearOption_Compile::glOption_glSome<V>>(x.v));
    }
    return seed;
  }
};
template <typename V>
struct std::hash<Ptrs::PointsTo<V>> {
  std::size_t operator()(const Ptrs::PointsTo<V>& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <typename V>
struct std::hash<Ptrs::PointsToLinear_PointsToLinear<V>> {
  std::size_t operator()(const Ptrs::PointsToLinear_PointsToLinear<V>& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <typename V>
struct std::hash<Ptrs::PointsToLinear_PointsToEmpty<V>> {
  std::size_t operator()(const Ptrs::PointsToLinear_PointsToEmpty<V>& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <typename V>
struct std::hash<Ptrs::PointsToLinear<V>> {
  std::size_t operator()(const Ptrs::PointsToLinear<V>& x) const {
    size_t seed = 0;
    if (x.is_PointsToLinear_PointsToLinear()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct Ptrs::PointsToLinear_PointsToLinear<V>>(seed, std::get<Ptrs::PointsToLinear_PointsToLinear<V>>(x.v));
    }
    if (x.is_PointsToLinear_PointsToEmpty()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct Ptrs::PointsToLinear_PointsToEmpty<V>>(seed, std::get<Ptrs::PointsToLinear_PointsToEmpty<V>>(x.v));
    }
    return seed;
  }
};
template <typename V>
struct std::hash<Ptrs::PointsToArray<V>> {
  std::size_t operator()(const Ptrs::PointsToArray<V>& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<IocbStruct::Iocb_IocbUninitialized> {
  std::size_t operator()(const IocbStruct::Iocb_IocbUninitialized& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<IocbStruct::Iocb_IocbRead> {
  std::size_t operator()(const IocbStruct::Iocb_IocbRead& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<IocbStruct::Iocb_IocbWrite> {
  std::size_t operator()(const IocbStruct::Iocb_IocbWrite& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<IocbStruct::Iocb_IocbReadv> {
  std::size_t operator()(const IocbStruct::Iocb_IocbReadv& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<IocbStruct::Iocb_IocbWritev> {
  std::size_t operator()(const IocbStruct::Iocb_IocbWritev& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<IocbStruct::Iocb> {
  std::size_t operator()(const IocbStruct::Iocb& x) const {
    size_t seed = 0;
    if (x.is_Iocb_IocbUninitialized()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct IocbStruct::Iocb_IocbUninitialized>(seed, std::get<IocbStruct::Iocb_IocbUninitialized>(x.v));
    }
    if (x.is_Iocb_IocbRead()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct IocbStruct::Iocb_IocbRead>(seed, std::get<IocbStruct::Iocb_IocbRead>(x.v));
    }
    if (x.is_Iocb_IocbWrite()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct IocbStruct::Iocb_IocbWrite>(seed, std::get<IocbStruct::Iocb_IocbWrite>(x.v));
    }
    if (x.is_Iocb_IocbReadv()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct IocbStruct::Iocb_IocbReadv>(seed, std::get<IocbStruct::Iocb_IocbReadv>(x.v));
    }
    if (x.is_Iocb_IocbWritev()) {
      hash_combine<uint64>(seed, 4);
      hash_combine<struct IocbStruct::Iocb_IocbWritev>(seed, std::get<IocbStruct::Iocb_IocbWritev>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<Constants_Compile::PreConfig> {
  std::size_t operator()(const Constants_Compile::PreConfig& x) const {
    size_t seed = 0;
    hash_combine<uint32>(seed, x.cache__size);
    hash_combine<uint64>(seed, x.num__disk__pages);
    hash_combine<uint64>(seed, x.pages__per__extent);
    hash_combine<uint64>(seed, x.num__io__slots);
    return seed;
  }
};
template <>
struct std::hash<Constants_Compile::Config> {
  std::size_t operator()(const Constants_Compile::Config& x) const {
    size_t seed = 0;
    hash_combine<uint32>(seed, x.cache__size);
    hash_combine<uint64>(seed, x.num__disk__pages);
    hash_combine<uint64>(seed, x.pages__per__extent);
    hash_combine<uint64>(seed, x.num__io__slots);
    hash_combine<uint64>(seed, x.batch__capacity);
    hash_combine<uint64>(seed, x.cacheline__capacity);
    return seed;
  }
};
template <typename K>
struct std::hash<FullMaps_Compile::pre__FullMap<K>> {
  std::size_t operator()(const FullMaps_Compile::pre__FullMap<K>& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<GhostLoc_Compile::Loc_BaseLoc> {
  std::size_t operator()(const GhostLoc_Compile::Loc_BaseLoc& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<GhostLoc_Compile::Loc_ExtLoc> {
  std::size_t operator()(const GhostLoc_Compile::Loc_ExtLoc& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<GhostLoc_Compile::Loc> {
  std::size_t operator()(const GhostLoc_Compile::Loc& x) const {
    size_t seed = 0;
    if (x.is_Loc_BaseLoc()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct GhostLoc_Compile::Loc_BaseLoc>(seed, std::get<GhostLoc_Compile::Loc_BaseLoc>(x.v));
    }
    if (x.is_Loc_ExtLoc()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct GhostLoc_Compile::Loc_ExtLoc>(seed, std::get<GhostLoc_Compile::Loc_ExtLoc>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<std::shared_ptr<GhostLoc_Compile::Loc>> {
  std::size_t operator()(const std::shared_ptr<GhostLoc_Compile::Loc>& x) const {
    struct std::hash<GhostLoc_Compile::Loc> hasher;
    std::size_t h = hasher(*x);
    return h;
  }
};
template <typename V>
struct std::hash<Cells::CellContents<V>> {
  std::size_t operator()(const Cells::CellContents<V>& x) const {
    size_t seed = 0;
    hash_combine<V>(seed, x.v);
    return seed;
  }
};
template <>
struct std::hash<CacheStatusType_Compile::Status_Clean> {
  std::size_t operator()(const CacheStatusType_Compile::Status_Clean& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheStatusType_Compile::Status_Dirty> {
  std::size_t operator()(const CacheStatusType_Compile::Status_Dirty& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheStatusType_Compile::Status_Writeback> {
  std::size_t operator()(const CacheStatusType_Compile::Status_Writeback& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheStatusType_Compile::Status> {
  std::size_t operator()(const CacheStatusType_Compile::Status& x) const {
    size_t seed = 0;
    if (x.is_Status_Clean()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct CacheStatusType_Compile::Status_Clean>(seed, std::get<CacheStatusType_Compile::Status_Clean>(x.v));
    }
    if (x.is_Status_Dirty()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct CacheStatusType_Compile::Status_Dirty>(seed, std::get<CacheStatusType_Compile::Status_Dirty>(x.v));
    }
    if (x.is_Status_Writeback()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct CacheStatusType_Compile::Status_Writeback>(seed, std::get<CacheStatusType_Compile::Status_Writeback>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::ReqRead> {
  std::size_t operator()(const DiskIfc_Compile::ReqRead& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::ReqWrite> {
  std::size_t operator()(const DiskIfc_Compile::ReqWrite& x) const {
    size_t seed = 0;
    hash_combine<DafnySequence<uint8>>(seed, x.data);
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::RespRead> {
  std::size_t operator()(const DiskIfc_Compile::RespRead& x) const {
    size_t seed = 0;
    hash_combine<DafnySequence<uint8>>(seed, x.data);
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::RespWrite> {
  std::size_t operator()(const DiskIfc_Compile::RespWrite& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::DiskOp_ReqReadOp> {
  std::size_t operator()(const DiskIfc_Compile::DiskOp_ReqReadOp& x) const {
    size_t seed = 0;
    hash_combine<DiskIfc_Compile::ReqRead>(seed, x.reqRead);
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::DiskOp_ReqWriteOp> {
  std::size_t operator()(const DiskIfc_Compile::DiskOp_ReqWriteOp& x) const {
    size_t seed = 0;
    hash_combine<DiskIfc_Compile::ReqWrite>(seed, x.reqWrite);
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::DiskOp_RespReadOp> {
  std::size_t operator()(const DiskIfc_Compile::DiskOp_RespReadOp& x) const {
    size_t seed = 0;
    hash_combine<DiskIfc_Compile::RespRead>(seed, x.respRead);
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::DiskOp_RespWriteOp> {
  std::size_t operator()(const DiskIfc_Compile::DiskOp_RespWriteOp& x) const {
    size_t seed = 0;
    hash_combine<DiskIfc_Compile::RespWrite>(seed, x.respWrite);
    return seed;
  }
};
template <>
struct std::hash<DiskIfc_Compile::DiskOp> {
  std::size_t operator()(const DiskIfc_Compile::DiskOp& x) const {
    size_t seed = 0;
    if (x.is_DiskOp_ReqReadOp()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct DiskIfc_Compile::DiskOp_ReqReadOp>(seed, std::get<DiskIfc_Compile::DiskOp_ReqReadOp>(x.v));
    }
    if (x.is_DiskOp_ReqWriteOp()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct DiskIfc_Compile::DiskOp_ReqWriteOp>(seed, std::get<DiskIfc_Compile::DiskOp_ReqWriteOp>(x.v));
    }
    if (x.is_DiskOp_RespReadOp()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct DiskIfc_Compile::DiskOp_RespReadOp>(seed, std::get<DiskIfc_Compile::DiskOp_RespReadOp>(x.v));
    }
    if (x.is_DiskOp_RespWriteOp()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct DiskIfc_Compile::DiskOp_RespWriteOp>(seed, std::get<DiskIfc_Compile::DiskOp_RespWriteOp>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Input_WriteInput> {
  std::size_t operator()(const CacheIfc_Compile::Input_WriteInput& x) const {
    size_t seed = 0;
    hash_combine<DafnySequence<uint8>>(seed, x.data);
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Input_ReadInput> {
  std::size_t operator()(const CacheIfc_Compile::Input_ReadInput& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Input_SyncInput> {
  std::size_t operator()(const CacheIfc_Compile::Input_SyncInput& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Input_HavocInput> {
  std::size_t operator()(const CacheIfc_Compile::Input_HavocInput& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Input> {
  std::size_t operator()(const CacheIfc_Compile::Input& x) const {
    size_t seed = 0;
    if (x.is_Input_WriteInput()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct CacheIfc_Compile::Input_WriteInput>(seed, std::get<CacheIfc_Compile::Input_WriteInput>(x.v));
    }
    if (x.is_Input_ReadInput()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct CacheIfc_Compile::Input_ReadInput>(seed, std::get<CacheIfc_Compile::Input_ReadInput>(x.v));
    }
    if (x.is_Input_SyncInput()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct CacheIfc_Compile::Input_SyncInput>(seed, std::get<CacheIfc_Compile::Input_SyncInput>(x.v));
    }
    if (x.is_Input_HavocInput()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct CacheIfc_Compile::Input_HavocInput>(seed, std::get<CacheIfc_Compile::Input_HavocInput>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Output_WriteOutput> {
  std::size_t operator()(const CacheIfc_Compile::Output_WriteOutput& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Output_ReadOutput> {
  std::size_t operator()(const CacheIfc_Compile::Output_ReadOutput& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Output_SyncOutput> {
  std::size_t operator()(const CacheIfc_Compile::Output_SyncOutput& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Output_HavocOutput> {
  std::size_t operator()(const CacheIfc_Compile::Output_HavocOutput& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Output> {
  std::size_t operator()(const CacheIfc_Compile::Output& x) const {
    size_t seed = 0;
    if (x.is_Output_WriteOutput()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct CacheIfc_Compile::Output_WriteOutput>(seed, std::get<CacheIfc_Compile::Output_WriteOutput>(x.v));
    }
    if (x.is_Output_ReadOutput()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct CacheIfc_Compile::Output_ReadOutput>(seed, std::get<CacheIfc_Compile::Output_ReadOutput>(x.v));
    }
    if (x.is_Output_SyncOutput()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct CacheIfc_Compile::Output_SyncOutput>(seed, std::get<CacheIfc_Compile::Output_SyncOutput>(x.v));
    }
    if (x.is_Output_HavocOutput()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct CacheIfc_Compile::Output_HavocOutput>(seed, std::get<CacheIfc_Compile::Output_HavocOutput>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<CacheIfc_Compile::Op> {
  std::size_t operator()(const CacheIfc_Compile::Op& x) const {
    size_t seed = 0;
    hash_combine<CacheIfc_Compile::Input>(seed, x.input);
    hash_combine<CacheIfc_Compile::Output>(seed, x.output);
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Entry_Empty> {
  std::size_t operator()(const CacheSSM_Compile::Entry_Empty& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Entry_Reading> {
  std::size_t operator()(const CacheSSM_Compile::Entry_Reading& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Entry_Entry> {
  std::size_t operator()(const CacheSSM_Compile::Entry_Entry& x) const {
    size_t seed = 0;
    hash_combine<DafnySequence<uint8>>(seed, x.data);
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Entry> {
  std::size_t operator()(const CacheSSM_Compile::Entry& x) const {
    size_t seed = 0;
    if (x.is_Entry_Empty()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct CacheSSM_Compile::Entry_Empty>(seed, std::get<CacheSSM_Compile::Entry_Empty>(x.v));
    }
    if (x.is_Entry_Reading()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct CacheSSM_Compile::Entry_Reading>(seed, std::get<CacheSSM_Compile::Entry_Reading>(x.v));
    }
    if (x.is_Entry_Entry()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct CacheSSM_Compile::Entry_Entry>(seed, std::get<CacheSSM_Compile::Entry_Entry>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::M_M> {
  std::size_t operator()(const CacheSSM_Compile::M_M& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::M_Fail> {
  std::size_t operator()(const CacheSSM_Compile::M_Fail& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::M> {
  std::size_t operator()(const CacheSSM_Compile::M& x) const {
    size_t seed = 0;
    if (x.is_M_M()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct CacheSSM_Compile::M_M>(seed, std::get<CacheSSM_Compile::M_M>(x.v));
    }
    if (x.is_M_Fail()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct CacheSSM_Compile::M_Fail>(seed, std::get<CacheSSM_Compile::M_Fail>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_StartReadStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_StartReadStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_FinishReadStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_FinishReadStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_StartWritebackStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_StartWritebackStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_FinishWritebackStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_FinishWritebackStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_EvictStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_EvictStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_ObserveCleanForSyncStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_ObserveCleanForSyncStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_ApplyReadStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_ApplyReadStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_ApplyWriteStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_ApplyWriteStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_MarkDirtyStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_MarkDirtyStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_HavocNewStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_HavocNewStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step_HavocEvictStep> {
  std::size_t operator()(const CacheSSM_Compile::Step_HavocEvictStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheSSM_Compile::Step> {
  std::size_t operator()(const CacheSSM_Compile::Step& x) const {
    size_t seed = 0;
    if (x.is_Step_StartReadStep()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct CacheSSM_Compile::Step_StartReadStep>(seed, std::get<CacheSSM_Compile::Step_StartReadStep>(x.v));
    }
    if (x.is_Step_FinishReadStep()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct CacheSSM_Compile::Step_FinishReadStep>(seed, std::get<CacheSSM_Compile::Step_FinishReadStep>(x.v));
    }
    if (x.is_Step_StartWritebackStep()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct CacheSSM_Compile::Step_StartWritebackStep>(seed, std::get<CacheSSM_Compile::Step_StartWritebackStep>(x.v));
    }
    if (x.is_Step_FinishWritebackStep()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct CacheSSM_Compile::Step_FinishWritebackStep>(seed, std::get<CacheSSM_Compile::Step_FinishWritebackStep>(x.v));
    }
    if (x.is_Step_EvictStep()) {
      hash_combine<uint64>(seed, 4);
      hash_combine<struct CacheSSM_Compile::Step_EvictStep>(seed, std::get<CacheSSM_Compile::Step_EvictStep>(x.v));
    }
    if (x.is_Step_ObserveCleanForSyncStep()) {
      hash_combine<uint64>(seed, 5);
      hash_combine<struct CacheSSM_Compile::Step_ObserveCleanForSyncStep>(seed, std::get<CacheSSM_Compile::Step_ObserveCleanForSyncStep>(x.v));
    }
    if (x.is_Step_ApplyReadStep()) {
      hash_combine<uint64>(seed, 6);
      hash_combine<struct CacheSSM_Compile::Step_ApplyReadStep>(seed, std::get<CacheSSM_Compile::Step_ApplyReadStep>(x.v));
    }
    if (x.is_Step_ApplyWriteStep()) {
      hash_combine<uint64>(seed, 7);
      hash_combine<struct CacheSSM_Compile::Step_ApplyWriteStep>(seed, std::get<CacheSSM_Compile::Step_ApplyWriteStep>(x.v));
    }
    if (x.is_Step_MarkDirtyStep()) {
      hash_combine<uint64>(seed, 8);
      hash_combine<struct CacheSSM_Compile::Step_MarkDirtyStep>(seed, std::get<CacheSSM_Compile::Step_MarkDirtyStep>(x.v));
    }
    if (x.is_Step_HavocNewStep()) {
      hash_combine<uint64>(seed, 9);
      hash_combine<struct CacheSSM_Compile::Step_HavocNewStep>(seed, std::get<CacheSSM_Compile::Step_HavocNewStep>(x.v));
    }
    if (x.is_Step_HavocEvictStep()) {
      hash_combine<uint64>(seed, 10);
      hash_combine<struct CacheSSM_Compile::Step_HavocEvictStep>(seed, std::get<CacheSSM_Compile::Step_HavocEvictStep>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile::Token> {
  std::size_t operator()(const Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile::Token& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile::Token> {
  std::size_t operator()(const Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile::Token& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<DiskToken_ON_CacheIfc_CacheSSM__Compile::Token> {
  std::size_t operator()(const DiskToken_ON_CacheIfc_CacheSSM__Compile::Token& x) const {
    size_t seed = 0;
    hash_combine<CacheSSM_Compile::M>(seed, x.val);
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::DiskPageMap> {
  std::size_t operator()(const CacheResources_Compile::DiskPageMap& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::HavocPermission> {
  std::size_t operator()(const CacheResources_Compile::HavocPermission& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::CacheStatus> {
  std::size_t operator()(const CacheResources_Compile::CacheStatus& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::CacheEmpty> {
  std::size_t operator()(const CacheResources_Compile::CacheEmpty& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::CacheReading> {
  std::size_t operator()(const CacheResources_Compile::CacheReading& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::CacheEntry> {
  std::size_t operator()(const CacheResources_Compile::CacheEntry& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::DiskWriteTicket> {
  std::size_t operator()(const CacheResources_Compile::DiskWriteTicket& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::DiskWriteStub> {
  std::size_t operator()(const CacheResources_Compile::DiskWriteStub& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::DiskReadTicket> {
  std::size_t operator()(const CacheResources_Compile::DiskReadTicket& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheResources_Compile::DiskReadStub> {
  std::size_t operator()(const CacheResources_Compile::DiskReadStub& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheHandle_Compile::PageHandle> {
  std::size_t operator()(const CacheHandle_Compile::PageHandle& x) const {
    size_t seed = 0;
    hash_combine<Ptrs::Ptr>(seed, x.data__ptr);
    hash_combine<int64>(seed, x.disk__addr);
    return seed;
  }
};
template <>
struct std::hash<CacheHandle_Compile::Key> {
  std::size_t operator()(const CacheHandle_Compile::Key& x) const {
    size_t seed = 0;
    hash_combine<Ptrs::Ptr>(seed, x.data__ptr);
    hash_combine<Cells::Cell <CacheHandle_Compile::PageHandle> >(seed, x.idx__cell);
    return seed;
  }
};
template <>
struct std::hash<CacheHandle_Compile::Handle_CacheEmptyHandle> {
  std::size_t operator()(const CacheHandle_Compile::Handle_CacheEmptyHandle& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheHandle_Compile::Handle_CacheReadingHandle> {
  std::size_t operator()(const CacheHandle_Compile::Handle_CacheReadingHandle& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheHandle_Compile::Handle_CacheEntryHandle> {
  std::size_t operator()(const CacheHandle_Compile::Handle_CacheEntryHandle& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<CacheHandle_Compile::Handle> {
  std::size_t operator()(const CacheHandle_Compile::Handle& x) const {
    size_t seed = 0;
    if (x.is_Handle_CacheEmptyHandle()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct CacheHandle_Compile::Handle_CacheEmptyHandle>(seed, std::get<CacheHandle_Compile::Handle_CacheEmptyHandle>(x.v));
    }
    if (x.is_Handle_CacheReadingHandle()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct CacheHandle_Compile::Handle_CacheReadingHandle>(seed, std::get<CacheHandle_Compile::Handle_CacheReadingHandle>(x.v));
    }
    if (x.is_Handle_CacheEntryHandle()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct CacheHandle_Compile::Handle_CacheEntryHandle>(seed, std::get<CacheHandle_Compile::Handle_CacheEntryHandle>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Unmapped> {
  std::size_t operator()(const RwLock_Compile::Flag_Unmapped& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Reading> {
  std::size_t operator()(const RwLock_Compile::Flag_Reading& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Reading__ExcLock> {
  std::size_t operator()(const RwLock_Compile::Flag_Reading__ExcLock& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Available> {
  std::size_t operator()(const RwLock_Compile::Flag_Available& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Claimed> {
  std::size_t operator()(const RwLock_Compile::Flag_Claimed& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Writeback> {
  std::size_t operator()(const RwLock_Compile::Flag_Writeback& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Writeback__Claimed> {
  std::size_t operator()(const RwLock_Compile::Flag_Writeback__Claimed& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_Writeback__PendingExcLock> {
  std::size_t operator()(const RwLock_Compile::Flag_Writeback__PendingExcLock& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_PendingExcLock> {
  std::size_t operator()(const RwLock_Compile::Flag_PendingExcLock& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_ExcLock__Clean> {
  std::size_t operator()(const RwLock_Compile::Flag_ExcLock__Clean& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag_ExcLock__Dirty> {
  std::size_t operator()(const RwLock_Compile::Flag_ExcLock__Dirty& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::Flag> {
  std::size_t operator()(const RwLock_Compile::Flag& x) const {
    size_t seed = 0;
    if (x.is_Flag_Unmapped()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct RwLock_Compile::Flag_Unmapped>(seed, std::get<RwLock_Compile::Flag_Unmapped>(x.v));
    }
    if (x.is_Flag_Reading()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct RwLock_Compile::Flag_Reading>(seed, std::get<RwLock_Compile::Flag_Reading>(x.v));
    }
    if (x.is_Flag_Reading__ExcLock()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct RwLock_Compile::Flag_Reading__ExcLock>(seed, std::get<RwLock_Compile::Flag_Reading__ExcLock>(x.v));
    }
    if (x.is_Flag_Available()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct RwLock_Compile::Flag_Available>(seed, std::get<RwLock_Compile::Flag_Available>(x.v));
    }
    if (x.is_Flag_Claimed()) {
      hash_combine<uint64>(seed, 4);
      hash_combine<struct RwLock_Compile::Flag_Claimed>(seed, std::get<RwLock_Compile::Flag_Claimed>(x.v));
    }
    if (x.is_Flag_Writeback()) {
      hash_combine<uint64>(seed, 5);
      hash_combine<struct RwLock_Compile::Flag_Writeback>(seed, std::get<RwLock_Compile::Flag_Writeback>(x.v));
    }
    if (x.is_Flag_Writeback__Claimed()) {
      hash_combine<uint64>(seed, 6);
      hash_combine<struct RwLock_Compile::Flag_Writeback__Claimed>(seed, std::get<RwLock_Compile::Flag_Writeback__Claimed>(x.v));
    }
    if (x.is_Flag_Writeback__PendingExcLock()) {
      hash_combine<uint64>(seed, 7);
      hash_combine<struct RwLock_Compile::Flag_Writeback__PendingExcLock>(seed, std::get<RwLock_Compile::Flag_Writeback__PendingExcLock>(x.v));
    }
    if (x.is_Flag_PendingExcLock()) {
      hash_combine<uint64>(seed, 8);
      hash_combine<struct RwLock_Compile::Flag_PendingExcLock>(seed, std::get<RwLock_Compile::Flag_PendingExcLock>(x.v));
    }
    if (x.is_Flag_ExcLock__Clean()) {
      hash_combine<uint64>(seed, 9);
      hash_combine<struct RwLock_Compile::Flag_ExcLock__Clean>(seed, std::get<RwLock_Compile::Flag_ExcLock__Clean>(x.v));
    }
    if (x.is_Flag_ExcLock__Dirty()) {
      hash_combine<uint64>(seed, 10);
      hash_combine<struct RwLock_Compile::Flag_ExcLock__Dirty>(seed, std::get<RwLock_Compile::Flag_ExcLock__Dirty>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::SharedState_SharedPending> {
  std::size_t operator()(const RwLock_Compile::SharedState_SharedPending& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::SharedState_SharedPending2> {
  std::size_t operator()(const RwLock_Compile::SharedState_SharedPending2& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::SharedState_SharedObtained> {
  std::size_t operator()(const RwLock_Compile::SharedState_SharedObtained& x) const {
    size_t seed = 0;
    hash_combine<CacheHandle_Compile::Handle>(seed, x.b);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::SharedState> {
  std::size_t operator()(const RwLock_Compile::SharedState& x) const {
    size_t seed = 0;
    if (x.is_SharedState_SharedPending()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct RwLock_Compile::SharedState_SharedPending>(seed, std::get<RwLock_Compile::SharedState_SharedPending>(x.v));
    }
    if (x.is_SharedState_SharedPending2()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct RwLock_Compile::SharedState_SharedPending2>(seed, std::get<RwLock_Compile::SharedState_SharedPending2>(x.v));
    }
    if (x.is_SharedState_SharedObtained()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct RwLock_Compile::SharedState_SharedObtained>(seed, std::get<RwLock_Compile::SharedState_SharedObtained>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ExcState_ExcNone> {
  std::size_t operator()(const RwLock_Compile::ExcState_ExcNone& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ExcState_ExcClaim> {
  std::size_t operator()(const RwLock_Compile::ExcState_ExcClaim& x) const {
    size_t seed = 0;
    hash_combine<CacheHandle_Compile::Handle>(seed, x.b);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ExcState_ExcPendingAwaitWriteback> {
  std::size_t operator()(const RwLock_Compile::ExcState_ExcPendingAwaitWriteback& x) const {
    size_t seed = 0;
    hash_combine<CacheHandle_Compile::Handle>(seed, x.b);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ExcState_ExcPending> {
  std::size_t operator()(const RwLock_Compile::ExcState_ExcPending& x) const {
    size_t seed = 0;
    hash_combine<bool>(seed, x.clean);
    hash_combine<CacheHandle_Compile::Handle>(seed, x.b);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ExcState_ExcObtained> {
  std::size_t operator()(const RwLock_Compile::ExcState_ExcObtained& x) const {
    size_t seed = 0;
    hash_combine<bool>(seed, x.clean);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ExcState> {
  std::size_t operator()(const RwLock_Compile::ExcState& x) const {
    size_t seed = 0;
    if (x.is_ExcState_ExcNone()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct RwLock_Compile::ExcState_ExcNone>(seed, std::get<RwLock_Compile::ExcState_ExcNone>(x.v));
    }
    if (x.is_ExcState_ExcClaim()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct RwLock_Compile::ExcState_ExcClaim>(seed, std::get<RwLock_Compile::ExcState_ExcClaim>(x.v));
    }
    if (x.is_ExcState_ExcPendingAwaitWriteback()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct RwLock_Compile::ExcState_ExcPendingAwaitWriteback>(seed, std::get<RwLock_Compile::ExcState_ExcPendingAwaitWriteback>(x.v));
    }
    if (x.is_ExcState_ExcPending()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct RwLock_Compile::ExcState_ExcPending>(seed, std::get<RwLock_Compile::ExcState_ExcPending>(x.v));
    }
    if (x.is_ExcState_ExcObtained()) {
      hash_combine<uint64>(seed, 4);
      hash_combine<struct RwLock_Compile::ExcState_ExcObtained>(seed, std::get<RwLock_Compile::ExcState_ExcObtained>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::WritebackState_WritebackNone> {
  std::size_t operator()(const RwLock_Compile::WritebackState_WritebackNone& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::WritebackState_WritebackObtained> {
  std::size_t operator()(const RwLock_Compile::WritebackState_WritebackObtained& x) const {
    size_t seed = 0;
    hash_combine<CacheHandle_Compile::Handle>(seed, x.b);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::WritebackState> {
  std::size_t operator()(const RwLock_Compile::WritebackState& x) const {
    size_t seed = 0;
    if (x.is_WritebackState_WritebackNone()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct RwLock_Compile::WritebackState_WritebackNone>(seed, std::get<RwLock_Compile::WritebackState_WritebackNone>(x.v));
    }
    if (x.is_WritebackState_WritebackObtained()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct RwLock_Compile::WritebackState_WritebackObtained>(seed, std::get<RwLock_Compile::WritebackState_WritebackObtained>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ReadState_ReadNone> {
  std::size_t operator()(const RwLock_Compile::ReadState_ReadNone& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ReadState_ReadPending> {
  std::size_t operator()(const RwLock_Compile::ReadState_ReadPending& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ReadState_ReadPendingCounted> {
  std::size_t operator()(const RwLock_Compile::ReadState_ReadPendingCounted& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ReadState_ReadObtained> {
  std::size_t operator()(const RwLock_Compile::ReadState_ReadObtained& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::ReadState> {
  std::size_t operator()(const RwLock_Compile::ReadState& x) const {
    size_t seed = 0;
    if (x.is_ReadState_ReadNone()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct RwLock_Compile::ReadState_ReadNone>(seed, std::get<RwLock_Compile::ReadState_ReadNone>(x.v));
    }
    if (x.is_ReadState_ReadPending()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct RwLock_Compile::ReadState_ReadPending>(seed, std::get<RwLock_Compile::ReadState_ReadPending>(x.v));
    }
    if (x.is_ReadState_ReadPendingCounted()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct RwLock_Compile::ReadState_ReadPendingCounted>(seed, std::get<RwLock_Compile::ReadState_ReadPendingCounted>(x.v));
    }
    if (x.is_ReadState_ReadObtained()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct RwLock_Compile::ReadState_ReadObtained>(seed, std::get<RwLock_Compile::ReadState_ReadObtained>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::CentralState_CentralNone> {
  std::size_t operator()(const RwLock_Compile::CentralState_CentralNone& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::CentralState_CentralState> {
  std::size_t operator()(const RwLock_Compile::CentralState_CentralState& x) const {
    size_t seed = 0;
    hash_combine<RwLock_Compile::Flag>(seed, x.flag);
    hash_combine<CacheHandle_Compile::Handle>(seed, x.stored__value);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::CentralState> {
  std::size_t operator()(const RwLock_Compile::CentralState& x) const {
    size_t seed = 0;
    if (x.is_CentralState_CentralNone()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct RwLock_Compile::CentralState_CentralNone>(seed, std::get<RwLock_Compile::CentralState_CentralNone>(x.v));
    }
    if (x.is_CentralState_CentralState()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct RwLock_Compile::CentralState_CentralState>(seed, std::get<RwLock_Compile::CentralState_CentralState>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::M_M> {
  std::size_t operator()(const RwLock_Compile::M_M& x) const {
    size_t seed = 0;
    hash_combine<RwLock_Compile::CentralState>(seed, x.central);
    hash_combine<RwLock_Compile::ExcState>(seed, x.exc);
    hash_combine<RwLock_Compile::ReadState>(seed, x.read);
    hash_combine<RwLock_Compile::WritebackState>(seed, x.writeback);
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::M_Fail> {
  std::size_t operator()(const RwLock_Compile::M_Fail& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<RwLock_Compile::M> {
  std::size_t operator()(const RwLock_Compile::M& x) const {
    size_t seed = 0;
    if (x.is_M_M()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct RwLock_Compile::M_M>(seed, std::get<RwLock_Compile::M_M>(x.v));
    }
    if (x.is_M_Fail()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct RwLock_Compile::M_Fail>(seed, std::get<RwLock_Compile::M_Fail>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<Rw_PCMWrap_ON_RwLock__Compile::M> {
  std::size_t operator()(const Rw_PCMWrap_ON_RwLock__Compile::M& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile::Token> {
  std::size_t operator()(const Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile::Token& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<Tokens_ON_Rw__PCMExt__ON__RwLock____Compile::Token> {
  std::size_t operator()(const Tokens_ON_Rw__PCMExt__ON__RwLock____Compile::Token& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<RwLockToken_Compile::CentralToken> {
  std::size_t operator()(const RwLockToken_Compile::CentralToken& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<RwLockToken_Compile::WritebackObtainedToken> {
  std::size_t operator()(const RwLockToken_Compile::WritebackObtainedToken& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<RwLockToken_Compile::SharedPendingToken> {
  std::size_t operator()(const RwLockToken_Compile::SharedPendingToken& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<RwLockToken_Compile::SharedPending2Token> {
  std::size_t operator()(const RwLockToken_Compile::SharedPending2Token& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<RwLockToken_Compile::SharedObtainedToken> {
  std::size_t operator()(const RwLockToken_Compile::SharedObtainedToken& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheAIOParams_Compile::IOSlotAccess> {
  std::size_t operator()(const CacheAIOParams_Compile::IOSlotAccess& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheAIOParams_Compile::ReadG> {
  std::size_t operator()(const CacheAIOParams_Compile::ReadG& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheAIOParams_Compile::ReadvG> {
  std::size_t operator()(const CacheAIOParams_Compile::ReadvG& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheAIOParams_Compile::WriteG> {
  std::size_t operator()(const CacheAIOParams_Compile::WriteG& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheAIOParams_Compile::WritevG> {
  std::size_t operator()(const CacheAIOParams_Compile::WritevG& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CounterPCM_Compile::M> {
  std::size_t operator()(const CounterPCM_Compile::M& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<Tokens_ON_CounterPCM__Compile::Token> {
  std::size_t operator()(const Tokens_ON_CounterPCM__Compile::Token& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<ClientCounter_Compile::Client> {
  std::size_t operator()(const ClientCounter_Compile::Client& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<ClientCounter_Compile::Clients> {
  std::size_t operator()(const ClientCounter_Compile::Clients& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<AtomicRefcountImpl_Compile::RG> {
  std::size_t operator()(const AtomicRefcountImpl_Compile::RG& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<AtomicRefcountImpl_Compile::AtomicRefcount> {
  std::size_t operator()(const AtomicRefcountImpl_Compile::AtomicRefcount& x) const {
    size_t seed = 0;
    hash_combine<Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG> >(seed, x.a);
    return seed;
  }
};
template <>
struct std::hash<AtomicStatusImpl_Compile::G> {
  std::size_t operator()(const AtomicStatusImpl_Compile::G& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<AtomicStatusImpl_Compile::AtomicStatus> {
  std::size_t operator()(const AtomicStatusImpl_Compile::AtomicStatus& x) const {
    size_t seed = 0;
    hash_combine<Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> >(seed, x.atomic);
    return seed;
  }
};
template <typename G>
struct std::hash<BasicLockImpl_Compile::pre__BasicLock<G>> {
  std::size_t operator()(const BasicLockImpl_Compile::pre__BasicLock<G>& x) const {
    size_t seed = 0;
    hash_combine<Atomics::Atomic <bool, GlinearOption_Compile::glOption <G> > >(seed, x.a);
    return seed;
  }
};
template <>
struct std::hash<InstantiatedDiskInterface::FinishedReq_FRNone> {
  std::size_t operator()(const InstantiatedDiskInterface::FinishedReq_FRNone& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<InstantiatedDiskInterface::FinishedReq_FRWrite> {
  std::size_t operator()(const InstantiatedDiskInterface::FinishedReq_FRWrite& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<InstantiatedDiskInterface::FinishedReq_FRWritev> {
  std::size_t operator()(const InstantiatedDiskInterface::FinishedReq_FRWritev& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<InstantiatedDiskInterface::FinishedReq_FRRead> {
  std::size_t operator()(const InstantiatedDiskInterface::FinishedReq_FRRead& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<InstantiatedDiskInterface::FinishedReq_FRReadv> {
  std::size_t operator()(const InstantiatedDiskInterface::FinishedReq_FRReadv& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<InstantiatedDiskInterface::FinishedReq> {
  std::size_t operator()(const InstantiatedDiskInterface::FinishedReq& x) const {
    size_t seed = 0;
    if (x.is_FinishedReq_FRNone()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct InstantiatedDiskInterface::FinishedReq_FRNone>(seed, std::get<InstantiatedDiskInterface::FinishedReq_FRNone>(x.v));
    }
    if (x.is_FinishedReq_FRWrite()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct InstantiatedDiskInterface::FinishedReq_FRWrite>(seed, std::get<InstantiatedDiskInterface::FinishedReq_FRWrite>(x.v));
    }
    if (x.is_FinishedReq_FRWritev()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct InstantiatedDiskInterface::FinishedReq_FRWritev>(seed, std::get<InstantiatedDiskInterface::FinishedReq_FRWritev>(x.v));
    }
    if (x.is_FinishedReq_FRRead()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct InstantiatedDiskInterface::FinishedReq_FRRead>(seed, std::get<InstantiatedDiskInterface::FinishedReq_FRRead>(x.v));
    }
    if (x.is_FinishedReq_FRReadv()) {
      hash_combine<uint64>(seed, 4);
      hash_combine<struct InstantiatedDiskInterface::FinishedReq_FRReadv>(seed, std::get<InstantiatedDiskInterface::FinishedReq_FRReadv>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<CacheTypes_ON_TheAIO__Compile::NullGhostType> {
  std::size_t operator()(const CacheTypes_ON_TheAIO__Compile::NullGhostType& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheTypes_ON_TheAIO__Compile::StatusIdx> {
  std::size_t operator()(const CacheTypes_ON_TheAIO__Compile::StatusIdx& x) const {
    size_t seed = 0;
    hash_combine<AtomicStatusImpl_Compile::AtomicStatus>(seed, x.status);
    hash_combine<Cells::Cell <CacheHandle_Compile::PageHandle> >(seed, x.page__handle);
    return seed;
  }
};
template <>
struct std::hash<CacheTypes_ON_TheAIO__Compile::Cache> {
  std::size_t operator()(const CacheTypes_ON_TheAIO__Compile::Cache& x) const {
    size_t seed = 0;
    hash_combine<Constants_Compile::Config>(seed, x.config);
    hash_combine<Ptrs::Ptr>(seed, x.data__base__ptr);
    hash_combine<Ptrs::Ptr>(seed, x.iocb__base__ptr);
    hash_combine<LinearExtern::lseq <AtomicRefcountImpl_Compile::AtomicRefcount> >(seed, x.read__refcounts__array);
    hash_combine<LinearExtern::lseq <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> > >(seed, x.cache__idx__of__page__array);
    hash_combine<LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::StatusIdx> >(seed, x.status__idx__array);
    hash_combine<Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType> >(seed, x.global__clockpointer);
    hash_combine<Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType> >(seed, x.req__hand__base);
    hash_combine<LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> > >(seed, x.batch__busy);
    hash_combine<LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot> >(seed, x.io__slots);
    hash_combine<InstantiatedDiskInterface::IOCtx>(seed, x.ioctx);
    return seed;
  }
};
template <>
struct std::hash<CacheTypes_ON_TheAIO__Compile::LocalState> {
  std::size_t operator()(const CacheTypes_ON_TheAIO__Compile::LocalState& x) const {
    size_t seed = 0;
    hash_combine<uint64>(seed, x.t);
    hash_combine<uint64>(seed, x.free__hand);
    hash_combine<uint64>(seed, x.io__slot__hand);
    return seed;
  }
};
template <>
struct std::hash<CacheTypes_ON_TheAIO__Compile::IOSlot> {
  std::size_t operator()(const CacheTypes_ON_TheAIO__Compile::IOSlot& x) const {
    size_t seed = 0;
    hash_combine<Ptrs::Ptr>(seed, x.iocb__ptr);
    hash_combine<Ptrs::Ptr>(seed, x.iovec__ptr);
    hash_combine<BasicLockImpl_Compile::pre__BasicLock <CacheAIOParams_Compile::IOSlotAccess> >(seed, x.lock);
    return seed;
  }
};
template <>
struct std::hash<CacheOps_ON_TheAIO__Compile::PageHandleIdx> {
  std::size_t operator()(const CacheOps_ON_TheAIO__Compile::PageHandleIdx& x) const {
    size_t seed = 0;
    hash_combine<uint32>(seed, x.cache__idx);
    return seed;
  }
};
template <>
struct std::hash<CacheOps_ON_TheAIO__Compile::WriteablePageHandle> {
  std::size_t operator()(const CacheOps_ON_TheAIO__Compile::WriteablePageHandle& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheOps_ON_TheAIO__Compile::ReadonlyPageHandle> {
  std::size_t operator()(const CacheOps_ON_TheAIO__Compile::ReadonlyPageHandle& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<CacheOps_ON_TheAIO__Compile::ClaimPageHandle> {
  std::size_t operator()(const CacheOps_ON_TheAIO__Compile::ClaimPageHandle& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::Variables> {
  std::size_t operator()(const AsyncDisk_Compile::Variables& x) const {
    size_t seed = 0;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::Step_RecvReadStep> {
  std::size_t operator()(const AsyncDisk_Compile::Step_RecvReadStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::Step_RecvWriteStep> {
  std::size_t operator()(const AsyncDisk_Compile::Step_RecvWriteStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::Step_AckReadStep> {
  std::size_t operator()(const AsyncDisk_Compile::Step_AckReadStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::Step_AckWriteStep> {
  std::size_t operator()(const AsyncDisk_Compile::Step_AckWriteStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::Step> {
  std::size_t operator()(const AsyncDisk_Compile::Step& x) const {
    size_t seed = 0;
    if (x.is_Step_RecvReadStep()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct AsyncDisk_Compile::Step_RecvReadStep>(seed, std::get<AsyncDisk_Compile::Step_RecvReadStep>(x.v));
    }
    if (x.is_Step_RecvWriteStep()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct AsyncDisk_Compile::Step_RecvWriteStep>(seed, std::get<AsyncDisk_Compile::Step_RecvWriteStep>(x.v));
    }
    if (x.is_Step_AckReadStep()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct AsyncDisk_Compile::Step_AckReadStep>(seed, std::get<AsyncDisk_Compile::Step_AckReadStep>(x.v));
    }
    if (x.is_Step_AckWriteStep()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct AsyncDisk_Compile::Step_AckWriteStep>(seed, std::get<AsyncDisk_Compile::Step_AckWriteStep>(x.v));
    }
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::InternalStep_ProcessReadStep> {
  std::size_t operator()(const AsyncDisk_Compile::InternalStep_ProcessReadStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::InternalStep_ProcessWriteStep> {
  std::size_t operator()(const AsyncDisk_Compile::InternalStep_ProcessWriteStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::InternalStep_HavocConflictingWritesStep> {
  std::size_t operator()(const AsyncDisk_Compile::InternalStep_HavocConflictingWritesStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::InternalStep_HavocConflictingWriteReadStep> {
  std::size_t operator()(const AsyncDisk_Compile::InternalStep_HavocConflictingWriteReadStep& x) const {
    size_t seed = 0;
    (void)x;
    return seed;
  }
};
template <>
struct std::hash<AsyncDisk_Compile::InternalStep> {
  std::size_t operator()(const AsyncDisk_Compile::InternalStep& x) const {
    size_t seed = 0;
    if (x.is_InternalStep_ProcessReadStep()) {
      hash_combine<uint64>(seed, 0);
      hash_combine<struct AsyncDisk_Compile::InternalStep_ProcessReadStep>(seed, std::get<AsyncDisk_Compile::InternalStep_ProcessReadStep>(x.v));
    }
    if (x.is_InternalStep_ProcessWriteStep()) {
      hash_combine<uint64>(seed, 1);
      hash_combine<struct AsyncDisk_Compile::InternalStep_ProcessWriteStep>(seed, std::get<AsyncDisk_Compile::InternalStep_ProcessWriteStep>(x.v));
    }
    if (x.is_InternalStep_HavocConflictingWritesStep()) {
      hash_combine<uint64>(seed, 2);
      hash_combine<struct AsyncDisk_Compile::InternalStep_HavocConflictingWritesStep>(seed, std::get<AsyncDisk_Compile::InternalStep_HavocConflictingWritesStep>(x.v));
    }
    if (x.is_InternalStep_HavocConflictingWriteReadStep()) {
      hash_combine<uint64>(seed, 3);
      hash_combine<struct AsyncDisk_Compile::InternalStep_HavocConflictingWriteReadStep>(seed, std::get<AsyncDisk_Compile::InternalStep_HavocConflictingWriteReadStep>(x.v));
    }
    return seed;
  }
};
template <typename V>
struct std::hash<LinearCells::LCellContents<V>> {
  std::size_t operator()(const LinearCells::LCellContents<V>& x) const {
    size_t seed = 0;
    hash_combine<Options_Compile::Option <V> >(seed, x.v);
    return seed;
  }
};
