// generated from seagull code git rev. 3df6ab1b7ac0242da1273d2d048b5f0e7c4ee5c3

// Dafny program Application.i.dfy compiled into Cpp
#include "DafnyRuntime.h"
#include "Extern.h"
#include "LinearExtern.h"
#include "DiskExtern.h"
#include "Application.i.h"
namespace _System  {














}// end of namespace _System 
namespace NativeTypes_Compile  {



  typedef int16 int16;

  typedef uint16 uint16;

  typedef int32 int32;

  typedef uint32 uint32;

  typedef int64 int64;

  typedef uint64 uint64;

  typedef int8 nat8;

  typedef int16 nat16;

  typedef int32 nat32;

  typedef int64 nat64;



  uint64 __default::Uint64Size()
  {
    return (uint64)8;
  }
  uint64 __default::Uint32Size()
  {
    return (uint64)4;
  }
  uint64 __default::Uint16Size()
  {
    return (uint64)2;
  }
}// end of namespace NativeTypes_Compile 
namespace Options_Compile  {

  template <typename V>
bool operator==(const Option_None<V> &left, const Option_None<V> &right) {
    (void)left; (void) right;
	return true ;
  }
  template <typename V>
bool operator==(const Option_Some<V> &left, const Option_Some<V> &right) {
    	return true 		&& left.value == right.value
    ;
  }
  template <typename V>
Option<V>::Option() {
    Option_None<V> COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  template <typename V>
inline bool is_Option_None(const struct Option<V> d) { return std::holds_alternative<Option_None<V>>(d.v); }
  template <typename V>
inline bool is_Option_Some(const struct Option<V> d) { return std::holds_alternative<Option_Some<V>>(d.v); }

}// end of namespace Options_Compile 
namespace GlinearOption_Compile  {


  template <typename V>
bool operator==(const glOption_glNone<V> &left, const glOption_glNone<V> &right) {
    (void)left; (void) right;
	return true ;
  }
  template <typename V>
bool operator==(const glOption_glSome<V> &left, const glOption_glSome<V> &right) {
    (void)left; (void) right;
	return true ;
  }
  template <typename V>
glOption<V>::glOption() {
    glOption_glNone<V> COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  template <typename V>
inline bool is_glOption_glNone(const struct glOption<V> d) { return std::holds_alternative<glOption_glNone<V>>(d.v); }
  template <typename V>
inline bool is_glOption_glSome(const struct glOption<V> d) { return std::holds_alternative<glOption_glSome<V>>(d.v); }

}// end of namespace GlinearOption_Compile 
namespace Ptrs  {



  template <typename V>
PointsTo<V>::PointsTo() {
  }
  template <typename V>
bool operator==(const PointsTo<V> &left, const PointsTo<V> &right)  {
    	return true ;
  }

  template <typename V>
bool operator==(const PointsToLinear_PointsToLinear<V> &left, const PointsToLinear_PointsToLinear<V> &right) {
    (void)left; (void) right;
	return true ;
  }
  template <typename V>
bool operator==(const PointsToLinear_PointsToEmpty<V> &left, const PointsToLinear_PointsToEmpty<V> &right) {
    (void)left; (void) right;
	return true ;
  }
  template <typename V>
PointsToLinear<V>::PointsToLinear() {
    PointsToLinear_PointsToLinear<V> COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  template <typename V>
inline bool is_PointsToLinear_PointsToLinear(const struct PointsToLinear<V> d) { return std::holds_alternative<PointsToLinear_PointsToLinear<V>>(d.v); }
  template <typename V>
inline bool is_PointsToLinear_PointsToEmpty(const struct PointsToLinear<V> d) { return std::holds_alternative<PointsToLinear_PointsToEmpty<V>>(d.v); }

  template <typename V>
PointsToArray<V>::PointsToArray() {
  }
  template <typename V>
bool operator==(const PointsToArray<V> &left, const PointsToArray<V> &right)  {
    	return true ;
  }


}// end of namespace Ptrs 
namespace PageSizeConstant_Compile  {


  uint64 __default::PageSize64()
  {
    return (uint64)4096;
  }
}// end of namespace PageSizeConstant_Compile 
namespace IocbStruct  {




  
bool operator==(const Iocb_IocbUninitialized &left, const Iocb_IocbUninitialized &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Iocb_IocbRead &left, const Iocb_IocbRead &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Iocb_IocbWrite &left, const Iocb_IocbWrite &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Iocb_IocbReadv &left, const Iocb_IocbReadv &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Iocb_IocbWritev &left, const Iocb_IocbWritev &right) {
    (void)left; (void) right;
	return true ;
  }
  
Iocb::Iocb() {
    Iocb_IocbUninitialized COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Iocb_IocbUninitialized(const struct Iocb d) { return std::holds_alternative<Iocb_IocbUninitialized>(d.v); }
  
inline bool is_Iocb_IocbRead(const struct Iocb d) { return std::holds_alternative<Iocb_IocbRead>(d.v); }
  
inline bool is_Iocb_IocbWrite(const struct Iocb d) { return std::holds_alternative<Iocb_IocbWrite>(d.v); }
  
inline bool is_Iocb_IocbReadv(const struct Iocb d) { return std::holds_alternative<Iocb_IocbReadv>(d.v); }
  
inline bool is_Iocb_IocbWritev(const struct Iocb d) { return std::holds_alternative<Iocb_IocbWritev>(d.v); }


}// end of namespace IocbStruct 
namespace NonlinearLemmas_Compile  {

}// end of namespace NonlinearLemmas_Compile 
namespace Math_Compile  {


}// end of namespace Math_Compile 
namespace Constants_Compile  {




  
PreConfig::PreConfig() {
    cache__size = 0;
    num__disk__pages = 0;
    pages__per__extent = 0;
    num__io__slots = 0;
  }
  
bool operator==(const PreConfig &left, const PreConfig &right)  {
    	return true 		&& left.cache__size == right.cache__size
    		&& left.num__disk__pages == right.num__disk__pages
    		&& left.pages__per__extent == right.pages__per__extent
    		&& left.num__io__slots == right.num__io__slots
    ;
  }
  bool PreConfig::WF()
  {
    return ((((((((((uint64(((*this).cache__size))) % ((Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64()) * (Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64()))) == ((uint64)0)) && (((((*this).cache__size)) % (Constants_Compile::__default::ENTRIES__PER__BATCH__32())) == ((uint32)0))) && ((((*this).cache__size)) > ((uint32)0))) && ((((*this).cache__size)) < ((uint32)1073741824))) && ((((uint64)0) < (((*this).num__disk__pages))) && ((((*this).num__disk__pages)) < ((uint64)281474976710656)))) && ((((*this).pages__per__extent)) != ((uint64)0))) && ((((*this).pages__per__extent)) <= ((uint64)65536))) && ((((uint64)0) < (((*this).num__io__slots))) && ((((*this).num__io__slots)) <= ((uint64)65536)))) && (((((*this).num__io__slots)) % (Constants_Compile::__default::AIO__HAND__BATCH__SIZE__64())) == ((uint64)0));
  }

  
Config::Config() {
    cache__size = 0;
    num__disk__pages = 0;
    pages__per__extent = 0;
    num__io__slots = 0;
    batch__capacity = 0;
    cacheline__capacity = 0;
  }
  
bool operator==(const Config &left, const Config &right)  {
    	return true 		&& left.cache__size == right.cache__size
    		&& left.num__disk__pages == right.num__disk__pages
    		&& left.pages__per__extent == right.pages__per__extent
    		&& left.num__io__slots == right.num__io__slots
    		&& left.batch__capacity == right.batch__capacity
    		&& left.cacheline__capacity == right.cacheline__capacity
    ;
  }

  uint64 __default::PLATFORM__CACHELINE__SIZE__64()
  {
    return (uint64)64;
  }
  uint32 __default::ENTRIES__PER__BATCH__32()
  {
    return (uint32)64;
  }
  Constants_Compile::Config __default::fromPreConfig(Constants_Compile::PreConfig pre)
  {
    Constants_Compile::Config config = Constants_Compile::Config();
    config = Constants_Compile::Config(((pre).cache__size), ((pre).num__disk__pages), ((pre).pages__per__extent), ((pre).num__io__slots), (uint64(((pre).cache__size))) / (uint64(Constants_Compile::__default::ENTRIES__PER__BATCH__32())), (uint64(((pre).cache__size))) / (Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64()));
    return config;
  }
  uint32 __default::CHUNK__SIZE__32()
  {
    return (uint32)64;
  }
  uint64 __default::AIO__HAND__BATCH__SIZE__64()
  {
    return (uint64)32;
  }
  uint64 __default::DEFAULT__MAX__IO__EVENTS__64()
  {
    return (uint64)32;
  }
  uint64 __default::RC__WIDTH__64()
  {
    return (uint64)4;
  }
  uint64 __default::CLEAN__AHEAD__64()
  {
    return (uint64)512;
  }
  uint32 __default::ref__internal(uint32 i)
  {
    uint32 _3322_block__modulus = (i) % ((uint32(Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64())) * (uint32(Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64())));
    uint32 _3323_column = (_3322_block__modulus) % (uint32(Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64()));
    uint32 _3324_row = (_3322_block__modulus) / (uint32(Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64()));
    uint32 _3325_new__modulus = ((_3323_column) * (uint32(Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64()))) + (_3324_row);
    return ((i) - (_3322_block__modulus)) + (_3325_new__modulus);
  }
  uint64 __default::rc__index(Constants_Compile::Config config, uint64 j, uint32 i)
  {
    uint32 _3326_rc__number = Constants_Compile::__default::ref__internal(i);
    return uint64(((uint32(j)) * (((config).cache__size))) + (_3326_rc__number));
  }
}// end of namespace Constants_Compile 
namespace MapSum_Compile  {

}// end of namespace MapSum_Compile 
namespace FullMaps_Compile  {




  template <typename K>
pre__FullMap<K>::pre__FullMap() {
  }
  template <typename K>
bool operator==(const pre__FullMap<K> &left, const pre__FullMap<K> &right)  {
    	return true ;
  }


}// end of namespace FullMaps_Compile 
namespace GhostLoc_Compile  {

  
bool operator==(const Loc_BaseLoc &left, const Loc_BaseLoc &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Loc_ExtLoc &left, const Loc_ExtLoc &right) {
    (void)left; (void) right;
	return true ;
  }
  
Loc::Loc() {
    Loc_BaseLoc COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Loc_BaseLoc(const struct Loc d) { return std::holds_alternative<Loc_BaseLoc>(d.v); }
  
inline bool is_Loc_ExtLoc(const struct Loc d) { return std::holds_alternative<Loc_ExtLoc>(d.v); }

}// end of namespace GhostLoc_Compile 
namespace Cells  {


  template <typename V>
CellContents<V>::CellContents() {
    v = get_default<V>::call();
  }
  template <typename V>
bool operator==(const CellContents<V> &left, const CellContents<V> &right)  {
    	return true 		&& left.v == right.v
    ;
  }

}// end of namespace Cells 
namespace RequestIds_Compile  {


}// end of namespace RequestIds_Compile 
namespace CacheStatusType_Compile  {

  
bool operator==(const Status_Clean &left, const Status_Clean &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Status_Dirty &left, const Status_Dirty &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Status_Writeback &left, const Status_Writeback &right) {
    (void)left; (void) right;
	return true ;
  }
  
Status::Status() {
    Status_Clean COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Status_Clean(const struct Status d) { return std::holds_alternative<Status_Clean>(d.v); }
  
inline bool is_Status_Dirty(const struct Status d) { return std::holds_alternative<Status_Dirty>(d.v); }
  
inline bool is_Status_Writeback(const struct Status d) { return std::holds_alternative<Status_Writeback>(d.v); }

}// end of namespace CacheStatusType_Compile 
namespace DiskIfc_Compile  {




  
ReqRead::ReqRead() {
  }
  
bool operator==(const ReqRead &left, const ReqRead &right)  {
    	return true ;
  }

  
ReqWrite::ReqWrite() {
    data = DafnySequence<uint8>();
  }
  
bool operator==(const ReqWrite &left, const ReqWrite &right)  {
    	return true 		&& left.data == right.data
    ;
  }

  
RespRead::RespRead() {
    data = DafnySequence<uint8>();
  }
  
bool operator==(const RespRead &left, const RespRead &right)  {
    	return true 		&& left.data == right.data
    ;
  }

  
RespWrite::RespWrite() {
  }
  
bool operator==(const RespWrite &left, const RespWrite &right)  {
    	return true ;
  }

  
bool operator==(const DiskOp_ReqReadOp &left, const DiskOp_ReqReadOp &right) {
    	return true 		&& left.reqRead == right.reqRead
    ;
  }
  
bool operator==(const DiskOp_ReqWriteOp &left, const DiskOp_ReqWriteOp &right) {
    	return true 		&& left.reqWrite == right.reqWrite
    ;
  }
  
bool operator==(const DiskOp_RespReadOp &left, const DiskOp_RespReadOp &right) {
    	return true 		&& left.respRead == right.respRead
    ;
  }
  
bool operator==(const DiskOp_RespWriteOp &left, const DiskOp_RespWriteOp &right) {
    	return true 		&& left.respWrite == right.respWrite
    ;
  }
  
DiskOp::DiskOp() {
    DiskOp_ReqReadOp COMPILER_result_subStruct;
    COMPILER_result_subStruct.reqRead = DiskIfc_Compile::ReqRead();
    v = COMPILER_result_subStruct;
  }
  
inline bool is_DiskOp_ReqReadOp(const struct DiskOp d) { return std::holds_alternative<DiskOp_ReqReadOp>(d.v); }
  
inline bool is_DiskOp_ReqWriteOp(const struct DiskOp d) { return std::holds_alternative<DiskOp_ReqWriteOp>(d.v); }
  
inline bool is_DiskOp_RespReadOp(const struct DiskOp d) { return std::holds_alternative<DiskOp_RespReadOp>(d.v); }
  
inline bool is_DiskOp_RespWriteOp(const struct DiskOp d) { return std::holds_alternative<DiskOp_RespWriteOp>(d.v); }


}// end of namespace DiskIfc_Compile 
namespace CacheIfc_Compile  {


  
bool operator==(const Input_WriteInput &left, const Input_WriteInput &right) {
    	return true 		&& left.data == right.data
    ;
  }
  
bool operator==(const Input_ReadInput &left, const Input_ReadInput &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Input_SyncInput &left, const Input_SyncInput &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Input_HavocInput &left, const Input_HavocInput &right) {
    (void)left; (void) right;
	return true ;
  }
  
Input::Input() {
    Input_WriteInput COMPILER_result_subStruct;
    COMPILER_result_subStruct.data = DafnySequence<uint8>();
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Input_WriteInput(const struct Input d) { return std::holds_alternative<Input_WriteInput>(d.v); }
  
inline bool is_Input_ReadInput(const struct Input d) { return std::holds_alternative<Input_ReadInput>(d.v); }
  
inline bool is_Input_SyncInput(const struct Input d) { return std::holds_alternative<Input_SyncInput>(d.v); }
  
inline bool is_Input_HavocInput(const struct Input d) { return std::holds_alternative<Input_HavocInput>(d.v); }

  
bool operator==(const Output_WriteOutput &left, const Output_WriteOutput &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Output_ReadOutput &left, const Output_ReadOutput &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Output_SyncOutput &left, const Output_SyncOutput &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Output_HavocOutput &left, const Output_HavocOutput &right) {
    (void)left; (void) right;
	return true ;
  }
  
Output::Output() {
    Output_WriteOutput COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Output_WriteOutput(const struct Output d) { return std::holds_alternative<Output_WriteOutput>(d.v); }
  
inline bool is_Output_ReadOutput(const struct Output d) { return std::holds_alternative<Output_ReadOutput>(d.v); }
  
inline bool is_Output_SyncOutput(const struct Output d) { return std::holds_alternative<Output_SyncOutput>(d.v); }
  
inline bool is_Output_HavocOutput(const struct Output d) { return std::holds_alternative<Output_HavocOutput>(d.v); }


  
Op::Op() {
    input = CacheIfc_Compile::Input();
    output = CacheIfc_Compile::Output();
  }
  
bool operator==(const Op &left, const Op &right)  {
    	return true 		&& left.input == right.input
    		&& left.output == right.output
    ;
  }
}// end of namespace CacheIfc_Compile 
namespace CacheSSM_Compile  {





  
bool operator==(const Entry_Empty &left, const Entry_Empty &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Entry_Reading &left, const Entry_Reading &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Entry_Entry &left, const Entry_Entry &right) {
    	return true 		&& left.data == right.data
    ;
  }
  
Entry::Entry() {
    Entry_Empty COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Entry_Empty(const struct Entry d) { return std::holds_alternative<Entry_Empty>(d.v); }
  
inline bool is_Entry_Reading(const struct Entry d) { return std::holds_alternative<Entry_Reading>(d.v); }
  
inline bool is_Entry_Entry(const struct Entry d) { return std::holds_alternative<Entry_Entry>(d.v); }

  
bool operator==(const M_M &left, const M_M &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const M_Fail &left, const M_Fail &right) {
    (void)left; (void) right;
	return true ;
  }
  
M::M() {
    M_M COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_M_M(const struct M d) { return std::holds_alternative<M_M>(d.v); }
  
inline bool is_M_Fail(const struct M d) { return std::holds_alternative<M_Fail>(d.v); }

  
bool operator==(const Step_StartReadStep &left, const Step_StartReadStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_FinishReadStep &left, const Step_FinishReadStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_StartWritebackStep &left, const Step_StartWritebackStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_FinishWritebackStep &left, const Step_FinishWritebackStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_EvictStep &left, const Step_EvictStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_ObserveCleanForSyncStep &left, const Step_ObserveCleanForSyncStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_ApplyReadStep &left, const Step_ApplyReadStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_ApplyWriteStep &left, const Step_ApplyWriteStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_MarkDirtyStep &left, const Step_MarkDirtyStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_HavocNewStep &left, const Step_HavocNewStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_HavocEvictStep &left, const Step_HavocEvictStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
Step::Step() {
    Step_StartReadStep COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Step_StartReadStep(const struct Step d) { return std::holds_alternative<Step_StartReadStep>(d.v); }
  
inline bool is_Step_FinishReadStep(const struct Step d) { return std::holds_alternative<Step_FinishReadStep>(d.v); }
  
inline bool is_Step_StartWritebackStep(const struct Step d) { return std::holds_alternative<Step_StartWritebackStep>(d.v); }
  
inline bool is_Step_FinishWritebackStep(const struct Step d) { return std::holds_alternative<Step_FinishWritebackStep>(d.v); }
  
inline bool is_Step_EvictStep(const struct Step d) { return std::holds_alternative<Step_EvictStep>(d.v); }
  
inline bool is_Step_ObserveCleanForSyncStep(const struct Step d) { return std::holds_alternative<Step_ObserveCleanForSyncStep>(d.v); }
  
inline bool is_Step_ApplyReadStep(const struct Step d) { return std::holds_alternative<Step_ApplyReadStep>(d.v); }
  
inline bool is_Step_ApplyWriteStep(const struct Step d) { return std::holds_alternative<Step_ApplyWriteStep>(d.v); }
  
inline bool is_Step_MarkDirtyStep(const struct Step d) { return std::holds_alternative<Step_MarkDirtyStep>(d.v); }
  
inline bool is_Step_HavocNewStep(const struct Step d) { return std::holds_alternative<Step_HavocNewStep>(d.v); }
  
inline bool is_Step_HavocEvictStep(const struct Step d) { return std::holds_alternative<Step_HavocEvictStep>(d.v); }





}// end of namespace CacheSSM_Compile 
namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile  {


  
Token::Token() {
  }
  
bool operator==(const Token &left, const Token &right)  {
    	return true ;
  }


}// end of namespace Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile 
namespace DiskSingletonLoc_Compile  {


}// end of namespace DiskSingletonLoc_Compile 
namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile  {




}// end of namespace DiskPCM_ON_CacheIfc_CacheSSM__Compile 
namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile  {


  
Token::Token() {
  }
  
bool operator==(const Token &left, const Token &right)  {
    	return true ;
  }


}// end of namespace Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile 
namespace DiskToken_ON_CacheIfc_CacheSSM__Compile  {




  
Token::Token() {
    val = CacheSSM_Compile::M();
  }
  
bool operator==(const Token &left, const Token &right)  {
    	return true 		&& left.val == right.val
    ;
  }



}// end of namespace DiskToken_ON_CacheIfc_CacheSSM__Compile 
namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile  {








}// end of namespace DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile 
namespace CacheResources_Compile  {












  
DiskPageMap::DiskPageMap() {
  }
  
bool operator==(const DiskPageMap &left, const DiskPageMap &right)  {
    	return true ;
  }

  
HavocPermission::HavocPermission() {
  }
  
bool operator==(const HavocPermission &left, const HavocPermission &right)  {
    	return true ;
  }

  
CacheStatus::CacheStatus() {
  }
  
bool operator==(const CacheStatus &left, const CacheStatus &right)  {
    	return true ;
  }

  
CacheEmpty::CacheEmpty() {
  }
  
bool operator==(const CacheEmpty &left, const CacheEmpty &right)  {
    	return true ;
  }

  
CacheReading::CacheReading() {
  }
  
bool operator==(const CacheReading &left, const CacheReading &right)  {
    	return true ;
  }

  
CacheEntry::CacheEntry() {
  }
  
bool operator==(const CacheEntry &left, const CacheEntry &right)  {
    	return true ;
  }

  
DiskWriteTicket::DiskWriteTicket() {
  }
  
bool operator==(const DiskWriteTicket &left, const DiskWriteTicket &right)  {
    	return true ;
  }

  
DiskWriteStub::DiskWriteStub() {
  }
  
bool operator==(const DiskWriteStub &left, const DiskWriteStub &right)  {
    	return true ;
  }

  
DiskReadTicket::DiskReadTicket() {
  }
  
bool operator==(const DiskReadTicket &left, const DiskReadTicket &right)  {
    	return true ;
  }

  
DiskReadStub::DiskReadStub() {
  }
  
bool operator==(const DiskReadStub &left, const DiskReadStub &right)  {
    	return true ;
  }

}// end of namespace CacheResources_Compile 
namespace CacheHandle_Compile  {







  
PageHandle::PageHandle() {
    data__ptr = Ptrs::get_Ptr_default();
    disk__addr = 0;
  }
  
bool operator==(const PageHandle &left, const PageHandle &right)  {
    	return true 		&& left.data__ptr == right.data__ptr
    		&& left.disk__addr == right.disk__addr
    ;
  }

  
Key::Key() {
    data__ptr = Ptrs::get_Ptr_default();
    idx__cell = Cells::get_Cell_default<CacheHandle_Compile::PageHandle>();
  }
  
bool operator==(const Key &left, const Key &right)  {
    	return true 		&& left.data__ptr == right.data__ptr
    		&& left.idx__cell == right.idx__cell
    ;
  }

  
bool operator==(const Handle_CacheEmptyHandle &left, const Handle_CacheEmptyHandle &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Handle_CacheReadingHandle &left, const Handle_CacheReadingHandle &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Handle_CacheEntryHandle &left, const Handle_CacheEntryHandle &right) {
    (void)left; (void) right;
	return true ;
  }
  
Handle::Handle() {
    Handle_CacheEmptyHandle COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Handle_CacheEmptyHandle(const struct Handle d) { return std::holds_alternative<Handle_CacheEmptyHandle>(d.v); }
  
inline bool is_Handle_CacheReadingHandle(const struct Handle d) { return std::holds_alternative<Handle_CacheReadingHandle>(d.v); }
  
inline bool is_Handle_CacheEntryHandle(const struct Handle d) { return std::holds_alternative<Handle_CacheEntryHandle>(d.v); }

}// end of namespace CacheHandle_Compile 
namespace RwLock_Compile  {




  
bool operator==(const Flag_Unmapped &left, const Flag_Unmapped &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_Reading &left, const Flag_Reading &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_Reading__ExcLock &left, const Flag_Reading__ExcLock &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_Available &left, const Flag_Available &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_Claimed &left, const Flag_Claimed &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_Writeback &left, const Flag_Writeback &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_Writeback__Claimed &left, const Flag_Writeback__Claimed &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_Writeback__PendingExcLock &left, const Flag_Writeback__PendingExcLock &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_PendingExcLock &left, const Flag_PendingExcLock &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_ExcLock__Clean &left, const Flag_ExcLock__Clean &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Flag_ExcLock__Dirty &left, const Flag_ExcLock__Dirty &right) {
    (void)left; (void) right;
	return true ;
  }
  
Flag::Flag() {
    Flag_Unmapped COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Flag_Unmapped(const struct Flag d) { return std::holds_alternative<Flag_Unmapped>(d.v); }
  
inline bool is_Flag_Reading(const struct Flag d) { return std::holds_alternative<Flag_Reading>(d.v); }
  
inline bool is_Flag_Reading__ExcLock(const struct Flag d) { return std::holds_alternative<Flag_Reading__ExcLock>(d.v); }
  
inline bool is_Flag_Available(const struct Flag d) { return std::holds_alternative<Flag_Available>(d.v); }
  
inline bool is_Flag_Claimed(const struct Flag d) { return std::holds_alternative<Flag_Claimed>(d.v); }
  
inline bool is_Flag_Writeback(const struct Flag d) { return std::holds_alternative<Flag_Writeback>(d.v); }
  
inline bool is_Flag_Writeback__Claimed(const struct Flag d) { return std::holds_alternative<Flag_Writeback__Claimed>(d.v); }
  
inline bool is_Flag_Writeback__PendingExcLock(const struct Flag d) { return std::holds_alternative<Flag_Writeback__PendingExcLock>(d.v); }
  
inline bool is_Flag_PendingExcLock(const struct Flag d) { return std::holds_alternative<Flag_PendingExcLock>(d.v); }
  
inline bool is_Flag_ExcLock__Clean(const struct Flag d) { return std::holds_alternative<Flag_ExcLock__Clean>(d.v); }
  
inline bool is_Flag_ExcLock__Dirty(const struct Flag d) { return std::holds_alternative<Flag_ExcLock__Dirty>(d.v); }



  
bool operator==(const SharedState_SharedPending &left, const SharedState_SharedPending &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const SharedState_SharedPending2 &left, const SharedState_SharedPending2 &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const SharedState_SharedObtained &left, const SharedState_SharedObtained &right) {
    	return true 		&& left.b == right.b
    ;
  }
  
SharedState::SharedState() {
    SharedState_SharedPending COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_SharedState_SharedPending(const struct SharedState d) { return std::holds_alternative<SharedState_SharedPending>(d.v); }
  
inline bool is_SharedState_SharedPending2(const struct SharedState d) { return std::holds_alternative<SharedState_SharedPending2>(d.v); }
  
inline bool is_SharedState_SharedObtained(const struct SharedState d) { return std::holds_alternative<SharedState_SharedObtained>(d.v); }

  
bool operator==(const ExcState_ExcNone &left, const ExcState_ExcNone &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const ExcState_ExcClaim &left, const ExcState_ExcClaim &right) {
    	return true 		&& left.b == right.b
    ;
  }
  
bool operator==(const ExcState_ExcPendingAwaitWriteback &left, const ExcState_ExcPendingAwaitWriteback &right) {
    	return true 		&& left.b == right.b
    ;
  }
  
bool operator==(const ExcState_ExcPending &left, const ExcState_ExcPending &right) {
    	return true 		&& left.clean == right.clean
    		&& left.b == right.b
    ;
  }
  
bool operator==(const ExcState_ExcObtained &left, const ExcState_ExcObtained &right) {
    	return true 		&& left.clean == right.clean
    ;
  }
  
ExcState::ExcState() {
    ExcState_ExcNone COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_ExcState_ExcNone(const struct ExcState d) { return std::holds_alternative<ExcState_ExcNone>(d.v); }
  
inline bool is_ExcState_ExcClaim(const struct ExcState d) { return std::holds_alternative<ExcState_ExcClaim>(d.v); }
  
inline bool is_ExcState_ExcPendingAwaitWriteback(const struct ExcState d) { return std::holds_alternative<ExcState_ExcPendingAwaitWriteback>(d.v); }
  
inline bool is_ExcState_ExcPending(const struct ExcState d) { return std::holds_alternative<ExcState_ExcPending>(d.v); }
  
inline bool is_ExcState_ExcObtained(const struct ExcState d) { return std::holds_alternative<ExcState_ExcObtained>(d.v); }

  
bool operator==(const WritebackState_WritebackNone &left, const WritebackState_WritebackNone &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const WritebackState_WritebackObtained &left, const WritebackState_WritebackObtained &right) {
    	return true 		&& left.b == right.b
    ;
  }
  
WritebackState::WritebackState() {
    WritebackState_WritebackNone COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_WritebackState_WritebackNone(const struct WritebackState d) { return std::holds_alternative<WritebackState_WritebackNone>(d.v); }
  
inline bool is_WritebackState_WritebackObtained(const struct WritebackState d) { return std::holds_alternative<WritebackState_WritebackObtained>(d.v); }

  
bool operator==(const ReadState_ReadNone &left, const ReadState_ReadNone &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const ReadState_ReadPending &left, const ReadState_ReadPending &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const ReadState_ReadPendingCounted &left, const ReadState_ReadPendingCounted &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const ReadState_ReadObtained &left, const ReadState_ReadObtained &right) {
    (void)left; (void) right;
	return true ;
  }
  
ReadState::ReadState() {
    ReadState_ReadNone COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_ReadState_ReadNone(const struct ReadState d) { return std::holds_alternative<ReadState_ReadNone>(d.v); }
  
inline bool is_ReadState_ReadPending(const struct ReadState d) { return std::holds_alternative<ReadState_ReadPending>(d.v); }
  
inline bool is_ReadState_ReadPendingCounted(const struct ReadState d) { return std::holds_alternative<ReadState_ReadPendingCounted>(d.v); }
  
inline bool is_ReadState_ReadObtained(const struct ReadState d) { return std::holds_alternative<ReadState_ReadObtained>(d.v); }

  
bool operator==(const CentralState_CentralNone &left, const CentralState_CentralNone &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const CentralState_CentralState &left, const CentralState_CentralState &right) {
    	return true 		&& left.flag == right.flag
    		&& left.stored__value == right.stored__value
    ;
  }
  
CentralState::CentralState() {
    CentralState_CentralNone COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_CentralState_CentralNone(const struct CentralState d) { return std::holds_alternative<CentralState_CentralNone>(d.v); }
  
inline bool is_CentralState_CentralState(const struct CentralState d) { return std::holds_alternative<CentralState_CentralState>(d.v); }

  
bool operator==(const M_M &left, const M_M &right) {
    	return true 		&& left.central == right.central
    		&& left.exc == right.exc
    		&& left.read == right.read
    		&& left.writeback == right.writeback
    ;
  }
  
bool operator==(const M_Fail &left, const M_Fail &right) {
    (void)left; (void) right;
	return true ;
  }
  
M::M() {
    M_M COMPILER_result_subStruct;
    COMPILER_result_subStruct.central = RwLock_Compile::CentralState();
    COMPILER_result_subStruct.exc = RwLock_Compile::ExcState();
    COMPILER_result_subStruct.read = RwLock_Compile::ReadState();
    COMPILER_result_subStruct.writeback = RwLock_Compile::WritebackState();
    v = COMPILER_result_subStruct;
  }
  
inline bool is_M_M(const struct M d) { return std::holds_alternative<M_M>(d.v); }
  
inline bool is_M_Fail(const struct M d) { return std::holds_alternative<M_Fail>(d.v); }


}// end of namespace RwLock_Compile 
namespace Rw_PCMWrap_ON_RwLock__Compile  {





  
M::M() {
  }
  
bool operator==(const M &left, const M &right)  {
    	return true ;
  }
}// end of namespace Rw_PCMWrap_ON_RwLock__Compile 
namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {


  
Token::Token() {
  }
  
bool operator==(const Token &left, const Token &right)  {
    	return true ;
  }


}// end of namespace Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile 
namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile  {





}// end of namespace PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile 
namespace Rw_PCMExt_ON_RwLock__Compile  {








}// end of namespace Rw_PCMExt_ON_RwLock__Compile 
namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile  {


  
Token::Token() {
  }
  
bool operator==(const Token &left, const Token &right)  {
    	return true ;
  }


}// end of namespace Tokens_ON_Rw__PCMExt__ON__RwLock____Compile 
namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile  {






}// end of namespace ExtTokens_ON_Rw__PCMWrap__ON__RwLock___Rw__PCMExt__ON__RwLock____Compile 
namespace RwTokens_ON_RwLock__Compile  {











}// end of namespace RwTokens_ON_RwLock__Compile 
namespace RwLockToken_Compile  {







  
CentralToken::CentralToken() {
  }
  
bool operator==(const CentralToken &left, const CentralToken &right)  {
    	return true ;
  }

  
WritebackObtainedToken::WritebackObtainedToken() {
  }
  
bool operator==(const WritebackObtainedToken &left, const WritebackObtainedToken &right)  {
    	return true ;
  }

  
SharedPendingToken::SharedPendingToken() {
  }
  
bool operator==(const SharedPendingToken &left, const SharedPendingToken &right)  {
    	return true ;
  }

  
SharedPending2Token::SharedPending2Token() {
  }
  
bool operator==(const SharedPending2Token &left, const SharedPending2Token &right)  {
    	return true ;
  }

  
SharedObtainedToken::SharedObtainedToken() {
  }
  
bool operator==(const SharedObtainedToken &left, const SharedObtainedToken &right)  {
    	return true ;
  }

}// end of namespace RwLockToken_Compile 
namespace GlinearMap_Compile  {

}// end of namespace GlinearMap_Compile 
namespace CacheAIOParams_Compile  {






  
IOSlotAccess::IOSlotAccess() {
  }
  
bool operator==(const IOSlotAccess &left, const IOSlotAccess &right)  {
    	return true ;
  }

  
ReadG::ReadG() {
  }
  
bool operator==(const ReadG &left, const ReadG &right)  {
    	return true ;
  }

  
ReadvG::ReadvG() {
  }
  
bool operator==(const ReadvG &left, const ReadvG &right)  {
    	return true ;
  }

  
WriteG::WriteG() {
  }
  
bool operator==(const WriteG &left, const WriteG &right)  {
    	return true ;
  }

  
WritevG::WritevG() {
  }
  
bool operator==(const WritevG &left, const WritevG &right)  {
    	return true ;
  }




}// end of namespace CacheAIOParams_Compile 
namespace BitOps_Compile  {


  uint8 __default::bit__or__uint8(uint8 a, uint8 b)
  {
    return uint8((uint8(a)) | (uint8(b)));
  }
  uint8 __default::bit__and__uint8(uint8 a, uint8 b)
  {
    return uint8((uint8(a)) & (uint8(b)));
  }
  uint8 __default::bit__xor__uint8(uint8 a, uint8 b)
  {
    return uint8((uint8(a)) ^ (uint8(b)));
  }
  uint64 __default::bit__or__uint64(uint64 a, uint64 b)
  {
    return uint64((uint64(a)) | (uint64(b)));
  }
  uint64 __default::bit__and__uint64(uint64 a, uint64 b)
  {
    return uint64((uint64(a)) & (uint64(b)));
  }
  uint64 __default::bit__xor__uint64(uint64 a, uint64 b)
  {
    return uint64((uint64(a)) ^ (uint64(b)));
  }
}// end of namespace BitOps_Compile 
namespace Atomics  {







}// end of namespace Atomics 
namespace CounterPCM_Compile  {

  
M::M() {
  }
  
bool operator==(const M &left, const M &right)  {
    	return true ;
  }

}// end of namespace CounterPCM_Compile 
namespace Tokens_ON_CounterPCM__Compile  {


  
Token::Token() {
  }
  
bool operator==(const Token &left, const Token &right)  {
    	return true ;
  }


}// end of namespace Tokens_ON_CounterPCM__Compile 
namespace ClientCounter_Compile  {




  
Client::Client() {
  }
  
bool operator==(const Client &left, const Client &right)  {
    	return true ;
  }

  
Clients::Clients() {
  }
  
bool operator==(const Clients &left, const Clients &right)  {
    	return true ;
  }

}// end of namespace ClientCounter_Compile 
namespace AtomicRefcountImpl_Compile  {










  
RG::RG() {
  }
  
bool operator==(const RG &left, const RG &right)  {
    	return true ;
  }

  
AtomicRefcount::AtomicRefcount() {
    a = Atomics::get_Atomic_default<uint8, AtomicRefcountImpl_Compile::RG>();
  }
  
bool operator==(const AtomicRefcount &left, const AtomicRefcount &right)  {
    	return true 		&& left.a == right.a
    ;
  }

  bool __default::is__refcount__eq(AtomicRefcountImpl_Compile::AtomicRefcount& a, uint8 val)
  {
    bool is__zero = false;
    uint8 _3327_c = 0;
    {
      Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG> * _3328_atomic__tmp0;
      _3328_atomic__tmp0 = &( ((a).a));
      uint8 _out0;
      _out0 = Atomics::execute__atomic__load <uint8, AtomicRefcountImpl_Compile::RG> ((*_3328_atomic__tmp0));
      _3327_c = _out0;
      if ((_3327_c) == (val)) {
      } else {
      }
    }
    is__zero = (_3327_c) == (val);
    return is__zero;
  }
  void __default::inc__refcount__for__reading(AtomicRefcountImpl_Compile::AtomicRefcount& a)
  {
    uint8 _3329_orig__value = 0;
    {
      Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG> * _3330_atomic__tmp0;
      _3330_atomic__tmp0 = &( ((a).a));
      uint8 _out1;
      _out1 = Atomics::execute__atomic__fetch__add__uint8 <AtomicRefcountImpl_Compile::RG> ((*_3330_atomic__tmp0), (uint8)1);
      _3329_orig__value = _out1;
    }
  }
  void __default::inc__refcount__for__shared(AtomicRefcountImpl_Compile::AtomicRefcount& a)
  {
    uint8 _3331_orig__value = 0;
    {
      Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG> * _3332_atomic__tmp0;
      _3332_atomic__tmp0 = &( ((a).a));
      uint8 _out2;
      _out2 = Atomics::execute__atomic__fetch__add__uint8 <AtomicRefcountImpl_Compile::RG> ((*_3332_atomic__tmp0), (uint8)1);
      _3331_orig__value = _out2;
    }
  }
  void __default::inc__refcount__for__exc(AtomicRefcountImpl_Compile::AtomicRefcount& a)
  {
    uint8 _3333_orig__value = 0;
    {
      Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG> * _3334_atomic__tmp0;
      _3334_atomic__tmp0 = &( ((a).a));
      uint8 _out3;
      _out3 = Atomics::execute__atomic__fetch__add__uint8 <AtomicRefcountImpl_Compile::RG> ((*_3334_atomic__tmp0), (uint8)1);
      _3333_orig__value = _out3;
    }
  }
  void __default::dec__refcount__for__shared__pending(AtomicRefcountImpl_Compile::AtomicRefcount& a)
  {
    uint8 _3335_orig__value = 0;
    {
      Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG> * _3336_atomic__tmp0;
      _3336_atomic__tmp0 = &( ((a).a));
      uint8 _out4;
      _out4 = Atomics::execute__atomic__fetch__sub__uint8 <AtomicRefcountImpl_Compile::RG> ((*_3336_atomic__tmp0), (uint8)1);
      _3335_orig__value = _out4;
    }
  }
  void __default::dec__refcount__for__shared__obtained(AtomicRefcountImpl_Compile::AtomicRefcount& a)
  {
    uint8 _3337_orig__value = 0;
    {
      Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG> * _3338_atomic__tmp0;
      _3338_atomic__tmp0 = &( ((a).a));
      uint8 _out5;
      _out5 = Atomics::execute__atomic__fetch__sub__uint8 <AtomicRefcountImpl_Compile::RG> ((*_3338_atomic__tmp0), (uint8)1);
      _3337_orig__value = _out5;
    }
  }
}// end of namespace AtomicRefcountImpl_Compile 
namespace AtomicIndexLookupImpl_Compile  {










  uint32 __default::read__known__cache__idx(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a)
  {
    uint32 cache__idx = 0;
    uint32 _3339_ci = 0;
    {
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * _3340_atomic__tmp0;
      _3340_atomic__tmp0 = &( a);
      uint32 _out6;
      _out6 = Atomics::execute__atomic__load <uint32, CacheResources_Compile::DiskPageMap> ((*_3340_atomic__tmp0));
      _3339_ci = _out6;
    }
    cache__idx = _3339_ci;
    return cache__idx;
  }
  uint32 __default::atomic__index__lookup__read(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a)
  {
    uint32 cache__idx = 0;
    uint32 _3341_ci = 0;
    {
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * _3342_atomic__tmp0;
      _3342_atomic__tmp0 = &( a);
      uint32 _out7;
      _out7 = Atomics::execute__atomic__load <uint32, CacheResources_Compile::DiskPageMap> ((*_3342_atomic__tmp0));
      _3341_ci = _out7;
    }
    cache__idx = _3341_ci;
    return cache__idx;
  }
  void __default::atomic__index__lookup__clear__mapping(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a)
  {
    {
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * _3343_atomic__tmp0;
      _3343_atomic__tmp0 = &( a);
      Atomics::execute__atomic__store <uint32, CacheResources_Compile::DiskPageMap> ((*_3343_atomic__tmp0), uint32(AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED));
    }
  }
  void __default::atomic__index__lookup__clear__mapping__havoc(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a)
  {
    {
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * _3344_atomic__tmp0;
      _3344_atomic__tmp0 = &( a);
      Atomics::execute__atomic__store <uint32, CacheResources_Compile::DiskPageMap> ((*_3344_atomic__tmp0), uint32(AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED));
    }
  }
  bool __default::atomic__index__lookup__add__mapping(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a, uint64 disk__idx, uint32 cache__idx)
  {
    bool success = false;
    bool _3345_did__set = false;
    {
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * _3346_atomic__tmp0;
      _3346_atomic__tmp0 = &( a);
      bool _out8;
      _out8 = Atomics::execute__atomic__compare__and__set__strong <uint32, CacheResources_Compile::DiskPageMap> ((*_3346_atomic__tmp0), uint32(AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED), uint32(cache__idx));
      _3345_did__set = _out8;
      if (_3345_did__set) {
      } else {
      }
    }
    success = _3345_did__set;
    return success;
  }
  bool __default::atomic__index__lookup__add__mapping__instant(Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> & a, uint64 disk__idx, uint32 cache__idx)
  {
    bool success = false;
    bool _3347_did__set = false;
    {
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * _3348_atomic__tmp0;
      _3348_atomic__tmp0 = &( a);
      bool _out9;
      _out9 = Atomics::execute__atomic__compare__and__set__strong <uint32, CacheResources_Compile::DiskPageMap> ((*_3348_atomic__tmp0), uint32(AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED), uint32(cache__idx));
      _3347_did__set = _out9;
      if (_3347_did__set) {
      } else {
      }
    }
    success = _3347_did__set;
    return success;
  }
   uint32 __default::NOT__MAPPED =  init__NOT__MAPPED();
}// end of namespace AtomicIndexLookupImpl_Compile 
namespace AtomicStatusImpl_Compile  {













  
G::G() {
  }
  
bool operator==(const G &left, const G &right)  {
    	return true ;
  }

  
AtomicStatus::AtomicStatus() {
    atomic = Atomics::get_Atomic_default<uint8, AtomicStatusImpl_Compile::G>();
  }
  
bool operator==(const AtomicStatus &left, const AtomicStatus &right)  {
    	return true 		&& left.atomic == right.atomic
    ;
  }
  bool AtomicStatus::try__acquire__writeback(bool with__access)
  {
    bool success = false;
    uint8 _3349_cur__flag = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3350_atomic__tmp0;
      _3350_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out10;
      _out10 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3350_atomic__tmp0));
      _3349_cur__flag = _out10;
    }
    if (!(((_3349_cur__flag) == ((uint8)0)) || ((with__access) && ((_3349_cur__flag) == (AtomicStatusImpl_Compile::__default::flag__accessed()))))) {
      success = false;
    } else {
      bool _3351_did__set = false;
      {
        Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3352_atomic__tmp1;
        _3352_atomic__tmp1 = &( ((*this).atomic));
        bool _out11;
        _out11 = Atomics::execute__atomic__compare__and__set__strong <uint8, AtomicStatusImpl_Compile::G> ((*_3352_atomic__tmp1), (uint8)0, AtomicStatusImpl_Compile::__default::flag__writeback());
        _3351_did__set = _out11;
      }
      if (_3351_did__set) {
        success = true;
      } else if (!(with__access)) {
        success = false;
      } else {
        bool _3353_did__set = false;
        {
          Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3354_atomic__tmp2;
          _3354_atomic__tmp2 = &( ((*this).atomic));
          bool _out12;
          _out12 = Atomics::execute__atomic__compare__and__set__strong <uint8, AtomicStatusImpl_Compile::G> ((*_3354_atomic__tmp2), AtomicStatusImpl_Compile::__default::flag__accessed(), (AtomicStatusImpl_Compile::__default::flag__writeback()) + (AtomicStatusImpl_Compile::__default::flag__accessed()));
          _3353_did__set = _out12;
          if (_3353_did__set) {
          } else {
          }
        }
        success = _3353_did__set;
      }
    }
    return success;
  }
  void AtomicStatus::release__writeback()
  {
    uint8 _3355___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3356_atomic__tmp0;
      _3356_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out13;
      _out13 = Atomics::execute__atomic__fetch__xor__uint8 <AtomicStatusImpl_Compile::G> ((*_3356_atomic__tmp0), (AtomicStatusImpl_Compile::__default::flag__writeback()) + (AtomicStatusImpl_Compile::__default::flag__clean()));
      _3355___ = _out13;
    }
  }
  struct Tuple<bool, bool> AtomicStatus::try__check__writeback__isnt__set()
  {
    bool success = false;
    bool clean = false;
    uint8 _3357_f = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3358_atomic__tmp0;
      _3358_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out14;
      _out14 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3358_atomic__tmp0));
      _3357_f = _out14;
    }
    success = (BitOps_Compile::__default::bit__and__uint8(_3357_f, AtomicStatusImpl_Compile::__default::flag__writeback())) == ((uint8)0);
    clean = (BitOps_Compile::__default::bit__and__uint8(_3357_f, AtomicStatusImpl_Compile::__default::flag__clean())) != ((uint8)0);
    return Tuple<bool, bool>(success, clean);
  }
  bool AtomicStatus::try__alloc()
  {
    bool success = false;
    uint8 _3359_f = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3360_atomic__tmp0;
      _3360_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out15;
      _out15 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3360_atomic__tmp0));
      _3359_f = _out15;
    }
    if ((_3359_f) != (AtomicStatusImpl_Compile::__default::flag__unmapped())) {
      success = false;
    } else {
      bool _3361_did__set = false;
      {
        Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3362_atomic__tmp1;
        _3362_atomic__tmp1 = &( ((*this).atomic));
        bool _out16;
        _out16 = Atomics::execute__atomic__compare__and__set__strong <uint8, AtomicStatusImpl_Compile::G> ((*_3362_atomic__tmp1), AtomicStatusImpl_Compile::__default::flag__unmapped(), (AtomicStatusImpl_Compile::__default::flag__exc()) + (AtomicStatusImpl_Compile::__default::flag__claim()));
        _3361_did__set = _out16;
        if (_3361_did__set) {
        } else {
        }
      }
      success = _3361_did__set;
    }
    return success;
  }
  void AtomicStatus::clear__exc__bit__during__load__phase()
  {
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3363_atomic__tmp0;
      _3363_atomic__tmp0 = &( ((*this).atomic));
      Atomics::execute__atomic__store <uint8, AtomicStatusImpl_Compile::G> ((*_3363_atomic__tmp0), ((AtomicStatusImpl_Compile::__default::flag__accessed()) + (AtomicStatusImpl_Compile::__default::flag__reading())) + (AtomicStatusImpl_Compile::__default::flag__clean()));
    }
  }
  void AtomicStatus::load__phase__finish()
  {
    uint8 _3364___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3365_atomic__tmp0;
      _3365_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out17;
      _out17 = Atomics::execute__atomic__fetch__and__uint8 <AtomicStatusImpl_Compile::G> ((*_3365_atomic__tmp0), ((uint8)255) - (AtomicStatusImpl_Compile::__default::flag__reading()));
      _3364___ = _out17;
    }
  }
  void AtomicStatus::load__phase__finish__threadless()
  {
    uint8 _3366___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3367_atomic__tmp0;
      _3367_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out18;
      _out18 = Atomics::execute__atomic__fetch__and__uint8 <AtomicStatusImpl_Compile::G> ((*_3367_atomic__tmp0), ((uint8)255) - (AtomicStatusImpl_Compile::__default::flag__reading()));
      _3366___ = _out18;
    }
  }
  bool AtomicStatus::quicktest__is__exc__locked()
  {
    bool is__exc__locked = false;
    uint8 _3368_v = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3369_atomic__tmp0;
      _3369_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out19;
      _out19 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3369_atomic__tmp0));
      _3368_v = _out19;
    }
    is__exc__locked = (uint8((uint8(_3368_v)) & (uint8(AtomicStatusImpl_Compile::__default::flag__exc())))) != ((uint8)0);
    return is__exc__locked;
    return is__exc__locked;
  }
  struct Tuple<bool, bool, bool> __attribute__((always_inline)) AtomicStatus::is__exc__locked__or__free()
  {
    bool is__locked = false;
    bool is__free = false;
    bool is__accessed = false;
    uint8 _3370_f = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3371_atomic__tmp0;
      _3371_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out20;
      _out20 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3371_atomic__tmp0));
      _3370_f = _out20;
    }
    is__locked = (BitOps_Compile::__default::bit__and__uint8(_3370_f, AtomicStatusImpl_Compile::__default::flag__exc())) != ((uint8)0);
    is__free = (BitOps_Compile::__default::bit__and__uint8(_3370_f, AtomicStatusImpl_Compile::__default::flag__unmapped())) != ((uint8)0);
    is__accessed = (BitOps_Compile::__default::bit__and__uint8(_3370_f, AtomicStatusImpl_Compile::__default::flag__accessed())) != ((uint8)0);
    return Tuple<bool, bool, bool>(is__locked, is__free, is__accessed);
  }
  void AtomicStatus::mark__accessed()
  {
    uint8 _3372___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3373_atomic__tmp0;
      _3373_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out21;
      _out21 = Atomics::execute__atomic__fetch__or__uint8 <AtomicStatusImpl_Compile::G> ((*_3373_atomic__tmp0), AtomicStatusImpl_Compile::__default::flag__accessed());
      _3372___ = _out21;
    }
  }
  void AtomicStatus::clear__accessed()
  {
    uint8 _3374_orig__value = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3375_atomic__tmp0;
      _3375_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out22;
      _out22 = Atomics::execute__atomic__fetch__and__uint8 <AtomicStatusImpl_Compile::G> ((*_3375_atomic__tmp0), ((uint8)255) - (AtomicStatusImpl_Compile::__default::flag__accessed()));
      _3374_orig__value = _out22;
    }
  }
  bool AtomicStatus::is__reading()
  {
    bool success = false;
    uint8 _3376_f = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3377_atomic__tmp0;
      _3377_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out23;
      _out23 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3377_atomic__tmp0));
      _3376_f = _out23;
    }
    success = (BitOps_Compile::__default::bit__and__uint8(_3376_f, AtomicStatusImpl_Compile::__default::flag__reading())) == ((uint8)0);
    return success;
  }
  bool AtomicStatus::take__exc__if__eq__clean()
  {
    bool success = false;
    bool _3378_did__set = false;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3379_atomic__tmp0;
      _3379_atomic__tmp0 = &( ((*this).atomic));
      bool _out24;
      _out24 = Atomics::execute__atomic__compare__and__set__strong <uint8, AtomicStatusImpl_Compile::G> ((*_3379_atomic__tmp0), AtomicStatusImpl_Compile::__default::flag__clean(), ((AtomicStatusImpl_Compile::__default::flag__exc()) + (AtomicStatusImpl_Compile::__default::flag__clean())) + (AtomicStatusImpl_Compile::__default::flag__claim()));
      _3378_did__set = _out24;
      if (_3378_did__set) {
      } else {
      }
    }
    success = _3378_did__set;
    return success;
  }
  void AtomicStatus::set__to__free()
  {
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3380_atomic__tmp0;
      _3380_atomic__tmp0 = &( ((*this).atomic));
      Atomics::execute__atomic__store <uint8, AtomicStatusImpl_Compile::G> ((*_3380_atomic__tmp0), AtomicStatusImpl_Compile::__default::flag__unmapped());
    }
  }
  void AtomicStatus::set__to__free2()
  {
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3381_atomic__tmp0;
      _3381_atomic__tmp0 = &( ((*this).atomic));
      Atomics::execute__atomic__store <uint8, AtomicStatusImpl_Compile::G> ((*_3381_atomic__tmp0), AtomicStatusImpl_Compile::__default::flag__unmapped());
    }
  }
  void AtomicStatus::abandon__exc()
  {
    uint8 _3382_orig__value = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3383_atomic__tmp0;
      _3383_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out25;
      _out25 = Atomics::execute__atomic__fetch__and__uint8 <AtomicStatusImpl_Compile::G> ((*_3383_atomic__tmp0), (((uint8)255) - (AtomicStatusImpl_Compile::__default::flag__exc())) - (AtomicStatusImpl_Compile::__default::flag__claim()));
      _3382_orig__value = _out25;
    }
  }
  void AtomicStatus::abandon__reading__pending()
  {
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3384_atomic__tmp0;
      _3384_atomic__tmp0 = &( ((*this).atomic));
      Atomics::execute__atomic__store <uint8, AtomicStatusImpl_Compile::G> ((*_3384_atomic__tmp0), AtomicStatusImpl_Compile::__default::flag__unmapped());
    }
  }
  void AtomicStatus::mark__dirty()
  {
    uint8 _3385___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3386_atomic__tmp0;
      _3386_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out26;
      _out26 = Atomics::execute__atomic__fetch__and__uint8 <AtomicStatusImpl_Compile::G> ((*_3386_atomic__tmp0), ((uint8)255) - (AtomicStatusImpl_Compile::__default::flag__clean()));
      _3385___ = _out26;
    }
  }
  bool AtomicStatus::try__set__claim()
  {
    bool success = false;
    uint8 _3387_ret = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3388_atomic__tmp0;
      _3388_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out27;
      _out27 = Atomics::execute__atomic__fetch__or__uint8 <AtomicStatusImpl_Compile::G> ((*_3388_atomic__tmp0), AtomicStatusImpl_Compile::__default::flag__claim());
      _3387_ret = _out27;
      if ((BitOps_Compile::__default::bit__and__uint8(AtomicStatusImpl_Compile::__default::flag__claim(), _3387_ret)) == ((uint8)0)) {
      } else {
      }
    }
    success = (BitOps_Compile::__default::bit__and__uint8(AtomicStatusImpl_Compile::__default::flag__claim(), _3387_ret)) == ((uint8)0);
    return success;
  }
  void AtomicStatus::unset__claim()
  {
    uint8 _3389___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3390_atomic__tmp0;
      _3390_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out28;
      _out28 = Atomics::execute__atomic__fetch__and__uint8 <AtomicStatusImpl_Compile::G> ((*_3390_atomic__tmp0), ((uint8)255) - (AtomicStatusImpl_Compile::__default::flag__claim()));
      _3389___ = _out28;
    }
  }
  void AtomicStatus::set__exc()
  {
    uint8 _3391___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3392_atomic__tmp0;
      _3392_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out29;
      _out29 = Atomics::execute__atomic__fetch__or__uint8 <AtomicStatusImpl_Compile::G> ((*_3392_atomic__tmp0), AtomicStatusImpl_Compile::__default::flag__exc());
      _3391___ = _out29;
    }
  }
  void AtomicStatus::unset__exc()
  {
    uint8 _3393___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3394_atomic__tmp0;
      _3394_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out30;
      _out30 = Atomics::execute__atomic__fetch__and__uint8 <AtomicStatusImpl_Compile::G> ((*_3394_atomic__tmp0), ((uint8)255) - (AtomicStatusImpl_Compile::__default::flag__exc()));
      _3393___ = _out30;
    }
  }
  void AtomicStatus::read2exc__noop()
  {
    uint8 _3395___ = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3396_atomic__tmp0;
      _3396_atomic__tmp0 = &( ((*this).atomic));
      uint8 _out31;
      _out31 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3396_atomic__tmp0));
      _3395___ = _out31;
    }
  }

  uint8 __default::flag__writeback()
  {
    return (uint8)1;
  }
  uint8 __default::flag__exc()
  {
    return (uint8)2;
  }
  uint8 __default::flag__accessed()
  {
    return (uint8)4;
  }
  uint8 __default::flag__unmapped()
  {
    return (uint8)8;
  }
  uint8 __default::flag__reading()
  {
    return (uint8)16;
  }
  uint8 __default::flag__clean()
  {
    return (uint8)32;
  }
  uint8 __default::flag__claim()
  {
    return (uint8)64;
  }
}// end of namespace AtomicStatusImpl_Compile 
namespace BasicLockImpl_Compile  {





  template <typename G>
pre__BasicLock<G>::pre__BasicLock() {
    a = Atomics::get_Atomic_default<bool, GlinearOption_Compile::glOption <G> >();
  }
  template <typename G>
bool operator==(const pre__BasicLock<G> &left, const pre__BasicLock<G> &right)  {
    	return true 		&& left.a == right.a
    ;
  }


  template <typename __G>
  bool __default::try__acquire(BasicLockImpl_Compile::pre__BasicLock <__G> & l)
  {
    bool success = false;
    {
      Atomics::Atomic <bool, GlinearOption_Compile::glOption <__G> > * _3397_atomic__tmp0;
      _3397_atomic__tmp0 = &( ((l).a));
      bool _out32;
      _out32 = Atomics::execute__atomic__compare__and__set__strong <bool, GlinearOption_Compile::glOption <__G> > ((*_3397_atomic__tmp0), false, true);
      success = _out32;
      if (success) {
      } else {
      }
    }
    return success;
  }
  template <typename __G>
  void __default::release(BasicLockImpl_Compile::pre__BasicLock <__G> & l)
  {
    {
      Atomics::Atomic <bool, GlinearOption_Compile::glOption <__G> > * _3398_atomic__tmp0;
      _3398_atomic__tmp0 = &( ((l).a));
      Atomics::execute__atomic__store <bool, GlinearOption_Compile::glOption <__G> > ((*_3398_atomic__tmp0), false);
    }
  }
  template <typename __G>
  bool __default::is__locked(BasicLockImpl_Compile::pre__BasicLock <__G> & l)
  {
    bool b = false;
    {
      Atomics::Atomic <bool, GlinearOption_Compile::glOption <__G> > * _3399_atomic__tmp0;
      _3399_atomic__tmp0 = &( ((l).a));
      bool _out33;
      _out33 = Atomics::execute__atomic__load <bool, GlinearOption_Compile::glOption <__G> > ((*_3399_atomic__tmp0));
      b = _out33;
    }
    return b;
  }
  template <typename __G>
  BasicLockImpl_Compile::pre__BasicLock <__G>  __default::new__basic__lock()
  {
    BasicLockImpl_Compile::pre__BasicLock <__G>  l = BasicLockImpl_Compile::pre__BasicLock<__G>();
    Atomics::Atomic <bool, GlinearOption_Compile::glOption <__G> >  _3400_at;
    Atomics::Atomic <bool, GlinearOption_Compile::glOption <__G> >  _out34;
    _out34 = Atomics::new__atomic <bool, GlinearOption_Compile::glOption <__G> > (false);
    _3400_at = _out34;
    l = BasicLockImpl_Compile::pre__BasicLock<__G>(_3400_at);
    return l;
  }
}// end of namespace BasicLockImpl_Compile 
namespace LinearMaybe  {


}// end of namespace LinearMaybe 
namespace LinearExtern  {




}// end of namespace LinearExtern 
namespace LinearSequence__i_Compile  {






  template <typename __A>
  LinearExtern::linear_seq<__A> __default::seq__alloc__init(uint64 length, __A a)
  {
    return LinearExtern::seq_alloc <__A> (length, a);
  }
  template <typename __A>
  uint64 __default::lseq__length__as__uint64(LinearExtern::lseq <__A> & s)
  {
    return LinearExtern::lseq_length_raw <__A> (s);
  }
  template <typename __A>
  uint64 __default::lseq__length__uint64(LinearExtern::lseq <__A> & s)
  {
    uint64 n = 0;
    LinearExtern::lseq_length_bound <__A> (s);
    n = LinearExtern::lseq_length_raw <__A> (s);
    return n;
  }
  template <typename __A>
  __A* __default::lseq__peek(LinearExtern::lseq <__A> & s, uint64 i)
  {
    return &( *(LinearMaybe::peek <__A> (*(LinearExtern::lseq_share_raw <__A> (s, i)))) );
  }
  template <typename __A>
  LinearExtern::lseq <__A>  __default::lseq__alloc(uint64 length)
  {
    LinearExtern::lseq <__A>  s = LinearExtern::get_lseq_default<__A>();
    s = LinearExtern::lseq_alloc_raw <__A> (length);
    return s;
  }
  template <typename __A>
  LinearExtern::lseq <__A>  __default::lseq__alloc__hugetables(uint64 length)
  {
    LinearExtern::lseq <__A>  s = LinearExtern::get_lseq_default<__A>();
    s = LinearExtern::lseq_alloc_raw_hugetables <__A> (length);
    return s;
  }
  template <typename __A>
  void __default::lseq__free(LinearExtern::lseq <__A>  s)
  {
    Tuple0 _3401___v0;
    _3401___v0 = LinearExtern::lseq_free_raw <__A> (s);
  }
  template <typename __A>
  Tuple0 __default::lseq__free__fun(LinearExtern::lseq <__A>  s)
  {
    return LinearExtern::lseq_free_raw <__A> (s);
  }
  template <typename __A>
  struct Tuple<LinearExtern::lseq <__A> , __A> __default::lseq__swap(LinearExtern::lseq <__A>  s1, uint64 i, __A a1)
  {
    LinearExtern::lseq <__A>  s2 = LinearExtern::get_lseq_default<__A>();
    __A a2 = get_default<__A>::call();
    LinearMaybe::maybe <__A>  _3402_x1;
    _3402_x1 = LinearMaybe::give <__A> (a1);
    Tuple <LinearExtern::lseq <__A> , LinearMaybe::maybe <__A> >  _let_tmp_rhs0 = LinearExtern::lseq_swap_raw_fun <__A> (s1, i, _3402_x1);
    LinearExtern::lseq <__A>  _3403_s2tmp = (_let_tmp_rhs0).template get<0>();
    LinearMaybe::maybe <__A>  _3404_x2 = (_let_tmp_rhs0).template get<1>();
    s2 = _3403_s2tmp;
    a2 = LinearMaybe::unwrap <__A> (_3404_x2);
    return Tuple<LinearExtern::lseq <__A> , __A>(s2, a2);
  }
  template <typename __A>
  __A __default::lseq__swap__inout(LinearExtern::lseq <__A> & s, uint64 i, __A a1)
  {
    __A a2 = get_default<__A>::call();
    LinearExtern::lseq <__A>  _out35;
    __A _out36;
    auto _outcollector0 = LinearSequence__i_Compile::__default::lseq__swap <__A> (s, i, a1);
    _out35 = _outcollector0.template get<0>();
    _out36 = _outcollector0.template get<1>();
    s = _out35;
    a2 = _out36;
    return a2;
  }
  template <typename __A>
  struct Tuple<LinearExtern::lseq <__A> , __A> __default::lseq__take(LinearExtern::lseq <__A>  s1, uint64 i)
  {
    LinearExtern::lseq <__A>  s2 = LinearExtern::get_lseq_default<__A>();
    __A a = get_default<__A>::call();
    LinearMaybe::maybe <__A>  _3405_x1;
    _3405_x1 = LinearMaybe::empty <__A> ();
    Tuple <LinearExtern::lseq <__A> , LinearMaybe::maybe <__A> >  _let_tmp_rhs1 = LinearExtern::lseq_swap_raw_fun <__A> (s1, i, _3405_x1);
    LinearExtern::lseq <__A>  _3406_s2tmp = (_let_tmp_rhs1).template get<0>();
    LinearMaybe::maybe <__A>  _3407_x2 = (_let_tmp_rhs1).template get<1>();
    s2 = _3406_s2tmp;
    a = LinearMaybe::unwrap <__A> (_3407_x2);
    return Tuple<LinearExtern::lseq <__A> , __A>(s2, a);
  }
  template <typename __A>
  __A __default::lseq__take__inout(LinearExtern::lseq <__A> & s, uint64 i)
  {
    __A a = get_default<__A>::call();
    LinearExtern::lseq <__A>  _out37;
    __A _out38;
    auto _outcollector1 = LinearSequence__i_Compile::__default::lseq__take <__A> (s, i);
    _out37 = _outcollector1.template get<0>();
    _out38 = _outcollector1.template get<1>();
    s = _out37;
    a = _out38;
    return a;
  }
  template <typename __A>
  Tuple <LinearExtern::lseq <__A> , __A>  __default::lseq__take__fun(LinearExtern::lseq <__A>  s1, uint64 i)
  {
    LinearMaybe::maybe <__A>  _3408_x1 = LinearMaybe::empty <__A> ();
    Tuple <LinearExtern::lseq <__A> , LinearMaybe::maybe <__A> >  _let_tmp_rhs2 = LinearExtern::lseq_swap_raw_fun <__A> (s1, i, _3408_x1);
    LinearExtern::lseq <__A>  _3409_s2tmp = (_let_tmp_rhs2).template get<0>();
    LinearMaybe::maybe <__A>  _3410_x2 = (_let_tmp_rhs2).template get<1>();
    return Tuple<LinearExtern::lseq <__A> , __A>(_3409_s2tmp, LinearMaybe::unwrap <__A> (_3410_x2));
  }
  template <typename __A>
  LinearExtern::lseq <__A>  __default::lseq__give(LinearExtern::lseq <__A>  s1, uint64 i, __A a)
  {
    LinearExtern::lseq <__A>  s2 = LinearExtern::get_lseq_default<__A>();
    LinearMaybe::maybe <__A>  _3411_x1;
    _3411_x1 = LinearMaybe::give <__A> (a);
    Tuple <LinearExtern::lseq <__A> , LinearMaybe::maybe <__A> >  _let_tmp_rhs3 = LinearExtern::lseq_swap_raw_fun <__A> (s1, i, _3411_x1);
    LinearExtern::lseq <__A>  _3412_s2tmp = (_let_tmp_rhs3).template get<0>();
    LinearMaybe::maybe <__A>  _3413_x2 = (_let_tmp_rhs3).template get<1>();
    s2 = _3412_s2tmp;
    Tuple0 _3414___v1;
    _3414___v1 = LinearMaybe::discard <__A> (_3413_x2);
    return s2;
  }
  template <typename __A>
  void __default::lseq__give__inout(LinearExtern::lseq <__A> & s1, uint64 i, __A a)
  {
    LinearExtern::lseq <__A>  _out39;
    _out39 = LinearSequence__i_Compile::__default::lseq__give <__A> (s1, i, a);
    s1 = _out39;
  }
  template <typename __A>
  void __default::SeqCopy(LinearExtern::shared_seq<__A>& source, LinearExtern::linear_seq<__A>& dest, uint64 start, uint64 end, uint64 dest__start)
  {
    uint64 _3415_i;
    _3415_i = (uint64)0;
    uint64 _3416_len;
    _3416_len = (end) - (start);
    while ((_3415_i) < (_3416_len)) {
      LinearSequence__i_Compile::__default::mut__seq__set <__A> (dest, (_3415_i) + (dest__start), LinearExtern::seq_get <__A> (source, (_3415_i) + (start)));
      _3415_i = (_3415_i) + ((uint64)1);
    }
  }
  template <typename __A>
  LinearExtern::linear_seq<__A> __default::AllocAndCopy(LinearExtern::shared_seq<__A>& source, uint64 from, uint64 to)
  {
    LinearExtern::linear_seq<__A> dest = LinearExtern::linear_seq<__A>();
    if ((to) == (from)) {
      dest = LinearExtern::seq_empty <__A> ();
    } else {
      dest = LinearExtern::seq_alloc <__A> ((to) - (from), LinearExtern::seq_get <__A> (source, from));
    }
    LinearSequence__i_Compile::__default::SeqCopy <__A> (source, dest, from, to, (uint64)0);
    return dest;
  }
  template <typename __A>
  struct Tuple<LinearExtern::lseq <__A> , LinearExtern::lseq <__A> > __default::AllocAndMoveLseq(LinearExtern::lseq <__A>  source, uint64 from, uint64 to)
  {
    LinearExtern::lseq <__A>  looted = LinearExtern::get_lseq_default<__A>();
    LinearExtern::lseq <__A>  loot = LinearExtern::get_lseq_default<__A>();
    looted = source;
    LinearExtern::lseq <__A>  _out40;
    _out40 = LinearSequence__i_Compile::__default::lseq__alloc <__A> ((to) - (from));
    loot = _out40;
    uint64 _3417_i;
    _3417_i = from;
    while ((_3417_i) < (to)) {
      __A _3418_elt = get_default<__A>::call();
      LinearExtern::lseq <__A>  _out41;
      __A _out42;
      auto _outcollector2 = LinearSequence__i_Compile::__default::lseq__take <__A> (looted, _3417_i);
      _out41 = _outcollector2.template get<0>();
      _out42 = _outcollector2.template get<1>();
      looted = _out41;
      _3418_elt = _out42;
      LinearExtern::lseq <__A>  _out43;
      _out43 = LinearSequence__i_Compile::__default::lseq__give <__A> (loot, (_3417_i) - (from), _3418_elt);
      loot = _out43;
      _3417_i = (_3417_i) + ((uint64)1);
    }
    return Tuple<LinearExtern::lseq <__A> , LinearExtern::lseq <__A> >(looted, loot);
  }
  template <typename __A>
  LinearExtern::linear_seq<__A> __default::SeqResize(LinearExtern::linear_seq<__A> s, uint64 newlen, __A a)
  {
    LinearExtern::linear_seq<__A> s2 = LinearExtern::linear_seq<__A>();
    LinearExtern::shared_seq_length_bound <__A> (s);
    uint64 _3419_i;
    _3419_i = LinearExtern::seq_length <__A> (s);
    LinearExtern::linear_seq<__A> _out44;
    _out44 = LinearExtern::TrustedRuntimeSeqResize <__A> (s, newlen);
    s2 = _out44;
    while ((_3419_i) < (newlen)) {
      s2 = LinearExtern::seq_set <__A> (s2, _3419_i, a);
      _3419_i = (_3419_i) + ((uint64)1);
    }
    return s2;
  }
  template <typename __A>
  void __default::SeqResizeMut(LinearExtern::linear_seq<__A>& s, uint64 newlen, __A a)
  {
    LinearExtern::shared_seq_length_bound <__A> (s);
    uint64 _3420_i;
    _3420_i = LinearExtern::seq_length <__A> (s);
    LinearExtern::linear_seq<__A> _out45;
    _out45 = LinearExtern::TrustedRuntimeSeqResize <__A> (s, newlen);
    s = _out45;
    while ((_3420_i) < (newlen)) {
      LinearSequence__i_Compile::__default::mut__seq__set <__A> (s, _3420_i, a);
      _3420_i = (_3420_i) + ((uint64)1);
    }
  }
  template <typename __A>
  LinearExtern::linear_seq<__A> __default::InsertSeq(LinearExtern::linear_seq<__A> s, __A a, uint64 pos)
  {
    LinearExtern::linear_seq<__A> s2 = LinearExtern::linear_seq<__A>();
    uint64 _3421_len;
    _3421_len = LinearExtern::seq_length <__A> (s);
    uint64 _3422_newlen;
    _3422_newlen = (uint64(_3421_len)) + ((uint64)1);
    LinearExtern::linear_seq<__A> _out46;
    _out46 = LinearExtern::TrustedRuntimeSeqResize <__A> (s, _3422_newlen);
    s2 = _out46;
    uint64 _3423_i;
    _3423_i = (_3422_newlen) - ((uint64)1);
    while ((_3423_i) > (pos)) {
      __A _3424_prevElt;
      _3424_prevElt = LinearExtern::seq_get <__A> (s2, (_3423_i) - ((uint64)1));
      s2 = LinearExtern::seq_set <__A> (s2, _3423_i, _3424_prevElt);
      _3423_i = (_3423_i) - ((uint64)1);
    }
    s2 = LinearExtern::seq_set <__A> (s2, pos, a);
    return s2;
  }
  template <typename __A>
  LinearExtern::lseq <__A>  __default::InsertLSeq(LinearExtern::lseq <__A>  s, __A a, uint64 pos)
  {
    LinearExtern::lseq <__A>  s2 = LinearExtern::get_lseq_default<__A>();
    uint64 _3425_len;
    _3425_len = LinearExtern::lseq_length_raw <__A> (s);
    uint64 _3426_newlen;
    _3426_newlen = (_3425_len) + ((uint64)1);
    LinearExtern::lseq <__A>  _out47;
    _out47 = LinearExtern::TrustedRuntimeLSeqResize <__A> (s, _3426_newlen);
    s2 = _out47;
    uint64 _3427_i;
    _3427_i = (_3426_newlen) - ((uint64)1);
    while ((_3427_i) > (pos)) {
      __A _3428_prevElt = get_default<__A>::call();
      LinearExtern::lseq <__A>  _out48;
      __A _out49;
      auto _outcollector3 = LinearSequence__i_Compile::__default::lseq__take <__A> (s2, (_3427_i) - ((uint64)1));
      _out48 = _outcollector3.template get<0>();
      _out49 = _outcollector3.template get<1>();
      s2 = _out48;
      _3428_prevElt = _out49;
      LinearExtern::lseq <__A>  _out50;
      _out50 = LinearSequence__i_Compile::__default::lseq__give <__A> (s2, _3427_i, _3428_prevElt);
      s2 = _out50;
      _3427_i = (_3427_i) - ((uint64)1);
    }
    LinearExtern::lseq <__A>  _out51;
    _out51 = LinearSequence__i_Compile::__default::lseq__give <__A> (s2, pos, a);
    s2 = _out51;
    return s2;
  }
  template <typename __A>
  struct Tuple<LinearExtern::lseq <__A> , __A> __default::Replace1With2Lseq(LinearExtern::lseq <__A>  s, __A l, __A r, uint64 pos)
  {
    LinearExtern::lseq <__A>  s2 = LinearExtern::get_lseq_default<__A>();
    __A replaced = get_default<__A>::call();
    LinearExtern::lseq <__A>  _out52;
    __A _out53;
    auto _outcollector4 = LinearSequence__i_Compile::__default::lseq__swap <__A> (s, pos, l);
    _out52 = _outcollector4.template get<0>();
    _out53 = _outcollector4.template get<1>();
    s2 = _out52;
    replaced = _out53;
    LinearExtern::lseq <__A>  _out54;
    _out54 = LinearSequence__i_Compile::__default::InsertLSeq <__A> (s2, r, (pos) + ((uint64)1));
    s2 = _out54;
    return Tuple<LinearExtern::lseq <__A> , __A>(s2, replaced);
  }
  template <typename __A>
  __A __default::Replace1With2Lseq__inout(LinearExtern::lseq <__A> & s, __A l, __A r, uint64 pos)
  {
    __A replaced = get_default<__A>::call();
    __A _out55;
    _out55 = LinearSequence__i_Compile::__default::lseq__swap__inout <__A> (s, pos, l);
    replaced = _out55;
    LinearExtern::lseq <__A>  _out56;
    _out56 = LinearSequence__i_Compile::__default::InsertLSeq <__A> (s, r, (pos) + ((uint64)1));
    s = _out56;
    return replaced;
  }
  template <typename __A>
  void __default::mut__seq__set(LinearExtern::linear_seq<__A>& s, uint64 i, __A a)
  {
    s = LinearExtern::seq_set <__A> (s, i, a);
  }
}// end of namespace LinearSequence__i_Compile 
namespace ThreadUtils  {


}// end of namespace ThreadUtils 
namespace MemSplit_Compile  {





}// end of namespace MemSplit_Compile 
namespace InstantiatedDiskInterface  {








  
bool operator==(const FinishedReq_FRNone &left, const FinishedReq_FRNone &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const FinishedReq_FRWrite &left, const FinishedReq_FRWrite &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const FinishedReq_FRWritev &left, const FinishedReq_FRWritev &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const FinishedReq_FRRead &left, const FinishedReq_FRRead &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const FinishedReq_FRReadv &left, const FinishedReq_FRReadv &right) {
    (void)left; (void) right;
	return true ;
  }
  
FinishedReq::FinishedReq() {
    FinishedReq_FRNone COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_FinishedReq_FRNone(const struct FinishedReq d) { return std::holds_alternative<FinishedReq_FRNone>(d.v); }
  
inline bool is_FinishedReq_FRWrite(const struct FinishedReq d) { return std::holds_alternative<FinishedReq_FRWrite>(d.v); }
  
inline bool is_FinishedReq_FRWritev(const struct FinishedReq d) { return std::holds_alternative<FinishedReq_FRWritev>(d.v); }
  
inline bool is_FinishedReq_FRRead(const struct FinishedReq d) { return std::holds_alternative<FinishedReq_FRRead>(d.v); }
  
inline bool is_FinishedReq_FRReadv(const struct FinishedReq d) { return std::holds_alternative<FinishedReq_FRReadv>(d.v); }



}// end of namespace InstantiatedDiskInterface 
namespace CacheTypes_ON_TheAIO__Compile  {




















  
NullGhostType::NullGhostType() {
  }
  
bool operator==(const NullGhostType &left, const NullGhostType &right)  {
    	return true ;
  }

  
StatusIdx::StatusIdx() {
    status = AtomicStatusImpl_Compile::AtomicStatus();
    page__handle = Cells::get_Cell_default<CacheHandle_Compile::PageHandle>();
  }
  
bool operator==(const StatusIdx &left, const StatusIdx &right)  {
    	return true 		&& left.status == right.status
    		&& left.page__handle == right.page__handle
    ;
  }

  
Cache::Cache() {
    config = Constants_Compile::Config();
    data__base__ptr = Ptrs::get_Ptr_default();
    iocb__base__ptr = Ptrs::get_Ptr_default();
    read__refcounts__array = LinearExtern::get_lseq_default<AtomicRefcountImpl_Compile::AtomicRefcount>();
    cache__idx__of__page__array = LinearExtern::get_lseq_default<Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> >();
    status__idx__array = LinearExtern::get_lseq_default<CacheTypes_ON_TheAIO__Compile::StatusIdx>();
    global__clockpointer = Atomics::get_Atomic_default<uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>();
    req__hand__base = Atomics::get_Atomic_default<uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>();
    batch__busy = LinearExtern::get_lseq_default<Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >();
    io__slots = LinearExtern::get_lseq_default<CacheTypes_ON_TheAIO__Compile::IOSlot>();
    ioctx = InstantiatedDiskInterface::get_IOCtx_default();
  }
  
bool operator==(const Cache &left, const Cache &right)  {
    	return true 		&& left.config == right.config
    		&& left.data__base__ptr == right.data__base__ptr
    		&& left.iocb__base__ptr == right.iocb__base__ptr
    		&& left.read__refcounts__array == right.read__refcounts__array
    		&& left.cache__idx__of__page__array == right.cache__idx__of__page__array
    		&& left.status__idx__array == right.status__idx__array
    		&& left.global__clockpointer == right.global__clockpointer
    		&& left.req__hand__base == right.req__hand__base
    		&& left.batch__busy == right.batch__busy
    		&& left.io__slots == right.io__slots
    		&& left.ioctx == right.ioctx
    ;
  }
  Ptrs::Ptr Cache::data__ptr(uint32 i)
  {
    return Ptrs::ptr__add(((*this).data__base__ptr), (PageSizeConstant_Compile::__default::PageSize64()) * (uint64(i)));
  }
  AtomicStatusImpl_Compile::AtomicStatus* Cache::status__atomic(uint32 i)
  {
    return &( ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::StatusIdx> (((*this).status__idx__array), uint64(i)))).status) );
  }
  Cells::Cell <CacheHandle_Compile::PageHandle> * Cache::page__handle__ptr(uint32 i)
  {
    return &( ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::StatusIdx> (((*this).status__idx__array), uint64(i)))).page__handle) );
  }
  AtomicRefcountImpl_Compile::AtomicRefcount* Cache::read__refcount__atomic(uint64 j, uint32 i)
  {
    return &( *(LinearSequence__i_Compile::__default::lseq__peek <AtomicRefcountImpl_Compile::AtomicRefcount> (((*this).read__refcounts__array), Constants_Compile::__default::rc__index(((*this).config), j, i))) );
  }
  Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> * Cache::cache__idx__of__page__atomic(uint64 i)
  {
    return &( *(LinearSequence__i_Compile::__default::lseq__peek <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> > (((*this).cache__idx__of__page__array), i)) );
  }

  
LocalState::LocalState() {
    t = 0;
    free__hand = 0;
    io__slot__hand = 0;
  }
  
bool operator==(const LocalState &left, const LocalState &right)  {
    	return true 		&& left.t == right.t
    		&& left.free__hand == right.free__hand
    		&& left.io__slot__hand == right.io__slot__hand
    ;
  }

  
IOSlot::IOSlot() {
    iocb__ptr = Ptrs::get_Ptr_default();
    iovec__ptr = Ptrs::get_Ptr_default();
    lock = BasicLockImpl_Compile::pre__BasicLock<CacheAIOParams_Compile::IOSlotAccess>();
  }
  
bool operator==(const IOSlot &left, const IOSlot &right)  {
    	return true 		&& left.iocb__ptr == right.iocb__ptr
    		&& left.iovec__ptr == right.iovec__ptr
    		&& left.lock == right.lock
    ;
  }


}// end of namespace CacheTypes_ON_TheAIO__Compile 
namespace CacheIO_ON_TheAIO__Compile  {





















  uint64 __default::get__free__io__slot(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local)
  {
    uint64 idx = 0;
    uint64 _3429_i;
    _3429_i = ((local).io__slot__hand);
    bool _3430_done;
    _3430_done = false;
    while (!(_3430_done)) {
      if (((_3429_i) % (Constants_Compile::__default::AIO__HAND__BATCH__SIZE__64())) == ((uint64)0)) {
        uint32 _3431_j = 0;
        {
          Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType> * _3432_atomic__tmp0;
          _3432_atomic__tmp0 = &( ((cache).req__hand__base));
          uint32 _out57;
          _out57 = Atomics::execute__atomic__fetch__add__uint32 <CacheTypes_ON_TheAIO__Compile::NullGhostType> ((*_3432_atomic__tmp0), (uint32)32);
          _3431_j = _out57;
        }
        _3429_i = (uint64(_3431_j)) % (((((cache).config)).num__io__slots));
        bool _3433_cleanup__done;
        _3433_cleanup__done = false;
        while (!(_3433_cleanup__done)) {
          bool _out58;
          _out58 = CacheIO_ON_TheAIO__Compile::__default::io__cleanup__1(cache);
          _3433_cleanup__done = _out58;
        }
      }
      bool _out59;
      _out59 = BasicLockImpl_Compile::__default::try__acquire <CacheAIOParams_Compile::IOSlotAccess> (((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3429_i))).lock));
      _3430_done = _out59;
      if (!(_3430_done)) {
        _3429_i = (_3429_i) + ((uint64)1);
      } else {
        idx = _3429_i;
        _3429_i = (_3429_i) + ((uint64)1);
      }
    }
    ((local).io__slot__hand) = _3429_i;
    return idx;
  }
  void __default::disk__writeback__async(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__idx, uint32 cache__idx)
  {
    uint64 _3434_idx = 0;
    uint64 _out60;
    _out60 = CacheIO_ON_TheAIO__Compile::__default::get__free__io__slot(cache, local);
    _3434_idx = _out60;
    IocbStruct::iocb__prepare__write(((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3434_idx))).iocb__ptr), int64(disk__idx), (uint64)4096, (cache)->data__ptr(cache__idx));
    InstantiatedDiskInterface::async__write(((cache).ioctx), ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3434_idx))).iocb__ptr));
  }
  void __default::disk__read__async(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__idx, uint32 cache__idx, Ptrs::Ptr ptr)
  {
    uint64 _3435_idx = 0;
    uint64 _out61;
    _out61 = CacheIO_ON_TheAIO__Compile::__default::get__free__io__slot(cache, local);
    _3435_idx = _out61;
    IocbStruct::iocb__prepare__read(((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3435_idx))).iocb__ptr), int64(disk__idx), (uint64)4096, (cache)->data__ptr(cache__idx));
    InstantiatedDiskInterface::async__read(((cache).ioctx), ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3435_idx))).iocb__ptr));
  }
  void __default::disk__read__sync(uint64 disk__idx, Ptrs::Ptr ptr)
  {
    InstantiatedDiskInterface::sync__read(ptr, (uint64)4096, disk__idx);
  }
  void __default::disk__writeback__sync(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 disk__idx, Ptrs::Ptr ptr)
  {
    InstantiatedDiskInterface::sync__write(ptr, (uint64)4096, disk__idx);
  }
  void __default::disk__read__callback(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx)
  {
    (*((cache)->status__atomic(cache__idx)))->load__phase__finish__threadless();
  }
  void __default::disk__writeback__callback(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx)
  {
    (*((cache)->status__atomic(cache__idx)))->release__writeback();
  }
  void __default::disk__writeback__callback__vec(CacheTypes_ON_TheAIO__Compile::Cache& cache, Ptrs::Ptr iovec__ptr, uint64 iovec__len)
  {
    uint64 _3436_j;
    _3436_j = (uint64)0;
    while ((_3436_j) < (iovec__len)) {
      IocbStruct::Iovec _3437_my__iovec;
      IocbStruct::Iovec _out62;
      _out62 = (iovec__ptr)->index__read <IocbStruct::Iovec> (_3436_j);
      _3437_my__iovec = _out62;
      Ptrs::Ptr _3438_data__ptr;
      _3438_data__ptr = (_3437_my__iovec)->iov__base();
      uint32 _3439_cache__idx;
      uint32 _out63;
      _out63 = CacheIO_ON_TheAIO__Compile::__default::cache__idx__of__data__ptr(cache, _3438_data__ptr);
      _3439_cache__idx = _out63;
      CacheIO_ON_TheAIO__Compile::__default::disk__writeback__callback(cache, _3439_cache__idx);
      _3436_j = (_3436_j) + ((uint64)1);
    }
  }
  void __default::disk__read__callback__vec(CacheTypes_ON_TheAIO__Compile::Cache& cache, Ptrs::Ptr iovec__ptr, uint64 iovec__len)
  {
    uint64 _3440_j;
    _3440_j = (uint64)0;
    while ((_3440_j) < (iovec__len)) {
      IocbStruct::Iovec _3441_my__iovec;
      IocbStruct::Iovec _out64;
      _out64 = (iovec__ptr)->index__read <IocbStruct::Iovec> (_3440_j);
      _3441_my__iovec = _out64;
      Ptrs::Ptr _3442_data__ptr;
      _3442_data__ptr = (_3441_my__iovec)->iov__base();
      uint32 _3443_cache__idx;
      uint32 _out65;
      _out65 = CacheIO_ON_TheAIO__Compile::__default::cache__idx__of__data__ptr(cache, _3442_data__ptr);
      _3443_cache__idx = _out65;
      CacheIO_ON_TheAIO__Compile::__default::disk__read__callback(cache, _3443_cache__idx);
      _3440_j = (_3440_j) + ((uint64)1);
    }
  }
  void __default::io__cleanup(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 max__io__events)
  {
    uint64 _3444_counter;
    _3444_counter = (uint64)0;
    bool _3445_done;
    _3445_done = false;
    while (((_3444_counter) < (max__io__events)) && (!(_3445_done))) {
      _3444_counter = (_3444_counter) + ((uint64)1);
      bool _out66;
      _out66 = CacheIO_ON_TheAIO__Compile::__default::io__cleanup__1(cache);
      _3445_done = _out66;
    }
  }
  void __default::io__cleanup__all(CacheTypes_ON_TheAIO__Compile::Cache& cache)
  {
    uint64 _3446_i;
    _3446_i = (uint64)0;
    while ((_3446_i) < (((((cache).config)).num__io__slots))) {
      bool _3447_isl;
      bool _out67;
      _out67 = BasicLockImpl_Compile::__default::is__locked <CacheAIOParams_Compile::IOSlotAccess> (((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3446_i))).lock));
      _3447_isl = _out67;
      while (_3447_isl) {
        bool _3448_done;
        _3448_done = false;
        while (!(_3448_done)) {
          bool _out68;
          _out68 = CacheIO_ON_TheAIO__Compile::__default::io__cleanup__1(cache);
          _3448_done = _out68;
        }
        bool _out69;
        _out69 = BasicLockImpl_Compile::__default::is__locked <CacheAIOParams_Compile::IOSlotAccess> (((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3446_i))).lock));
        _3447_isl = _out69;
      }
      _3446_i = (_3446_i) + ((uint64)1);
    }
  }
  uint32 __default::cache__idx__of__data__ptr(CacheTypes_ON_TheAIO__Compile::Cache& cache, Ptrs::Ptr data__ptr)
  {
    uint32 ci = 0;
    ci = uint32((Ptrs::ptr__diff(data__ptr, ((cache).data__base__ptr))) / ((uint64)4096));
    return ci;
  }
  bool __default::io__cleanup__1(CacheTypes_ON_TheAIO__Compile::Cache& cache)
  {
    bool done = false;
    Ptrs::Ptr _3449_iocb__ptr = Ptrs::get_Ptr_default();
    Ptrs::Ptr _out70;
    _out70 = InstantiatedDiskInterface::get__event(((cache).ioctx));
    _3449_iocb__ptr = _out70;
    if ((_3449_iocb__ptr) == (Ptrs::null_ptr())) {
      done = true;
    } else {
      uint64 _3450_slot__idx;
      _3450_slot__idx = (Ptrs::ptr__diff(_3449_iocb__ptr, ((cache).iocb__base__ptr))) / (IocbStruct::SizeOfIocb());
      bool _3451_is__write;
      bool _out71;
      _out71 = IocbStruct::iocb__is__write(_3449_iocb__ptr);
      _3451_is__write = _out71;
      bool _3452_is__writev;
      bool _out72;
      _out72 = IocbStruct::iocb__is__writev(_3449_iocb__ptr);
      _3452_is__writev = _out72;
      bool _3453_is__read;
      bool _out73;
      _out73 = IocbStruct::iocb__is__read(_3449_iocb__ptr);
      _3453_is__read = _out73;
      if (_3451_is__write) {
        Ptrs::Ptr _3454_data__ptr;
        Ptrs::Ptr _out74;
        _out74 = IocbStruct::iocb__buf(_3449_iocb__ptr);
        _3454_data__ptr = _out74;
        uint32 _3455_cache__idx;
        uint32 _out75;
        _out75 = CacheIO_ON_TheAIO__Compile::__default::cache__idx__of__data__ptr(cache, _3454_data__ptr);
        _3455_cache__idx = _out75;
        CacheIO_ON_TheAIO__Compile::__default::disk__writeback__callback(cache, _3455_cache__idx);
      } else if (_3452_is__writev) {
        Ptrs::Ptr _3456_iovec__ptr;
        Ptrs::Ptr _out76;
        _out76 = IocbStruct::iocb__iovec(_3449_iocb__ptr);
        _3456_iovec__ptr = _out76;
        uint64 _3457_iovec__len;
        uint64 _out77;
        _out77 = IocbStruct::iocb__iovec__len(_3449_iocb__ptr);
        _3457_iovec__len = _out77;
        CacheIO_ON_TheAIO__Compile::__default::disk__writeback__callback__vec(cache, _3456_iovec__ptr, _3457_iovec__len);
      } else if (_3453_is__read) {
        Ptrs::Ptr _3458_data__ptr;
        Ptrs::Ptr _out78;
        _out78 = IocbStruct::iocb__buf(_3449_iocb__ptr);
        _3458_data__ptr = _out78;
        uint32 _3459_cache__idx;
        uint32 _out79;
        _out79 = CacheIO_ON_TheAIO__Compile::__default::cache__idx__of__data__ptr(cache, _3458_data__ptr);
        _3459_cache__idx = _out79;
        CacheIO_ON_TheAIO__Compile::__default::disk__read__callback(cache, _3459_cache__idx);
      } else {
        Ptrs::Ptr _3460_iovec__ptr;
        Ptrs::Ptr _out80;
        _out80 = IocbStruct::iocb__iovec(_3449_iocb__ptr);
        _3460_iovec__ptr = _out80;
        uint64 _3461_iovec__len;
        uint64 _out81;
        _out81 = IocbStruct::iocb__iovec__len(_3449_iocb__ptr);
        _3461_iovec__len = _out81;
        CacheIO_ON_TheAIO__Compile::__default::disk__read__callback__vec(cache, _3460_iovec__ptr, _3461_iovec__len);
      }
      BasicLockImpl_Compile::__default::release <CacheAIOParams_Compile::IOSlotAccess> (((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3450_slot__idx))).lock));
    }
    return done;
  }

}// end of namespace CacheIO_ON_TheAIO__Compile 
namespace CacheWritebackBatch_ON_TheAIO__Compile  {




























  bool __default::pages__share__extent(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 a, uint64 b)
  {
    return ((a) / (((((cache).config)).pages__per__extent))) == ((b) / (((((cache).config)).pages__per__extent)));
  }
  uint64 __default::walk__forward(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__addr, bool is__urgent)
  {
    uint64 end__addr = 0;
    end__addr = (disk__addr) + ((uint64)1);
    bool _3462_done;
    _3462_done = false;
    while (((end__addr) < (((((cache).config)).num__disk__pages))) && (!(_3462_done))) {
      uint64 _3463_next;
      _3463_next = end__addr;
      if (!(CacheWritebackBatch_ON_TheAIO__Compile::__default::pages__share__extent(cache, _3463_next, disk__addr))) {
        _3462_done = true;
      } else {
        uint32 _3464_cache__idx;
        uint32 _out82;
        _out82 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__read(*((cache)->cache__idx__of__page__atomic(_3463_next)));
        _3464_cache__idx = _out82;
        if ((_3464_cache__idx) == (AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED)) {
          _3462_done = true;
        } else {
          bool _3465_do__write__back = false;
          bool _out83;
          _out83 = (*((cache)->status__atomic(uint32(_3464_cache__idx))))->try__acquire__writeback(is__urgent);
          _3465_do__write__back = _out83;
          if (!(_3465_do__write__back)) {
            _3462_done = true;
          } else {
            CacheHandle_Compile::PageHandle _3466_ph;
            CacheHandle_Compile::PageHandle _out84;
            _out84 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3464_cache__idx)));
            _3466_ph = _out84;
            int64 _3467_disk__idx;
            _3467_disk__idx = EuclideanDivision_int64(((_3466_ph).disk__addr), int64(PageSizeConstant_Compile::__default::PageSize64()));
            if ((_3467_disk__idx) == (int64(_3463_next))) {
              end__addr = (_3463_next) + ((uint64)1);
            } else {
              CacheIO_ON_TheAIO__Compile::__default::disk__writeback__async(cache, local, uint64(_3467_disk__idx), _3464_cache__idx);
              _3462_done = true;
            }
          }
        }
      }
    }
    return end__addr;
  }
  uint64 __default::walk__backward(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 disk__addr, bool is__urgent)
  {
    uint64 start__addr = 0;
    start__addr = disk__addr;
    bool _3468_done;
    _3468_done = false;
    while (((start__addr) > ((uint64)0)) && (!(_3468_done))) {
      uint64 _3469_next;
      _3469_next = (start__addr) - ((uint64)1);
      if (!(CacheWritebackBatch_ON_TheAIO__Compile::__default::pages__share__extent(cache, _3469_next, disk__addr))) {
        _3468_done = true;
      } else {
        uint32 _3470_cache__idx;
        uint32 _out85;
        _out85 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__read(*((cache)->cache__idx__of__page__atomic(_3469_next)));
        _3470_cache__idx = _out85;
        if ((_3470_cache__idx) == (AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED)) {
          _3468_done = true;
        } else {
          bool _3471_do__write__back = false;
          bool _out86;
          _out86 = (*((cache)->status__atomic(_3470_cache__idx)))->try__acquire__writeback(is__urgent);
          _3471_do__write__back = _out86;
          if (!(_3471_do__write__back)) {
            _3468_done = true;
          } else {
            CacheHandle_Compile::PageHandle _3472_ph;
            CacheHandle_Compile::PageHandle _out87;
            _out87 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3470_cache__idx)));
            _3472_ph = _out87;
            int64 _3473_disk__idx;
            _3473_disk__idx = EuclideanDivision_int64(((_3472_ph).disk__addr), int64(PageSizeConstant_Compile::__default::PageSize64()));
            if ((_3473_disk__idx) == (int64(_3469_next))) {
              start__addr = _3469_next;
            } else {
              CacheIO_ON_TheAIO__Compile::__default::disk__writeback__async(cache, local, uint64(_3473_disk__idx), _3470_cache__idx);
              _3468_done = true;
            }
          }
        }
      }
    }
    return start__addr;
  }
  void __default::vec__writeback__async(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint64 start__addr, uint64 end__addr)
  {
    uint64 _3474_idx = 0;
    uint64 _out88;
    _out88 = CacheIO_ON_TheAIO__Compile::__default::get__free__io__slot(cache, local);
    _3474_idx = _out88;
    Ptrs::Ptr _3475_iovec__ptr;
    _3475_iovec__ptr = ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3474_idx))).iovec__ptr);
    IocbStruct::iocb__prepare__writev(((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3474_idx))).iocb__ptr), int64(start__addr), _3475_iovec__ptr, (end__addr) - (start__addr));
    uint64 _3476_j;
    _3476_j = (uint64)0;
    while ((_3476_j) < ((end__addr) - (start__addr))) {
      uint32 _3477_cache__idx;
      uint32 _out89;
      _out89 = AtomicIndexLookupImpl_Compile::__default::read__known__cache__idx(*((cache)->cache__idx__of__page__atomic((start__addr) + (_3476_j))));
      _3477_cache__idx = _out89;
      IocbStruct::Iovec _3478_iov;
      IocbStruct::Iovec _out90;
      _out90 = IocbStruct::new__iovec((cache)->data__ptr(_3477_cache__idx), (uint64)4096);
      _3478_iov = _out90;
      (_3475_iovec__ptr)->index__write <IocbStruct::Iovec> (_3476_j, _3478_iov);
      _3476_j = (_3476_j) + ((uint64)1);
    }
    Ptrs::Ptr _3479_iocb__ptr;
    _3479_iocb__ptr = ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3474_idx))).iocb__ptr);
    InstantiatedDiskInterface::async__writev(((cache).ioctx), _3479_iocb__ptr);
  }
  void __default::batch__start__writeback(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, uint32 batch__idx, bool is__urgent)
  {
    uint32 _3480_i;
    _3480_i = (uint32)0;
    while ((_3480_i) < (Constants_Compile::__default::ENTRIES__PER__BATCH__32())) {
      uint32 _3481_cache__idx;
      _3481_cache__idx = ((batch__idx) * (Constants_Compile::__default::ENTRIES__PER__BATCH__32())) + (_3480_i);
      bool _3482_do__write__back = false;
      bool _out91;
      _out91 = (*((cache)->status__atomic(_3481_cache__idx)))->try__acquire__writeback(is__urgent);
      _3482_do__write__back = _out91;
      if (_3482_do__write__back) {
        CacheHandle_Compile::PageHandle _3483_ph;
        CacheHandle_Compile::PageHandle _out92;
        _out92 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3481_cache__idx)));
        _3483_ph = _out92;
        int64 _3484_disk__idx;
        _3484_disk__idx = EuclideanDivision_int64(((_3483_ph).disk__addr), int64(PageSizeConstant_Compile::__default::PageSize64()));
        uint64 _3485_start__addr = 0;
        uint64 _3486_end__addr = 0;
        uint64 _out93;
        _out93 = CacheWritebackBatch_ON_TheAIO__Compile::__default::walk__backward(cache, local, uint64(_3484_disk__idx), is__urgent);
        _3485_start__addr = _out93;
        uint64 _out94;
        _out94 = CacheWritebackBatch_ON_TheAIO__Compile::__default::walk__forward(cache, local, uint64(_3484_disk__idx), is__urgent);
        _3486_end__addr = _out94;
        CacheWritebackBatch_ON_TheAIO__Compile::__default::vec__writeback__async(cache, local, _3485_start__addr, _3486_end__addr);
      } else {
      }
      _3480_i = (_3480_i) + ((uint32)1);
    }
  }

}// end of namespace CacheWritebackBatch_ON_TheAIO__Compile 
namespace CacheOps_ON_TheAIO__Compile  {



























  
PageHandleIdx::PageHandleIdx() {
    cache__idx = 0;
  }
  
bool operator==(const PageHandleIdx &left, const PageHandleIdx &right)  {
    	return true 		&& left.cache__idx == right.cache__idx
    ;
  }

  
WriteablePageHandle::WriteablePageHandle() {
  }
  
bool operator==(const WriteablePageHandle &left, const WriteablePageHandle &right)  {
    	return true ;
  }

  
ReadonlyPageHandle::ReadonlyPageHandle() {
  }
  
bool operator==(const ReadonlyPageHandle &left, const ReadonlyPageHandle &right)  {
    	return true ;
  }

  
ClaimPageHandle::ClaimPageHandle() {
  }
  
bool operator==(const ClaimPageHandle &left, const ClaimPageHandle &right)  {
    	return true ;
  }

  uint8 __attribute__((always_inline)) __default::try__get__read(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState)
  {
    uint8 success = 0;
    bool _3487_is__exc__locked;
    bool _out95;
    _out95 = (*((cache)->status__atomic(cache__idx)))->quicktest__is__exc__locked();
    _3487_is__exc__locked = _out95;
    if (_3487_is__exc__locked) {
      success = (uint8)1;
      success = (uint8)1;
    } else {
      AtomicRefcountImpl_Compile::__default::inc__refcount__for__shared(*((cache)->read__refcount__atomic(((localState).t), cache__idx)));
      bool _3488_is__accessed = false;
      bool _3489_is__locked = false;
      bool _3490_is__free = false;
      bool _out96;
      bool _out97;
      bool _out98;
      auto _outcollector5 = (*((cache)->status__atomic(cache__idx)))->is__exc__locked__or__free();
      _out96 = _outcollector5.template get<0>();
      _out97 = _outcollector5.template get<1>();
      _out98 = _outcollector5.template get<2>();
      _3489_is__locked = _out96;
      _3490_is__free = _out97;
      _3488_is__accessed = _out98;
      if ((_3489_is__locked) || (_3490_is__free)) {
        AtomicRefcountImpl_Compile::__default::dec__refcount__for__shared__pending(*((cache)->read__refcount__atomic(((localState).t), cache__idx)));
        success = ((_3490_is__free) ? ((uint8)2) : ((uint8)1));
      } else {
        if (!(_3488_is__accessed)) {
          (*((cache)->status__atomic(cache__idx)))->mark__accessed();
        }
        success = (uint8)0;
      }
    }
    return success;
  }
  void __attribute__((always_inline)) __default::platform__sleep(uint64 ns)
  {
    uint64 _3491_i;
    _3491_i = (uint64)0;
    while ((_3491_i) < (((ns) / ((uint64)5)) + ((uint64)1))) {
      ThreadUtils::pause();
      _3491_i = (_3491_i) + ((uint64)1);
    }
  }
  uint8 __attribute__((always_inline)) __default::get__read(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState)
  {
    uint8 success = 0;
    uint8 _out99;
    _out99 = CacheOps_ON_TheAIO__Compile::__default::try__get__read(cache, cache__idx, localState);
    success = _out99;
    uint64 _3492_wait;
    _3492_wait = (uint64)1;
    while ((success) == ((uint8)1)) {
      CacheOps_ON_TheAIO__Compile::__default::platform__sleep(_3492_wait);
      _3492_wait = (((_3492_wait) > ((uint64)1024)) ? (_3492_wait) : (((uint64)2) * (_3492_wait)));
      uint8 _out100;
      _out100 = CacheOps_ON_TheAIO__Compile::__default::try__get__read(cache, cache__idx, localState);
      success = _out100;
    }
    return success;
  }
  bool __attribute__((always_inline)) __default::try__take__read__lock__on__cache__entry(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, int64 expected__disk__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState)
  {
    bool success = false;
    uint8 _3493_success__code = 0;
    uint8 _out101;
    _out101 = CacheOps_ON_TheAIO__Compile::__default::get__read(cache, cache__idx, localState);
    _3493_success__code = _out101;
    if ((_3493_success__code) != ((uint8)0)) {
      success = false;
    } else {
      bool _3494_is__done__reading;
      _3494_is__done__reading = false;
      while (!(_3494_is__done__reading)) {
        bool _out102;
        _out102 = (*((cache)->status__atomic(cache__idx)))->is__reading();
        _3494_is__done__reading = _out102;
        if (!(_3494_is__done__reading)) {
          CacheIO_ON_TheAIO__Compile::__default::io__cleanup(cache, Constants_Compile::__default::DEFAULT__MAX__IO__EVENTS__64());
        }
      }
      CacheHandle_Compile::PageHandle _3495_ph;
      CacheHandle_Compile::PageHandle _out103;
      _out103 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(cache__idx)));
      _3495_ph = _out103;
      int64 _3496_actual__disk__idx;
      _3496_actual__disk__idx = EuclideanDivision_int64(((_3495_ph).disk__addr), int64(PageSizeConstant_Compile::__default::PageSize64()));
      if ((_3496_actual__disk__idx) != (expected__disk__idx)) {
        AtomicRefcountImpl_Compile::__default::dec__refcount__for__shared__obtained(*((cache)->read__refcount__atomic(((localState).t), cache__idx)));
        success = false;
      } else {
        success = true;
      }
    }
    return success;
  }
  void __default::move__hand(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local, bool is__urgent)
  {
    uint64 _3497_evict__hand;
    _3497_evict__hand = ((local).free__hand);
    if ((_3497_evict__hand) != ((uint64)18446744073709551615U)) {
      {
        Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> * _3498_atomic__tmp0;
        _3498_atomic__tmp0 = &( *(LinearSequence__i_Compile::__default::lseq__peek <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> > (((cache).batch__busy), _3497_evict__hand)));
        Atomics::execute__atomic__store <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> ((*_3498_atomic__tmp0), false);
      }
    }
    bool _3499_done;
    _3499_done = false;
    while (!(_3499_done)) {
      uint32 _3500_l = 0;
      {
        Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType> * _3501_atomic__tmp1;
        _3501_atomic__tmp1 = &( ((cache).global__clockpointer));
        uint32 _out104;
        _out104 = Atomics::execute__atomic__fetch__add__uint32 <CacheTypes_ON_TheAIO__Compile::NullGhostType> ((*_3501_atomic__tmp1), (uint32)1);
        _3500_l = _out104;
      }
      _3497_evict__hand = (uint64(_3500_l)) % (((((cache).config)).batch__capacity));
      uint64 _3502_cleaner__hand;
      _3502_cleaner__hand = ((_3497_evict__hand) + (Constants_Compile::__default::CLEAN__AHEAD__64())) % (((((cache).config)).batch__capacity));
      bool _3503_do__clean = false;
      {
        Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> * _3504_atomic__tmp2;
        _3504_atomic__tmp2 = &( *(LinearSequence__i_Compile::__default::lseq__peek <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> > (((cache).batch__busy), _3502_cleaner__hand)));
        bool _out105;
        _out105 = Atomics::execute__atomic__compare__and__set__strong <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> ((*_3504_atomic__tmp2), false, true);
        _3503_do__clean = _out105;
      }
      if (_3503_do__clean) {
        CacheWritebackBatch_ON_TheAIO__Compile::__default::batch__start__writeback(cache, local, uint32(_3502_cleaner__hand), is__urgent);
        {
          Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> * _3505_atomic__tmp3;
          _3505_atomic__tmp3 = &( *(LinearSequence__i_Compile::__default::lseq__peek <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> > (((cache).batch__busy), _3502_cleaner__hand)));
          Atomics::execute__atomic__store <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> ((*_3505_atomic__tmp3), false);
        }
      }
      {
        Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> * _3506_atomic__tmp4;
        _3506_atomic__tmp4 = &( *(LinearSequence__i_Compile::__default::lseq__peek <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> > (((cache).batch__busy), _3497_evict__hand)));
        bool _out106;
        _out106 = Atomics::execute__atomic__compare__and__set__strong <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> ((*_3506_atomic__tmp4), false, true);
        _3499_done = _out106;
      }
    }
    CacheOps_ON_TheAIO__Compile::__default::evict__batch(cache, uint32(_3497_evict__hand));
    ((local).free__hand) = _3497_evict__hand;
  }
  bool __default::check__all__refcounts__dont__wait(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx)
  {
    bool success = false;
    uint64 _3507_i;
    _3507_i = (uint64)0;
    success = true;
    while (((_3507_i) < (Constants_Compile::__default::RC__WIDTH__64())) && (success)) {
      bool _out107;
      _out107 = AtomicRefcountImpl_Compile::__default::is__refcount__eq(*((cache)->read__refcount__atomic(_3507_i, cache__idx)), (uint8)0);
      success = _out107;
      _3507_i = (_3507_i) + ((uint64)1);
    }
    return success;
  }
  void __default::check__all__refcounts__with__t__block(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 t, uint32 cache__idx)
  {
    uint64 _3508_i;
    _3508_i = (uint64)0;
    while ((_3508_i) < (Constants_Compile::__default::RC__WIDTH__64())) {
      bool _3509_success = false;
      bool _out108;
      _out108 = AtomicRefcountImpl_Compile::__default::is__refcount__eq(*((cache)->read__refcount__atomic(_3508_i, cache__idx)), (((_3508_i) == (t)) ? ((uint8)1) : ((uint8)0)));
      _3509_success = _out108;
      if (_3509_success) {
        _3508_i = (_3508_i) + ((uint64)1);
      } else {
        ThreadUtils::pause();
      }
    }
  }
  void __default::try__evict__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx)
  {
    uint8 _3510_status = 0;
    {
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G> * _3511_atomic__tmp0;
      _3511_atomic__tmp0 = &( ((*((cache)->status__atomic(cache__idx))).atomic));
      uint8 _out109;
      _out109 = Atomics::execute__atomic__load <uint8, AtomicStatusImpl_Compile::G> ((*_3511_atomic__tmp0));
      _3510_status = _out109;
    }
    if ((BitOps_Compile::__default::bit__or__uint8(_3510_status, AtomicStatusImpl_Compile::__default::flag__accessed())) != ((uint8)0)) {
      (*((cache)->status__atomic(cache__idx)))->clear__accessed();
    }
    if ((_3510_status) != (AtomicStatusImpl_Compile::__default::flag__clean())) {
    } else {
      bool _3512_success = false;
      bool _out110;
      _out110 = (*((cache)->status__atomic(cache__idx)))->take__exc__if__eq__clean();
      _3512_success = _out110;
      if (!(_3512_success)) {
      } else {
        bool _out111;
        _out111 = CacheOps_ON_TheAIO__Compile::__default::check__all__refcounts__dont__wait(cache, cache__idx);
        _3512_success = _out111;
        if (!(_3512_success)) {
          (*((cache)->status__atomic(cache__idx)))->abandon__exc();
        } else {
          CacheHandle_Compile::PageHandle _3513_ph;
          CacheHandle_Compile::PageHandle _out112;
          _out112 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(cache__idx)));
          _3513_ph = _out112;
          int64 _3514_disk__idx;
          _3514_disk__idx = EuclideanDivision_int64(((_3513_ph).disk__addr), int64(PageSizeConstant_Compile::__default::PageSize64()));
          AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__clear__mapping(*((cache)->cache__idx__of__page__atomic(uint64(_3514_disk__idx))));
          (*((cache)->status__atomic(cache__idx)))->set__to__free();
        }
      }
    }
  }
  void __default::evict__batch(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 chunk)
  {
    uint32 _3515_i;
    _3515_i = (uint32)0;
    while ((_3515_i) < (Constants_Compile::__default::CHUNK__SIZE__32())) {
      uint32 _3516_j;
      _3516_j = ((chunk) * (Constants_Compile::__default::CHUNK__SIZE__32())) + (_3515_i);
      CacheOps_ON_TheAIO__Compile::__default::try__evict__page(cache, _3516_j);
      _3515_i = (_3515_i) + ((uint32)1);
    }
  }
  uint32 __default::get__free__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState)
  {
    uint32 cache__idx = 0;
    bool _3517_success;
    _3517_success = false;
    uint64 _3518_max__hand;
    _3518_max__hand = ((localState).free__hand);
    if ((((localState).free__hand)) == ((uint64)18446744073709551615U)) {
      CacheOps_ON_TheAIO__Compile::__default::move__hand(cache, localState, false);
    }
    uint32 _3519_num__passes;
    _3519_num__passes = (uint32)0;
    while (!(_3517_success)) {
      uint32 _3520_chunk;
      _3520_chunk = uint32(((localState).free__hand));
      uint32 _3521_i;
      _3521_i = (uint32)0;
      while (((_3521_i) < (Constants_Compile::__default::CHUNK__SIZE__32())) && (!(_3517_success))) {
        cache__idx = ((_3520_chunk) * (Constants_Compile::__default::CHUNK__SIZE__32())) + (_3521_i);
        bool _out113;
        _out113 = (*((cache)->status__atomic(cache__idx)))->try__alloc();
        _3517_success = _out113;
        _3521_i = (_3521_i) + ((uint32)1);
      }
      if (!(_3517_success)) {
        CacheOps_ON_TheAIO__Compile::__default::move__hand(cache, localState, (_3519_num__passes) != ((uint32)0));
        if ((((localState).free__hand)) < (_3518_max__hand)) {
          if ((_3519_num__passes) < ((uint32)3)) {
            _3519_num__passes = (_3519_num__passes) + ((uint32)1);
          }
          CacheIO_ON_TheAIO__Compile::__default::io__cleanup(cache, Constants_Compile::__default::DEFAULT__MAX__IO__EVENTS__64());
        }
        _3518_max__hand = ((localState).free__hand);
      }
    }
    return cache__idx;
  }
  int64 __default::try__take__read__lock__disk__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 disk__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState)
  {
    int64 ret__cache__idx = 0;
    uint32 _3522_cache__idx;
    uint32 _out114;
    _out114 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__read(*((cache)->cache__idx__of__page__atomic(disk__idx)));
    _3522_cache__idx = _out114;
    if ((_3522_cache__idx) == (AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED)) {
      uint32 _out115;
      _out115 = CacheOps_ON_TheAIO__Compile::__default::get__free__page(cache, localState);
      _3522_cache__idx = _out115;
      bool _3523_success = false;
      bool _out116;
      _out116 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__add__mapping(*((cache)->cache__idx__of__page__atomic(disk__idx)), disk__idx, _3522_cache__idx);
      _3523_success = _out116;
      if (!(_3523_success)) {
        ret__cache__idx = (int64)-1;
        (*((cache)->status__atomic(_3522_cache__idx)))->abandon__reading__pending();
      } else {
        AtomicRefcountImpl_Compile::__default::inc__refcount__for__reading(*((cache)->read__refcount__atomic(((localState).t), _3522_cache__idx)));
        (*((cache)->status__atomic(_3522_cache__idx)))->clear__exc__bit__during__load__phase();
        CacheIO_ON_TheAIO__Compile::__default::disk__read__sync(uint64(disk__idx), (cache)->data__ptr(_3522_cache__idx));
        CacheHandle_Compile::PageHandle _3524_ph;
        CacheHandle_Compile::PageHandle _out117;
        _out117 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3522_cache__idx)));
        _3524_ph = _out117;
        Cells::write__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3522_cache__idx)), CacheHandle_Compile::PageHandle(((_3524_ph).data__ptr), (int64(disk__idx)) * (int64(PageSizeConstant_Compile::__default::PageSize64()))));
        (*((cache)->status__atomic(_3522_cache__idx)))->load__phase__finish();
        ret__cache__idx = int64(_3522_cache__idx);
      }
    } else {
      bool _3525_success = false;
      bool _out118;
      _out118 = CacheOps_ON_TheAIO__Compile::__default::try__take__read__lock__on__cache__entry(cache, _3522_cache__idx, int64(disk__idx), localState);
      _3525_success = _out118;
      if (_3525_success) {
        ret__cache__idx = int64(_3522_cache__idx);
      } else {
        ret__cache__idx = (int64)-1;
      }
    }
    return ret__cache__idx;
  }
  CacheOps_ON_TheAIO__Compile::PageHandleIdx __default::get(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx)
  {
    CacheOps_ON_TheAIO__Compile::PageHandleIdx ph = CacheOps_ON_TheAIO__Compile::PageHandleIdx();
    int64 _3526_cache__idx;
    _3526_cache__idx = (int64)-1;
    while ((_3526_cache__idx) == ((int64)-1)) {
      int64 _out119;
      _out119 = CacheOps_ON_TheAIO__Compile::__default::try__take__read__lock__disk__page(cache, disk__idx, localState);
      _3526_cache__idx = _out119;
    }
    ph = CacheOps_ON_TheAIO__Compile::PageHandleIdx(uint32(_3526_cache__idx));
    return ph;
  }
  void __default::unget(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    AtomicRefcountImpl_Compile::__default::dec__refcount__for__shared__obtained(*((cache)->read__refcount__atomic(((localState).t), ((ph).cache__idx))));
  }
  bool __default::claim(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    bool success = false;
    bool _out120;
    _out120 = (*((cache)->status__atomic(((ph).cache__idx))))->try__set__claim();
    success = _out120;
    bool _3527_ghosty;
    _3527_ghosty = true;
    if (success) {
    } else {
    }
    return success;
  }
  void __default::unclaim(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    (*((cache)->status__atomic(((ph).cache__idx))))->unset__claim();
  }
  void __default::lock(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    bool _3528_writeback__done;
    _3528_writeback__done = false;
    (*((cache)->status__atomic(((ph).cache__idx))))->set__exc();
    while (!(_3528_writeback__done)) {
      bool _out121;
      bool _out122;
      auto _outcollector6 = (*((cache)->status__atomic(((ph).cache__idx))))->try__check__writeback__isnt__set();
      _out121 = _outcollector6.template get<0>();
      _out122 = _outcollector6.template get<1>();
      _3528_writeback__done = _out121;
      if (!(_3528_writeback__done)) {
        CacheIO_ON_TheAIO__Compile::__default::io__cleanup(cache, Constants_Compile::__default::DEFAULT__MAX__IO__EVENTS__64());
      }
    }
    CacheOps_ON_TheAIO__Compile::__default::check__all__refcounts__with__t__block(cache, ((localState).t), ((ph).cache__idx));
  }
  void __default::unlock(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    (*((cache)->status__atomic(((ph).cache__idx))))->unset__exc();
  }
  CacheOps_ON_TheAIO__Compile::PageHandleIdx __default::get__claim__lock(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx)
  {
    CacheOps_ON_TheAIO__Compile::PageHandleIdx ph = CacheOps_ON_TheAIO__Compile::PageHandleIdx();
    bool _3529_success;
    _3529_success = false;
    ph = CacheOps_ON_TheAIO__Compile::PageHandleIdx((uint32)0);
    while (!(_3529_success)) {
      CacheOps_ON_TheAIO__Compile::PageHandleIdx _out123;
      _out123 = CacheOps_ON_TheAIO__Compile::__default::get(cache, localState, disk__idx);
      ph = _out123;
      bool _out124;
      _out124 = CacheOps_ON_TheAIO__Compile::__default::claim(cache, ph);
      _3529_success = _out124;
      if (!(_3529_success)) {
        CacheOps_ON_TheAIO__Compile::__default::unget(cache, localState, ph);
        ThreadUtils::pause();
      } else {
        CacheOps_ON_TheAIO__Compile::__default::lock(cache, localState, ph);
      }
    }
    return ph;
  }
  void __default::mark__dirty(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    (*((cache)->status__atomic(((ph).cache__idx))))->mark__dirty();
  }
  void __default::page__sync__nonblocking(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    uint32 _3530_cache__idx;
    _3530_cache__idx = ((ph).cache__idx);
    bool _3531_do__write__back = false;
    bool _out125;
    _out125 = (*((cache)->status__atomic(_3530_cache__idx)))->try__acquire__writeback(true);
    _3531_do__write__back = _out125;
    if (_3531_do__write__back) {
      CacheHandle_Compile::PageHandle _3532_p;
      CacheHandle_Compile::PageHandle _out126;
      _out126 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3530_cache__idx)));
      _3532_p = _out126;
      int64 _3533_disk__idx;
      _3533_disk__idx = EuclideanDivision_int64(((_3532_p).disk__addr), int64(PageSizeConstant_Compile::__default::PageSize64()));
      CacheIO_ON_TheAIO__Compile::__default::disk__writeback__async(cache, localState, uint64(_3533_disk__idx), _3530_cache__idx);
    } else {
    }
  }
  void __default::page__sync__blocking(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, CacheOps_ON_TheAIO__Compile::PageHandleIdx ph)
  {
    uint32 _3534_cache__idx;
    _3534_cache__idx = ((ph).cache__idx);
    bool _3535_do__write__back = false;
    bool _out127;
    _out127 = (*((cache)->status__atomic(_3534_cache__idx)))->try__acquire__writeback(true);
    _3535_do__write__back = _out127;
    if (_3535_do__write__back) {
      CacheHandle_Compile::PageHandle _3536_p;
      CacheHandle_Compile::PageHandle _out128;
      _out128 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3534_cache__idx)));
      _3536_p = _out128;
      int64 _3537_disk__idx;
      _3537_disk__idx = EuclideanDivision_int64(((_3536_p).disk__addr), int64(PageSizeConstant_Compile::__default::PageSize64()));
      CacheIO_ON_TheAIO__Compile::__default::disk__writeback__sync(cache, uint64(_3537_disk__idx), (cache)->data__ptr(_3534_cache__idx));
      (*((cache)->status__atomic(_3534_cache__idx)))->release__writeback();
    } else {
    }
  }
  void __default::evict__all(CacheTypes_ON_TheAIO__Compile::Cache& cache)
  {
    uint32 _3538_i;
    _3538_i = (uint32)0;
    while ((_3538_i) < (uint32(((((cache).config)).batch__capacity)))) {
      CacheOps_ON_TheAIO__Compile::__default::evict__batch(cache, _3538_i);
      CacheOps_ON_TheAIO__Compile::__default::evict__batch(cache, _3538_i);
      _3538_i = (_3538_i) + ((uint32)1);
    }
  }
  void __default::flush(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& local)
  {
    CacheIO_ON_TheAIO__Compile::__default::io__cleanup__all(cache);
    uint32 _3539_flush__hand;
    _3539_flush__hand = (uint32)0;
    while ((_3539_flush__hand) < (uint32(((((cache).config)).batch__capacity)))) {
      CacheWritebackBatch_ON_TheAIO__Compile::__default::batch__start__writeback(cache, local, _3539_flush__hand, true);
      _3539_flush__hand = (_3539_flush__hand) + ((uint32)1);
    }
    CacheIO_ON_TheAIO__Compile::__default::io__cleanup__all(cache);
  }
  bool __default::try__get__read__and__release(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint32 cache__idx, CacheTypes_ON_TheAIO__Compile::LocalState& localState)
  {
    bool in__cache = false;
    uint8 _3540_success__op = 0;
    uint8 _out129;
    _out129 = CacheOps_ON_TheAIO__Compile::__default::try__get__read(cache, cache__idx, localState);
    _3540_success__op = _out129;
    if ((_3540_success__op) == ((uint8)0)) {
      in__cache = true;
      AtomicRefcountImpl_Compile::__default::dec__refcount__for__shared__pending(*((cache)->read__refcount__atomic(((localState).t), cache__idx)));
    } else if ((_3540_success__op) == ((uint8)1)) {
      in__cache = true;
    } else {
      in__cache = false;
    }
    return in__cache;
  }
  void __default::prefetch__io(CacheTypes_ON_TheAIO__Compile::Cache& cache, uint64 pages__in__req, uint64 addr, uint64 slot__idx, Ptrs::Ptr iovec__ptr)
  {
    Ptrs::Ptr _3541_iocb__ptr;
    _3541_iocb__ptr = ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), slot__idx))).iocb__ptr);
    IocbStruct::iocb__prepare__readv(_3541_iocb__ptr, int64((addr) - (pages__in__req)), iovec__ptr, pages__in__req);
    InstantiatedDiskInterface::async__readv(((cache).ioctx), _3541_iocb__ptr);
  }
  void __default::prefetch(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 base__addr)
  {
    uint64 _3542_pages__in__req;
    _3542_pages__in__req = (uint64)0;
    uint64 _3543_slot__idx;
    _3543_slot__idx = (uint64)0;
    Ptrs::Ptr _3544_iovec__ptr;
    _3544_iovec__ptr = Ptrs::null_ptr();
    uint64 _3545_page__off;
    _3545_page__off = (uint64)0;
    while ((_3545_page__off) < (((((cache).config)).pages__per__extent))) {
      uint64 _3546_addr;
      _3546_addr = (base__addr) + (_3545_page__off);
      uint32 _3547_cache__idx;
      uint32 _out130;
      _out130 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__read(*((cache)->cache__idx__of__page__atomic(_3546_addr)));
      _3547_cache__idx = _out130;
      bool _3548_already__in__cache = false;
      if ((_3547_cache__idx) == (AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED)) {
        _3548_already__in__cache = false;
      } else {
        bool _out131;
        _out131 = CacheOps_ON_TheAIO__Compile::__default::try__get__read__and__release(cache, _3547_cache__idx, localState);
        _3548_already__in__cache = _out131;
      }
      if (_3548_already__in__cache) {
        if ((_3542_pages__in__req) != ((uint64)0)) {
          CacheOps_ON_TheAIO__Compile::__default::prefetch__io(cache, _3542_pages__in__req, _3546_addr, _3543_slot__idx, _3544_iovec__ptr);
        } else {
        }
        _3542_pages__in__req = (uint64)0;
        _3545_page__off = (_3545_page__off) + ((uint64)1);
      } else {
        uint32 _3549_cache__idx = 0;
        uint32 _out132;
        _out132 = CacheOps_ON_TheAIO__Compile::__default::get__free__page(cache, localState);
        _3549_cache__idx = _out132;
        bool _3550_success = false;
        bool _out133;
        _out133 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__add__mapping(*((cache)->cache__idx__of__page__atomic(_3546_addr)), _3546_addr, _3549_cache__idx);
        _3550_success = _out133;
        if (!(_3550_success)) {
          (*((cache)->status__atomic(_3549_cache__idx)))->abandon__reading__pending();
        } else {
          (*((cache)->status__atomic(_3549_cache__idx)))->clear__exc__bit__during__load__phase();
          CacheHandle_Compile::PageHandle _3551_p;
          CacheHandle_Compile::PageHandle _out134;
          _out134 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3549_cache__idx)));
          _3551_p = _out134;
          Cells::write__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3549_cache__idx)), CacheHandle_Compile::PageHandle(((_3551_p).data__ptr), (int64(_3546_addr)) * (int64(PageSizeConstant_Compile::__default::PageSize64()))));
          if ((_3542_pages__in__req) == ((uint64)0)) {
            uint64 _3552_sidx = 0;
            uint64 _out135;
            _out135 = CacheIO_ON_TheAIO__Compile::__default::get__free__io__slot(cache, localState);
            _3552_sidx = _out135;
            _3544_iovec__ptr = ((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::IOSlot> (((cache).io__slots), _3552_sidx))).iovec__ptr);
            _3543_slot__idx = _3552_sidx;
          }
          IocbStruct::Iovec _3553_iov;
          IocbStruct::Iovec _out136;
          _out136 = IocbStruct::new__iovec((cache)->data__ptr(_3549_cache__idx), (uint64)4096);
          _3553_iov = _out136;
          (_3544_iovec__ptr)->index__write <IocbStruct::Iovec> (_3542_pages__in__req, _3553_iov);
          _3542_pages__in__req = (_3542_pages__in__req) + ((uint64)1);
          _3545_page__off = (_3545_page__off) + ((uint64)1);
        }
      }
    }
    if ((_3542_pages__in__req) != ((uint64)0)) {
      uint64 _3554_addr;
      _3554_addr = (base__addr) + (_3545_page__off);
      CacheOps_ON_TheAIO__Compile::__default::prefetch__io(cache, _3542_pages__in__req, _3554_addr, _3543_slot__idx, _3544_iovec__ptr);
    } else {
    }
  }
  struct Tuple<bool, CacheOps_ON_TheAIO__Compile::PageHandleIdx> __default::alloc(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx)
  {
    bool success = false;
    CacheOps_ON_TheAIO__Compile::PageHandleIdx ph = CacheOps_ON_TheAIO__Compile::PageHandleIdx();
    uint32 _3555_cache__idx = 0;
    uint32 _out137;
    _out137 = CacheOps_ON_TheAIO__Compile::__default::get__free__page(cache, localState);
    _3555_cache__idx = _out137;
    bool _out138;
    _out138 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__add__mapping__instant(*((cache)->cache__idx__of__page__atomic(disk__idx)), disk__idx, _3555_cache__idx);
    success = _out138;
    if (!(success)) {
      (*((cache)->status__atomic(_3555_cache__idx)))->abandon__reading__pending();
      ph = CacheOps_ON_TheAIO__Compile::PageHandleIdx((uint32)0);
    } else {
      AtomicRefcountImpl_Compile::__default::inc__refcount__for__reading(*((cache)->read__refcount__atomic(((localState).t), _3555_cache__idx)));
      CacheHandle_Compile::PageHandle _3556_p;
      CacheHandle_Compile::PageHandle _out139;
      _out139 = Cells::read__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3555_cache__idx)));
      _3556_p = _out139;
      Cells::write__cell <CacheHandle_Compile::PageHandle> (*((cache)->page__handle__ptr(_3555_cache__idx)), CacheHandle_Compile::PageHandle(((_3556_p).data__ptr), (int64(disk__idx)) * (int64(PageSizeConstant_Compile::__default::PageSize64()))));
      (*((cache)->status__atomic(_3555_cache__idx)))->read2exc__noop();
      ph = CacheOps_ON_TheAIO__Compile::PageHandleIdx(_3555_cache__idx);
    }
    return Tuple<bool, CacheOps_ON_TheAIO__Compile::PageHandleIdx>(success, ph);
  }
  void __default::try__dealloc__page(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx)
  {
    bool _3557_done;
    _3557_done = false;
    while (!(_3557_done)) {
      uint32 _3558_cache__idx;
      uint32 _out140;
      _out140 = AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__read(*((cache)->cache__idx__of__page__atomic(disk__idx)));
      _3558_cache__idx = _out140;
      if ((_3558_cache__idx) == (AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED)) {
        _3557_done = true;
      } else {
        bool _3559_success = false;
        bool _out141;
        _out141 = CacheOps_ON_TheAIO__Compile::__default::try__take__read__lock__on__cache__entry(cache, _3558_cache__idx, int64(disk__idx), localState);
        _3559_success = _out141;
        if (!(_3559_success)) {
        } else {
          bool _out142;
          _out142 = (*((cache)->status__atomic(_3558_cache__idx)))->try__set__claim();
          _3559_success = _out142;
          if (!(_3559_success)) {
            AtomicRefcountImpl_Compile::__default::dec__refcount__for__shared__obtained(*((cache)->read__refcount__atomic(((localState).t), _3558_cache__idx)));
          } else {
            (*((cache)->status__atomic(_3558_cache__idx)))->set__exc();
            bool _3560_writeback__done;
            _3560_writeback__done = false;
            while (!(_3560_writeback__done)) {
              bool _out143;
              bool _out144;
              auto _outcollector7 = (*((cache)->status__atomic(_3558_cache__idx)))->try__check__writeback__isnt__set();
              _out143 = _outcollector7.template get<0>();
              _out144 = _outcollector7.template get<1>();
              _3560_writeback__done = _out143;
              if (!(_3560_writeback__done)) {
                CacheIO_ON_TheAIO__Compile::__default::io__cleanup(cache, Constants_Compile::__default::DEFAULT__MAX__IO__EVENTS__64());
              }
            }
            CacheOps_ON_TheAIO__Compile::__default::check__all__refcounts__with__t__block(cache, ((localState).t), _3558_cache__idx);
            AtomicIndexLookupImpl_Compile::__default::atomic__index__lookup__clear__mapping__havoc(*((cache)->cache__idx__of__page__atomic(uint64(disk__idx))));
            (*((cache)->status__atomic(_3558_cache__idx)))->set__to__free2();
            AtomicRefcountImpl_Compile::__default::dec__refcount__for__shared__pending(*((cache)->read__refcount__atomic(((localState).t), _3558_cache__idx)));
            _3557_done = true;
          }
        }
      }
    }
  }
  void __default::wait(CacheTypes_ON_TheAIO__Compile::Cache& cache)
  {
    CacheIO_ON_TheAIO__Compile::__default::io__cleanup(cache, Constants_Compile::__default::DEFAULT__MAX__IO__EVENTS__64());
  }

}// end of namespace CacheOps_ON_TheAIO__Compile 
namespace CacheInit_ON_TheAIO__Compile  {




























  LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  __default::init__batch__busy(Constants_Compile::Config config)
  {
    LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  batch__busy = LinearExtern::get_lseq_default<Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >();
    LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  _out145;
    _out145 = LinearSequence__i_Compile::__default::lseq__alloc <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> > (((config).batch__capacity));
    batch__busy = _out145;
    uint64 _3561_i;
    _3561_i = (uint64)0;
    while ((_3561_i) < (((config).batch__capacity))) {
      Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType>  _3562_ato;
      Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType>  _out146;
      _out146 = Atomics::new__atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> (false);
      _3562_ato = _out146;
      LinearSequence__i_Compile::__default::lseq__give__inout <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> > (batch__busy, _3561_i, _3562_ato);
      _3561_i = (_3561_i) + ((uint64)1);
    }
    return batch__busy;
  }
  struct Tuple<Ptrs::Ptr, LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot> > __default::init__ioslots(Constants_Compile::Config config)
  {
    Ptrs::Ptr iocb__base__ptr = Ptrs::get_Ptr_default();
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot>  io__slots = LinearExtern::get_lseq_default<CacheTypes_ON_TheAIO__Compile::IOSlot>();
    Ptrs::Ptr _out147;
    _out147 = IocbStruct::new__iocb__array(((config).num__io__slots));
    iocb__base__ptr = _out147;
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot>  _out148;
    _out148 = LinearSequence__i_Compile::__default::lseq__alloc <CacheTypes_ON_TheAIO__Compile::IOSlot> (((config).num__io__slots));
    io__slots = _out148;
    Ptrs::Ptr _3563_full__iovec__ptr = Ptrs::get_Ptr_default();
    IocbStruct::Iovec _3564_dummy__iovec;
    IocbStruct::Iovec _out149;
    _out149 = IocbStruct::new__iovec(Ptrs::null_ptr(), (uint64)0);
    _3564_dummy__iovec = _out149;
    Ptrs::Ptr _out150;
    _out150 = Ptrs::alloc__array <IocbStruct::Iovec> ((((config).pages__per__extent)) * (((config).num__io__slots)), _3564_dummy__iovec);
    _3563_full__iovec__ptr = _out150;
    uint64 _3565_i3;
    _3565_i3 = (uint64)0;
    while ((_3565_i3) < (((config).num__io__slots))) {
      Ptrs::Ptr _3566_iovec__ptr;
      _3566_iovec__ptr = Ptrs::ptr__add(_3563_full__iovec__ptr, ((_3565_i3) * (((config).pages__per__extent))) * (Ptrs::sizeof_ <IocbStruct::Iovec> ()));
      Ptrs::Ptr _3567_iocb__ptr;
      _3567_iocb__ptr = Ptrs::ptr__add(iocb__base__ptr, (uint64(_3565_i3)) * (IocbStruct::SizeOfIocb()));
      BasicLockImpl_Compile::pre__BasicLock <CacheAIOParams_Compile::IOSlotAccess>  _3568_slot__lock;
      BasicLockImpl_Compile::pre__BasicLock <CacheAIOParams_Compile::IOSlotAccess>  _out151;
      _out151 = BasicLockImpl_Compile::__default::new__basic__lock <CacheAIOParams_Compile::IOSlotAccess> ();
      _3568_slot__lock = _out151;
      CacheTypes_ON_TheAIO__Compile::IOSlot _3569_io__slot;
      _3569_io__slot = CacheTypes_ON_TheAIO__Compile::IOSlot(_3567_iocb__ptr, _3566_iovec__ptr, _3568_slot__lock);
      LinearSequence__i_Compile::__default::lseq__give__inout <CacheTypes_ON_TheAIO__Compile::IOSlot> (io__slots, _3565_i3, _3569_io__slot);
      _3565_i3 = (_3565_i3) + ((uint64)1);
    }
    return Tuple<Ptrs::Ptr, LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot> >(iocb__base__ptr, io__slots);
  }
  CacheTypes_ON_TheAIO__Compile::Cache __default::init__cache(Constants_Compile::PreConfig preConfig)
  {
    CacheTypes_ON_TheAIO__Compile::Cache c = CacheTypes_ON_TheAIO__Compile::Cache();
    Constants_Compile::Config _3570_config;
    Constants_Compile::Config _out152;
    _out152 = Constants_Compile::__default::fromPreConfig(preConfig);
    _3570_config = _out152;
    Ptrs::Ptr _3571_data__base__ptr = Ptrs::get_Ptr_default();
    Ptrs::Ptr _out153;
    _out153 = Ptrs::alloc__array__hugetables <uint8> ((uint64(((_3570_config).cache__size))) * (PageSizeConstant_Compile::__default::PageSize64()), (uint8)0);
    _3571_data__base__ptr = _out153;
    LinearExtern::lseq <AtomicRefcountImpl_Compile::AtomicRefcount>  _3572_read__refcounts__array;
    LinearExtern::lseq <AtomicRefcountImpl_Compile::AtomicRefcount>  _out154;
    _out154 = LinearSequence__i_Compile::__default::lseq__alloc__hugetables <AtomicRefcountImpl_Compile::AtomicRefcount> ((Constants_Compile::__default::RC__WIDTH__64()) * (uint64(((_3570_config).cache__size))));
    _3572_read__refcounts__array = _out154;
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::StatusIdx>  _3573_status__idx__array;
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::StatusIdx>  _out155;
    _out155 = LinearSequence__i_Compile::__default::lseq__alloc <CacheTypes_ON_TheAIO__Compile::StatusIdx> (uint64(((_3570_config).cache__size)));
    _3573_status__idx__array = _out155;
    uint64 _3574_i;
    _3574_i = (uint64)0;
    while ((_3574_i) < (uint64(((_3570_config).cache__size)))) {
      Cells::Cell <CacheHandle_Compile::PageHandle>  _3575_cell__idx = Cells::get_Cell_default<CacheHandle_Compile::PageHandle>();
      Cells::Cell <CacheHandle_Compile::PageHandle>  _out156;
      _out156 = Cells::new__cell <CacheHandle_Compile::PageHandle> (CacheHandle_Compile::PageHandle(Ptrs::ptr__add(_3571_data__base__ptr, (_3574_i) * (PageSizeConstant_Compile::__default::PageSize64())), (int64)0));
      _3575_cell__idx = _out156;
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G>  _3576_atomic__status__atomic;
      Atomics::Atomic <uint8, AtomicStatusImpl_Compile::G>  _out157;
      _out157 = Atomics::new__atomic <uint8, AtomicStatusImpl_Compile::G> (AtomicStatusImpl_Compile::__default::flag__unmapped());
      _3576_atomic__status__atomic = _out157;
      AtomicStatusImpl_Compile::AtomicStatus _3577_atomic__status;
      _3577_atomic__status = AtomicStatusImpl_Compile::AtomicStatus(_3576_atomic__status__atomic);
      CacheTypes_ON_TheAIO__Compile::StatusIdx _3578_status__idx;
      _3578_status__idx = CacheTypes_ON_TheAIO__Compile::StatusIdx(_3577_atomic__status, _3575_cell__idx);
      LinearSequence__i_Compile::__default::lseq__give__inout <CacheTypes_ON_TheAIO__Compile::StatusIdx> (_3573_status__idx__array, _3574_i, _3578_status__idx);
      uint64 _3579_j;
      _3579_j = (uint64)0;
      while ((_3579_j) < (Constants_Compile::__default::RC__WIDTH__64())) {
        Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG>  _3580_ar__atomic;
        Atomics::Atomic <uint8, AtomicRefcountImpl_Compile::RG>  _out158;
        _out158 = Atomics::new__atomic <uint8, AtomicRefcountImpl_Compile::RG> ((uint8)0);
        _3580_ar__atomic = _out158;
        AtomicRefcountImpl_Compile::AtomicRefcount _3581_ar;
        _3581_ar = AtomicRefcountImpl_Compile::AtomicRefcount(_3580_ar__atomic);
        LinearSequence__i_Compile::__default::lseq__give__inout <AtomicRefcountImpl_Compile::AtomicRefcount> (_3572_read__refcounts__array, Constants_Compile::__default::rc__index(_3570_config, _3579_j, uint32(_3574_i)), _3581_ar);
        _3579_j = (_3579_j) + ((uint64)1);
      }
      _3574_i = (_3574_i) + ((uint64)1);
    }
    LinearExtern::lseq <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> >  _3582_cache__idx__of__page__array;
    LinearExtern::lseq <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> >  _out159;
    _out159 = LinearSequence__i_Compile::__default::lseq__alloc <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> > (((_3570_config).num__disk__pages));
    _3582_cache__idx__of__page__array = _out159;
    uint64 _3583_i2;
    _3583_i2 = (uint64)0;
    while ((_3583_i2) < (((_3570_config).num__disk__pages))) {
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap>  _3584_ail;
      Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap>  _out160;
      _out160 = Atomics::new__atomic <uint32, CacheResources_Compile::DiskPageMap> (uint32(AtomicIndexLookupImpl_Compile::__default::NOT__MAPPED));
      _3584_ail = _out160;
      LinearSequence__i_Compile::__default::lseq__give__inout <Atomics::Atomic <uint32, CacheResources_Compile::DiskPageMap> > (_3582_cache__idx__of__page__array, _3583_i2, _3584_ail);
      _3583_i2 = (_3583_i2) + ((uint64)1);
    }
    Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  _3585_global__clockpointer;
    Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  _out161;
    _out161 = Atomics::new__atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType> (uint32(0));
    _3585_global__clockpointer = _out161;
    Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  _3586_req__hand__base;
    Atomics::Atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType>  _out162;
    _out162 = Atomics::new__atomic <uint32, CacheTypes_ON_TheAIO__Compile::NullGhostType> (uint32(0));
    _3586_req__hand__base = _out162;
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot>  _3587_io__slots = LinearExtern::get_lseq_default<CacheTypes_ON_TheAIO__Compile::IOSlot>();
    Ptrs::Ptr _3588_iocb__base__ptr = Ptrs::get_Ptr_default();
    Ptrs::Ptr _out163;
    LinearExtern::lseq <CacheTypes_ON_TheAIO__Compile::IOSlot>  _out164;
    auto _outcollector8 = CacheInit_ON_TheAIO__Compile::__default::init__ioslots(_3570_config);
    _out163 = _outcollector8.template get<0>();
    _out164 = _outcollector8.template get<1>();
    _3588_iocb__base__ptr = _out163;
    _3587_io__slots = _out164;
    InstantiatedDiskInterface::IOCtx _3589_ioctx;
    InstantiatedDiskInterface::IOCtx _out165;
    _out165 = InstantiatedDiskInterface::init__ctx();
    _3589_ioctx = _out165;
    LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  _3590_batch__busy;
    LinearExtern::lseq <Atomics::Atomic <bool, CacheTypes_ON_TheAIO__Compile::NullGhostType> >  _out166;
    _out166 = CacheInit_ON_TheAIO__Compile::__default::init__batch__busy(_3570_config);
    _3590_batch__busy = _out166;
    c = CacheTypes_ON_TheAIO__Compile::Cache(_3570_config, _3571_data__base__ptr, _3588_iocb__base__ptr, _3572_read__refcounts__array, _3582_cache__idx__of__page__array, _3573_status__idx__array, _3585_global__clockpointer, _3586_req__hand__base, _3590_batch__busy, _3587_io__slots, _3589_ioctx);
    return c;
  }
  CacheTypes_ON_TheAIO__Compile::LocalState __default::init__thread__local__state(uint64 t)
  {
    CacheTypes_ON_TheAIO__Compile::LocalState l = CacheTypes_ON_TheAIO__Compile::LocalState();
    l = CacheTypes_ON_TheAIO__Compile::LocalState((t) % (Constants_Compile::__default::RC__WIDTH__64()), (uint64)18446744073709551615U, (uint64)0);
    return l;
  }

}// end of namespace CacheInit_ON_TheAIO__Compile 
namespace Application_ON_TheAIO__Compile  {



















  DafnySequence<uint8> __default::copy__seq__out(Ptrs::Ptr ptr)
  {
    DafnySequence<uint8> s = DafnySequence<uint8>();
    LinearExtern::linear_seq<uint8> _3591_sl;
    _3591_sl = LinearExtern::seq_alloc <uint8> ((uint64)4096, (uint8)0);
    uint64 _3592_i;
    _3592_i = (uint64)0;
    while ((_3592_i) < ((uint64)4096)) {
      uint8 _3593_val;
      uint8 _out167;
      _out167 = (ptr)->index__read <uint8> (_3592_i);
      _3593_val = _out167;
      _3591_sl = LinearExtern::seq_set <uint8> (_3591_sl, _3592_i, _3593_val);
      _3592_i = (_3592_i) + ((uint64)1);
    }
    s = LinearExtern::seq_unleash <uint8> (_3591_sl);
    return s;
  }
  void __default::copy__seq__in(Ptrs::Ptr ptr, DafnySequence<uint8> data)
  {
    uint64 _3594_i;
    _3594_i = (uint64)0;
    while ((_3594_i) < ((uint64)4096)) {
      (ptr)->index__write <uint8> (_3594_i, (data).select(_3594_i));
      _3594_i = (_3594_i) + ((uint64)1);
    }
  }
  CacheTypes_ON_TheAIO__Compile::Cache __default::init(Constants_Compile::PreConfig preConfig)
  {
    CacheTypes_ON_TheAIO__Compile::Cache cache = CacheTypes_ON_TheAIO__Compile::Cache();
    CacheTypes_ON_TheAIO__Compile::Cache _out168;
    _out168 = CacheInit_ON_TheAIO__Compile::__default::init__cache(preConfig);
    cache = _out168;
    return cache;
  }
  CacheTypes_ON_TheAIO__Compile::LocalState __default::init__thread__local__state(uint64 t)
  {
    CacheTypes_ON_TheAIO__Compile::LocalState l = CacheTypes_ON_TheAIO__Compile::LocalState();
    CacheTypes_ON_TheAIO__Compile::LocalState _out169;
    _out169 = CacheInit_ON_TheAIO__Compile::__default::init__thread__local__state(t);
    l = _out169;
    return l;
  }
  DafnySequence<uint8> __default::read__block(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx)
  {
    DafnySequence<uint8> block = DafnySequence<uint8>();
    CacheOps_ON_TheAIO__Compile::PageHandleIdx _3595_php = CacheOps_ON_TheAIO__Compile::PageHandleIdx();
    CacheOps_ON_TheAIO__Compile::PageHandleIdx _out170;
    _out170 = CacheOps_ON_TheAIO__Compile::__default::get(cache, localState, disk__idx);
    _3595_php = _out170;
    CacheHandle_Compile::PageHandle _3596_ph;
    CacheHandle_Compile::PageHandle _out171;
    _out171 = Cells::read__cell <CacheHandle_Compile::PageHandle> (((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::StatusIdx> (((cache).status__idx__array), uint64(((_3595_php).cache__idx))))).page__handle));
    _3596_ph = _out171;
    Ptrs::Ptr _3597_ptr;
    _3597_ptr = ((_3596_ph).data__ptr);
    DafnySequence<uint8> _out172;
    _out172 = Application_ON_TheAIO__Compile::__default::copy__seq__out(_3597_ptr);
    block = _out172;
    CacheOps_ON_TheAIO__Compile::__default::unget(cache, localState, _3595_php);
    return block;
  }
  void __default::write__block(CacheTypes_ON_TheAIO__Compile::Cache& cache, CacheTypes_ON_TheAIO__Compile::LocalState& localState, uint64 disk__idx, DafnySequence<uint8> data)
  {
    CacheOps_ON_TheAIO__Compile::PageHandleIdx _3598_php = CacheOps_ON_TheAIO__Compile::PageHandleIdx();
    CacheOps_ON_TheAIO__Compile::PageHandleIdx _out173;
    _out173 = CacheOps_ON_TheAIO__Compile::__default::get__claim__lock(cache, localState, disk__idx);
    _3598_php = _out173;
    CacheOps_ON_TheAIO__Compile::__default::mark__dirty(cache, _3598_php);
    CacheHandle_Compile::PageHandle _3599_ph;
    CacheHandle_Compile::PageHandle _out174;
    _out174 = Cells::read__cell <CacheHandle_Compile::PageHandle> (((*(LinearSequence__i_Compile::__default::lseq__peek <CacheTypes_ON_TheAIO__Compile::StatusIdx> (((cache).status__idx__array), uint64(((_3598_php).cache__idx))))).page__handle));
    _3599_ph = _out174;
    Ptrs::Ptr _3600_ptr;
    _3600_ptr = ((_3599_ph).data__ptr);
    Application_ON_TheAIO__Compile::__default::copy__seq__in(_3600_ptr, data);
    CacheOps_ON_TheAIO__Compile::__default::unlock(cache, _3598_php);
    CacheOps_ON_TheAIO__Compile::__default::unclaim(cache, _3598_php);
    CacheOps_ON_TheAIO__Compile::__default::unget(cache, localState, _3598_php);
  }

}// end of namespace Application_ON_TheAIO__Compile 
namespace AsyncDisk_Compile  {




  
Variables::Variables() {
  }
  
bool operator==(const Variables &left, const Variables &right)  {
    	return true ;
  }

  
bool operator==(const Step_RecvReadStep &left, const Step_RecvReadStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_RecvWriteStep &left, const Step_RecvWriteStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_AckReadStep &left, const Step_AckReadStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const Step_AckWriteStep &left, const Step_AckWriteStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
Step::Step() {
    Step_RecvReadStep COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_Step_RecvReadStep(const struct Step d) { return std::holds_alternative<Step_RecvReadStep>(d.v); }
  
inline bool is_Step_RecvWriteStep(const struct Step d) { return std::holds_alternative<Step_RecvWriteStep>(d.v); }
  
inline bool is_Step_AckReadStep(const struct Step d) { return std::holds_alternative<Step_AckReadStep>(d.v); }
  
inline bool is_Step_AckWriteStep(const struct Step d) { return std::holds_alternative<Step_AckWriteStep>(d.v); }

  
bool operator==(const InternalStep_ProcessReadStep &left, const InternalStep_ProcessReadStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const InternalStep_ProcessWriteStep &left, const InternalStep_ProcessWriteStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const InternalStep_HavocConflictingWritesStep &left, const InternalStep_HavocConflictingWritesStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
bool operator==(const InternalStep_HavocConflictingWriteReadStep &left, const InternalStep_HavocConflictingWriteReadStep &right) {
    (void)left; (void) right;
	return true ;
  }
  
InternalStep::InternalStep() {
    InternalStep_ProcessReadStep COMPILER_result_subStruct;
    v = COMPILER_result_subStruct;
  }
  
inline bool is_InternalStep_ProcessReadStep(const struct InternalStep d) { return std::holds_alternative<InternalStep_ProcessReadStep>(d.v); }
  
inline bool is_InternalStep_ProcessWriteStep(const struct InternalStep d) { return std::holds_alternative<InternalStep_ProcessWriteStep>(d.v); }
  
inline bool is_InternalStep_HavocConflictingWritesStep(const struct InternalStep d) { return std::holds_alternative<InternalStep_HavocConflictingWritesStep>(d.v); }
  
inline bool is_InternalStep_HavocConflictingWriteReadStep(const struct InternalStep d) { return std::holds_alternative<InternalStep_HavocConflictingWriteReadStep>(d.v); }


}// end of namespace AsyncDisk_Compile 
namespace LinearCells  {



  template <typename V>
LCellContents<V>::LCellContents() {
    v = Options_Compile::Option<V>();
  }
  template <typename V>
bool operator==(const LCellContents<V> &left, const LCellContents<V> &right)  {
    	return true 		&& left.v == right.v
    ;
  }

}// end of namespace LinearCells 
namespace _module  {











































































}// end of namespace _module 
template <typename V>
struct get_default<Options_Compile::Option<V> > {
  static Options_Compile::Option<V> call() {
    return Options_Compile::Option<V>();
  }
};
template <typename V>
struct get_default<GlinearOption_Compile::glOption<V> > {
  static GlinearOption_Compile::glOption<V> call() {
    return GlinearOption_Compile::glOption<V>();
  }
};
template <typename V>
struct get_default<Ptrs::PointsTo<V> > {
  static Ptrs::PointsTo<V> call() {
    return Ptrs::PointsTo<V>();
  }
};
template <typename V>
struct get_default<Ptrs::PointsToLinear<V> > {
  static Ptrs::PointsToLinear<V> call() {
    return Ptrs::PointsToLinear<V>();
  }
};
template <typename V>
struct get_default<Ptrs::PointsToArray<V> > {
  static Ptrs::PointsToArray<V> call() {
    return Ptrs::PointsToArray<V>();
  }
};
template <>
struct get_default<IocbStruct::Iocb > {
  static IocbStruct::Iocb call() {
    return IocbStruct::Iocb();
  }
};
template <>
struct get_default<Constants_Compile::PreConfig > {
  static Constants_Compile::PreConfig call() {
    return Constants_Compile::PreConfig();
  }
};
template <>
struct get_default<Constants_Compile::Config > {
  static Constants_Compile::Config call() {
    return Constants_Compile::Config();
  }
};
template <typename K>
struct get_default<FullMaps_Compile::pre__FullMap<K> > {
  static FullMaps_Compile::pre__FullMap<K> call() {
    return FullMaps_Compile::pre__FullMap<K>();
  }
};
template <>
struct get_default<GhostLoc_Compile::Loc > {
  static GhostLoc_Compile::Loc call() {
    return GhostLoc_Compile::Loc();
  }
};
template <typename V>
struct get_default<Cells::CellContents<V> > {
  static Cells::CellContents<V> call() {
    return Cells::CellContents<V>();
  }
};
template <>
struct get_default<CacheStatusType_Compile::Status > {
  static CacheStatusType_Compile::Status call() {
    return CacheStatusType_Compile::Status();
  }
};
template <>
struct get_default<DiskIfc_Compile::ReqRead > {
  static DiskIfc_Compile::ReqRead call() {
    return DiskIfc_Compile::ReqRead();
  }
};
template <>
struct get_default<DiskIfc_Compile::ReqWrite > {
  static DiskIfc_Compile::ReqWrite call() {
    return DiskIfc_Compile::ReqWrite();
  }
};
template <>
struct get_default<DiskIfc_Compile::RespRead > {
  static DiskIfc_Compile::RespRead call() {
    return DiskIfc_Compile::RespRead();
  }
};
template <>
struct get_default<DiskIfc_Compile::RespWrite > {
  static DiskIfc_Compile::RespWrite call() {
    return DiskIfc_Compile::RespWrite();
  }
};
template <>
struct get_default<DiskIfc_Compile::DiskOp > {
  static DiskIfc_Compile::DiskOp call() {
    return DiskIfc_Compile::DiskOp();
  }
};
template <>
struct get_default<CacheIfc_Compile::Input > {
  static CacheIfc_Compile::Input call() {
    return CacheIfc_Compile::Input();
  }
};
template <>
struct get_default<CacheIfc_Compile::Output > {
  static CacheIfc_Compile::Output call() {
    return CacheIfc_Compile::Output();
  }
};
template <>
struct get_default<CacheIfc_Compile::Op > {
  static CacheIfc_Compile::Op call() {
    return CacheIfc_Compile::Op();
  }
};
template <>
struct get_default<CacheSSM_Compile::Entry > {
  static CacheSSM_Compile::Entry call() {
    return CacheSSM_Compile::Entry();
  }
};
template <>
struct get_default<CacheSSM_Compile::M > {
  static CacheSSM_Compile::M call() {
    return CacheSSM_Compile::M();
  }
};
template <>
struct get_default<CacheSSM_Compile::Step > {
  static CacheSSM_Compile::Step call() {
    return CacheSSM_Compile::Step();
  }
};
template <>
struct get_default<Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile::Token > {
  static Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile::Token call() {
    return Tokens_ON_DiskPCM__ON__InputOutputIfc__DiskSSM____ON____InputOutputIfc________Compile::Token();
  }
};
template <>
struct get_default<Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile::Token > {
  static Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile::Token call() {
    return Tokens_ON_DiskPCM__ON__CacheIfc__CacheSSM____Compile::Token();
  }
};
template <>
struct get_default<DiskToken_ON_CacheIfc_CacheSSM__Compile::Token > {
  static DiskToken_ON_CacheIfc_CacheSSM__Compile::Token call() {
    return DiskToken_ON_CacheIfc_CacheSSM__Compile::Token();
  }
};
template <>
struct get_default<CacheResources_Compile::DiskPageMap > {
  static CacheResources_Compile::DiskPageMap call() {
    return CacheResources_Compile::DiskPageMap();
  }
};
template <>
struct get_default<CacheResources_Compile::HavocPermission > {
  static CacheResources_Compile::HavocPermission call() {
    return CacheResources_Compile::HavocPermission();
  }
};
template <>
struct get_default<CacheResources_Compile::CacheStatus > {
  static CacheResources_Compile::CacheStatus call() {
    return CacheResources_Compile::CacheStatus();
  }
};
template <>
struct get_default<CacheResources_Compile::CacheEmpty > {
  static CacheResources_Compile::CacheEmpty call() {
    return CacheResources_Compile::CacheEmpty();
  }
};
template <>
struct get_default<CacheResources_Compile::CacheReading > {
  static CacheResources_Compile::CacheReading call() {
    return CacheResources_Compile::CacheReading();
  }
};
template <>
struct get_default<CacheResources_Compile::CacheEntry > {
  static CacheResources_Compile::CacheEntry call() {
    return CacheResources_Compile::CacheEntry();
  }
};
template <>
struct get_default<CacheResources_Compile::DiskWriteTicket > {
  static CacheResources_Compile::DiskWriteTicket call() {
    return CacheResources_Compile::DiskWriteTicket();
  }
};
template <>
struct get_default<CacheResources_Compile::DiskWriteStub > {
  static CacheResources_Compile::DiskWriteStub call() {
    return CacheResources_Compile::DiskWriteStub();
  }
};
template <>
struct get_default<CacheResources_Compile::DiskReadTicket > {
  static CacheResources_Compile::DiskReadTicket call() {
    return CacheResources_Compile::DiskReadTicket();
  }
};
template <>
struct get_default<CacheResources_Compile::DiskReadStub > {
  static CacheResources_Compile::DiskReadStub call() {
    return CacheResources_Compile::DiskReadStub();
  }
};
template <>
struct get_default<CacheHandle_Compile::PageHandle > {
  static CacheHandle_Compile::PageHandle call() {
    return CacheHandle_Compile::PageHandle();
  }
};
template <>
struct get_default<CacheHandle_Compile::Key > {
  static CacheHandle_Compile::Key call() {
    return CacheHandle_Compile::Key();
  }
};
template <>
struct get_default<CacheHandle_Compile::Handle > {
  static CacheHandle_Compile::Handle call() {
    return CacheHandle_Compile::Handle();
  }
};
template <>
struct get_default<RwLock_Compile::Flag > {
  static RwLock_Compile::Flag call() {
    return RwLock_Compile::Flag();
  }
};
template <>
struct get_default<RwLock_Compile::SharedState > {
  static RwLock_Compile::SharedState call() {
    return RwLock_Compile::SharedState();
  }
};
template <>
struct get_default<RwLock_Compile::ExcState > {
  static RwLock_Compile::ExcState call() {
    return RwLock_Compile::ExcState();
  }
};
template <>
struct get_default<RwLock_Compile::WritebackState > {
  static RwLock_Compile::WritebackState call() {
    return RwLock_Compile::WritebackState();
  }
};
template <>
struct get_default<RwLock_Compile::ReadState > {
  static RwLock_Compile::ReadState call() {
    return RwLock_Compile::ReadState();
  }
};
template <>
struct get_default<RwLock_Compile::CentralState > {
  static RwLock_Compile::CentralState call() {
    return RwLock_Compile::CentralState();
  }
};
template <>
struct get_default<RwLock_Compile::M > {
  static RwLock_Compile::M call() {
    return RwLock_Compile::M();
  }
};
template <>
struct get_default<Rw_PCMWrap_ON_RwLock__Compile::M > {
  static Rw_PCMWrap_ON_RwLock__Compile::M call() {
    return Rw_PCMWrap_ON_RwLock__Compile::M();
  }
};
template <>
struct get_default<Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile::Token > {
  static Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile::Token call() {
    return Tokens_ON_Rw__PCMWrap__ON__RwLock____Compile::Token();
  }
};
template <>
struct get_default<Tokens_ON_Rw__PCMExt__ON__RwLock____Compile::Token > {
  static Tokens_ON_Rw__PCMExt__ON__RwLock____Compile::Token call() {
    return Tokens_ON_Rw__PCMExt__ON__RwLock____Compile::Token();
  }
};
template <>
struct get_default<RwLockToken_Compile::CentralToken > {
  static RwLockToken_Compile::CentralToken call() {
    return RwLockToken_Compile::CentralToken();
  }
};
template <>
struct get_default<RwLockToken_Compile::WritebackObtainedToken > {
  static RwLockToken_Compile::WritebackObtainedToken call() {
    return RwLockToken_Compile::WritebackObtainedToken();
  }
};
template <>
struct get_default<RwLockToken_Compile::SharedPendingToken > {
  static RwLockToken_Compile::SharedPendingToken call() {
    return RwLockToken_Compile::SharedPendingToken();
  }
};
template <>
struct get_default<RwLockToken_Compile::SharedPending2Token > {
  static RwLockToken_Compile::SharedPending2Token call() {
    return RwLockToken_Compile::SharedPending2Token();
  }
};
template <>
struct get_default<RwLockToken_Compile::SharedObtainedToken > {
  static RwLockToken_Compile::SharedObtainedToken call() {
    return RwLockToken_Compile::SharedObtainedToken();
  }
};
template <>
struct get_default<CacheAIOParams_Compile::IOSlotAccess > {
  static CacheAIOParams_Compile::IOSlotAccess call() {
    return CacheAIOParams_Compile::IOSlotAccess();
  }
};
template <>
struct get_default<CacheAIOParams_Compile::ReadG > {
  static CacheAIOParams_Compile::ReadG call() {
    return CacheAIOParams_Compile::ReadG();
  }
};
template <>
struct get_default<CacheAIOParams_Compile::ReadvG > {
  static CacheAIOParams_Compile::ReadvG call() {
    return CacheAIOParams_Compile::ReadvG();
  }
};
template <>
struct get_default<CacheAIOParams_Compile::WriteG > {
  static CacheAIOParams_Compile::WriteG call() {
    return CacheAIOParams_Compile::WriteG();
  }
};
template <>
struct get_default<CacheAIOParams_Compile::WritevG > {
  static CacheAIOParams_Compile::WritevG call() {
    return CacheAIOParams_Compile::WritevG();
  }
};
template <>
struct get_default<CounterPCM_Compile::M > {
  static CounterPCM_Compile::M call() {
    return CounterPCM_Compile::M();
  }
};
template <>
struct get_default<Tokens_ON_CounterPCM__Compile::Token > {
  static Tokens_ON_CounterPCM__Compile::Token call() {
    return Tokens_ON_CounterPCM__Compile::Token();
  }
};
template <>
struct get_default<ClientCounter_Compile::Client > {
  static ClientCounter_Compile::Client call() {
    return ClientCounter_Compile::Client();
  }
};
template <>
struct get_default<ClientCounter_Compile::Clients > {
  static ClientCounter_Compile::Clients call() {
    return ClientCounter_Compile::Clients();
  }
};
template <>
struct get_default<AtomicRefcountImpl_Compile::RG > {
  static AtomicRefcountImpl_Compile::RG call() {
    return AtomicRefcountImpl_Compile::RG();
  }
};
template <>
struct get_default<AtomicRefcountImpl_Compile::AtomicRefcount > {
  static AtomicRefcountImpl_Compile::AtomicRefcount call() {
    return AtomicRefcountImpl_Compile::AtomicRefcount();
  }
};
template <>
struct get_default<AtomicStatusImpl_Compile::G > {
  static AtomicStatusImpl_Compile::G call() {
    return AtomicStatusImpl_Compile::G();
  }
};
template <>
struct get_default<AtomicStatusImpl_Compile::AtomicStatus > {
  static AtomicStatusImpl_Compile::AtomicStatus call() {
    return AtomicStatusImpl_Compile::AtomicStatus();
  }
};
template <typename G>
struct get_default<BasicLockImpl_Compile::pre__BasicLock<G> > {
  static BasicLockImpl_Compile::pre__BasicLock<G> call() {
    return BasicLockImpl_Compile::pre__BasicLock<G>();
  }
};
template <>
struct get_default<InstantiatedDiskInterface::FinishedReq > {
  static InstantiatedDiskInterface::FinishedReq call() {
    return InstantiatedDiskInterface::FinishedReq();
  }
};
template <>
struct get_default<CacheTypes_ON_TheAIO__Compile::NullGhostType > {
  static CacheTypes_ON_TheAIO__Compile::NullGhostType call() {
    return CacheTypes_ON_TheAIO__Compile::NullGhostType();
  }
};
template <>
struct get_default<CacheTypes_ON_TheAIO__Compile::StatusIdx > {
  static CacheTypes_ON_TheAIO__Compile::StatusIdx call() {
    return CacheTypes_ON_TheAIO__Compile::StatusIdx();
  }
};
template <>
struct get_default<CacheTypes_ON_TheAIO__Compile::Cache > {
  static CacheTypes_ON_TheAIO__Compile::Cache call() {
    return CacheTypes_ON_TheAIO__Compile::Cache();
  }
};
template <>
struct get_default<CacheTypes_ON_TheAIO__Compile::LocalState > {
  static CacheTypes_ON_TheAIO__Compile::LocalState call() {
    return CacheTypes_ON_TheAIO__Compile::LocalState();
  }
};
template <>
struct get_default<CacheTypes_ON_TheAIO__Compile::IOSlot > {
  static CacheTypes_ON_TheAIO__Compile::IOSlot call() {
    return CacheTypes_ON_TheAIO__Compile::IOSlot();
  }
};
template <>
struct get_default<CacheOps_ON_TheAIO__Compile::PageHandleIdx > {
  static CacheOps_ON_TheAIO__Compile::PageHandleIdx call() {
    return CacheOps_ON_TheAIO__Compile::PageHandleIdx();
  }
};
template <>
struct get_default<CacheOps_ON_TheAIO__Compile::WriteablePageHandle > {
  static CacheOps_ON_TheAIO__Compile::WriteablePageHandle call() {
    return CacheOps_ON_TheAIO__Compile::WriteablePageHandle();
  }
};
template <>
struct get_default<CacheOps_ON_TheAIO__Compile::ReadonlyPageHandle > {
  static CacheOps_ON_TheAIO__Compile::ReadonlyPageHandle call() {
    return CacheOps_ON_TheAIO__Compile::ReadonlyPageHandle();
  }
};
template <>
struct get_default<CacheOps_ON_TheAIO__Compile::ClaimPageHandle > {
  static CacheOps_ON_TheAIO__Compile::ClaimPageHandle call() {
    return CacheOps_ON_TheAIO__Compile::ClaimPageHandle();
  }
};
template <>
struct get_default<AsyncDisk_Compile::Variables > {
  static AsyncDisk_Compile::Variables call() {
    return AsyncDisk_Compile::Variables();
  }
};
template <>
struct get_default<AsyncDisk_Compile::Step > {
  static AsyncDisk_Compile::Step call() {
    return AsyncDisk_Compile::Step();
  }
};
template <>
struct get_default<AsyncDisk_Compile::InternalStep > {
  static AsyncDisk_Compile::InternalStep call() {
    return AsyncDisk_Compile::InternalStep();
  }
};
template <typename V>
struct get_default<LinearCells::LCellContents<V> > {
  static LinearCells::LCellContents<V> call() {
    return LinearCells::LCellContents<V>();
  }
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_sbyte > > {
static std::shared_ptr<NativeTypes_Compile::class_sbyte > call() {
return std::shared_ptr<NativeTypes_Compile::class_sbyte >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_byte > > {
static std::shared_ptr<NativeTypes_Compile::class_byte > call() {
return std::shared_ptr<NativeTypes_Compile::class_byte >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_int16 > > {
static std::shared_ptr<NativeTypes_Compile::class_int16 > call() {
return std::shared_ptr<NativeTypes_Compile::class_int16 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_uint16 > > {
static std::shared_ptr<NativeTypes_Compile::class_uint16 > call() {
return std::shared_ptr<NativeTypes_Compile::class_uint16 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_int32 > > {
static std::shared_ptr<NativeTypes_Compile::class_int32 > call() {
return std::shared_ptr<NativeTypes_Compile::class_int32 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_uint32 > > {
static std::shared_ptr<NativeTypes_Compile::class_uint32 > call() {
return std::shared_ptr<NativeTypes_Compile::class_uint32 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_int64 > > {
static std::shared_ptr<NativeTypes_Compile::class_int64 > call() {
return std::shared_ptr<NativeTypes_Compile::class_int64 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_uint64 > > {
static std::shared_ptr<NativeTypes_Compile::class_uint64 > call() {
return std::shared_ptr<NativeTypes_Compile::class_uint64 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_nat8 > > {
static std::shared_ptr<NativeTypes_Compile::class_nat8 > call() {
return std::shared_ptr<NativeTypes_Compile::class_nat8 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_nat16 > > {
static std::shared_ptr<NativeTypes_Compile::class_nat16 > call() {
return std::shared_ptr<NativeTypes_Compile::class_nat16 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_nat32 > > {
static std::shared_ptr<NativeTypes_Compile::class_nat32 > call() {
return std::shared_ptr<NativeTypes_Compile::class_nat32 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_nat64 > > {
static std::shared_ptr<NativeTypes_Compile::class_nat64 > call() {
return std::shared_ptr<NativeTypes_Compile::class_nat64 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::class_uint128 > > {
static std::shared_ptr<NativeTypes_Compile::class_uint128 > call() {
return std::shared_ptr<NativeTypes_Compile::class_uint128 >();}
};
template <>
struct get_default<std::shared_ptr<NativeTypes_Compile::__default > > {
static std::shared_ptr<NativeTypes_Compile::__default > call() {
return std::shared_ptr<NativeTypes_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<GlinearOption_Compile::__default > > {
static std::shared_ptr<GlinearOption_Compile::__default > call() {
return std::shared_ptr<GlinearOption_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<PageSizeConstant_Compile::__default > > {
static std::shared_ptr<PageSizeConstant_Compile::__default > call() {
return std::shared_ptr<PageSizeConstant_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<Constants_Compile::__default > > {
static std::shared_ptr<Constants_Compile::__default > call() {
return std::shared_ptr<Constants_Compile::__default >();}
};
template <typename K>
struct get_default<std::shared_ptr<FullMaps_Compile::class_FullMap<K> > > {
static std::shared_ptr<FullMaps_Compile::class_FullMap<K> > call() {
return std::shared_ptr<FullMaps_Compile::class_FullMap<K> >();}
};
template <>
struct get_default<std::shared_ptr<DiskIfc_Compile::class_Block > > {
static std::shared_ptr<DiskIfc_Compile::class_Block > call() {
return std::shared_ptr<DiskIfc_Compile::class_Block >();}
};
template <>
struct get_default<std::shared_ptr<DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile::__default > > {
static std::shared_ptr<DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile::__default > call() {
return std::shared_ptr<DiskTokenUtils_ON_CacheIfc_CacheSSM__Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<CacheResources_Compile::__default > > {
static std::shared_ptr<CacheResources_Compile::__default > call() {
return std::shared_ptr<CacheResources_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile::class_GToken > > {
static std::shared_ptr<PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile::class_GToken > call() {
return std::shared_ptr<PCMWrapTokens_ON_Rw__PCMWrap__ON__RwLock____Compile::class_GToken >();}
};
template <>
struct get_default<std::shared_ptr<RwTokens_ON_RwLock__Compile::class_Token > > {
static std::shared_ptr<RwTokens_ON_RwLock__Compile::class_Token > call() {
return std::shared_ptr<RwTokens_ON_RwLock__Compile::class_Token >();}
};
template <>
struct get_default<std::shared_ptr<RwTokens_ON_RwLock__Compile::__default > > {
static std::shared_ptr<RwTokens_ON_RwLock__Compile::__default > call() {
return std::shared_ptr<RwTokens_ON_RwLock__Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<RwLockToken_Compile::__default > > {
static std::shared_ptr<RwLockToken_Compile::__default > call() {
return std::shared_ptr<RwLockToken_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<CacheAIOParams_Compile::__default > > {
static std::shared_ptr<CacheAIOParams_Compile::__default > call() {
return std::shared_ptr<CacheAIOParams_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<BitOps_Compile::__default > > {
static std::shared_ptr<BitOps_Compile::__default > call() {
return std::shared_ptr<BitOps_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<ClientCounter_Compile::__default > > {
static std::shared_ptr<ClientCounter_Compile::__default > call() {
return std::shared_ptr<ClientCounter_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<AtomicRefcountImpl_Compile::__default > > {
static std::shared_ptr<AtomicRefcountImpl_Compile::__default > call() {
return std::shared_ptr<AtomicRefcountImpl_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<AtomicIndexLookupImpl_Compile::__default > > {
static std::shared_ptr<AtomicIndexLookupImpl_Compile::__default > call() {
return std::shared_ptr<AtomicIndexLookupImpl_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<AtomicStatusImpl_Compile::__default > > {
static std::shared_ptr<AtomicStatusImpl_Compile::__default > call() {
return std::shared_ptr<AtomicStatusImpl_Compile::__default >();}
};
template <typename G>
struct get_default<std::shared_ptr<BasicLockImpl_Compile::class_BasicLock<G> > > {
static std::shared_ptr<BasicLockImpl_Compile::class_BasicLock<G> > call() {
return std::shared_ptr<BasicLockImpl_Compile::class_BasicLock<G> >();}
};
template <>
struct get_default<std::shared_ptr<BasicLockImpl_Compile::__default > > {
static std::shared_ptr<BasicLockImpl_Compile::__default > call() {
return std::shared_ptr<BasicLockImpl_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<LinearSequence__i_Compile::__default > > {
static std::shared_ptr<LinearSequence__i_Compile::__default > call() {
return std::shared_ptr<LinearSequence__i_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<MemSplit_Compile::__default > > {
static std::shared_ptr<MemSplit_Compile::__default > call() {
return std::shared_ptr<MemSplit_Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<CacheIO_ON_TheAIO__Compile::__default > > {
static std::shared_ptr<CacheIO_ON_TheAIO__Compile::__default > call() {
return std::shared_ptr<CacheIO_ON_TheAIO__Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<CacheWritebackBatch_ON_TheAIO__Compile::__default > > {
static std::shared_ptr<CacheWritebackBatch_ON_TheAIO__Compile::__default > call() {
return std::shared_ptr<CacheWritebackBatch_ON_TheAIO__Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<CacheOps_ON_TheAIO__Compile::__default > > {
static std::shared_ptr<CacheOps_ON_TheAIO__Compile::__default > call() {
return std::shared_ptr<CacheOps_ON_TheAIO__Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<CacheInit_ON_TheAIO__Compile::__default > > {
static std::shared_ptr<CacheInit_ON_TheAIO__Compile::__default > call() {
return std::shared_ptr<CacheInit_ON_TheAIO__Compile::__default >();}
};
template <>
struct get_default<std::shared_ptr<Application_ON_TheAIO__Compile::__default > > {
static std::shared_ptr<Application_ON_TheAIO__Compile::__default > call() {
return std::shared_ptr<Application_ON_TheAIO__Compile::__default >();}
};
