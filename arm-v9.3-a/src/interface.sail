
$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>

enum Shareability = {Shareability_NSH, Shareability_ISH, Shareability_OSH}

enum SecurityState = {SS_NonSecure, SS_Root, SS_Realm, SS_Secure}

enum AccType = {
  AccType_NORMAL,
  AccType_STREAM,
  AccType_VEC,
  AccType_VECSTREAM,
  AccType_SVE,
  AccType_SVESTREAM,
  AccType_SME,
  AccType_SMESTREAM,
  AccType_UNPRIVSTREAM,
  AccType_A32LSMD,
  AccType_ATOMIC,
  AccType_ATOMICRW,
  AccType_ORDERED,
  AccType_ORDEREDRW,
  AccType_ORDEREDATOMIC,
  AccType_ORDEREDATOMICRW,
  AccType_ATOMICLS64,
  AccType_LIMITEDORDERED,
  AccType_UNPRIV,
  AccType_IFETCH,
  AccType_TTW,
  AccType_NONFAULT,
  AccType_CNOTFIRST,
  AccType_NV2REGISTER,
  AccType_DC,
  AccType_IC,
  AccType_DCZVA,
  AccType_ATPAN,
  AccType_AT
}

enum Fault = {
  Fault_None,
  Fault_AccessFlag,
  Fault_Alignment,
  Fault_Background,
  Fault_Domain,
  Fault_Permission,
  Fault_Translation,
  Fault_AddressSize,
  Fault_SyncExternal,
  Fault_SyncExternalOnWalk,
  Fault_SyncParity,
  Fault_SyncParityOnWalk,
  Fault_GPCFOnWalk,
  Fault_GPCFOnOutput,
  Fault_AsyncParity,
  Fault_AsyncExternal,
  Fault_Debug,
  Fault_TLBConflict,
  Fault_BranchTarget,
  Fault_HWUpdateAccessFlag,
  Fault_Lockdown,
  Fault_Exclusive,
  Fault_ICacheMaint
}

enum Regime = {Regime_EL3, Regime_EL30, Regime_EL2, Regime_EL20, Regime_EL10}

enum PASpace = {PAS_NonSecure, PAS_Secure, PAS_Root, PAS_Realm}

struct FullAddress = {paspace : PASpace, address : bits(52)}

enum GPCF = {GPCF_None, GPCF_AddressSize, GPCF_Walk, GPCF_EABT, GPCF_Fail}

struct GPCFRecord = {gpf : GPCF, level : int}

struct FaultRecord = {
  statuscode : Fault,
  acctype : AccType,
  ipaddress : FullAddress,
  gpcf : GPCFRecord,
  paddress : FullAddress,
  gpcfs2walk : bool,
  s2fs1walk : bool,
  write : bool,
  level : int,
  extflag : bits(1),
  secondstage : bool,
  domain : bits(4),
  errortype : bits(2),
  debugmoe : bits(4)
}

type TranslationInfo = unit

// This the set of all Arm access types that are not covered by the generic
// interface access type.
union arm_acc_type = {
  // Streaming access from a LDNP/STNP or some CPY* instruction
  SAcc_STREAM : unit,
  // Vector access, the boolean means that is a streaming access
  SAcc_VEC : /* streaming access :*/ bool,
  // SVE access, the boolean means that is a streaming access
  SAcc_SVE : /* streaming access :*/ bool,
  // SME access, the boolean means that is a streaming access
  SAcc_SME : /* streaming access :*/ bool,
  // Unpriviledged access, the boolean means that is a streaming access
  SAcc_UNPRIV : /* streaming access :*/ bool,
  // Load and store multiple from Aarch32
  SAcc_A32LSMD : unit,
  // Atomic 64 bytes access from LD64B/ST64B and some weirder versions
  SAcc_ATOMICLS64 : unit,
  // Load-LOAcquire and Store-LORelease
  SAcc_LIMITEDORDERED : unit,
  // Non-faulting access (exact semantics unclear)
  SAcc_NONFAULT : unit,
  // Contiguous FF load, not first element
  SAcc_CNOTFIRST : unit,
  // MRS/MSR instruction used at EL1 and which is
  // converted to a memory access that uses the
  // EL2 translation regime
  SAcc_NV2REGISTER : unit,
  // Data cache maintenance
  SAcc_DC : unit,
  // Instruction cache maintenance
  SAcc_IC : unit,
  // DC ZVA instructions
  SAcc_DCZVA : unit,
  // Address translation with PAN permission checks
  SAcc_ATPAN : unit,
  // Address translation
  SAcc_AT : unit
}


enum CacheOp = {CacheOp_Clean, CacheOp_Invalidate, CacheOp_CleanInvalidate}

enum CacheOpScope = {
  CacheOpScope_SetWay,
  CacheOpScope_PoU,
  CacheOpScope_PoC,
  CacheOpScope_PoP,
  CacheOpScope_PoDP,
  CacheOpScope_ALLU,
  CacheOpScope_ALLUIS
}

enum CachePASpace = {
  CPAS_NonSecure,
  CPAS_Any,
  CPAS_RealmNonSecure,
  CPAS_Realm,
  CPAS_Root,
  CPAS_SecureNonSecure,
  CPAS_Secure
}

enum CacheType = {
  CacheType_Data,
  CacheType_Tag,
  CacheType_Data_Tag,
  CacheType_Instruction
}

struct CacheRecord = {
  acctype : AccType,
  cacheop : CacheOp,
  opscope : CacheOpScope,
  cachetype : CacheType,
  regval : bits(64),
  paddress : FullAddress,
  vaddress : bits(64),
  set : int,
  way : int,
  level : int,
  shareability : Shareability,
  translated : bool,
  is_vmid_valid : bool,
  vmid : bits(16),
  is_asid_valid : bool,
  asid : bits(16),
  security : SecurityState,
  cpas : CachePASpace
}

function AccType_to_Access_kind(acc : AccType) -> Access_kind(arm_acc_type) = {
  match acc {
    AccType_NORMAL => AK_explicit(struct{variety = AV_plain, strength = AS_normal}),
    AccType_STREAM => AK_arch(SAcc_STREAM()),
    AccType_VEC => AK_arch(SAcc_VEC(false)),
    AccType_VECSTREAM => AK_arch(SAcc_VEC(true)),
    AccType_SVE => AK_arch(SAcc_SVE(false)),
    AccType_SVESTREAM => AK_arch(SAcc_SVE(true)),
    AccType_SME => AK_arch(SAcc_SME(false)),
    AccType_SMESTREAM => AK_arch(SAcc_SME(true)),
    AccType_UNPRIVSTREAM => AK_arch(SAcc_UNPRIV(true)),
    AccType_A32LSMD => AK_arch(SAcc_A32LSMD()),
    AccType_ATOMIC => AK_explicit(struct{variety = AV_exclusive, strength = AS_normal}),
    AccType_ATOMICRW => AK_explicit(struct{variety = AV_atomic_rmw, strength = AS_normal}),
    AccType_ORDERED => AK_explicit(struct {variety = AV_plain, strength = AS_rel_or_acq}),
    AccType_ORDEREDRW => undefined,
    AccType_ORDEREDATOMIC => AK_explicit(struct {variety = AV_exclusive, strength = AS_rel_or_acq}),
    AccType_ORDEREDATOMICRW => AK_explicit(struct {variety = AV_atomic_rmw, strength = AS_rel_or_acq}),
    AccType_ATOMICLS64 => AK_arch(SAcc_ATOMICLS64()),
    AccType_LIMITEDORDERED => AK_arch(SAcc_LIMITEDORDERED()),
    AccType_UNPRIV => AK_arch(SAcc_UNPRIV(false)),
    AccType_IFETCH => AK_ifetch(),
    AccType_TTW => AK_ttw(),
    AccType_NONFAULT => AK_arch(SAcc_NONFAULT()),
    AccType_CNOTFIRST => AK_arch(SAcc_CNOTFIRST()),
    AccType_NV2REGISTER => AK_arch(SAcc_NV2REGISTER()),
    AccType_DC => AK_arch(SAcc_DC()),
    AccType_IC => AK_arch(SAcc_IC()),
    AccType_DCZVA => AK_arch(SAcc_DCZVA()),
    AccType_ATPAN => AK_arch(SAcc_ATPAN()),
    AccType_AT => AK_arch(SAcc_AT()),
  }
}

val pa_bits : bits(56) -> bits(64)

function pa_bits(bv) = sail_zero_extend(bv, 64)

instantiation sail_mem_read with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = Fault,
  pa_bits = pa_bits

val read_request : forall 'n, 'n > 0. (AccType, option(TranslationInfo), int('n), bits(64), bits(56)) -> Mem_read_request('n, 64, bits(56), option(TranslationInfo), arm_acc_type)

function read_request(acc, ti, size, va, pa) = struct {
  access_kind = AccType_to_Access_kind(acc),
  va = Some(va),
  pa = pa,
  translation = ti,
  size = size,
  tag = false
}

instantiation sail_mem_write with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = Fault,
  pa_bits = pa_bits

val write_request : forall 'n, 'n > 0. (AccType, option(TranslationInfo), int('n), bits(64), bits(56), bits(8 * 'n)) -> Mem_write_request('n, 64, bits(56), option(TranslationInfo), arm_acc_type)

function write_request(acc, ti, size, va, pa, value) = struct {
  access_kind = AccType_to_Access_kind(acc),
  va = Some(va),
  pa = pa,
  translation = ti,
  size = size,
  value = Some(value),
  tag = None(),
}

enum TLBILevel = {TLBILevel_Any, TLBILevel_Last}

enum TLBIMemAttr = {TLBI_AllAttr, TLBI_ExcludeXS}

enum TLBIOp = {
  TLBIOp_DALL,
  TLBIOp_DASID,
  TLBIOp_DVA,
  TLBIOp_IALL,
  TLBIOp_IASID,
  TLBIOp_IVA,
  TLBIOp_ALL,
  TLBIOp_ASID,
  TLBIOp_IPAS2,
  TLBIOp_VAA,
  TLBIOp_VA,
  TLBIOp_VMALL,
  TLBIOp_VMALLS12,
  TLBIOp_RIPAS2,
  TLBIOp_RVAA,
  TLBIOp_RVA,
  TLBIOp_RPA,
  TLBIOp_PAALL
}

struct TLBIRecord = {
  op : TLBIOp,
  from_aarch64 : bool,
  security : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  level : TLBILevel,
  attr : TLBIMemAttr,
  ipaspace : PASpace,
  address : bits(64),
  end_address_name : bits(64),
  tg : bits(2)
}

struct TLBI = {
  rec: TLBIRecord,
  shareability : Shareability,
}

instantiation sail_tlbi with
  'tlbi = TLBI

instantiation sail_cache_op with
  'cache_op = CacheRecord

enum MBReqDomain = {
  MBReqDomain_Nonshareable,
  MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable,
  MBReqDomain_FullSystem
}

enum MBReqTypes = {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}

// The details of a data memory/synchonisation barrier
struct DxB = {
  domain : MBReqDomain,
  types : MBReqTypes,
  nXS : bool
}

// An Arm barrier
union Barrier = {
  Barrier_DSB : DxB,
  Barrier_DMB : DxB, // The nXS field is ignored from DMBs
  Barrier_ISB : unit,
  Barrier_SSBB : unit,
  Barrier_PSSBB : unit,
  Barrier_SB : unit,
}

instantiation sail_barrier with
  'barrier = Barrier

instantiation sail_return_exception

instantiation sail_take_exception with
  'fault = option(FaultRecord)

val __mark_register = "mark_register" : forall ('a: Type). (register('a), string) -> unit
val __mark_register_pair = "mark_register_pair" : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit

val __ignore_write_to : forall ('a: Type). register('a) -> unit

function __ignore_write_to(reg) = __mark_register(reg, "ignore_write")