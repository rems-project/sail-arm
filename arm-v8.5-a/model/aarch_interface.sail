
$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/eret.sail>
$include <concurrency_interface/cache_op.sail>

type Level = int

// The translation information provided with every memory access.
struct TranslationInfo = {
  regime : bits(2),
  vmid : option(bits(16)),
  asid : option(bits(16)),
  va : bits(64),
  s1level : option(Level),
  s2info : option((bits(64), Level)),
  memattrs: MemoryAttributes,
}

let dummy_translation_info: TranslationInfo = struct {
  regime = 0b00,
  vmid = None(),
  asid = None(),
  va = 0x0000_0000_0000_0000,
  s1level = None(),
  s2info = None(),
  memattrs = struct {
    typ = MemType_Normal,
    device = DeviceType_GRE,
    inner = struct { attrs = 0b00, hints = 0b00, transient = false },
    outer = struct { attrs = 0b00, hints = 0b00, transient = false },
    tagged = false,
    shareable = false,
    outershareable = false
  }
}

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
  SAcc_AT : unit,
}

function AccType_to_Access_kind(acc : AccType) -> Access_kind(arm_acc_type) = {
  match acc {
    AccType_NORMAL => AK_explicit(struct{variety = AV_plain, strength = AS_normal}),
    AccType_STREAM => AK_arch(SAcc_STREAM()),
    AccType_VEC => AK_arch(SAcc_VEC(false)),
    AccType_VECSTREAM => AK_arch(SAcc_VEC(true)),
    AccType_ATOMIC => AK_explicit(struct{variety = AV_exclusive, strength = AS_normal}),
    AccType_ATOMICRW => AK_explicit(struct{variety = AV_atomic_rmw, strength = AS_normal}),
    AccType_ORDERED => AK_explicit(struct {variety = AV_plain, strength = AS_rel_or_acq}),
    AccType_ORDEREDRW => undefined,
    AccType_ORDEREDATOMIC => AK_explicit(struct {variety = AV_exclusive, strength = AS_rel_or_acq}),
    AccType_ORDEREDATOMICRW => AK_explicit(struct {variety = AV_atomic_rmw, strength = AS_rel_or_acq}),
    AccType_LIMITEDORDERED => AK_arch(SAcc_LIMITEDORDERED()),
    AccType_UNPRIV => AK_arch(SAcc_UNPRIV(false)),
    AccType_IFETCH => AK_ifetch(),
    AccType_PTW => AK_ttw(),
    AccType_NV2REGISTER => AK_arch(SAcc_NV2REGISTER()),
    AccType_DC => AK_arch(SAcc_DC()),
    AccType_DC_UNPRIV => AK_arch(SAcc_DC()),
    AccType_IC => AK_arch(SAcc_IC()),
    AccType_DCZVA => AK_arch(SAcc_DCZVA()),
    AccType_AT => AK_arch(SAcc_AT()),
    AccType_TAG => AK_arch(SAcc_AT()), //FIXME
  }
}

val pa_bits : bits(56) -> bits(64)

function pa_bits(bv) = sail_zero_extend(bv, 64)

instantiation sail_mem_read with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = FaultRecord,
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
  'abort = FaultRecord,
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

// The details of a data memory/synchonisation barrier
struct DxB = {
  domain : MBReqDomain,
  types : MBReqTypes,
}

// An Arm barrier
union Barrier = {
  Barrier_DSB : DxB,
  Barrier_DMB : DxB,
  Barrier_ISB : unit,
  Barrier_SSBB : unit,
  Barrier_PSSBB : unit,
  Barrier_SB : unit,
}

instantiation sail_barrier with
  'barrier = Barrier

union TLBIType = {
  TLBIType_ALLE1 : unit,
  TLBIType_ALLE1IS : unit,
  TLBIType_ALLE1OS : unit,
  TLBIType_ALLE2 : unit,
  TLBIType_ALLE2IS : unit,
  TLBIType_ALLE2OS : unit,
  TLBIType_ALLE3 : unit,
  TLBIType_ALLE3IS : unit,
  TLBIType_ALLE3OS : unit, 
  TLBIType_ASIDE1 : bits(64),
  TLBIType_ASIDE1IS : bits(64),
  TLBIType_ASIDE1OS : bits(64),
  TLBIType_IPAS2E1 : bits(64),
  TLBIType_IPAS2E1IS : bits(64),
  TLBIType_IPAS2E1OS : bits(64),
  TLBIType_IPAS2LE1 : bits(64),
  TLBIType_IPAS2LE1IS : bits(64),
  TLBIType_IPAS2LE1OS : bits(64),
  TLBIType_RIPAS2E1 : bits(64),
  TLBIType_RIPAS2E1IS : bits(64),
  TLBIType_RIPAS2E1OS : bits(64),
  TLBIType_RIPAS2LE1 : bits(64),
  TLBIType_RIPAS2LE1IS : bits(64),
  TLBIType_RIPAS2LE1OS : bits(64),
  TLBIType_RVAAE1 : bits(64),
  TLBIType_RVAAE1IS : bits(64),
  TLBIType_RVAAE1OS : bits(64),
  TLBIType_RVAALE1 : bits(64),
  TLBIType_RVAALE1IS : bits(64),
  TLBIType_RVAALE1OS : bits(64),
  TLBIType_RVAE1 : bits(64),
  TLBIType_RVAE1IS : bits(64),
  TLBIType_RVAE1OS : bits(64),
  TLBIType_RVAE2 : bits(64),
  TLBIType_RVAE2IS : bits(64),
  TLBIType_RVAE2OS : bits(64),
  TLBIType_RVAE3 : bits(64),
  TLBIType_RVAE3IS : bits(64),
  TLBIType_RVAE3OS : bits(64),
  TLBIType_RVALE1 : bits(64),
  TLBIType_RVALE1IS : bits(64),
  TLBIType_RVALE1OS : bits(64),
  TLBIType_RVALE2 : bits(64),
  TLBIType_RVALE2IS : bits(64),
  TLBIType_RVALE2OS : bits(64),
  TLBIType_RVALE3 : bits(64),
  TLBIType_RVALE3IS : bits(64),
  TLBIType_VAAE1 : bits(64),
  TLBIType_VAAE1IS : bits(64),
  TLBIType_VAAE1OS : bits(64),
  TLBIType_VAALE1 : bits(64),
  TLBIType_VAALE1IS : bits(64),
  TLBIType_VAALE1OS : bits(64),
  TLBIType_VAE1 : bits(64),
  TLBIType_VAE1IS : bits(64),
  TLBIType_VAE1OS : bits(64),
  TLBIType_VAE2 : bits(64),
  TLBIType_VAE2IS : bits(64),
  TLBIType_VAE2OS : bits(64),
  TLBIType_VAE3 : bits(64),
  TLBIType_VAE3IS : bits(64),
  TLBIType_VAE3OS : bits(64),
  TLBIType_VALE1 : bits(64),
  TLBIType_VALE1IS : bits(64),
  TLBIType_VALE1OS : bits(64),
  TLBIType_VALE2 : bits(64),
  TLBIType_VALE2IS : bits(64),
  TLBIType_VALE2OS : bits(64),
  TLBIType_VALE3 : bits(64),
  TLBIType_VALE3IS : bits(64),
  TLBIType_VALE3OS : bits(64),
  TLBIType_VMALLE1 : unit,
  TLBIType_VMALLE1IS : unit,
  TLBIType_VMALLE1OS : unit,
  TLBIType_VMALLS12E1 : unit,
  TLBIType_VMALLS12E1IS : unit,
  TLBIType_VMALLS12E1OS : unit,
}

struct TLBIInfo = {
  typ : TLBIType,
  vmid : bits(16),
}

instantiation sail_tlbi with
  'tlbi = TLBIInfo

instantiation sail_eret

enum cache_op_kind = {
  Cache_op_D_IVAC, Cache_op_D_ISW,  Cache_op_D_CSW,  Cache_op_D_CISW,
  Cache_op_D_ZVA,  Cache_op_D_CVAC, Cache_op_D_CVAU, Cache_op_D_CIVAC,
  /* AArch64 IC */
  Cache_op_I_IALLUIS, Cache_op_I_IALLU, Cache_op_I_IVAU
}

struct cache_op_info = {
  kind : cache_op_kind,
  address : bits(64),
}

instantiation sail_cache_op with
  'cache_op = cache_op_info
