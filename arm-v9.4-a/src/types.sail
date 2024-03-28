/******************************************************************************/
/*  BSD 3-clause Clear License                                                */
/*                                                                            */
/*  Copyright (c) 2023                                                        */
/*    Arm Limited (or its affiliates),                                        */
/*    Thomas Bauereiss,                                                       */
/*    Brian Campbell,                                                         */
/*    Alasdair Armstrong,                                                     */
/*    Alastair Reid,                                                          */
/*    Peter Sewell                                                            */
/*                                                                            */
/*  All rights reserved.                                                      */
/*                                                                            */
/*  Redistribution and use in source and binary forms, with or without        */
/*  modification, are permitted (subject to the limitations in the            */
/*  disclaimer below) provided that the following conditions are met:         */
/*                                                                            */
/*    * Redistributions of source code must retain the above copyright        */
/*      notice, this list of conditions and the following disclaimer.         */
/*    * Redistributions in binary form must reproduce the above copyright     */
/*      notice, this list of conditions and the following disclaimer in the   */
/*      documentation and/or other materials provided with the distribution.  */
/*    * Neither the name of ARM Limited nor the names of its contributors     */
/*      may be used to endorse or promote products derived from this          */
/*      software without specific prior written permission.                   */
/*                                                                            */
/*  NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE GRANTED   */
/*  BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND   */
/*  CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,    */
/*  BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND         */
/*  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE   */
/*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT  */
/*  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON    */
/*  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT   */
/*  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF  */
/*  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.         */
/******************************************************************************/

bitfield SCRType : bits(64) =
  {
    NS : 0,
    IRQ : 1,
    FIQ : 2,
    EA : 3,
    FW : 4,
    AW : 5,
    nET : 6,
    SCD : 7,
    SMD : 7,
    HCE : 8,
    SIF : 9,
    RW : 10,
    ST : 11,
    TWI : 12,
    TWE : 13
  }

bitfield SCTLRType : bits(64) =
  {
    M : 0,
    A : 1,
    C : 2,
    SA : 3,
    SA0 : 4,
    CP15BEN : 5,
    nAA : 6,
    ITD : 7,
    SED : 8,
    UMA : 9,
    I : 12,
    DZE : 14,
    UCT : 15,
    nTWI : 16,
    nTWE : 18,
    WXN : 19,
    TSCXT : 20,
    IESB : 21,
    SPAN : 23,
    E0E : 24,
    EE : 25,
    UCI : 26,
    DSSBS : 44,
    TMT0 : 50,
    TMT : 51,
    TME0 : 52,
    TME : 53,
    EPAN : 57,
    NMI : 61,
    SPINTMASK : 62,
    TIDCP : 63
  }

bitfield MAIRType : bits(64) =
  {
    Attr0 : 7..0,
    Attr1 : 15..8,
    Attr2 : 23..16,
    Attr3 : 31..24,
    Attr4 : 39..32,
    Attr5 : 47..40,
    Attr6 : 55..48,
    Attr7 : 63..56
  }

bitfield S1PIRType : bits(64) =
  {
    Perm0 : 3..0,
    Perm1 : 7..4,
    Perm2 : 11..8,
    Perm3 : 15..12,
    Perm4 : 19..16,
    Perm5 : 23..20,
    Perm6 : 27..24,
    Perm7 : 31..28,
    Perm8 : 35..32,
    Perm9 : 39..36,
    Perm10 : 43..40,
    Perm11 : 47..44,
    Perm12 : 51..48,
    Perm13 : 55..52,
    Perm14 : 59..56,
    Perm15 : 63..60
  }

bitfield S1PORType : bits(64) =
  {
    Perm0 : 3..0,
    Perm1 : 7..4,
    Perm2 : 11..8,
    Perm3 : 15..12,
    Perm4 : 19..16,
    Perm5 : 23..20,
    Perm6 : 27..24,
    Perm7 : 31..28,
    Perm8 : 35..32,
    Perm9 : 39..36,
    Perm10 : 43..40,
    Perm11 : 47..44,
    Perm12 : 51..48,
    Perm13 : 55..52,
    Perm14 : 59..56,
    Perm15 : 63..60
  }

bitfield S2PIRType : bits(64) =
  {
    Perm0 : 3..0,
    Perm1 : 7..4,
    Perm2 : 11..8,
    Perm3 : 15..12,
    Perm4 : 19..16,
    Perm5 : 23..20,
    Perm6 : 27..24,
    Perm7 : 31..28,
    Perm8 : 35..32,
    Perm9 : 39..36,
    Perm10 : 43..40,
    Perm11 : 47..44,
    Perm12 : 51..48,
    Perm13 : 55..52,
    Perm14 : 59..56,
    Perm15 : 63..60
  }

bitfield ESRType : bits(64) = {ISS : 24..0, IL : 25, EC : 31..26}

bitfield FPCRType : bits(64) =
  {
    FIZ : 0,
    AH : 1,
    NEP : 2,
    IOE : 8,
    DZE : 9,
    OFE : 10,
    UFE : 11,
    IXE : 12,
    EBF : 13,
    IDE : 15,
    length : 18..16,
    FZ16 : 19,
    Stride : 21..20,
    RMode : 23..22,
    FZ : 24,
    DN : 25,
    AHP : 26,
    IOC : 32,
    DZC : 33,
    OFC : 34
  }

bitfield BRBSRCType : bits(64) = {ADDRESS : 63..0}

bitfield BRBTGTType : bits(64) = {ADDRESS : 63..0}

bitfield BRBINFType : bits(64) =
  {
    CCU : 46,
    CC : 45..32,
    LASTFAILED : 17,
    T : 16,
    TYPE : 13..8,
    EL : 7..6,
    MPRED : 5,
    VALID : 1..0
  }

enum Signal = {Signal_Low, Signal_High}

enum SecurityState = {SS_NonSecure, SS_Root, SS_Realm, SS_Secure}

enum Shareability = {Shareability_NSH, Shareability_ISH, Shareability_OSH}

val __UNKNOWN_Shareability : unit -> Shareability

function __UNKNOWN_Shareability () = undefined


enum PASpace = {PAS_NonSecure, PAS_Secure, PAS_Root, PAS_Realm}

val __UNKNOWN_PASpace : unit -> PASpace

function __UNKNOWN_PASpace () = undefined

struct FullAddress = {paspace : PASpace, address : bits(56)}

val __UNKNOWN_FullAddress : unit -> FullAddress

function __UNKNOWN_FullAddress () = undefined

type PARTIDtype = bits(16)

val __UNKNOWN_PARTIDtype : unit -> bits(16)

function __UNKNOWN_PARTIDtype () = undefined

type PMGtype = bits(8)

val __UNKNOWN_PMGtype : unit -> bits(8)

function __UNKNOWN_PMGtype () = undefined

enum PARTIDspaceType = {
  PIdSpace_Secure,
  PIdSpace_Root,
  PIdSpace_Realm,
  PIdSpace_NonSecure
}

struct MPAMinfo = {
  mpam_sp : PARTIDspaceType,
  partid : PARTIDtype,
  pmg : PMGtype
}

enum AccessType = {
  AccessType_IFETCH,
  AccessType_GPR,
  AccessType_ASIMD,
  AccessType_SVE,
  AccessType_SME,
  AccessType_IC,
  AccessType_DC,
  AccessType_DCZero,
  AccessType_AT,
  AccessType_NV2,
  AccessType_SPE,
  AccessType_GCS,
  AccessType_GPTW,
  AccessType_TTW
}

enum MemOp = {MemOp_LOAD, MemOp_STORE, MemOp_PREFETCH}

enum VARange = {VARange_LOWER, VARange_UPPER}

val __UNKNOWN_VARange : unit -> VARange

function __UNKNOWN_VARange () = undefined

enum MemAtomicOp = {
  MemAtomicOp_GCSSS1,
  MemAtomicOp_ADD,
  MemAtomicOp_BIC,
  MemAtomicOp_EOR,
  MemAtomicOp_ORR,
  MemAtomicOp_SMAX,
  MemAtomicOp_SMIN,
  MemAtomicOp_UMAX,
  MemAtomicOp_UMIN,
  MemAtomicOp_SWP,
  MemAtomicOp_CAS
}

enum CacheOp = {CacheOp_Clean, CacheOp_Invalidate, CacheOp_CleanInvalidate}

enum CacheOpScope = {
  CacheOpScope_SetWay,
  CacheOpScope_PoU,
  CacheOpScope_PoC,
  CacheOpScope_PoE,
  CacheOpScope_PoP,
  CacheOpScope_PoDP,
  CacheOpScope_PoPA,
  CacheOpScope_ALLU,
  CacheOpScope_ALLUIS
}

enum CacheType = {
  CacheType_Data,
  CacheType_Tag,
  CacheType_Data_Tag,
  CacheType_Instruction
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

struct CacheRecord = {
  acctype : AccessType,
  cacheop : CacheOp,
  opscope : CacheOpScope,
  cachetype : CacheType,
  regval : bits(64),
  paddress : FullAddress,
  vaddress : bits(64),
  setnum : int,
  waynum : int,
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


struct AccessDescriptor = {
  acctype : AccessType,
  el : bits(2),
  ss : SecurityState,
  acqsc : bool,
  acqpc : bool,
  relsc : bool,
  limitedordered : bool,
  exclusive : bool,
  atomicop : bool,
  modop : MemAtomicOp,
  nontemporal : bool,
  read : bool,
  write : bool,
  cacheop : CacheOp,
  opscope : CacheOpScope,
  cachetype : CacheType,
  pan : bool,
  transactional : bool,
  nonfault : bool,
  firstfault : bool,
  first : bool,
  contiguous : bool,
  streamingsve : bool,
  ls64 : bool,
  mops : bool,
  rcw : bool,
  rcws : bool,
  toplevel : bool,
  varange : VARange,
  a32lsmd : bool,
  tagchecked : bool,
  tagaccess : bool,
  mpam : MPAMinfo
}

val __UNKNOWN_AccessDescriptor : unit -> AccessDescriptor

function __UNKNOWN_AccessDescriptor () = undefined

enum MemType = {MemType_Normal, MemType_Device}

enum DeviceType = {
  DeviceType_GRE,
  DeviceType_nGRE,
  DeviceType_nGnRE,
  DeviceType_nGnRnE
}

struct MemAttrHints = {attrs : bits(2), hints : bits(2), transient : bool}

let LOG2_TAG_GRANULE : int(4) = 4

let MemAttr_NC : bits(2) = 0b00

let MemAttr_WT : bits(2) = 0b10

let MemAttr_WB : bits(2) = 0b11

let MemHint_No : bits(2) = 0b00

let MemHint_WA : bits(2) = 0b01

let MemHint_RA : bits(2) = 0b10

let MemHint_RWA : bits(2) = 0b11

enum MemTagType = {
  MemTag_Untagged,
  MemTag_AllocationTagged,
  MemTag_CanonicallyTagged
}

struct MemoryAttributes = {
  memtype : MemType,
  device : DeviceType,
  inner : MemAttrHints,
  outer : MemAttrHints,
  shareability : Shareability,
  tags : MemTagType,
  notagaccess : bool,
  xs : bits(1)
}

val __UNKNOWN_MemoryAttributes : unit -> MemoryAttributes

function __UNKNOWN_MemoryAttributes () = undefined


enum Exception = {
  Exception_Uncategorized,
  Exception_WFxTrap,
  Exception_CP15RTTrap,
  Exception_CP15RRTTrap,
  Exception_CP14RTTrap,
  Exception_CP14DTTrap,
  Exception_CP14RRTTrap,
  Exception_AdvSIMDFPAccessTrap,
  Exception_FPIDTrap,
  Exception_LDST64BTrap,
  Exception_PACTrap,
  Exception_IllegalState,
  Exception_SupervisorCall,
  Exception_HypervisorCall,
  Exception_MonitorCall,
  Exception_SystemRegisterTrap,
  Exception_ERetTrap,
  Exception_InstructionAbort,
  Exception_PCAlignment,
  Exception_DataAbort,
  Exception_NV2DataAbort,
  Exception_PACFail,
  Exception_SPAlignment,
  Exception_FPTrappedException,
  Exception_SError,
  Exception_Breakpoint,
  Exception_SoftwareStep,
  Exception_Watchpoint,
  Exception_NV2Watchpoint,
  Exception_SoftwareBreakpoint,
  Exception_VectorCatch,
  Exception_IRQ,
  Exception_SVEAccessTrap,
  Exception_SMEAccessTrap,
  Exception_TSTARTAccessTrap,
  Exception_GPC,
  Exception_BranchTarget,
  Exception_MemCpyMemSet,
  Exception_GCSFail,
  Exception_SystemRegister128Trap,
  Exception_FIQ
}

struct ExceptionRecord = {
  exceptype : Exception,
  syndrome : bits(25),
  syndrome2 : bits(24),
  paddress : FullAddress,
  vaddress : bits(64),
  ipavalid : bool,
  pavalid : bool,
  NS : bits(1),
  ipaddress : bits(56),
  trappedsyscallinst : bool
}

enum TranslationStage = {TranslationStage_1, TranslationStage_12}

enum ATAccess = {
  ATAccess_Read,
  ATAccess_Write,
  ATAccess_ReadPAN,
  ATAccess_WritePAN
}

enum Regime = {Regime_EL3, Regime_EL30, Regime_EL2, Regime_EL20, Regime_EL10}

enum TGx = {TGx_4KB, TGx_16KB, TGx_64KB}

enum DescriptorType = {
  DescriptorType_Table,
  DescriptorType_Leaf,
  DescriptorType_Invalid
}

let Domain_NoAccess : bits(2) = 0b00

let Domain_Client : bits(2) = 0b01

enum SDFType = {
  SDFType_Table,
  SDFType_Invalid,
  SDFType_Supersection,
  SDFType_Section,
  SDFType_LargePage,
  SDFType_SmallPage
}

val __UNKNOWN_SDFType : unit -> SDFType

function __UNKNOWN_SDFType () = undefined

struct Permissions = {
  ap_table : bits(2),
  xn_table : bits(1),
  pxn_table : bits(1),
  uxn_table : bits(1),
  ap : bits(3),
  xn : bits(1),
  uxn : bits(1),
  pxn : bits(1),
  ppi : bits(4),
  upi : bits(4),
  ndirty : bits(1),
  s2pi : bits(4),
  s2dirty : bits(1),
  po_index : bits(4),
  s2po_index : bits(4),
  s2ap : bits(2),
  s2tag_na : bits(1),
  s2xnx : bits(1),
  s2xn : bits(1)
}

struct TTWState = {
  istable : bool,
  level : int,
  baseaddress : FullAddress,
  contiguous : bits(1),
  s1assured : bool,
  s2assuredonly : bits(1),
  disch : bits(1),
  nG : bits(1),
  guardedpage : bits(1),
  sdftype : SDFType,
  domain : bits(4),
  memattrs : MemoryAttributes,
  permissions : Permissions
}

val __UNKNOWN_TTWState : unit -> TTWState

function __UNKNOWN_TTWState () = undefined

struct S1TTWParams = {
  ha : bits(1),
  hd : bits(1),
  tbi : bits(1),
  tbid : bits(1),
  nfd : bits(1),
  e0pd : bits(1),
  d128 : bits(1),
  aie : bits(1),
  mair2 : MAIRType,
  ds : bits(1),
  ps : bits(3),
  txsz : bits(6),
  epan : bits(1),
  dct : bits(1),
  nv1 : bits(1),
  cmow : bits(1),
  pnch : bits(1),
  disch : bits(1),
  haft : bits(1),
  mtx : bits(1),
  skl : bits(2),
  pie : bits(1),
  pir : S1PIRType,
  pire0 : S1PIRType,
  emec : bits(1),
  amec : bits(1),
  t0sz : bits(3),
  t1sz : bits(3),
  uwxn : bits(1),
  tgx : TGx,
  irgn : bits(2),
  orgn : bits(2),
  sh : bits(2),
  hpd : bits(1),
  ee : bits(1),
  wxn : bits(1),
  ntlsmd : bits(1),
  dc : bits(1),
  sif : bits(1),
  mair : MAIRType
}

struct S2TTWParams = {
  ha : bits(1),
  hd : bits(1),
  sl2 : bits(1),
  ds : bits(1),
  d128 : bits(1),
  sw : bits(1),
  nsw : bits(1),
  sa : bits(1),
  nsa : bits(1),
  ps : bits(3),
  txsz : bits(6),
  fwb : bits(1),
  cmow : bits(1),
  skl : bits(2),
  s2pie : bits(1),
  s2pir : S2PIRType,
  tl0 : bits(1),
  tl1 : bits(1),
  assuredonly : bits(1),
  haft : bits(1),
  emec : bits(1),
  s : bits(1),
  t0sz : bits(4),
  tgx : TGx,
  sl0 : bits(2),
  irgn : bits(2),
  orgn : bits(2),
  sh : bits(2),
  ee : bits(1),
  ptw : bits(1),
  vm : bits(1)
}

struct TLBContext = {
  ss : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  nG : bits(1),
  ipaspace : PASpace,
  includes_s1_name : bool,
  includes_s2_name : bool,
  includes_gpt_name : bool,
  ia : bits(64),
  tg : TGx,
  cnp : bits(1),
  level : int,
  isd128 : bool,
  xs : bits(1)
}

struct TLBRecord = {
  context : TLBContext,
  walkstate : TTWState,
  blocksize : int,
  contigsize : int,
  s1descriptor : bits(128),
  s2descriptor : bits(128)
}

enum GPCF = {GPCF_None, GPCF_AddressSize, GPCF_Walk, GPCF_EABT, GPCF_Fail}

struct GPCFRecord = {gpf : GPCF, level : int}

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
  Fault_TagCheck,
  Fault_Debug,
  Fault_TLBConflict,
  Fault_BranchTarget,
  Fault_HWUpdateAccessFlag,
  Fault_Lockdown,
  Fault_Exclusive,
  Fault_ICacheMaint
}

enum ErrorState = {
  ErrorState_UC,
  ErrorState_UEU,
  ErrorState_UEO,
  ErrorState_UER,
  ErrorState_CE,
  ErrorState_Uncategorized,
  ErrorState_IMPDEF
}

struct FaultRecord = {
  statuscode : Fault,
  access : AccessDescriptor,
  ipaddress : FullAddress,
  gpcf : GPCFRecord,
  paddress : FullAddress,
  gpcfs2walk : bool,
  s2fs1walk : bool,
  write : bool,
  s1tagnotdata : bool,
  tagaccess : bool,
  level : int,
  extflag : bits(1),
  secondstage : bool,
  assuredonly : bool,
  toplevel : bool,
  overlay : bool,
  dirtybit : bool,
  domain : bits(4),
  merrorstate : ErrorState,
  debugmoe : bits(4)
}

val __UNKNOWN_FaultRecord : unit -> FaultRecord

function __UNKNOWN_FaultRecord () = undefined


struct AddressDescriptor = {
  fault : FaultRecord,
  memattrs : MemoryAttributes,
  paddress : FullAddress,
  tlbcontext : TLBContext,
  s1assured : bool,
  s2fs1mro : bool,
  mecid : bits(16),
  vaddress : bits(64)
}

val __UNKNOWN_AddressDescriptor : unit -> AddressDescriptor

function __UNKNOWN_AddressDescriptor () = undefined

struct TranslationInfo = {
  regime : Regime,
  vmid : option(bits(16)),
  asid : option(bits(16)),
  va : bits(64),
  s1level : option(int),
  s2info : option((bits(64), int)),
  s1params : option(S1TTWParams),
  s2params : option(S2TTWParams),
  memattrs : MemoryAttributes
}

let VMID_NONE : bits(16) = Zeros(16)

enum TLBILevel = {TLBILevel_Any, TLBILevel_Last}

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
  TLBIPOp_IPAS2,
  TLBIOp_VAA,
  TLBIOp_VA,
  TLBIPOp_VAA,
  TLBIPOp_VA,
  TLBIOp_VMALL,
  TLBIOp_VMALLS12,
  TLBIOp_RIPAS2,
  TLBIPOp_RIPAS2,
  TLBIOp_RVAA,
  TLBIOp_RVA,
  TLBIPOp_RVAA,
  TLBIPOp_RVA,
  TLBIOp_RPA,
  TLBIOp_PAALL
}

enum TLBIMemAttr = {TLBI_AllAttr, TLBI_ExcludeXS}

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
  d64 : bool,
  d128 : bool,
  ttl : bits(4),
  tg : bits(2)
}

enum MBReqDomain = {
  MBReqDomain_Nonshareable,
  MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable,
  MBReqDomain_FullSystem
}

enum MBReqTypes = {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}

