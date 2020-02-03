/**************************************************************************/
/* BSD 3-clause Clear License                                             */
/*                                                                        */
/* Copyright (c) 2019                                                     */
/*   Arm Limited (or its affiliates),                                     */
/*   Alasdair Armstrong,                                                  */
/*   Alastair Reid,                                                       */
/*   Thomas Bauereiss,                                                    */
/*   Peter Sewell,                                                        */
/*   Kathryn Gray,                                                        */
/*   Anthony Fox                                                          */
/*                                                                        */
/* All rights reserved.                                                   */
/*                                                                        */
/* Redistribution and use in source and binary forms, with or without     */
/* modification, are permitted (subject to the limitations in the         */
/* disclaimer below) provided that the following conditions are met:      */
/*                                                                        */
/* 	* Redistributions of source code must retain the above            */
/*        copyright notice, this list of conditions and the following     */
/* 	  disclaimer.                                                     */
/*      * Redistributions in binary form must reproduce the above         */
/*        copyright notice, this list of conditions and the following     */
/*        disclaimer in the documentation and/or other materials          */
/* 	  provided with the distribution.                                 */
/* 	* Neither the name of ARM Limited nor the names of its            */
/*        contributors may be used to endorse or promote products         */
/*        derived from this software without specific prior written       */
/*        permission.                                                     */
/*                                                                        */
/* NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE        */
/* GRANTED BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT    */
/* HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED            */
/* WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF   */
/* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE               */
/* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE  */
/* LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR    */
/* CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF   */
/* SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        */
/* BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,  */
/* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE   */
/* OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN */
/* IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                          */
/**************************************************************************/

enum boolean = {FALSE, TRUE}

enum signal = {LOW, HIGH}

enum __RetCode = {
  __RC_OK,
  __RC_UNDEFINED,
  __RC_UNPREDICTABLE,
  __RC_SEE,
  __RC_IMPLEMENTATION_DEFINED,
  __RC_EXCEPTION_TAKEN,
  __RC_ASSERT_FAILED,
  __RC_UNMATCHED_CASE
}

type TUBE_Type = bits(32)

type ScheduleIRQ_Type = bits(32)

type ClearIRQ_Type = bits(32)

type ScheduleFIQ_Type = bits(32)

type ClearFIQ_Type = bits(32)

type TargetCPU_Type = bits(32)

type AbortRgn64Lo1_Type = bits(32)

type AbortRgn64Lo1_Hi_Type = bits(32)

type AbortRgn64Hi1_Type = bits(32)

type AbortRgn64Hi1_Hi_Type = bits(32)

type AbortRgn64Lo2_Type = bits(32)

type AbortRgn64Lo2_Hi_Type = bits(32)

type AbortRgn64Hi2_Type = bits(32)

type AbortRgn64Hi2_Hi_Type = bits(32)

type AXIAbortCtl_Type = bits(32)

type GTE_API_Type = bits(32)

type GTE_API_PARAM_Type = bits(32)

type GTE_API_STATUS_Type = bits(32)

type PPURBAR_Type = bits(32)

type PPURSER_Type = bits(32)

type PPURACR_Type = bits(32)

type GTE_API_STATUS_64_Type = bits(32)

type GTE_API_STATUS_64_HI_Type = bits(32)

type GTE_API_PARAM_64_Type = bits(32)

type GTE_API_PARAM_64_HI_Type = bits(32)

type SCRType = bits(32)

type SCTLRType = bits(64)

type MAIRType = bits(64)

type ESRType = bits(32)

type FPCRType = bits(32)

type FPSRType = bits(32)

type FPSCRType = bits(32)

type CPSRType = bits(32)

type APSRType = bits(32)

type ITSTATEType = bits(8)

type CPACRType = bits(32)

type CNTKCTLType = bits(32)

enum GTEParamType = {GTEParam_WORD, GTEParam_LIST, GTEParam_EOACCESS}

type GTE_PPU_SizeEn_Type = bits(32)

type GTEExtObsAccess_Type = bits(16)

type GTEASAccess_Type = bits(32)

type GTEASRecordedAccess_Type = bits(32)

enum AccType = {
  AccType_NORMAL,
  AccType_VEC,
  AccType_STREAM,
  AccType_VECSTREAM,
  AccType_ATOMIC,
  AccType_ATOMICRW,
  AccType_ORDERED,
  AccType_ORDEREDRW,
  AccType_ORDEREDATOMIC,
  AccType_ORDEREDATOMICRW,
  AccType_LIMITEDORDERED,
  AccType_UNPRIV,
  AccType_IFETCH,
  AccType_PTW,
  AccType_NV2REGISTER,
  AccType_DC,
  AccType_DC_UNPRIV,
  AccType_IC,
  AccType_DCZVA,
  AccType_AT,
  AccType_TAG
}

enum MemType = {MemType_Normal, MemType_Device}

enum DeviceType = {
  DeviceType_GRE,
  DeviceType_nGRE,
  DeviceType_nGnRE,
  DeviceType_nGnRnE
}

struct MemAttrHints = {attrs : bits(2), hints : bits(2), transient : bool}

struct MemoryAttributes = {
  typ : MemType,
  device : DeviceType,
  inner : MemAttrHints,
  outer : MemAttrHints,
  tagged : bool,
  shareable : bool,
  outershareable : bool
}

struct FullAddress = {address : bits(52), NS : bits(1)}

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

struct FaultRecord = {
  typ : Fault,
  acctype : AccType,
  ipaddress : FullAddress,
  s2fs1walk : bool,
  write : bool,
  level : int,
  extflag : bits(1),
  secondstage : bool,
  domain : bits(4),
  errortype : bits(2),
  debugmoe : bits(4)
}

type PARTIDtype = bits(16)

type PMGtype = bits(8)

struct MPAMinfo = {mpam_ns : bits(1), partid : bits(16), pmg : bits(8)}

struct AddressDescriptor = {
  fault : FaultRecord,
  memattrs : MemoryAttributes,
  paddress : FullAddress,
  vaddress : bits(64)
}

struct AccessDescriptor = {
  acctype : AccType,
  mpam : MPAMinfo,
  page_table_walk : bool,
  secondstage : bool,
  s2fs1walk : bool,
  level : int
}

struct Permissions = {ap : bits(3), xn : bits(1), xxn : bits(1), pxn : bits(1)}

struct DescriptorUpdate = {AF : bool, AP : bool, descaddr : AddressDescriptor}

struct TLBRecord = {
  perms : Permissions,
  nG : bits(1),
  domain : bits(4),
  GP : bits(1),
  contiguous : bool,
  level : int,
  blocksize : int,
  descupdate : DescriptorUpdate,
  CnP : bits(1),
  addrdesc : AddressDescriptor
}

enum MBReqDomain = {
  MBReqDomain_Nonshareable,
  MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable,
  MBReqDomain_FullSystem
}

enum MBReqTypes = {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}

enum PrefetchHint = {Prefetch_READ, Prefetch_WRITE, Prefetch_EXEC}

struct ProcState = {
  N : bits(1),
  Z : bits(1),
  C : bits(1),
  V : bits(1),
  D : bits(1),
  A : bits(1),
  I : bits(1),
  F : bits(1),
  PAN : bits(1),
  UAO : bits(1),
  DIT : bits(1),
  TCO : bits(1),
  BTYPE : bits(2),
  SS : bits(1),
  IL : bits(1),
  EL : bits(2),
  nRW : bits(1),
  SP : bits(1),
  Q : bits(1),
  GE : bits(4),
  SSBS : bits(1),
  IT : bits(8),
  J : bits(1),
  T : bits(1),
  E : bits(1),
  M : bits(5)
}

enum PrivilegeLevel = {PL3, PL2, PL1, PL0}

enum InstrSet = {InstrSet_A64, InstrSet_A32, InstrSet_T32}

enum ArchVersion = {ARMv8p0, ARMv8p1, ARMv8p2, ARMv8p3, ARMv8p4, ARMv8p5}

enum Unpredictable = {
  Unpredictable_WBOVERLAPLD,
  Unpredictable_WBOVERLAPST,
  Unpredictable_LDPOVERLAP,
  Unpredictable_BASEOVERLAP,
  Unpredictable_DATAOVERLAP,
  Unpredictable_DEVPAGE2,
  Unpredictable_INSTRDEVICE,
  Unpredictable_RESCPACR,
  Unpredictable_RESMAIR,
  Unpredictable_RESTEXCB,
  Unpredictable_RESPRRR,
  Unpredictable_RESDACR,
  Unpredictable_RESVTCRS,
  Unpredictable_RESTnSZ,
  Unpredictable_OORTnSZ,
  Unpredictable_LARGEIPA,
  Unpredictable_ESRCONDPASS,
  Unpredictable_ILZEROIT,
  Unpredictable_ILZEROT,
  Unpredictable_BPVECTORCATCHPRI,
  Unpredictable_VCMATCHHALF,
  Unpredictable_VCMATCHDAPA,
  Unpredictable_WPMASKANDBAS,
  Unpredictable_WPBASCONTIGUOUS,
  Unpredictable_RESWPMASK,
  Unpredictable_WPMASKEDBITS,
  Unpredictable_RESBPWPCTRL,
  Unpredictable_BPNOTIMPL,
  Unpredictable_RESBPTYPE,
  Unpredictable_BPNOTCTXCMP,
  Unpredictable_BPMATCHHALF,
  Unpredictable_BPMISMATCHHALF,
  Unpredictable_RESTARTALIGNPC,
  Unpredictable_RESTARTZEROUPPERPC,
  Unpredictable_ZEROUPPER,
  Unpredictable_ERETZEROUPPERPC,
  Unpredictable_A32FORCEALIGNPC,
  Unpredictable_SMD,
  Unpredictable_AFUPDATE,
  Unpredictable_IESBinDebug,
  Unpredictable_ZEROPMSEVFR,
  Unpredictable_NOOPTYPES,
  Unpredictable_ZEROMINLATENCY,
  Unpredictable_ZEROBTYPE,
  Unpredictable_CLEARERRITEZERO
}

enum Constraint = {
  Constraint_NONE,
  Constraint_UNKNOWN,
  Constraint_UNDEF,
  Constraint_UNDEFEL0,
  Constraint_NOP,
  Constraint_TRUE,
  Constraint_FALSE,
  Constraint_DISABLED,
  Constraint_UNCOND,
  Constraint_COND,
  Constraint_ADDITIONAL_DECODE,
  Constraint_WBSUPPRESS,
  Constraint_FAULT,
  Constraint_FORCE,
  Constraint_FORCENOSLCHECK
}

enum FPExc = {
  FPExc_InvalidOp,
  FPExc_DivideByZero,
  FPExc_Overflow,
  FPExc_Underflow,
  FPExc_Inexact,
  FPExc_InputDenorm
}

enum FPRounding = {
  FPRounding_TIEEVEN,
  FPRounding_POSINF,
  FPRounding_NEGINF,
  FPRounding_ZERO,
  FPRounding_TIEAWAY,
  FPRounding_ODD
}

enum FPType = {
  FPType_Nonzero,
  FPType_Zero,
  FPType_Infinity,
  FPType_QNaN,
  FPType_SNaN
}

enum BranchType = {
  BranchType_DIRCALL,
  BranchType_INDCALL,
  BranchType_ERET,
  BranchType_DBGEXIT,
  BranchType_RET,
  BranchType_DIR,
  BranchType_INDIR,
  BranchType_EXCEPTION,
  BranchType_RESET,
  BranchType_UNKNOWN
}

struct TLBContext = {
  twostage : bool,
  secondstage : bool,
  asid : bits(16),
  vmid : bits(16),
  el : bits(2),
  secure : bool,
  t_sz : bits(6),
  granule_size : int
}

struct TLBLine = {
  address : bits(64),
  context : TLBContext,
  data : TLBRecord,
  valid_name : bool
}

enum Exception = {
  Exception_Uncategorized,
  Exception_WFxTrap,
  Exception_CP15RTTrap,
  Exception_CP15RRTTrap,
  Exception_CP14RTTrap,
  Exception_CP14DTTrap,
  Exception_AdvSIMDFPAccessTrap,
  Exception_FPIDTrap,
  Exception_PACTrap,
  Exception_CP14RRTTrap,
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
  Exception_SPAlignment,
  Exception_FPTrappedException,
  Exception_SError,
  Exception_Breakpoint,
  Exception_SoftwareStep,
  Exception_Watchpoint,
  Exception_SoftwareBreakpoint,
  Exception_VectorCatch,
  Exception_IRQ,
  Exception_BranchTarget,
  Exception_FIQ
}

struct ExceptionRecord = {
  typ : Exception,
  syndrome : bits(25),
  vaddress : bits(64),
  ipavalid : bool,
  NS : bits(1),
  ipaddress : bits(52)
}

enum SystemAccessType = {
  SystemAccessType_RT,
  SystemAccessType_RRT,
  SystemAccessType_DT
}

enum SysRegAccess = {
  SysRegAccess_OK,
  SysRegAccess_UNDEFINED,
  SysRegAccess_TrapToEL1,
  SysRegAccess_TrapToEL2,
  SysRegAccess_TrapToEL3
}

enum OpType = {
  OpType_Load,
  OpType_Store,
  OpType_LoadAtomic,
  OpType_Branch,
  OpType_Other
}

enum TimeStamp = {TimeStamp_None, TimeStamp_Virtual, TimeStamp_Physical}

enum CountOp = {CountOp_CLZ, CountOp_CLS, CountOp_CNT}

enum ExtendType = {
  ExtendType_SXTB,
  ExtendType_SXTH,
  ExtendType_SXTW,
  ExtendType_SXTX,
  ExtendType_UXTB,
  ExtendType_UXTH,
  ExtendType_UXTW,
  ExtendType_UXTX
}

enum FPMaxMinOp = {
  FPMaxMinOp_MAX,
  FPMaxMinOp_MIN,
  FPMaxMinOp_MAXNUM,
  FPMaxMinOp_MINNUM
}

enum FPUnaryOp = {FPUnaryOp_ABS, FPUnaryOp_MOV, FPUnaryOp_NEG, FPUnaryOp_SQRT}

enum FPConvOp = {
  FPConvOp_CVT_FtoI,
  FPConvOp_CVT_ItoF,
  FPConvOp_MOV_FtoI,
  FPConvOp_MOV_ItoF,
  FPConvOp_CVT_FtoI_JS
}

enum MoveWideOp = {MoveWideOp_N, MoveWideOp_Z, MoveWideOp_K}

enum ShiftType = {ShiftType_LSL, ShiftType_LSR, ShiftType_ASR, ShiftType_ROR}

enum LogicalOp = {LogicalOp_AND, LogicalOp_EOR, LogicalOp_ORR}

enum MemOp = {MemOp_LOAD, MemOp_STORE, MemOp_PREFETCH}

enum MemAtomicOp = {
  MemAtomicOp_ADD,
  MemAtomicOp_BIC,
  MemAtomicOp_EOR,
  MemAtomicOp_ORR,
  MemAtomicOp_SMAX,
  MemAtomicOp_SMIN,
  MemAtomicOp_UMAX,
  MemAtomicOp_UMIN,
  MemAtomicOp_SWP
}

enum MemBarrierOp = {
  MemBarrierOp_DSB,
  MemBarrierOp_DMB,
  MemBarrierOp_ISB,
  MemBarrierOp_SSBB,
  MemBarrierOp_PSSBB,
  MemBarrierOp_SB
}

enum SystemHintOp = {
  SystemHintOp_NOP,
  SystemHintOp_YIELD,
  SystemHintOp_WFE,
  SystemHintOp_WFI,
  SystemHintOp_SEV,
  SystemHintOp_SEVL,
  SystemHintOp_ESB,
  SystemHintOp_PSB,
  SystemHintOp_TSB,
  SystemHintOp_BTI,
  SystemHintOp_CSDB
}

enum PSTATEField = {
  PSTATEField_DAIFSet,
  PSTATEField_DAIFClr,
  PSTATEField_PAN,
  PSTATEField_UAO,
  PSTATEField_DIT,
  PSTATEField_SP
}

enum SystemOp = {Sys_AT, Sys_DC, Sys_IC, Sys_TLBI, Sys_SYS}

enum VBitOp = {VBitOp_VBIF, VBitOp_VBIT, VBitOp_VBSL, VBitOp_VEOR}

enum CompareOp = {
  CompareOp_GT,
  CompareOp_GE,
  CompareOp_EQ,
  CompareOp_LE,
  CompareOp_LT
}

enum ImmediateOp = {
  ImmediateOp_MOVI,
  ImmediateOp_MVNI,
  ImmediateOp_ORR,
  ImmediateOp_BIC
}

enum ReduceOp = {
  ReduceOp_FMINNUM,
  ReduceOp_FMAXNUM,
  ReduceOp_FMIN,
  ReduceOp_FMAX,
  ReduceOp_FADD,
  ReduceOp_ADD
}

enum SRType = {SRType_LSL, SRType_LSR, SRType_ASR, SRType_ROR, SRType_RRX}

struct AArch32_SErrorSyndrome = {AET : bits(2), ExT : bits(1)}

enum CrossTriggerOut = {
  CrossTriggerOut_DebugRequest,
  CrossTriggerOut_RestartRequest,
  CrossTriggerOut_IRQ,
  CrossTriggerOut_RSVD3,
  CrossTriggerOut_TraceExtIn0,
  CrossTriggerOut_TraceExtIn1,
  CrossTriggerOut_TraceExtIn2,
  CrossTriggerOut_TraceExtIn3
}

enum CrossTriggerIn = {
  CrossTriggerIn_CrossHalt,
  CrossTriggerIn_PMUOverflow,
  CrossTriggerIn_RSVD2,
  CrossTriggerIn_RSVD3,
  CrossTriggerIn_TraceExtOut0,
  CrossTriggerIn_TraceExtOut1,
  CrossTriggerIn_TraceExtOut2,
  CrossTriggerIn_TraceExtOut3
}

enum InterruptID = {
  InterruptID_PMUIRQ,
  InterruptID_COMMIRQ,
  InterruptID_CTIIRQ,
  InterruptID_COMMRX,
  InterruptID_COMMTX
}

struct PCSample = {
  valid_name : bool,
  pc : bits(64),
  el : bits(2),
  rw : bits(1),
  ns : bits(1),
  has_el2 : bool,
  contextidr : bits(32),
  contextidr_el2 : bits(32),
  el0h : bool,
  vmid : bits(16)
}

enum VCGEtype = {VCGEtype_signed, VCGEtype_unsigned, VCGEtype_fp}

enum VCGTtype = {VCGTtype_signed, VCGTtype_unsigned, VCGTtype_fp}

enum VFPNegMul = {VFPNegMul_VNMLA, VFPNegMul_VNMLS, VFPNegMul_VNMUL}

struct InterruptReq = {
  take_SE : bool,
  take_vSE : bool,
  take_IRQ : bool,
  take_vIRQ : bool,
  take_FIQ : bool,
  take_vFIQ : bool,
  iesb_req : bool
}

enum AsyncErrorType = {
  AsyncErrorType_UC,
  AsyncErrorType_UEU,
  AsyncErrorType_UEO,
  AsyncErrorType_UER,
  AsyncErrorType_CE
}
