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

val Replicate : forall ('M : Int) ('N : Int), ('M >= 1 & mod('N, 'M) == 0).
  (implicit('N), bits('M)) -> bits('N)

function Replicate (N, x) = replicate_bits(x, N / 'M)

val Zeros = {ocaml: "zeros", lem: "zeros", smt: "zeros", interpreter: "zeros", c: "zeros"}: forall ('N : Int).
  implicit('N) -> bits('N)

val TakePendingInterrupts : InterruptReq -> bool effect {undef, escape, rreg, wreg}

val TakeSError : bool -> unit effect {escape, rreg, undef, wreg}

val AArch64_TranslationTableWalk : forall ('size : Int).
  (bits(52), bits(1), bits(64), AccType, bool, bool, bool, int('size)) -> (TLBRecord, option(TranslationInfo)) effect {escape, undef, rmem, rreg, wreg, wmem}

val IsZero_slice : forall ('n : Int), 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

val IsOnes_slice : forall ('n : Int), 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

val ZeroExtend_slice_append : forall 'n 'm 'o,
  ('n >= 0 & 'o >= 0).
  (implicit('o), bits('n), int, int, bits('m)) -> bits('o) effect {escape}

val AArch64_CheckAndUpdateDescriptor : (DescriptorUpdate, FaultRecord, bool, bits(64), AccType, bool, bool, bool) -> FaultRecord effect {undef, escape, rmem, rreg, wmem, wreg}

val AArch32_TranslationTableWalk : forall ('size : Int).
  (bits(40), bits(32), AccType, bool, bool, bool, int('size)) -> TLBRecord effect {escape, rmem, rreg, undef, wmem, wreg}

val AArch64_Abort : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

register __highest_el_aarch32 : bool

register __defaultRAM : bits(56)

register __currentInstrLength : int

register __currentInstr : bits(32)

register configuration __crypto_aes_implemented : int = 2

register configuration __block_bbm_implemented : int = 2

val __UNKNOWN_integer : unit -> int

function __UNKNOWN_integer () = {
    0
}

register __PC_changed : bool

register __LSISyndrome : bits(11)

val __IMPDEF_MemType : string -> MemType effect {escape}

function __IMPDEF_MemType x = {
    throw(Error_Implementation_Defined(""))
}

val __IMPDEF_DeviceType : string -> DeviceType effect {escape}

function __IMPDEF_DeviceType x = {
    throw(Error_Implementation_Defined(""))
}

register configuration __trickbox_mask_v8 : bits(52) = __GetSlice_int(52, 4503599627304960, 0)

register configuration __trickbox_base_v8 : bits(52) = __GetSlice_int(52, 318767104, 0)

register configuration __CNTControlMask : bits(52) = __GetSlice_int(52, 4503599627366400, 0)

register __CNTControlBase : bits(52)

register _TargetCPU : bits(32)

register _TLB : vector(1024, dec, TLBLine)

register _ScheduleIRQ : bits(32)

register _ScheduleFIQ : bits(32)

/* register _R : vector(31, dec, bits(64)) */

register R0 : bits(64)
register R1 : bits(64)
register R2 : bits(64)
register R3 : bits(64)
register R4 : bits(64)
register R5 : bits(64)
register R6 : bits(64)
register R7 : bits(64)
register R8 : bits(64)
register R9 : bits(64)
register R10 : bits(64)
register R11 : bits(64)
register R12 : bits(64)
register R13 : bits(64)
register R14 : bits(64)
register R15 : bits(64)
register R16 : bits(64)
register R17 : bits(64)
register R18 : bits(64)
register R19 : bits(64)
register R20 : bits(64)
register R21 : bits(64)
register R22 : bits(64)
register R23 : bits(64)
register R24 : bits(64)
register R25 : bits(64)
register R26 : bits(64)
register R27 : bits(64)
register R28 : bits(64)
register R29 : bits(64)
register R30 : bits(64)

let GPRs : vector(31, dec, register(bits(64))) = [
    ref R30,
    ref R29,
    ref R28,
    ref R27,
    ref R26,
    ref R25,
    ref R24,
    ref R23,
    ref R22,
    ref R21,
    ref R20,
    ref R19,
    ref R18,
    ref R17,
    ref R16,
    ref R15,
    ref R14,
    ref R13,
    ref R12,
    ref R11,
    ref R10,
    ref R9,
    ref R8,
    ref R7,
    ref R6,
    ref R5,
    ref R4,
    ref R3,
    ref R2,
    ref R1,
    ref R0
]

register __isla_vector_gpr: bool = false

val read_gpr = monadic "read_register_from_vector" : forall 'n, 0 <= 'n <= 30. (int('n), vector(31, dec, register(bits(64)))) -> bits(64)

val get_R : forall 'n, 0 <= 'n <= 30. int('n) -> bits(64) effect {rreg}

function get_R(n) = {
    if __isla_vector_gpr then read_gpr(n, GPRs) else {
        match n {
            0 => R0,
            1 => R1,
            2 => R2,
            3 => R3,
            4 => R4,
            5 => R5,
            6 => R6,
            7 => R7,
            8 => R8,
            9 => R9,
            10 => R10,
            11 => R11,
            12 => R12,
            13 => R13,
            14 => R14,
            15 => R15,
            16 => R16,
            17 => R17,
            18 => R18,
            19 => R19,
            20 => R20,
            21 => R21,
            22 => R22,
            23 => R23,
            24 => R24,
            25 => R25,
            26 => R26,
            27 => R27,
            28 => R28,
            29 => R29,
            _ => R30
        }
    }
}

val write_gpr = monadic "write_register_from_vector" : forall 'n, 0 <= 'n <= 30. (int('n), bits(64), vector(31, dec, register(bits(64)))) -> unit

val set_R : forall 'n, 0 <= 'n <= 30. (int('n), bits(64)) -> unit effect {wreg}

function set_R(n, v) = {
    if __isla_vector_gpr then write_gpr(n, v, GPRs) else {
        match n {
            0 => R0 = v,
            1 => R1 = v,
            2 => R2 = v,
            3 => R3 = v,
            4 => R4 = v,
            5 => R5 = v,
            6 => R6 = v,
            7 => R7 = v,
            8 => R8 = v,
            9 => R9 = v,
            10 => R10 = v,
            11 => R11 = v,
            12 => R12 = v,
            13 => R13 = v,
            14 => R14 = v,
            15 => R15 = v,
            16 => R16 = v,
            17 => R17 = v,
            18 => R18 = v,
            19 => R19 = v,
            20 => R20 = v,
            21 => R21 = v,
            22 => R22 = v,
            23 => R23 = v,
            24 => R24 = v,
            25 => R25 = v,
            26 => R26 = v,
            27 => R27 = v,
            28 => R28 = v,
            29 => R29 = v,
            _ => R30 = v
        }
    }
}

overload _R = {get_R, set_R}

val register_ref : forall 'n, 0 <= 'n <= 30. int('n) -> register(bits(64))

function register_ref(n) = {
    match n {
        0 => ref R0,
        1 => ref R1,
        2 => ref R2,
        3 => ref R3,
        4 => ref R4,
        5 => ref R5,
        6 => ref R6,
        7 => ref R7,
        8 => ref R8,
        9 => ref R9,
        10 => ref R10,
        11 => ref R11,
        12 => ref R12,
        13 => ref R13,
        14 => ref R14,
        15 => ref R15,
        16 => ref R16,
        17 => ref R17,
        18 => ref R18,
        19 => ref R19,
        20 => ref R20,
        21 => ref R21,
        22 => ref R22,
        23 => ref R23,
        24 => ref R24,
        25 => ref R25,
        26 => ref R26,
        27 => ref R27,
        28 => ref R28,
        29 => ref R29,
        _ => ref R30
    }
}

val ignore_data_dependency : forall 'n, 0 <= 'n <= 31. int('n) -> unit

function ignore_data_dependency(n) = {
    if n <= 30 then {
       __ignore_write_to(register_ref(n))
    }
}

val ignore_dependency_edge : forall 'n 'm, 0 <= 'n <= 31 & 0 <= 'm <= 31. (int('n), int('m)) -> unit

function ignore_dependency_edge(n, m) = {
    if n <= 30 & m <= 30 then {
        __mark_register_pair(register_ref(n), register_ref(m), "ignore_edge")
    }
}

register _PendingPhysicalSE : bool

register _PPURSER : bits(32)

register _PPURBAR : bits(64)

register _PPURACR : bits(32)

register _PC : bits(64)

val aget_PC : unit -> bits(64) effect {rreg}

function aget_PC () = {
    _PC
}

overload PC = {aget_PC}

register _IRQPending : bool

register _GTE_AS_Size : bits(64)

register _GTE_AS_Address : bits(64)

register _GTE_AS_AccessCount : int

register _GTE_AS_Access : bits(32)

register _GTEStatus : bits(64)

register _GTEParamsComplete : bool

register _GTEParamType : GTEParamType

register _GTEParamLo : bits(32)

val set_GTE_API_PARAM_64 : bits(32) -> unit effect {wreg}

function set_GTE_API_PARAM_64 val_name = {
    _GTEParamLo = slice(val_name, 0, 32);
    return()
}

register _GTEParamCount : int

register _GTEListParamTerminators : int

register _GTEListParamTerminatorCount : int

register _GTEListParamTerminator : bits(64)

register _GTEListParamIndex : int

register _GTEListParam : int

register _GTEHaveParamLo : bool

register _GTECurrentAPI : bits(32)

register _GTEActive : bool

register _FIQPending : bool

register _ClearIRQ : bits(32)

val get_ClearIRQ : unit -> bits(32) effect {rreg}

function get_ClearIRQ () = {
    slice(_ClearIRQ, 0, 32)
}

register _ClearFIQ : bits(32)

val get_ClearFIQ : unit -> bits(32) effect {rreg}

function get_ClearFIQ () = {
    slice(_ClearFIQ, 0, 32)
}

register _AXIAbortCtl : bits(32)

register VTTBR_EL2 : bits(64)

val get_VTTBR : unit -> bits(64) effect {rreg, undef}

function get_VTTBR () = {
    r : bits(64) = undefined : bits(64);
    let r = __SetSlice_bits(64, 64, r, 0, slice(VTTBR_EL2, 0, 64));
    r
}

register VTCR_EL2 : bits(32)

val get_VTCR : unit -> bits(32) effect {rreg, undef}

function get_VTCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(VTCR_EL2, 0, 32));
    r
}

register VSTTBR_EL2 : bits(64)

register VSTCR_EL2 : bits(32)

register VSESR_EL2 : bits(64)

val get_VDFSR : unit -> bits(32) effect {rreg}

function get_VDFSR () = {
    slice(VSESR_EL2, 0, 32)
}

register VBAR_S : bits(32)

register VBAR_EL3 : bits(64)

register VBAR_EL2 : bits(64)

val get_HVBAR : unit -> bits(32) effect {rreg, undef}

function get_HVBAR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(VBAR_EL2, 0, 32));
    r
}

register VBAR_EL1 : bits(64)

val get_VBAR_NS : unit -> bits(32) effect {rreg, undef}

function get_VBAR_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(VBAR_EL1, 0, 32));
    r
}

let VAL_SET_PPU_REGION : bits(32) = __GetSlice_int(32, 10, 0)

let VAL_SET_CRITICAL_EVENT : bits(32) = __GetSlice_int(32, 17, 0)

let VAL_SETUP_EXT_OBS_64 : bits(32) = __GetSlice_int(32, 25, 0)

let VAL_SETUP_EXT_OBS : bits(32) = __GetSlice_int(32, 13, 0)

let VAL_RETURN_OBS_DATA_64 : bits(32) = __GetSlice_int(32, 28, 0)

let VAL_RELEASE_EXT_OBS : bits(32) = __GetSlice_int(32, 16, 0)

let VAL_RANDNUM : bits(32) = __GetSlice_int(32, 20, 0)

let VAL_PPU_CONTROL : bits(32) = __GetSlice_int(32, 12, 0)

let VAL_PERFORM_EXT_OBS_64 : bits(32) = __GetSlice_int(32, 27, 0)

let VAL_PERFORM_EXT_OBS : bits(32) = __GetSlice_int(32, 15, 0)

let VAL_OBSERVER_PIN_VALUE : bits(32) = __GetSlice_int(32, 22, 0)

let VAL_GET_PPU_REGION : bits(32) = __GetSlice_int(32, 11, 0)

let VAL_GET_PPU_ID : bits(32) = __GetSlice_int(32, 9, 0)

let VAL_EVENTGEN_SETUP : bits(32) = __GetSlice_int(32, 1, 0)

let VAL_EVENTGEN_QUERY : bits(32) = __GetSlice_int(32, 4, 0)

let VAL_EVENTGEN_PRIME : bits(32) = __GetSlice_int(32, 2, 0)

let VAL_EVENTGEN_FREE : bits(32) = __GetSlice_int(32, 6, 0)

let VAL_EVENTGEN_DISABLE : bits(32) = __GetSlice_int(32, 5, 0)

let VAL_EVENTGEN_CLEAR : bits(32) = __GetSlice_int(32, 3, 0)

let VAL_EN_ACCESS_SENSITIVE_BEH : bits(32) = __GetSlice_int(32, 23, 0)

let VAL_ENABLE_EXT_OBS_64 : bits(32) = __GetSlice_int(32, 26, 0)

let VAL_ENABLE_EXT_OBS : bits(32) = __GetSlice_int(32, 14, 0)

let VAL_DEFINE_NO_ABORTING_REGIONS : bits(32) = __GetSlice_int(32, 21, 0)

let VAL_DEASSERT : bits(32) = __GetSlice_int(32, 8, 0)

let VAL_CRITICAL_SECTION_START : bits(32) = __GetSlice_int(32, 18, 0)

let VAL_CRITICAL_SECTION_END : bits(32) = __GetSlice_int(32, 19, 0)

let VAL_CHK_ACCESS_SENSITIVE_BEH : bits(32) = __GetSlice_int(32, 24, 0)

let VAL_ASSERT : bits(32) = __GetSlice_int(32, 7, 0)

val ThisInstr : unit -> bits(32) effect {rreg}

function ThisInstr () = {
    __currentInstr
}

register TTBR1_S : bits(64)

register TTBR1_EL2 : bits(64)

register TTBR1_EL1 : bits(64)

val get_TTBR1_NS : unit -> bits(64) effect {rreg, undef}

function get_TTBR1_NS () = {
    r : bits(64) = undefined : bits(64);
    let r = __SetSlice_bits(64, 64, r, 0, slice(TTBR1_EL1, 0, 64));
    r
}

register TTBR0_S : bits(64)

register TTBR0_EL3 : bits(64)

register TTBR0_EL2 : bits(64)

val get_HTTBR : unit -> bits(64) effect {rreg, undef}

function get_HTTBR () = {
    r : bits(64) = undefined : bits(64);
    let r = __SetSlice_bits(64, 64, r, 0, slice(TTBR0_EL2, 0, 64));
    r
}

register TTBR0_EL1 : bits(64)

val get_TTBR0_NS : unit -> bits(64) effect {rreg, undef}

function get_TTBR0_NS () = {
    r : bits(64) = undefined : bits(64);
    let r = __SetSlice_bits(64, 64, r, 0, slice(TTBR0_EL1, 0, 64));
    r
}

register TTBCR_S : bits(32)

register TTBCR2_S : bits(32)

register configuration __v85_implemented : bool = true

register configuration __v84_implemented : bool = true

register configuration __v83_implemented : bool = true

register configuration __v82_implemented : bool = true

register configuration __v81_implemented : bool = true

register configuration __unpred_tsize_aborts : bool = true

register configuration __trickbox_enabled : bool = true

register configuration __tlb_enabled : bool = true

register configuration __syncAbortOnTTWNonCache : bool = true

register configuration __syncAbortOnTTWCache : bool = true

register configuration __syncAbortOnSoWrite : bool = true

register configuration __syncAbortOnSoRead : bool = true

register configuration __syncAbortOnReadNormNonCache : bool = true

register configuration __syncAbortOnReadNormCache : bool = true

register configuration __syncAbortOnPrefetch : bool = true

register configuration __syncAbortOnDeviceRead : bool = true

register configuration __support_52bit_pa : bool = true

register configuration __mte_implemented : bool = true

register configuration __mpam_has_hcr : bool = true

register configuration __crypto_sha256_implemented : bool = true

register configuration __crypto_sha1_implemented : bool = true

register TLBMisses : int

register TLBHits : int

register TFSR_EL3 : bits(32)

register TFSR_EL2 : bits(32)

register TFSR_EL1 : bits(32)

register TFSRE0_EL1 : bits(32)

register TCR_EL3 : bits(32)

register TCR_EL1 : bits(64)

val get_TTBCR_NS : unit -> bits(32) effect {rreg, undef}

function get_TTBCR_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(TCR_EL1, 0, 32));
    r
}

val get_TTBCR2_NS : unit -> bits(32) effect {rreg, undef}

function get_TTBCR2_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(TCR_EL1, 32, 32));
    r
}

register configuration TAG_STORE_AREA : bits(56) = __GetSlice_int(56, 4503599627370496, 0)

val SynchronizeErrors : unit -> unit

function SynchronizeErrors () = {
    return()
}

val SynchronizeContext : unit -> unit

function SynchronizeContext () = {
    return()
}

val StopInstructionPrefetchAndEnableITR : unit -> unit effect {escape}

function StopInstructionPrefetchAndEnableITR () = {
    throw(Error_Implementation_Defined("StopInstructionPrefetchAndEnableITR unimplemented"))
}

val SoftwareStep_SteppedEX : unit -> bool effect {escape}

function SoftwareStep_SteppedEX () = {
    throw(Error_Implementation_Defined("SoftwareStep_SteppedEX unimplemented"))
}

val SoftwareStep_DidNotStep : unit -> bool effect {escape}

function SoftwareStep_DidNotStep () = {
    throw(Error_Implementation_Defined("SoftwareStep_DidNotStep unimplemented"))
}

val SetPendingPhysicalSE : forall ('val : Bool).
  bool('val) -> unit effect {wreg}

function SetPendingPhysicalSE val_name = {
    _PendingPhysicalSE = val_name
}

register ScheduledIRQ : bool

val set_ScheduleIRQ : bits(32) -> unit effect {wreg}

function set_ScheduleIRQ val_name = {
    _ScheduleIRQ = val_name;
    ScheduledIRQ = true;
    return()
}

register ScheduledFIQ : bool

val set_ScheduleFIQ : bits(32) -> unit effect {wreg}

function set_ScheduleFIQ val_name = {
    _ScheduleFIQ = val_name;
    ScheduledFIQ = true;
    return()
}

register SP_mon : bits(32)

register SPSR_und : bits(32)

register SPSR_irq : bits(32)

register SPSR_fiq : bits(32)

register SPSR_abt : bits(32)

register SPSR_EL3 : bits(32)

val set_SPSR_mon : bits(32) -> unit effect {rreg, wreg}

function set_SPSR_mon val_name = {
    let r : bits(32) = val_name;
    SPSR_EL3 = __SetSlice_bits(32, 32, SPSR_EL3, 0, slice(r, 0, 32));
    return()
}

register SPSR_EL2 : bits(32)

val set_SPSR_hyp : bits(32) -> unit effect {rreg, wreg}

function set_SPSR_hyp val_name = {
    let r : bits(32) = val_name;
    SPSR_EL2 = __SetSlice_bits(32, 32, SPSR_EL2, 0, slice(r, 0, 32));
    return()
}

register SPSR_EL1 : bits(32)

val set_SPSR_svc : bits(32) -> unit effect {rreg, wreg}

function set_SPSR_svc val_name = {
    let r : bits(32) = val_name;
    SPSR_EL1 = __SetSlice_bits(32, 32, SPSR_EL1, 0, slice(r, 0, 32));
    return()
}

register SPIDEN : signal

register SDER32_EL3 : bits(32)

val get_SDER : unit -> bits(32) effect {rreg, undef}

function get_SDER () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(SDER32_EL3, 0, 32));
    r
}

register SCTLR_S : bits(32)

register SCTLR_EL3 : bits(64)

register SCTLR_EL2 : bits(64)

val get_HSCTLR : unit -> bits(32) effect {rreg, undef}

function get_HSCTLR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(SCTLR_EL2, 0, 32));
    r
}

register SCTLR_EL1 : bits(64)

val get_SCTLR_NS : unit -> bits(32) effect {rreg, undef}

function get_SCTLR_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(SCTLR_EL1, 0, 32));
    r
}

register SCR_EL3 : bits(32)

val set_SCR : bits(32) -> unit effect {rreg, wreg}

function set_SCR val_name = {
    let r : bits(32) = val_name;
    SCR_EL3 = __SetSlice_bits(32, 32, SCR_EL3, 0, slice(r, 0, 32));
    return()
}

val get_SCR : unit -> bits(32) effect {rreg, undef}

function get_SCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(SCR_EL3, 0, 32));
    r
}

val RemapRegsHaveResetValues : unit -> bool

function RemapRegsHaveResetValues () = {
    true
}

register PSTATE : ProcState

register PRRR_S : bits(32)

register OSLSR_EL1 : bits(32)

val get_DBGOSLSR : unit -> bits(32) effect {rreg, undef}

function get_DBGOSLSR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(OSLSR_EL1, 0, 32));
    r
}

register OSDLR_EL1 : bits(32)

val get_DBGOSDLR : unit -> bits(32) effect {rreg, undef}

function get_DBGOSDLR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(OSDLR_EL1, 0, 32));
    r
}

let NUM_GTE_REGIONS : int(6) = 6

let NUM_GTE_PARAMS : int(8) = 8

let NUM_GTE_EXT_OBS_OBSERVERS : int(4) = 4

let NUM_GTE_EXT_OBS_OBSERVATIONS_PER_OBSERVER : int(64) = 64

let NUM_GTE_AS_ACCESSES : int(8) = 8

register NMRR_S : bits(32)

val __UNKNOWN_MemType : unit -> MemType

function __UNKNOWN_MemType () = {
    MemType_Normal
}

let MemHint_RWA : bits(2) = 0b11

let MemHint_RA : bits(2) = 0b10

let MemHint_No : bits(2) = 0b00

let MemAttr_WT : bits(2) = 0b10

let MemAttr_WB : bits(2) = 0b11

let MemAttr_NC : bits(2) = 0b00

register MVBAR : bits(32)

register MPIDR_EL1 : bits(64)

register MPAMVPMV_EL2 : bits(32)

register MPAMVPM7_EL2 : bits(64)

register MPAMVPM6_EL2 : bits(64)

register MPAMVPM5_EL2 : bits(64)

register MPAMVPM4_EL2 : bits(64)

register MPAMVPM3_EL2 : bits(64)

register MPAMVPM2_EL2 : bits(64)

register MPAMVPM1_EL2 : bits(64)

register MPAMVPM0_EL2 : bits(64)

register MPAMIDR_EL1 : bits(64)

register MPAMHCR_EL2 : bits(32)

register MPAM3_EL3 : bits(64)

register MPAM2_EL2 : bits(64)

register MPAM1_EL1 : bits(64)

register MPAM0_EL1 : bits(64)

register MDSCR_EL1 : bits(32)

val set_DBGDSCRext : bits(32) -> unit effect {rreg, wreg}

function set_DBGDSCRext val_name = {
    let r : bits(32) = val_name;
    MDSCR_EL1 = __SetSlice_bits(32, 32, MDSCR_EL1, 0, slice(r, 0, 32));
    return()
}

val get_DBGDSCRext : unit -> bits(32) effect {rreg, undef}

function get_DBGDSCRext () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MDSCR_EL1, 0, 32));
    r
}

register MDCR_EL3 : bits(32)

val get_SDCR : unit -> bits(32) effect {rreg, undef}

function get_SDCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MDCR_EL3, 0, 32));
    r
}

register MDCR_EL2 : bits(32)

val get_HDCR : unit -> bits(32) effect {rreg, undef}

function get_HDCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MDCR_EL2, 0, 32));
    r
}

register MAIR_EL3 : bits(64)

register MAIR_EL2 : bits(64)

val get_HMAIR1 : unit -> bits(32) effect {rreg, undef}

function get_HMAIR1 () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MAIR_EL2, 32, 32));
    r
}

val get_HMAIR0 : unit -> bits(32) effect {rreg, undef}

function get_HMAIR0 () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MAIR_EL2, 0, 32));
    r
}

register MAIR_EL1 : bits(64)

val get_PRRR_NS : unit -> bits(32) effect {rreg, undef}

function get_PRRR_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MAIR_EL1, 0, 32));
    r
}

val get_NMRR_NS : unit -> bits(32) effect {rreg, undef}

function get_NMRR_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MAIR_EL1, 32, 32));
    r
}

val get_MAIR1_NS : unit -> bits(32) effect {rreg, undef}

function get_MAIR1_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MAIR_EL1, 32, 32));
    r
}

val get_MAIR0_NS : unit -> bits(32) effect {rreg, undef}

function get_MAIR0_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(MAIR_EL1, 0, 32));
    r
}

register MAIR1_S : bits(32)

register MAIR0_S : bits(32)

let M32_User : bits(5) = 0b10000

let M32_Undef : bits(5) = 0b11011

let M32_System : bits(5) = 0b11111

let M32_Svc : bits(5) = 0b10011

let M32_Monitor : bits(5) = 0b10110

let M32_IRQ : bits(5) = 0b10010

let M32_Hyp : bits(5) = 0b11010

let M32_FIQ : bits(5) = 0b10001

let M32_Abort : bits(5) = 0b10111

val LSInstructionSyndrome : unit -> bits(11) effect {rreg}

function LSInstructionSyndrome () = {
    __LSISyndrome
}

register LR_mon : bits(32)

let LOG2_TAG_GRANULE_DEFAULT : int(4) = 4

register configuration LOG2_TAG_GRANULE : int = LOG2_TAG_GRANULE_DEFAULT

val IsPhysicalSErrorPending : unit -> bool effect {rreg}

function IsPhysicalSErrorPending () = {
    _PendingPhysicalSE
}

val __UNKNOWN_InstrSet : unit -> InstrSet

function __UNKNOWN_InstrSet () = {
    InstrSet_A64
}

register InGuardedPage : bool

val IRQPending : unit -> bool effect {rreg}

function IRQPending () = {
    _IRQPending
}

register IFSR_S : bits(32)

register IFSR32_EL2 : bits(32)

val set_IFSR_NS : bits(32) -> unit effect {rreg, wreg}

function set_IFSR_NS val_name = {
    let r : bits(32) = val_name;
    IFSR32_EL2 = __SetSlice_bits(32, 32, IFSR32_EL2, 0, slice(r, 0, 32));
    return()
}

register ID_AA64DFR0_EL1 : bits(64)

val Hint_Branch : BranchType -> unit

function Hint_Branch hint = {
    return()
}

val HighestELUsingAArch32 : unit -> bool effect {rreg}

function HighestELUsingAArch32 () = {
    __highest_el_aarch32
}

val Have52BitPAExt : unit -> bool

function Have52BitPAExt () = {
    __support_52bit_pa
}

register HPFAR_EL2 : bits(64)

val set_HPFAR : bits(32) -> unit effect {rreg, wreg}

function set_HPFAR val_name = {
    let r : bits(32) = val_name;
    HPFAR_EL2 = __SetSlice_bits(64, 32, HPFAR_EL2, 0, slice(r, 0, 32));
    return()
}

val get_HPFAR : unit -> bits(32) effect {rreg, undef}

function get_HPFAR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(HPFAR_EL2, 0, 32));
    r
}

register HCR_EL2 : bits(64)

val get_HCR2 : unit -> bits(32) effect {rreg, undef}

function get_HCR2 () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(HCR_EL2, 32, 32));
    r
}

val get_HCR : unit -> bits(32) effect {rreg, undef}

function get_HCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(HCR_EL2, 0, 32));
    r
}

let GTE_ST_REQUEST_GRANTED : bits(64) = __GetSlice_int(64, 0, 0)

let GTE_ST_REQUEST_FAIL : bits(64) = __GetSlice_int(64, 1, 0)

let GTE_LIST_PARAM_LEN : int(64) = 64

let GTE_EXT_OBS_RESULTS_ADDRESS : bits(64) = __GetSlice_int(64, 318775296, 0)

let GTE_EXT_OBS_OUTER_S : bits(3) = 0b011

let GTE_EXT_OBS_OUTER_NS : bits(3) = 0b101

let GTE_EXT_OBS_INNER_S : bits(3) = 0b100

let GTE_EXT_OBS_INNER_NS : bits(3) = 0b110

let GTE_EXT_OBS_ACC_WRITE : bits(3) = 0b010

let GTE_EXT_OBS_ACC_SIZE8 : bits(3) = 0b011

let GTE_EXT_OBS_ACC_SIZE64 : bits(3) = 0b000

let GTE_EXT_OBS_ACC_SIZE32 : bits(3) = 0b001

let GTE_EXT_OBS_ACC_SIZE16 : bits(3) = 0b010

let GTE_EXT_OBS_ACC_READ : bits(3) = 0b001

val GTEGetPPUID : unit -> unit effect {wreg}

function GTEGetPPUID () = {
    prerr("GTEGetPPUID()\n");
    _GTEStatus = __GetSlice_int(64, NUM_GTE_REGIONS, 0);
    return()
}

val GTECriticalSectionStart : unit -> unit

function GTECriticalSectionStart () = {
    prerr("TODO: implement GTECriticalSectionStart\n");
    return()
}

val GTECriticalSectionEnd : unit -> unit

function GTECriticalSectionEnd () = {
    prerr("TODO: implement GTECriticalSectionEnd\n");
    return()
}

val __UNKNOWN_Fault : unit -> Fault

function __UNKNOWN_Fault () = {
    Fault_None
}

val FIQPending : unit -> bool effect {rreg}

function FIQPending () = {
    _FIQPending
}

register FAR_EL3 : bits(64)

register FAR_EL2 : bits(64)

val set_IFAR_S : bits(32) -> unit effect {rreg, wreg}

function set_IFAR_S val_name = {
    let r : bits(32) = val_name;
    FAR_EL2 = __SetSlice_bits(64, 32, FAR_EL2, 32, slice(r, 0, 32));
    return()
}

val set_HIFAR : bits(32) -> unit effect {rreg, wreg}

function set_HIFAR val_name = {
    let r : bits(32) = val_name;
    FAR_EL2 = __SetSlice_bits(64, 32, FAR_EL2, 32, slice(r, 0, 32));
    return()
}

val set_HDFAR : bits(32) -> unit effect {rreg, wreg}

function set_HDFAR val_name = {
    let r : bits(32) = val_name;
    FAR_EL2 = __SetSlice_bits(64, 32, FAR_EL2, 0, slice(r, 0, 32));
    return()
}

val set_DFAR_S : bits(32) -> unit effect {rreg, wreg}

function set_DFAR_S val_name = {
    let r : bits(32) = val_name;
    FAR_EL2 = __SetSlice_bits(64, 32, FAR_EL2, 0, slice(r, 0, 32));
    return()
}

register FAR_EL1 : bits(64)

val set_IFAR_NS : bits(32) -> unit effect {rreg, wreg}

function set_IFAR_NS val_name = {
    let r : bits(32) = val_name;
    FAR_EL1 = __SetSlice_bits(64, 32, FAR_EL1, 32, slice(r, 0, 32));
    return()
}

val set_DFAR_NS : bits(32) -> unit effect {rreg, wreg}

function set_DFAR_NS val_name = {
    let r : bits(32) = val_name;
    FAR_EL1 = __SetSlice_bits(64, 32, FAR_EL1, 0, slice(r, 0, 32));
    return()
}

register configuration __syncAbortOnWriteNormNonCache : bool = false

register configuration __syncAbortOnWriteNormCache : bool = false

register configuration __syncAbortOnDeviceWrite : bool = false

register configuration __mpam_implemented : bool = false

register configuration __crypto_sm4_implemented : bool = false

register configuration __crypto_sm3_implemented : bool = false

register configuration __crypto_sha512_implemented : bool = false

register configuration __crypto_sha3_implemented : bool = false

val __UNKNOWN_boolean : unit -> bool

function __UNKNOWN_boolean () = {
    false
}

val Unreachable : unit -> unit effect {escape}

function Unreachable () = {
    assert(false)
}

val RBankSelect : forall 'usr 'fiq 'irq 'svc 'abt 'und 'hyp.
  (bits(5), int('usr), int('fiq), int('irq), int('svc), int('abt), int('und), int('hyp)) -> {'n, ('n == 'usr | 'n == 'fiq | 'n == 'irq | 'n == 'svc | 'n == 'abt | 'n == 'und | 'n == 'hyp). int('n)}

function RBankSelect (mode, usr, fiq, irq, svc, abt, und, hyp) = {
    match mode {
      ? if ? == M32_User => usr,
      ? if ? == M32_FIQ => fiq,
      ? if ? == M32_IRQ => irq,
      ? if ? == M32_Svc => svc,
      ? if ? == M32_Abort => abt,
      ? if ? == M32_Hyp => hyp,
      ? if ? == M32_Undef => und,
      ? if ? == M32_System => usr
    }
}

val TakeUnmaskedPhysicalSErrorInterrupts : forall ('iesb_req : Bool).
  bool('iesb_req) -> unit effect {escape, rreg, undef, wreg}

function TakeUnmaskedPhysicalSErrorInterrupts iesb_req = {
    let interrupt_req : InterruptReq = struct {
        take_SE = true,
        take_vSE = false,
        take_IRQ = false,
        take_vIRQ = false,
        take_FIQ = false,
        take_vFIQ = false,
        iesb_req = iesb_req
    };
    let interrupt_taken : bool = TakePendingInterrupts(interrupt_req);
    return()
}

val __UNKNOWN_Exception : unit -> Exception

function __UNKNOWN_Exception () = {
    Exception_Uncategorized
}

val EndOfInstruction : unit -> unit effect {escape}

function EndOfInstruction () = {
    throw(Error_ExceptionTaken())
}

register ESR_EL3 : bits(32)

register ESR_EL2 : bits(32)

val set_HSR : bits(32) -> unit effect {rreg, wreg}

function set_HSR val_name = {
    let r : bits(32) = val_name;
    ESR_EL2 = __SetSlice_bits(32, 32, ESR_EL2, 0, slice(r, 0, 32));
    return()
}

register ESR_EL1 : bits(32)

val set_DFSR_NS : bits(32) -> unit effect {rreg, wreg}

function set_DFSR_NS val_name = {
    let r : bits(32) = val_name;
    ESR_EL1 = __SetSlice_bits(32, 32, ESR_EL1, 0, slice(r, 0, 32));
    return()
}

val TLBIndex : (bits(64), TLBContext) -> bits(10) effect {undef}

function TLBIndex (address, context) = {
    res : bits(10) = undefined : bits(10);
    res = slice(address, context.granule_size, 10);
    if context.secondstage then {
        res = res ^ __GetSlice_int(10, 144, 0)
    };
    res
}

register ELR_EL3 : bits(64)

register ELR_EL2 : bits(64)

val set_ELR_hyp : bits(32) -> unit effect {rreg, wreg}

function set_ELR_hyp val_name = {
    let r : bits(32) = val_name;
    ELR_EL2 = __SetSlice_bits(64, 32, ELR_EL2, 0, slice(r, 0, 32));
    return()
}

register ELR_EL1 : bits(64)

let EL3 : bits(2) = 0b11

let EL2 : bits(2) = 0b10

let EL1 : bits(2) = 0b01

let EL0 : bits(2) = 0b00

register EDSCR : bits(32)

val __UNKNOWN_DeviceType : unit -> DeviceType

function __UNKNOWN_DeviceType () = {
    DeviceType_GRE
}

let DefaultPMG : bits(8) = __GetSlice_int(8, 0, 0)

let DefaultPARTID : bits(16) = __GetSlice_int(16, 0, 0)

val DefaultMPAMinfo : forall ('secure : Bool).
  bool('secure) -> MPAMinfo effect {undef}

function DefaultMPAMinfo secure = {
    DefaultInfo : MPAMinfo = undefined : MPAMinfo;
    DefaultInfo.mpam_ns = if secure then 0b0 else 0b1;
    DefaultInfo.partid = DefaultPARTID;
    DefaultInfo.pmg = DefaultPMG;
    DefaultInfo
}

let DebugHalt_Watchpoint : bits(6) = 0b101011

let DebugHalt_Breakpoint : bits(6) = 0b000111

let DebugException_Watchpoint : bits(4) = 0xA

let DebugException_VectorCatch : bits(4) = 0x5

let DebugException_Breakpoint : bits(4) = 0x1

register DSPSR_EL0 : bits(32)

val set_DSPSR : bits(32) -> unit effect {rreg, wreg}

function set_DSPSR val_name = {
    let r : bits(32) = val_name;
    DSPSR_EL0 = __SetSlice_bits(32, 32, DSPSR_EL0, 0, slice(r, 0, 32));
    return()
}

val get_DSPSR : unit -> bits(32) effect {rreg, undef}

function get_DSPSR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(DSPSR_EL0, 0, 32));
    r
}

register DLR_EL0 : bits(64)

val set_DLR : bits(32) -> unit effect {rreg, wreg}

function set_DLR val_name = {
    let r : bits(32) = val_name;
    DLR_EL0 = __SetSlice_bits(64, 32, DLR_EL0, 0, slice(r, 0, 32));
    return()
}

register DFSR_S : bits(32)

register DBGWVR_EL1 : vector(17, dec, bits(64))

register DBGWVR : vector(17, dec, bits(32))

register DBGWCR_EL1 : vector(17, dec, bits(32))

register DBGWCR : vector(17, dec, bits(32))

register DBGVCR32_EL2 : bits(32)

val get_DBGVCR : unit -> bits(32) effect {rreg, undef}

function get_DBGVCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(DBGVCR32_EL2, 0, 32));
    r
}

register DBGPRCR_EL1 : bits(32)

val get_DBGPRCR : unit -> bits(32) effect {rreg, undef}

function get_DBGPRCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(DBGPRCR_EL1, 0, 32));
    r
}

register DBGEN : signal

register DBGDIDR : bits(32)

register DBGBXVR : vector(17, dec, bits(32))

register DBGBVR_EL1 : vector(17, dec, bits(64))

register DBGBVR : vector(17, dec, bits(32))

register DBGBCR_EL1 : vector(17, dec, bits(32))

register DBGBCR : vector(17, dec, bits(32))

register DACR_S : bits(32)

register DACR32_EL2 : bits(32)

val get_DACR_NS : unit -> bits(32) effect {rreg, undef}

function get_DACR_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(DACR32_EL2, 0, 32));
    r
}

val __UNKNOWN_Constraint : unit -> Constraint

function __UNKNOWN_Constraint () = {
    Constraint_NONE
}

val ConstrainUnpredictable : Unpredictable -> Constraint

function ConstrainUnpredictable which = {
    match which {
      Unpredictable_WBOVERLAPLD => {
          return(Constraint_WBSUPPRESS)
      },
      Unpredictable_WBOVERLAPST => {
          return(Constraint_NONE)
      },
      Unpredictable_LDPOVERLAP => {
          return(Constraint_UNDEF)
      },
      Unpredictable_BASEOVERLAP => {
          return(Constraint_NONE)
      },
      Unpredictable_DATAOVERLAP => {
          return(Constraint_NONE)
      },
      Unpredictable_DEVPAGE2 => {
          return(Constraint_FAULT)
      },
      Unpredictable_INSTRDEVICE => {
          return(Constraint_NONE)
      },
      Unpredictable_RESCPACR => {
          return(Constraint_UNKNOWN)
      },
      Unpredictable_RESMAIR => {
          return(Constraint_UNKNOWN)
      },
      Unpredictable_RESTEXCB => {
          return(Constraint_UNKNOWN)
      },
      Unpredictable_RESDACR => {
          return(Constraint_UNKNOWN)
      },
      Unpredictable_RESPRRR => {
          return(Constraint_UNKNOWN)
      },
      Unpredictable_RESVTCRS => {
          return(Constraint_UNKNOWN)
      },
      Unpredictable_RESTnSZ => {
          return(Constraint_FORCE)
      },
      Unpredictable_OORTnSZ => {
          return(Constraint_FORCE)
      },
      Unpredictable_LARGEIPA => {
          if __unpred_tsize_aborts then {
              return(Constraint_FAULT)
          } else {
              return(Constraint_FORCE)
          }
      },
      Unpredictable_ESRCONDPASS => {
          return(Constraint_FALSE)
      },
      Unpredictable_ILZEROIT => {
          return(Constraint_FALSE)
      },
      Unpredictable_ILZEROT => {
          return(Constraint_FALSE)
      },
      Unpredictable_BPVECTORCATCHPRI => {
          return(Constraint_TRUE)
      },
      Unpredictable_VCMATCHHALF => {
          return(Constraint_FALSE)
      },
      Unpredictable_VCMATCHDAPA => {
          return(Constraint_FALSE)
      },
      Unpredictable_WPMASKANDBAS => {
          return(Constraint_FALSE)
      },
      Unpredictable_WPBASCONTIGUOUS => {
          return(Constraint_FALSE)
      },
      Unpredictable_RESWPMASK => {
          return(Constraint_DISABLED)
      },
      Unpredictable_WPMASKEDBITS => {
          return(Constraint_FALSE)
      },
      Unpredictable_RESBPWPCTRL => {
          return(Constraint_DISABLED)
      },
      Unpredictable_BPNOTIMPL => {
          return(Constraint_DISABLED)
      },
      Unpredictable_RESBPTYPE => {
          return(Constraint_DISABLED)
      },
      Unpredictable_BPNOTCTXCMP => {
          return(Constraint_DISABLED)
      },
      Unpredictable_BPMATCHHALF => {
          return(Constraint_FALSE)
      },
      Unpredictable_BPMISMATCHHALF => {
          return(Constraint_FALSE)
      },
      Unpredictable_RESTARTALIGNPC => {
          return(Constraint_FALSE)
      },
      Unpredictable_RESTARTZEROUPPERPC => {
          return(Constraint_TRUE)
      },
      Unpredictable_ZEROUPPER => {
          return(Constraint_TRUE)
      },
      Unpredictable_ERETZEROUPPERPC => {
          return(Constraint_TRUE)
      },
      Unpredictable_A32FORCEALIGNPC => {
          return(Constraint_FALSE)
      },
      Unpredictable_SMD => {
          return(Constraint_UNDEF)
      },
      Unpredictable_AFUPDATE => {
          return(Constraint_TRUE)
      },
      Unpredictable_IESBinDebug => {
          return(Constraint_TRUE)
      },
      Unpredictable_ZEROBTYPE => {
          return(Constraint_TRUE)
      },
      Unpredictable_CLEARERRITEZERO => {
          return(Constraint_FALSE)
      }
    }
}

val ClearPendingVirtualSError : unit -> unit effect {rreg, wreg}

function ClearPendingVirtualSError () = {
    HCR_EL2 = __SetSlice_bits(64, 1, HCR_EL2, 8, 0b0)
}

val ClearPendingPhysicalSError : unit -> unit effect {wreg}

function ClearPendingPhysicalSError () = {
    _PendingPhysicalSE = false
}

val CTI_SignalEvent : CrossTriggerIn -> unit effect {escape}

function CTI_SignalEvent id = {
    throw(Error_Implementation_Defined("CTI_SignalEvent unimplemented"))
}

register CONTEXTIDR_EL2 : bits(32)

register CONTEXTIDR_EL1 : bits(32)

register CNTSR : bits(32)

register CNTFID0 : bits(32)

register CNTCV : bits(64)

register CNTCR : bits(32)

val __WriteMemoryMappedCounterRegister : forall ('address : Int).
  (int('address), bits(32)) -> unit effect {rreg, wreg}

function __WriteMemoryMappedCounterRegister (address, val_name) = {
    match address {
      0 => {
          CNTCR = val_name
      },
      4 => {
          CNTSR = val_name
      },
      8 => {
          CNTCV = __SetSlice_bits(64, 32, CNTCV, 0, val_name)
      },
      12 => {
          CNTCV = __SetSlice_bits(64, 32, CNTCV, 32, val_name)
      },
      32 => {
          CNTFID0 = val_name
      },
      _ => {
          return()
      }
    }
}

val __ReadMemoryMappedCounterRegister : forall ('address : Int).
  int('address) -> bits(32) effect {rreg, undef}

function __ReadMemoryMappedCounterRegister address = {
    match address {
      0 => {
          return(CNTCR)
      },
      4 => {
          return(CNTSR)
      },
      8 => {
          return(slice(CNTCV, 0, 32))
      },
      12 => {
          return(slice(CNTCV, 32, 32))
      },
      32 => {
          return(CNTFID0)
      },
      _ => {
          return(undefined : bits(32))
      }
    }
}

register configuration CFG_RVBAR : bits(64) = __GetSlice_int(64, 271581184, 0)

register configuration CFG_ID_AA64PFR0_EL1_MPAM : bits(4) = 0x1

register configuration CFG_ID_AA64PFR0_EL1_EL3 : bits(4) = 0x2

register configuration CFG_ID_AA64PFR0_EL1_EL2 : bits(4) = 0x2

register configuration CFG_ID_AA64PFR0_EL1_EL1 : bits(4) = 0x2

register configuration CFG_ID_AA64PFR0_EL1_EL0 : bits(4) = 0x2

val AsynchronousErrorType : unit -> AsyncErrorType

function AsynchronousErrorType () = {
    AsyncErrorType_UC
}

val __UNKNOWN_AccType : unit -> AccType

function __UNKNOWN_AccType () = {
    AccType_NORMAL
}

register AbortRgn64Lo2_Hi : bits(32)

register AbortRgn64Lo2 : bits(32)

register AbortRgn64Lo1_Hi : bits(32)

register AbortRgn64Lo1 : bits(32)

register AbortRgn64Hi2_Hi : bits(32)

register AbortRgn64Hi2 : bits(32)

register AbortRgn64Hi1_Hi : bits(32)

register AbortRgn64Hi1 : bits(32)

val set_TargetCPU : bits(32) -> unit effect {wreg}

function set_TargetCPU val_name = {
    let _val : bits(32) = val_name & ~(__GetSlice_int(32, 4294967280, 0)) | __GetSlice_int(32, 0, 0);
    _TargetCPU = _val;
    return()
}

val set_AXIAbortCtl : bits(32) -> unit effect {wreg}

function set_AXIAbortCtl val_name = {
    let _val : bits(32) = val_name & ~(__GetSlice_int(32, 4027580415, 0)) | __GetSlice_int(32, 0, 0);
    _AXIAbortCtl = _val;
    return()
}

val get_AXIAbortCtl : unit -> bits(32) effect {rreg}

function get_AXIAbortCtl () = {
    val_name : bits(32) = _AXIAbortCtl;
    let val_name = val_name & ~(__GetSlice_int(32, 4027580415, 0)) | __GetSlice_int(32, 0, 0);
    val_name
}

val AArch64_CreateFaultRecord : forall 'level ('write : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (Fault, bits(52), bits(1), int('level), AccType, bool('write), bits(1), bits(2), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {undef}

function AArch64_CreateFaultRecord (typ, ipaddress, NS, level, acctype, write, extflag, errortype, secondstage, s2fs1walk) = {
    fault : FaultRecord = undefined : FaultRecord;
    fault.typ = typ;
    fault.domain = undefined : bits(4);
    fault.debugmoe = undefined : bits(4);
    fault.errortype = errortype;
    __tc1 : FullAddress = fault.ipaddress;
    __tc1.NS = NS;
    fault.ipaddress = __tc1;
    __tc2 : FullAddress = fault.ipaddress;
    __tc2.address = ipaddress;
    fault.ipaddress = __tc2;
    fault.level = level;
    fault.acctype = acctype;
    fault.write = write;
    fault.extflag = extflag;
    fault.secondstage = secondstage;
    fault.s2fs1walk = s2fs1walk;
    fault
}

val AArch64_TranslationFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(52), bits(1), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {undef}

function AArch64_TranslationFault (ipaddress, NS, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let errortype = undefined : bits(2);
    AArch64_CreateFaultRecord(Fault_Translation, ipaddress, NS, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk)
}

val AArch64_PermissionFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(52), bits(1), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {undef}

function AArch64_PermissionFault (ipaddress, NS, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let errortype = undefined : bits(2);
    AArch64_CreateFaultRecord(Fault_Permission, ipaddress, NS, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk)
}

val AArch64_NoFault : unit -> FaultRecord effect {undef}

function AArch64_NoFault () = {
    let ipaddress = undefined : bits(52);
    let level = undefined : int;
    let acctype = AccType_NORMAL;
    let iswrite = undefined : bool;
    let extflag = undefined : bits(1);
    let errortype = undefined : bits(2);
    let secondstage = false;
    let s2fs1walk = false;
    AArch64_CreateFaultRecord(Fault_None, ipaddress, undefined : bits(1), level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk)
}

val AArch64_DebugFault : forall ('iswrite : Bool).
  (AccType, bool('iswrite)) -> FaultRecord effect {undef}

function AArch64_DebugFault (acctype, iswrite) = {
    let ipaddress = undefined : bits(52);
    let errortype = undefined : bits(2);
    let level = undefined : int;
    let extflag = undefined : bits(1);
    let secondstage = false;
    let s2fs1walk = false;
    AArch64_CreateFaultRecord(Fault_Debug, ipaddress, undefined : bits(1), level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk)
}

val AArch64_AlignmentFault : forall ('iswrite : Bool) ('secondstage : Bool).
  (AccType, bool('iswrite), bool('secondstage)) -> FaultRecord effect {undef}

function AArch64_AlignmentFault (acctype, iswrite, secondstage) = {
    let ipaddress = undefined : bits(52);
    let level = undefined : int;
    let extflag = undefined : bits(1);
    let errortype = undefined : bits(2);
    let s2fs1walk = undefined : bool;
    AArch64_CreateFaultRecord(Fault_Alignment, ipaddress, undefined : bits(1), level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk)
}

val AArch64_AddressSizeFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(52), bits(1), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {undef}

function AArch64_AddressSizeFault (ipaddress, NS, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let errortype = undefined : bits(2);
    AArch64_CreateFaultRecord(Fault_AddressSize, ipaddress, NS, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk)
}

val AArch64_AccessFlagFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(52), bits(1), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {undef}

function AArch64_AccessFlagFault (ipaddress, NS, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let errortype = undefined : bits(2);
    AArch64_CreateFaultRecord(Fault_AccessFlag, ipaddress, NS, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk)
}

val AArch32_PhysicalSErrorSyndrome : unit -> AArch32_SErrorSyndrome effect {undef}

function AArch32_PhysicalSErrorSyndrome () = {
    value_name : AArch32_SErrorSyndrome = undefined : AArch32_SErrorSyndrome;
    match AsynchronousErrorType() {
      AsyncErrorType_UC => {
          value_name.AET = 0b00
      },
      AsyncErrorType_UEU => {
          value_name.AET = 0b01
      },
      AsyncErrorType_UEO => {
          value_name.AET = 0b10
      },
      AsyncErrorType_UER => {
          value_name.AET = 0b11
      },
      AsyncErrorType_CE => {
          value_name.AET = 0b10
      }
    };
    value_name.ExT = 0b0;
    value_name
}

val set_TUBE : bits(32) -> unit effect {escape}

function set_TUBE val_name = {
    if UInt(val_name) == 4 then {
        prerr("Program exited by writing ^D to TUBE\n");
        exit(())
    } else {
        putchar(UInt(slice(val_name, 0, 8)))
    }
}

val __IMPDEF_integer_map : string -> int effect {escape}

function __IMPDEF_integer_map x = {
    match () {
      () if x == "Maximum Physical Address Size" => {
          return(52)
      },
      () if x == "Reserved Intermediate Physical Address size value" => {
          return(52)
      },
      () if x == "Maximum Virtual Address Size" => {
          return(52)
      },
      _ => {
          throw(Error_Implementation_Defined("Unrecognized integer"))
      }
    }
}

val __IMPDEF_integer : string -> int effect {escape}

function __IMPDEF_integer x = {
    __IMPDEF_integer_map(x)
}

val PAMax : unit -> int effect {escape}

function PAMax () = {
    __IMPDEF_integer("Maximum Physical Address Size")
}

val __IMPDEF_boolean_map : string -> bool effect {escape}

function __IMPDEF_boolean_map x = {
    match () {
      () if x == "Reserved Control Space Supported" => {
          return(true)
      },
      () if x == "Reserved Control Space Traps Supported" => {
          return(true)
      },
      () if x == "Reserved Control Space EL0 Trapped" => {
          return(true)
      },
      () if x == "Illegal Execution State on return to AArch32" => {
          return(true)
      },
      () if x == "Floating-Point Traps Support" => {
          return(true)
      },
      () if x == "Floating-Point Traps Information" => {
          return(true)
      },
      () if x == "Condition valid for trapped T32" => {
          return(false)
      },
      () if x == "Translation fault on misprogrammed contiguous bit" => {
          return(false)
      },
      () if x == "Virtual SError syndrome valid" => {
          return(false)
      },
      () if x == "Have CRC extension" => {
          return(true)
      },
      () if x == "Report I-cache maintenance fault in IFSR" => {
          return(false)
      },
      () if x == "UNDEF unallocated CP15 access at EL0" => {
          return(true)
      },
      () if x == "Align PC on illegal exception return" => {
          return(true)
      },
      () if x == "EL from SPSR on illegal exception return" => {
          return(false)
      },
      () if x == "Has AES Crypto instructions" => {
          return(__crypto_aes_implemented == 1 | __crypto_aes_implemented == 2)
      },
      () if x == "Has SHA1 Crypto instructions" => {
          return(__crypto_sha1_implemented)
      },
      () if x == "Has SHA256 Crypto instructions" => {
          return(__crypto_sha256_implemented)
      },
      () if x == "Has 128-bit form of PMULL instructions" => {
          return(__crypto_aes_implemented == 2)
      },
      () if x == "vector instructions set TFV to 1" => {
          return(true)
      },
      () if x == "Has accumulate FP16 product into FP32 extension" => {
          return(true)
      },
      () if x == "Has RAS extension" => {
          return(true)
      },
      () if x == "Has Implicit Error Synchronization Barrier" => {
          return(true)
      },
      () if x == "Implicit Error Synchronization Barrier before Exception" => {
          return(true)
      },
      () if x == "Has Dot Product extension" => {
          return(true)
      },
      () if x == "Has SHA512 Crypto instructions" => {
          return(__crypto_sha512_implemented)
      },
      () if x == "Has SHA3 Crypto instructions" => {
          return(__crypto_sha3_implemented)
      },
      () if x == "Has SM3 Crypto instructions" => {
          return(__crypto_sm3_implemented)
      },
      () if x == "Has SM4 Crypto instructions" => {
          return(__crypto_sm4_implemented)
      },
      () if x == "Has MPAM extension" => {
          return(__mpam_implemented)
      },
      () if x == "Has MTE extension" => {
          return(__mte_implemented)
      },
      () if x == "Has Small Page Table extension" => {
          return(true)
      },
      () if x == "Secure-only implementation" => {
          return(true)
      },
      () if x == "OS Double Lock is implemented" => {
          return(false)
      },
      _ => {
          throw(Error_Implementation_Defined("Unrecognized IMPLEMENTATION_DEFINED boolean"))
      }
    }
}

val __IMPDEF_boolean : string -> bool effect {escape}

function __IMPDEF_boolean x = {
    __IMPDEF_boolean_map(x)
}

val TLBContextMatch : (TLBContext, TLBContext) -> bool

function TLBContextMatch (a, b) = {
    (((((a.secondstage == b.secondstage & a.twostage == b.twostage) & a.asid == b.asid) & a.vmid == b.vmid) & a.el == b.el) & a.secure == b.secure) & a.t_sz == b.t_sz
}

register TCR_EL2 : bits(64)

val get_HTCR : unit -> bits(32) effect {rreg, undef}

function get_HTCR () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(TCR_EL2, 0, 32));
    r
}

val ReportTagCheckFail : (bits(2), bits(1)) -> unit effect {escape, rreg, wreg}

function ReportTagCheckFail (el, ttbr) = {
    if el == EL3 then {
        assert(ttbr == 0b0);
        TFSR_EL3 = __SetSlice_bits(32, 1, TFSR_EL3, 0, 0b1)
    } else {
        if el == EL2 then {
            if ttbr == 0b0 then {
                TFSR_EL2 = __SetSlice_bits(32, 1, TFSR_EL2, 0, 0b1)
            } else {
                TFSR_EL2 = __SetSlice_bits(32, 1, TFSR_EL2, 1, 0b1)
            }
        } else {
            if el == EL1 then {
                if ttbr == 0b0 then {
                    TFSR_EL1 = __SetSlice_bits(32, 1, TFSR_EL1, 0, 0b1)
                } else {
                    TFSR_EL1 = __SetSlice_bits(32, 1, TFSR_EL1, 1, 0b1)
                }
            } else {
                if el == EL0 then {
                    if ttbr == 0b0 then {
                        TFSRE0_EL1 = __SetSlice_bits(32, 1, TFSRE0_EL1, 0, 0b1)
                    } else {
                        TFSRE0_EL1 = __SetSlice_bits(32, 1, TFSRE0_EL1, 1, 0b1)
                    }
                }
            }
        }
    }
}

val MemAttrDefaults : MemoryAttributes -> MemoryAttributes effect {undef}

function MemAttrDefaults memattrs__arg = {
    memattrs = memattrs__arg;
    if memattrs.typ == MemType_Device then {
        memattrs.inner = undefined : MemAttrHints;
        memattrs.outer = undefined : MemAttrHints;
        memattrs.shareable = true;
        memattrs.outershareable = true
    } else {
        memattrs.device = undefined : DeviceType;
        if memattrs.inner.attrs == MemAttr_NC & memattrs.outer.attrs == MemAttr_NC then {
            memattrs.shareable = true;
            memattrs.outershareable = true
        }
    };
    memattrs
}

val HaveAnyAArch32 : unit -> bool

function HaveAnyAArch32 () = {
    ((CFG_ID_AA64PFR0_EL1_EL0 == 0x2 | CFG_ID_AA64PFR0_EL1_EL1 == 0x2) | CFG_ID_AA64PFR0_EL1_EL2 == 0x2) | CFG_ID_AA64PFR0_EL1_EL3 == 0x2
}

val HasArchVersion : ArchVersion -> bool

function HasArchVersion version = {
    ((((version == ARMv8p0 | version == ARMv8p1 & __v81_implemented) | version == ARMv8p2 & __v82_implemented) | version == ARMv8p3 & __v83_implemented) | version == ARMv8p4 & __v84_implemented) | version == ARMv8p5 & __v85_implemented
}

val HaveVirtHostExt : unit -> bool

function HaveVirtHostExt () = {
    HasArchVersion(ARMv8p1)
}

val HaveUAOExt : unit -> bool

function HaveUAOExt () = {
    HasArchVersion(ARMv8p2)
}

val HaveTrapLoadStoreMultipleDeviceExt : unit -> bool

function HaveTrapLoadStoreMultipleDeviceExt () = {
    HasArchVersion(ARMv8p2)
}

val HaveStage2MemAttrControl : unit -> bool

function HaveStage2MemAttrControl () = {
    HasArchVersion(ARMv8p4)
}

val HaveSmallPageTblExt : unit -> bool effect {escape}

function HaveSmallPageTblExt () = {
    HasArchVersion(ARMv8p4) & __IMPDEF_boolean("Has Small Page Table extension")
}

val HaveSecureEL2Ext : unit -> bool

function HaveSecureEL2Ext () = {
    HasArchVersion(ARMv8p4)
}

val HaveRASExt : unit -> bool effect {escape}

function HaveRASExt () = {
    HasArchVersion(ARMv8p2) | __IMPDEF_boolean("Has RAS extension")
}

val HaveIESB : unit -> bool effect {escape}

function HaveIESB () = {
    HaveRASExt() & __IMPDEF_boolean("Has Implicit Error Synchronization Barrier")
}

val InsertIESBBeforeException : bits(2) -> bool effect {escape}

function InsertIESBBeforeException el = {
    HaveIESB() & __IMPDEF_boolean("Implicit Error Synchronization Barrier before Exception")
}

val HavePrivATExt : unit -> bool

function HavePrivATExt () = {
    HasArchVersion(ARMv8p2)
}

val HavePANExt : unit -> bool

function HavePANExt () = {
    HasArchVersion(ARMv8p1)
}

val HavePACExt : unit -> bool

function HavePACExt () = {
    HasArchVersion(ARMv8p3)
}

val HaveNVExt : unit -> bool

function HaveNVExt () = {
    HasArchVersion(ARMv8p3)
}

val HaveNV2Ext : unit -> bool

function HaveNV2Ext () = {
    HasArchVersion(ARMv8p4)
}

val HaveMPAMExt : unit -> bool effect {escape}

function HaveMPAMExt () = {
    HasArchVersion(ARMv8p2) & __IMPDEF_boolean("Has MPAM extension")
}

val HaveExtendedExecuteNeverExt : unit -> bool

function HaveExtendedExecuteNeverExt () = {
    HasArchVersion(ARMv8p2)
}

val HaveE0PDExt : unit -> bool

function HaveE0PDExt () = {
    HasArchVersion(ARMv8p5)
}

val HaveDirtyBitModifierExt : unit -> bool

function HaveDirtyBitModifierExt () = {
    HasArchVersion(ARMv8p1)
}

val HaveDITExt : unit -> bool

function HaveDITExt () = {
    HasArchVersion(ARMv8p4)
}

val HaveCommonNotPrivateTransExt : unit -> bool

function HaveCommonNotPrivateTransExt () = {
    HasArchVersion(ARMv8p2)
}

val HaveBlockBBM : unit -> bool

function HaveBlockBBM () = {
    HasArchVersion(ARMv8p4)
}

val IsBlockDescriptorNTBitValid : unit -> bool

function IsBlockDescriptorNTBitValid () = {
    HaveBlockBBM() & (__GetSlice_int(4, __block_bbm_implemented, 0) == 0x1 | __GetSlice_int(4, __block_bbm_implemented, 0) == 0x2)
}

val HaveBTIExt : unit -> bool

function HaveBTIExt () = {
    HasArchVersion(ARMv8p5)
}

val HaveAccessFlagUpdateExt : unit -> bool

function HaveAccessFlagUpdateExt () = {
    HasArchVersion(ARMv8p1)
}

val Have52BitVAExt : unit -> bool

function Have52BitVAExt () = {
    HasArchVersion(ARMv8p2)
}

val AArch64_HaveHPDExt : unit -> bool

function AArch64_HaveHPDExt () = {
    HasArchVersion(ARMv8p1)
}

val AArch32_HaveHPDExt : unit -> bool

function AArch32_HaveHPDExt () = {
    HasArchVersion(ARMv8p2)
}

val GranuleSizeTG0 : bits(2) -> bits(2)

function GranuleSizeTG0 tg1 = {
    if tg1 == 0b10 then {
        return(0b00)
    } else {
        if tg1 == 0b01 then {
            return(0b10)
        } else {
            return(0b01)
        }
    }
}

val ExternalDebugEnabled : unit -> bool effect {rreg}

function ExternalDebugEnabled () = {
    DBGEN == HIGH
}

val EncodeSDFSC : forall ('level : Int).
  (Fault, int('level)) -> bits(5) effect {escape, undef}

function EncodeSDFSC (typ, level) = {
    result : bits(5) = undefined : bits(5);
    match typ {
      Fault_AccessFlag => {
          assert(level == 1 | level == 2);
          result = if level == 1 then 0b00011 else 0b00110
      },
      Fault_Alignment => {
          result = 0b00001
      },
      Fault_Permission => {
          assert(level == 1 | level == 2);
          result = if level == 1 then 0b01101 else 0b01111
      },
      Fault_Domain => {
          assert(level == 1 | level == 2);
          result = if level == 1 then 0b01001 else 0b01011
      },
      Fault_Translation => {
          assert(level == 1 | level == 2);
          result = if level == 1 then 0b00101 else 0b00111
      },
      Fault_SyncExternal => {
          result = 0b01000
      },
      Fault_SyncExternalOnWalk => {
          assert(level == 1 | level == 2);
          result = if level == 1 then 0b01100 else 0b01110
      },
      Fault_SyncParity => {
          result = 0b11001
      },
      Fault_SyncParityOnWalk => {
          assert(level == 1 | level == 2);
          result = if level == 1 then 0b11100 else 0b11110
      },
      Fault_AsyncParity => {
          result = 0b11000
      },
      Fault_AsyncExternal => {
          result = 0b10110
      },
      Fault_Debug => {
          result = 0b00010
      },
      Fault_TLBConflict => {
          result = 0b10000
      },
      Fault_Lockdown => {
          result = 0b10100
      },
      Fault_Exclusive => {
          result = 0b10101
      },
      Fault_ICacheMaint => {
          result = 0b00100
      },
      _ => {
          Unreachable()
      }
    };
    result
}

val ConstrainUnpredictableInteger : forall ('low : Int) ('high : Int).
  (int('low), int('high), Unpredictable) -> (Constraint, int) effect {undef}

function ConstrainUnpredictableInteger (low, high, which) = {
    let c = ConstrainUnpredictable(which);
    if c == Constraint_UNKNOWN then {
        return((c, low))
    } else {
        return((c, undefined : int))
    }
}

val ConstrainUnpredictableBool : Unpredictable -> bool effect {escape}

function ConstrainUnpredictableBool which = {
    let c : Constraint = ConstrainUnpredictable(which);
    assert(c == Constraint_TRUE | c == Constraint_FALSE);
    c == Constraint_TRUE
}

val CombineS1S2Device : (DeviceType, DeviceType) -> DeviceType effect {undef}

function CombineS1S2Device (s1device, s2device) = {
    result : DeviceType = undefined : DeviceType;
    if s2device == DeviceType_nGnRnE | s1device == DeviceType_nGnRnE then {
        result = DeviceType_nGnRnE
    } else {
        if s2device == DeviceType_nGnRE | s1device == DeviceType_nGnRE then {
            result = DeviceType_nGnRE
        } else {
            if s2device == DeviceType_nGRE | s1device == DeviceType_nGRE then {
                result = DeviceType_nGRE
            } else {
                result = DeviceType_GRE
            }
        }
    };
    result
}

val CombineS1S2AttrHints : (MemAttrHints, MemAttrHints) -> MemAttrHints effect {rreg, undef}

function CombineS1S2AttrHints (s1desc, s2desc) = {
    result : MemAttrHints = undefined : MemAttrHints;
    if HaveStage2MemAttrControl() & [HCR_EL2[46]] == 0b1 then {
        if s2desc.attrs == MemAttr_WB then {
            result.attrs = s1desc.attrs
        } else {
            if s2desc.attrs == MemAttr_WT then {
                result.attrs = MemAttr_WB
            } else {
                result.attrs = MemAttr_NC
            }
        }
    } else {
        if s2desc.attrs == 0b01 | s1desc.attrs == 0b01 then {
            result.attrs = undefined : bits(2)
        } else {
            if s2desc.attrs == MemAttr_NC | s1desc.attrs == MemAttr_NC then {
                result.attrs = MemAttr_NC
            } else {
                if s2desc.attrs == MemAttr_WT | s1desc.attrs == MemAttr_WT then {
                    result.attrs = MemAttr_WT
                } else {
                    result.attrs = MemAttr_WB
                }
            }
        }
    };
    result.hints = s1desc.hints;
    result.transient = s1desc.transient;
    result
}

val AArch64_InstructionDevice : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (AddressDescriptor, bits(64), bits(52), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> AddressDescriptor effect {escape, undef}

function AArch64_InstructionDevice (addrdesc__arg, vaddress, ipaddress, level, acctype, iswrite, secondstage, s2fs1walk) = {
    addrdesc = addrdesc__arg;
    let c = ConstrainUnpredictable(Unpredictable_INSTRDEVICE);
    assert(c == Constraint_NONE | c == Constraint_FAULT);
    if c == Constraint_FAULT then {
        addrdesc.fault = AArch64_PermissionFault(ipaddress, undefined : bits(1), level, acctype, iswrite, secondstage, s2fs1walk)
    } else {
        __tc1 : MemoryAttributes = addrdesc.memattrs;
        __tc1.typ = MemType_Normal;
        addrdesc.memattrs = __tc1;
        __tc2 : MemAttrHints = addrdesc.memattrs.inner;
        __tc2.attrs = MemAttr_NC;
        __tc3 : MemoryAttributes = addrdesc.memattrs;
        __tc3.inner = __tc2;
        addrdesc.memattrs = __tc3;
        __tc4 : MemAttrHints = addrdesc.memattrs.inner;
        __tc4.hints = MemHint_No;
        __tc5 : MemoryAttributes = addrdesc.memattrs;
        __tc5.inner = __tc4;
        addrdesc.memattrs = __tc5;
        __tc6 : MemoryAttributes = addrdesc.memattrs;
        __tc6.outer = addrdesc.memattrs.inner;
        addrdesc.memattrs = __tc6;
        __tc7 : MemoryAttributes = addrdesc.memattrs;
        __tc7.tagged = false;
        addrdesc.memattrs = __tc7;
        addrdesc.memattrs = MemAttrDefaults(addrdesc.memattrs)
    };
    addrdesc
}

val AArch64_AccessUsesEL : AccType -> bits(2) effect {rreg}

function AArch64_AccessUsesEL acctype = {
    if acctype == AccType_UNPRIV then {
        return(EL0)
    } else {
        if acctype == AccType_NV2REGISTER then {
            return(EL2)
        } else {
            return(PSTATE.EL)
        }
    }
}

val AArch32_AccessUsesEL : AccType -> bits(2) effect {rreg}

function AArch32_AccessUsesEL acctype = {
    if acctype == AccType_UNPRIV then {
        return(EL0)
    } else {
        return(PSTATE.EL)
    }
}

val LookUpRIndex : forall ('n : Int), ('n >= 0 & 'n <= 15).
  (int('n), bits(5)) -> {'m, (0 <= 'm & 'm <= 30). int('m)} effect {escape}

function LookUpRIndex (n, mode) = {
    assert(n >= 0 & n <= 14);
    match n {
      8 => RBankSelect(mode, 8, 24, 8, 8, 8, 8, 8),
      9 => RBankSelect(mode, 9, 25, 9, 9, 9, 9, 9),
      10 => RBankSelect(mode, 10, 26, 10, 10, 10, 10, 10),
      11 => RBankSelect(mode, 11, 27, 11, 11, 11, 11, 11),
      12 => RBankSelect(mode, 12, 28, 12, 12, 12, 12, 12),
      13 => RBankSelect(mode, 13, 29, 17, 19, 21, 23, 15),
      14 => RBankSelect(mode, 14, 30, 16, 18, 20, 22, 14),
      _ => n
    }
}

register _GTE_PPU_SizeEn : vector(6, dec, bits(32))

register _GTE_PPU_Address : vector(6, dec, bits(64))

register _GTE_PPU_Access : vector(6, dec, bits(32))

register _GTE_AS_RecordedData : vector(8, dec, bits(64))

register _GTE_AS_RecordedAddress : vector(8, dec, bits(64))

register _GTE_AS_RecordedAccess : vector(8, dec, bits(32))

register _GTEParam : vector(8, dec, bits(64))

val GTESetCriticalEvent : unit -> unit effect {rreg}

function GTESetCriticalEvent () = {
    let 'list_count = UInt(_GTEParam[0]);
    prerr("TODO: implement GTESetCriticalEvent\n");
    return()
}

val GTERandNum : unit -> unit effect {rreg}

function GTERandNum () = {
    let data = slice(_GTEParam[0], 0, 32);
    prerr("TODO: implement GTERandNum\n");
    return()
}

val GTEEventGenSetup : unit -> unit effect {rreg}

function GTEEventGenSetup () = {
    let handle = slice(_GTEParam[0], 0, 32);
    let event = slice(_GTEParam[1], 0, 32);
    let 'triggers_count = UInt(_GTEParam[2]);
    prerr("TODO: implement GTEEventGenSetup\n");
    return()
}

val GTEEventGenQuery : unit -> unit effect {rreg}

function GTEEventGenQuery () = {
    let handle = slice(_GTEParam[0], 0, 32);
    prerr("TODO: implement GTEEventGenQuery\n");
    return()
}

val GTEEventGenPrime : unit -> unit effect {rreg}

function GTEEventGenPrime () = {
    let handle = slice(_GTEParam[0], 0, 32);
    prerr("TODO: implement GTEEventGenPrime\n");
    return()
}

val GTEEventGenFree : unit -> unit effect {rreg}

function GTEEventGenFree () = {
    let handle = slice(_GTEParam[0], 0, 32);
    prerr("TODO: implement GTEEventGenFree\n");
    return()
}

val GTEEventGenDisable : unit -> unit effect {rreg}

function GTEEventGenDisable () = {
    let handle = slice(_GTEParam[0], 0, 32);
    prerr("TODO: implement GTEEventGenDisable\n");
    return()
}

val GTEEventGenClear : unit -> unit effect {rreg}

function GTEEventGenClear () = {
    let handle = slice(_GTEParam[0], 0, 32);
    prerr("TODO: implement GTEEventGenClear\n");
    return()
}

val GTEDeassert : unit -> unit effect {rreg}

function GTEDeassert () = {
    let cpus = slice(_GTEParam[0], 0, 32);
    prerr("TODO: implement GTEDeassert\n");
    return()
}

val GTEAssert : unit -> unit effect {rreg}

function GTEAssert () = {
    let 'triggers_count = UInt(_GTEParam[0]);
    let cpus = slice(_GTEParam[1], 0, 32);
    prerr("TODO: implement GTEAssert\n");
    return()
}

register _GTEListParam1 : vector(64, dec, bits(64))

register _GTEListParam0 : vector(64, dec, bits(64))

register _GTEExtObsResultIsAddress : vector(4, dec, bool)

register _GTEExtObsResultIndex : vector(4, dec, int)

register _GTEExtObsIndex : vector(4, dec, int)

register _GTEExtObsCount : vector(4, dec, int)

register _GTEExtObsActive : vector(4, dec, bool)

val GTEAllocExtObs : unit -> int effect {rreg, wreg}

function GTEAllocExtObs () = {
    foreach (i from 0 to (NUM_GTE_EXT_OBS_OBSERVERS - 1) by 1 in inc) {
        if _GTEExtObsActive[i] == false then {
            _GTEExtObsActive[i] = true;
            return(i)
        }
    };
    negate(1)
}

register configuration TAG_GRANULE : int = shl_int(1, LOG2_TAG_GRANULE_DEFAULT)

val GTESetPPURegion : unit -> unit effect {rreg, undef, wreg}

function GTESetPPURegion () = {
    prerr("GTESetPPURegion(region=" ++ DecStr(UInt(_GTEParam[0])));
    prerr(", addr=" ++ HexStr(UInt(_GTEParam[1])));
    prerr(", size_en=" ++ HexStr(UInt(slice(_GTEParam[2], 0, 32))));
    prerr(", access=" ++ HexStr(UInt(slice(_GTEParam[3], 0, 32))));
    prerr(")\n");
    let 'region = UInt(_GTEParam[0]);
    GTEStatus : bits(64) = undefined : bits(64);
    if region >= NUM_GTE_REGIONS then {
        GTEStatus = GTE_ST_REQUEST_FAIL;
        prerr("    region out of range\n");
        return()
    };
    _GTE_PPU_Address[region] = _GTEParam[1];
    _GTE_PPU_SizeEn[region] = slice(_GTEParam[2], 0, 32);
    _GTE_PPU_Access[region] = slice(_GTEParam[3], 0, 32);
    _GTEStatus = GTE_ST_REQUEST_GRANTED;
    return()
}

val GTEPPUControl : unit -> unit effect {rreg, wreg}

function GTEPPUControl () = {
    prerr("GTEPPUControl(region=" ++ DecStr(UInt(slice(_GTEParam[0], 0, 32))));
    prerr(", enable=" ++ DecStr(UInt([_GTEParam[1][0]])));
    prerr(")\n");
    let 'region = UInt(slice(_GTEParam[0], 0, 32));
    let enable = [_GTEParam[1][0]];
    if region >= NUM_GTE_REGIONS then {
        foreach (i from 0 to (NUM_GTE_REGIONS - 1) by 1 in inc) {
            __tc1 : bits(32) = _GTE_PPU_SizeEn[region];
            __tc1 = __SetSlice_bits(32, 1, __tc1, 0, enable);
            _GTE_PPU_SizeEn[region] = __tc1
        }
    } else {
        __tc2 : bits(32) = _GTE_PPU_SizeEn[region];
        __tc2 = __SetSlice_bits(32, 1, __tc2, 0, enable);
        _GTE_PPU_SizeEn[region] = __tc2
    };
    return()
}

val GTEGetPPURegion : unit -> unit effect {rreg, undef, wreg}

function GTEGetPPURegion () = {
    prerr("GTEGetPPURegion(region=" ++ DecStr(UInt(slice(_GTEParam[0], 0, 32))));
    prerr(")\n");
    let 'region = UInt(slice(_GTEParam[0], 0, 32));
    GTEStatus : bits(64) = undefined : bits(64);
    if region >= NUM_GTE_REGIONS then {
        prerr("   region out of range\n");
        GTEStatus = GTE_ST_REQUEST_FAIL;
        return()
    };
    _PPURBAR = _GTE_PPU_Address[region];
    _PPURSER = _GTE_PPU_SizeEn[region];
    _PPURACR = _GTE_PPU_Access[region];
    _GTEStatus = GTE_ST_REQUEST_GRANTED;
    return()
}

val GTEAddListParam : bits(64) -> unit effect {escape, rreg, wreg}

function GTEAddListParam val_name = {
    assert(_GTEListParam < 2);
    prerr("_GTEListParam[" ++ DecStr(_GTEListParam) ++ "][" ++ DecStr(_GTEListParamIndex) ++ "] = " ++ HexStr(UInt(val_name)) ++ "\n");
    if _GTEListParam == 0 then {
        _GTEListParam0[_GTEListParamIndex] = val_name
    } else {
        _GTEListParam1[_GTEListParamIndex] = val_name
    };
    _GTEListParamIndex = _GTEListParamIndex + 1;
    return()
}

val EncodeLDFSC : forall ('level : Int).
  (Fault, int('level)) -> bits(6) effect {escape, undef}

function EncodeLDFSC (typ, level) = {
    result : bits(6) = undefined : bits(6);
    match typ {
      Fault_AddressSize => {
          result = 0x0 @ __GetSlice_int(2, level, 0);
          assert(level == 0 | level == 1 | level == 2 | level == 3)
      },
      Fault_AccessFlag => {
          result = 0x2 @ __GetSlice_int(2, level, 0);
          assert(level == 1 | level == 2 | level == 3)
      },
      Fault_Permission => {
          result = 0x3 @ __GetSlice_int(2, level, 0);
          assert(level == 1 | level == 2 | level == 3)
      },
      Fault_Translation => {
          result = 0x1 @ __GetSlice_int(2, level, 0);
          assert(level == 0 | level == 1 | level == 2 | level == 3)
      },
      Fault_SyncExternal => {
          result = 0b010000
      },
      Fault_SyncExternalOnWalk => {
          result = 0x5 @ __GetSlice_int(2, level, 0);
          assert(level == 0 | level == 1 | level == 2 | level == 3)
      },
      Fault_SyncParity => {
          result = 0b011000
      },
      Fault_SyncParityOnWalk => {
          result = 0x7 @ __GetSlice_int(2, level, 0);
          assert(level == 0 | level == 1 | level == 2 | level == 3)
      },
      Fault_AsyncParity => {
          result = 0b011001
      },
      Fault_AsyncExternal => {
          result = 0b010001
      },
      Fault_Alignment => {
          result = 0b100001
      },
      Fault_Debug => {
          result = 0b100010
      },
      Fault_TLBConflict => {
          result = 0b110000
      },
      Fault_HWUpdateAccessFlag => {
          result = 0b110001
      },
      Fault_Lockdown => {
          result = 0b110100
      },
      Fault_Exclusive => {
          result = 0b110101
      },
      _ => {
          Unreachable()
      }
    };
    result
}

val BigEndianReverse : forall ('width : Int), 'width >= 0.
  bits('width) -> bits('width) effect {escape}

function BigEndianReverse value_name = {
    assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64 | 'width == 128);
    let 'half = 'width / 2;
    if 'width == 8 then {
        return(value_name)
    };
    BigEndianReverse(slice(value_name, 0, half)) @ BigEndianReverse(slice(value_name, half, 'width - half))
}

val __WriteMemory : forall ('N : Int).
  (AccType, option(TranslationInfo), int('N), bits(64), bits(56), bits(8 * 'N)) -> unit effect {rreg, wmem}

function __WriteMemory (acctype, translation_info, N, vaddress, paddress, val_name) = {
    if N > 0 then {
        match sail_mem_write(write_request(acctype, translation_info, N, vaddress, paddress, val_name)) {
            Ok(_) => (),
            Err(fault) => AArch64_Abort(vaddress, fault),
        }
    }
}

val __ReadMemory : forall ('N : Int), 'N > 0.
  (AccType, option(TranslationInfo), int('N), bits(64), bits(56)) -> bits(8 * 'N) effect {rmem, rreg}

function __ReadMemory (acctype, translation_info, N, vaddress, paddress) = {
    match sail_mem_read(read_request(acctype, translation_info, N, vaddress, paddress)) {
        Ok((value, _)) => value,
        Err(fault) => {
            AArch64_Abort(vaddress, fault);
            Zeros(8 * N)
        }
    }
}

val ThisInstrLength : unit -> int effect {rreg}

function ThisInstrLength () = {
    __currentInstrLength * 8
}

val AArch32_ExceptionClass : Exception -> (int, bits(1)) effect {escape, rreg, undef}

function AArch32_ExceptionClass typ = {
    il : bits(1) = undefined : bits(1);
    il = if ThisInstrLength() == 32 then 0b1 else 0b0;
    ec : int = undefined : int;
    match typ {
      Exception_Uncategorized => {
          ec = 0;
          il = 0b1
      },
      Exception_WFxTrap => {
          ec = 1
      },
      Exception_CP15RTTrap => {
          ec = 3
      },
      Exception_CP15RRTTrap => {
          ec = 4
      },
      Exception_CP14RTTrap => {
          ec = 5
      },
      Exception_CP14DTTrap => {
          ec = 6
      },
      Exception_AdvSIMDFPAccessTrap => {
          ec = 7
      },
      Exception_FPIDTrap => {
          ec = 8
      },
      Exception_PACTrap => {
          ec = 9
      },
      Exception_CP14RRTTrap => {
          ec = 12
      },
      Exception_BranchTarget => {
          ec = 13
      },
      Exception_IllegalState => {
          ec = 14;
          il = 0b1
      },
      Exception_SupervisorCall => {
          ec = 17
      },
      Exception_HypervisorCall => {
          ec = 18
      },
      Exception_MonitorCall => {
          ec = 19
      },
      Exception_ERetTrap => {
          ec = 26
      },
      Exception_InstructionAbort => {
          ec = 32;
          il = 0b1
      },
      Exception_PCAlignment => {
          ec = 34;
          il = 0b1
      },
      Exception_DataAbort => {
          ec = 36
      },
      Exception_NV2DataAbort => {
          ec = 37
      },
      Exception_FPTrappedException => {
          ec = 40
      },
      _ => {
          Unreachable()
      }
    };
    if (ec == 32 | ec == 36) & PSTATE.EL == EL2 then {
        ec = ec + 1
    };
    return((ec, il))
}

val AArch32_ReportHypEntry : ExceptionRecord -> unit effect {escape, rreg, undef, wreg}

function AArch32_ReportHypEntry exception = {
    let typ : Exception = exception.typ;
    ec : int = undefined : int;
    il : bits(1) = undefined : bits(1);
    (ec, il) = AArch32_ExceptionClass(typ);
    let iss : bits(25) = exception.syndrome;
    if (ec == 36 | ec == 37) & [iss[24]] == 0b0 then {
        il = 0b1
    };
    set_HSR((__GetSlice_int(6, ec, 0) @ il) @ iss);
    if typ == Exception_InstructionAbort | typ == Exception_PCAlignment then {
        set_HIFAR(slice(exception.vaddress, 0, 32));
        set_HDFAR(undefined : bits(32))
    } else {
        if typ == Exception_DataAbort then {
            set_HIFAR(undefined : bits(32));
            set_HDFAR(slice(exception.vaddress, 0, 32))
        }
    };
    if exception.ipavalid then {
        __tc1 : bits(32) = get_HPFAR();
        __tc1 = __SetSlice_bits(32, 28, __tc1, 4, slice(exception.ipaddress, 12, 28));
        set_HPFAR(__tc1)
    } else {
        __tc2 : bits(32) = get_HPFAR();
        __tc2 = __SetSlice_bits(32, 28, __tc2, 4, undefined : bits(28));
        set_HPFAR(__tc2)
    };
    return()
}

val set_ClearIRQ : bits(32) -> unit effect {rreg, wreg}

function set_ClearIRQ val_name = {
    _ClearIRQ = __SetSlice_bits(32, 32, _ClearIRQ, 0, val_name);
    if get_ClearIRQ() == Zeros(32) then {
        _IRQPending = false
    };
    return()
}

val set_ClearFIQ : bits(32) -> unit effect {rreg, wreg}

function set_ClearFIQ val_name = {
    _ClearFIQ = __SetSlice_bits(32, 32, _ClearFIQ, 0, val_name);
    if get_ClearFIQ() == Zeros(32) then {
        _FIQPending = false
    };
    return()
}

val mapvpmw : forall ('vpartid : Int).
  int('vpartid) -> bits(16) effect {rreg, undef}

function mapvpmw vpartid = {
    vpmw : bits(64) = undefined : bits(64);
    let 'wd = vpartid / 4;
    match wd {
      0 => {
          vpmw = MPAMVPM0_EL2
      },
      1 => {
          vpmw = MPAMVPM1_EL2
      },
      2 => {
          vpmw = MPAMVPM2_EL2
      },
      3 => {
          vpmw = MPAMVPM3_EL2
      },
      4 => {
          vpmw = MPAMVPM4_EL2
      },
      5 => {
          vpmw = MPAMVPM5_EL2
      },
      6 => {
          vpmw = MPAMVPM6_EL2
      },
      7 => {
          vpmw = MPAMVPM7_EL2
      },
      _ => {
          vpmw = Zeros(64)
      }
    };
    let vpmw = vpmw;
    let 'vpme_lsb = vpartid % 4 * 16;
    slice(vpmw, vpme_lsb, 16)
}

val get_TUBE : unit -> bits(32)

function get_TUBE () = {
    Zeros(32)
}

val get_PPURSER : unit -> bits(32) effect {rreg}

function get_PPURSER () = {
    if _GTEActive then {
        return(_PPURSER)
    } else {
        return(Zeros(32))
    }
}

val get_PPURBAR : unit -> bits(32) effect {rreg}

function get_PPURBAR () = {
    if _GTEActive then {
        return(slice(_PPURBAR, 0, 32))
    } else {
        return(Zeros(32))
    }
}

val get_PPURACR : unit -> bits(32) effect {rreg}

function get_PPURACR () = {
    if _GTEActive then {
        return(_PPURACR)
    } else {
        return(Zeros(32))
    }
}

val get_GTE_API_STATUS_64_HI : unit -> bits(32) effect {rreg}

function get_GTE_API_STATUS_64_HI () = {
    if _GTEActive then {
        return(slice(_GTEStatus, 32, 32))
    } else {
        return(Zeros(32))
    }
}

val get_GTE_API_STATUS_64 : unit -> bits(32) effect {rreg}

function get_GTE_API_STATUS_64 () = {
    if _GTEActive then {
        return(slice(_GTEStatus, 0, 32))
    } else {
        return(Zeros(32))
    }
}

val get_GTE_API_STATUS : unit -> bits(32) effect {rreg}

function get_GTE_API_STATUS () = {
    if _GTEActive then {
        return(slice(_GTEStatus, 0, 32))
    } else {
        return(Zeros(32))
    }
}

val get_GTE_API_PARAM_64_HI : unit -> bits(32) effect {rreg}

function get_GTE_API_PARAM_64_HI () = {
    if _GTEActive then {
        return(slice(_PPURBAR, 32, 32))
    } else {
        return(Zeros(32))
    }
}

val get_GTE_API_PARAM_64 : unit -> bits(32) effect {rreg}

function get_GTE_API_PARAM_64 () = {
    if _GTEActive then {
        return(slice(_PPURBAR, 0, 32))
    } else {
        return(Zeros(32))
    }
}

val get_GTE_API_PARAM : unit -> bits(32)

function get_GTE_API_PARAM () = {
    Zeros(32)
}

register configuration __mpam_vpmr_max : bits(3) = Zeros()

register configuration __mpam_pmg_max : bits(8) = Zeros()

register configuration __mpam_partid_max : bits(16) = Zeros()

val __IMPDEF_bits_map : forall ('N : Int), 'N >= 0.
  (int('N), string) -> bits('N) effect {escape}

function __IMPDEF_bits_map (N, x) = match () {
  () if x == "Virtual Asynchronous Abort ExT bit" => return(Zeros()),
  () if x == "FPEXC.EN value when TGE==1 and RW==0" => return(__GetSlice_int(N, 1, 0)),
  () if x == "MPAM version" => return(__GetSlice_int(N, UInt(CFG_ID_AA64PFR0_EL1_MPAM), 0)),
  () if x == "MPAM maximum PARTID" => return(__GetSlice_int(N, UInt(__mpam_partid_max), 0)),
  () if x == "MPAM maximum PMG" => return(__GetSlice_int(N, UInt(__mpam_pmg_max), 0)),
  () if x == "Has MPAMHCR_EL2" => return(if __mpam_has_hcr then __GetSlice_int(N, 1, 0) else Zeros()),
  () if x == "MPAM maximum VPMR" => return(__GetSlice_int(N, UInt(__mpam_vpmr_max), 0)),
  () if x == "reset vector address" => return(slice(CFG_RVBAR, 0, N)),
  _ => throw(Error_Implementation_Defined("Unrecognized bits(N)"))
}

val __IMPDEF_bits : forall ('N : Int), 'N >= 0.
  (int('N), string) -> bits('N) effect {escape}

function __IMPDEF_bits (N, x) = __IMPDEF_bits_map(N, x)

val ZeroExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0.
  (bits('M), int('N)) -> bits('N) effect {escape}

val ZeroExtend__1 : forall ('M : Int) ('N : Int), 'M >= 0.
  (implicit('N), bits('M)) -> bits('N) effect {escape}

overload ZeroExtend = {ZeroExtend__0, ZeroExtend__1}

function ZeroExtend__0 (x, N) = {
    assert(N >= 'M);
    Zeros(N - 'M) @ x
}

function ZeroExtend__1 (N, x) = ZeroExtend__0(x, N)

val get_ScheduleIRQ : unit -> bits(32) effect {escape, rreg}

function get_ScheduleIRQ () = let status : bits(1) = if IRQPending() then 0b1 else 0b0 in ZeroExtend(status)

val get_ScheduleFIQ : unit -> bits(32) effect {rreg, escape}

function get_ScheduleFIQ () = let status : bits(1) = if FIQPending() then 0b1 else 0b0 in ZeroExtend(status)

val _ReadTrickbox : forall 'address ('UNP : Bool) ('UP : Bool) ('PNP : Bool) ('PP : Bool).
  (int('address), bool('UNP), bool('UP), bool('PNP), bool('PP)) -> bits(32) effect {escape, rreg, undef}

function _ReadTrickbox (address, UNP, UP, PNP, PP) = {
    match address {
      0 if ((UNP | PNP) | UP) | PP => {
          return(get_TUBE())
      },
      8 if ((UNP | PNP) | UP) | PP => {
          return(get_ScheduleFIQ())
      },
      12 if ((UNP | PNP) | UP) | PP => {
          return(get_ScheduleIRQ())
      },
      256 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Lo1)
      },
      260 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Lo1_Hi)
      },
      264 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Hi1)
      },
      268 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Hi1_Hi)
      },
      272 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Lo2)
      },
      276 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Lo2_Hi)
      },
      280 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Hi2)
      },
      284 if ((UNP | PNP) | UP) | PP => {
          return(AbortRgn64Hi2_Hi)
      },
      1280 if ((UNP | PNP) | UP) | PP => {
          return(get_AXIAbortCtl())
      },
      2564 if ((UNP | PNP) | UP) | PP => {
          return(get_GTE_API_PARAM())
      },
      2568 if ((UNP | PNP) | UP) | PP => {
          return(get_GTE_API_STATUS())
      },
      2576 if ((UNP | PNP) | UP) | PP => {
          return(get_PPURBAR())
      },
      2580 if ((UNP | PNP) | UP) | PP => {
          return(get_PPURSER())
      },
      2584 if ((UNP | PNP) | UP) | PP => {
          return(get_PPURACR())
      },
      2592 if ((UNP | PNP) | UP) | PP => {
          return(get_GTE_API_STATUS_64())
      },
      2596 if ((UNP | PNP) | UP) | PP => {
          return(get_GTE_API_STATUS_64_HI())
      },
      2600 if ((UNP | PNP) | UP) | PP => {
          return(get_GTE_API_PARAM_64())
      },
      2604 if ((UNP | PNP) | UP) | PP => {
          return(get_GTE_API_PARAM_64_HI())
      },
      _ => {
          prerr("Undefined trickbox read at offset " ++ HexStr(address) ++ "\n");
          return(undefined : bits(32))
      }
    }
}

val TransformTag : bits(64) -> bits(4) effect {escape}

function TransformTag vaddr = let vtag : bits(4) = slice(vaddr, 56, 4) in let tagdelta : bits(4) = ZeroExtend([vaddr[55]]) in let ptag : bits(4) = vtag + tagdelta in ptag

/*
val LSR_C : forall ('N : Int) ('shift : Int), 'N >= 0.
  (bits('N), int('shift)) -> (bits('N), bits(1)) effect {escape}

function LSR_C (x, shift) = {
    assert(shift > 0);
    let (shift as 'S) : {'n, (0 <= 'n & 'n <= 'N). int('n)} = if shift > 'N then 'N else shift;
    let extended_x : bits('S + 'N) = ZeroExtend(x, shift + 'N);
    let result : bits('N) = slice(extended_x, shift, 'N);
    let carry_out : bits(1) = [extended_x[shift - 1]];
    return((result, carry_out))
}
*/
val LSR_C : forall 'N 'shift. (bits('N), int('shift)) -> (bits('N), bits(1))

function LSR_C (x, shift) = {
    let carry_out = if (shift > 0 & shift <= 'N) then x[shift - 1] else bitzero;
    (sail_shiftright(x, shift), [carry_out])
}

val LSR : forall ('N : Int) ('shift : Int), ('shift >= 0 & 'N >= 0).
  (bits('N), int('shift)) -> bits('N) effect {escape, undef}

function LSR (x, shift) = {
    assert(shift >= 0);
    __anon1 : bits(1) = undefined : bits(1);
    result : bits('N) = undefined : bits('N);
    if shift == 0 then result = x
    else (result, __anon1) = LSR_C(x, shift);
    result
}

val aget__MemTag : AddressDescriptor -> bits(4) effect {escape, rmem, rreg, undef}

function aget__MemTag desc = {
    let offset : bits(64) = ZeroExtend(desc.paddress.address);
    let log2_tag_granule = LOG2_TAG_GRANULE;
    assert(log2_tag_granule >= 0);
    let tag_index : bits(64) = LSR(offset, log2_tag_granule);
    let tagaddress : bits(56) = TAG_STORE_AREA + slice(tag_index, 0, 56);
    let tagbyte : bits(8) = __ReadMemory(AccType_TAG, None(), 1, desc.vaddress, ZeroExtend(tagaddress));
    slice(tagbyte, 0, 4)
}

overload _MemTag = {aget__MemTag}

val IsZero : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsZero x = {
    x == Zeros('N)
}

val GTEEnAccessSensitiveBEH : unit -> unit effect {rreg, wreg}

function GTEEnAccessSensitiveBEH () = {
    prerr("GTEEnAccessSensitiveBEH");
    prerr("( address=" ++ HexStr(UInt(_GTEParam[0])));
    prerr(", size=" ++ HexStr(UInt(_GTEParam[1])));
    prerr(", access=" ++ HexStr(UInt(slice(_GTEParam[2], 0, 32))));
    prerr(")\n");
    _GTE_AS_Address = _GTEParam[0];
    _GTE_AS_Size = _GTEParam[1];
    _GTE_AS_Access = slice(_GTEParam[2], 0, 32);
    _GTE_AS_AccessCount = 0;
    _GTEStatus = Zeros();
    return()
}

val ExceptionSyndrome : Exception -> ExceptionRecord effect {undef}

function ExceptionSyndrome typ = {
    r : ExceptionRecord = undefined : ExceptionRecord;
    r.typ = typ;
    r.syndrome = Zeros();
    r.vaddress = Zeros();
    r.ipavalid = false;
    r.NS = 0b0;
    r.ipaddress = Zeros();
    r
}

val ConstrainUnpredictableBits : forall ('width : Int).
  (implicit('width), Unpredictable) -> (Constraint, bits('width)) effect {undef}

function ConstrainUnpredictableBits (width, which) = {
    let c = ConstrainUnpredictable(which);
    if c == Constraint_UNKNOWN then {
        return((c, Zeros('width)))
    } else {
        return((c, undefined : bits('width)))
    }
}

val AArch64_PhysicalSErrorSyndrome : forall ('implicit_esb : Bool).
  bool('implicit_esb) -> bits(25)

function AArch64_PhysicalSErrorSyndrome implicit_esb = {
    syndrome : bits(25) = Zeros();
    syndrome = __SetSlice_bits(25, 1, syndrome, 24, 0b0);
    syndrome = __SetSlice_bits(25, 1, syndrome, 13, if implicit_esb then 0b1 else 0b0);
    match AsynchronousErrorType() {
      AsyncErrorType_UC => {
          syndrome = __SetSlice_bits(25, 3, syndrome, 10, 0b000)
      },
      AsyncErrorType_UEU => {
          syndrome = __SetSlice_bits(25, 3, syndrome, 10, 0b001)
      },
      AsyncErrorType_UEO => {
          syndrome = __SetSlice_bits(25, 3, syndrome, 10, 0b010)
      },
      AsyncErrorType_UER => {
          syndrome = __SetSlice_bits(25, 3, syndrome, 10, 0b011)
      },
      AsyncErrorType_CE => {
          syndrome = __SetSlice_bits(25, 3, syndrome, 10, 0b110)
      }
    };
    let syndrome = __SetSlice_bits(25, 6, syndrome, 0, 0b010001);
    syndrome
}

val SignExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0.
  (bits('M), int('N)) -> bits('N) effect {escape}

val SignExtend__1 : forall ('M : Int) ('N : Int), 'M >= 0.
  (implicit('N), bits('M)) -> bits('N) effect {escape}

overload SignExtend = {SignExtend__0, SignExtend__1}

function SignExtend__0 (x, N) = {
    assert(N >= 'M);
    replicate_bits([x['M - 1]], N - 'M) @ x
}

function SignExtend__1 (N, x) = {
    SignExtend(x, 'N)
}

val Ones : forall ('N : Int). implicit('N) -> bits('N)

function Ones N = replicate_bits(0b1, N)

register configuration sp_rel_access_pc : bits(64) = Ones(64)

val IsOnes : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsOnes x = {
    x == Ones('N)
}

let NUM_GTE_EXT_OBS_OBSERVATIONS : int(4 * 64) = NUM_GTE_EXT_OBS_OBSERVERS * NUM_GTE_EXT_OBS_OBSERVATIONS_PER_OBSERVER

register _GTEExtObsResult : vector(256, dec, bits(64))

register _GTEExtObsData : vector(256, dec, bits(64))

register _GTEExtObsAddress : vector(256, dec, bits(64))

register _GTEExtObsAccess : vector(256, dec, bits(16))

val GTEPerformExtObsCommon : forall ('observer : Int).
  int('observer) -> unit effect {rmem, rreg, undef, wmem, wreg}

function GTEPerformExtObsCommon observer = {
    let currentNS = 0b1;
    let 'procid = UInt(MPIDR_EL1);
    ok : bool = undefined : bool;
    foreach (i
    from _GTEExtObsIndex[observer]
    to (_GTEExtObsIndex[observer] + _GTEExtObsCount[observer] - 1)
    by 1
    in inc) {
        NS : bits(1) = undefined : bits(1);
        match slice(_GTEExtObsAccess[i], 5, 3) {
          ? if ? == GTE_EXT_OBS_OUTER_NS => {
              NS = 0b1
          },
          ? if ? == GTE_EXT_OBS_INNER_NS => {
              NS = 0b1
          },
          ? if ? == GTE_EXT_OBS_OUTER_S => {
              NS = 0b0
          },
          ? if ? == GTE_EXT_OBS_INNER_S => {
              NS = 0b0
          },
          _ => {
              prerr("TODO: GTE External observer requires 'current' security state\n");
              NS = currentNS
          }
        };
        let NS = NS;
        match slice(_GTEExtObsAccess[i], 0, 3) {
          ? if ? == GTE_EXT_OBS_ACC_READ => {
              data : bits(64) = Zeros(64);
              ok = true;
              match slice(_GTEExtObsAccess[i], 8, 3) {
                ? if ? == GTE_EXT_OBS_ACC_SIZE64 => {
                    data = __SetSlice_bits(64, 64, data, 0, __ReadMemory(AccType_NORMAL, None(), 8, Zeros(), slice(_GTEExtObsAddress[i], 0, 56)))
                },
                ? if ? == GTE_EXT_OBS_ACC_SIZE32 => {
                    data = __SetSlice_bits(64, 32, data, 0, __ReadMemory(AccType_NORMAL, None(), 4, Zeros(), slice(_GTEExtObsAddress[i], 0, 56)))
                },
                ? if ? == GTE_EXT_OBS_ACC_SIZE16 => {
                    data = __SetSlice_bits(64, 16, data, 0, __ReadMemory(AccType_NORMAL, None(), 2, Zeros(), slice(_GTEExtObsAddress[i], 0, 56)))
                },
                ? if ? == GTE_EXT_OBS_ACC_SIZE8 => {
                    data = __SetSlice_bits(64, 8, data, 0, __ReadMemory(AccType_NORMAL, None(), 1, Zeros(), slice(_GTEExtObsAddress[i], 0, 56)))
                },
                _ => {
                    ok = false
                }
              };
              if ok then {
                  _GTEExtObsResult[i] = data
              } else {
                  _GTEExtObsResult[i] = GTE_ST_REQUEST_FAIL
              }
          },
          ? if ? == GTE_EXT_OBS_ACC_WRITE => {
              ok = true;
              let addr = _GTEExtObsAddress[i];
              match slice(_GTEExtObsAccess[i], 8, 3) {
                ? if ? == GTE_EXT_OBS_ACC_SIZE64 => {
                    __WriteMemory(AccType_NORMAL, None(), 8, addr, slice(addr, 0, 56), slice(_GTEExtObsData[i], 0, 64))
                },
                ? if ? == GTE_EXT_OBS_ACC_SIZE32 => {
                    __WriteMemory(AccType_NORMAL, None(), 4, addr, slice(addr, 0, 56), slice(_GTEExtObsData[i], 0, 32))
                },
                ? if ? == GTE_EXT_OBS_ACC_SIZE16 => {
                    __WriteMemory(AccType_NORMAL, None(), 2, addr, slice(addr, 0, 56), slice(_GTEExtObsData[i], 0, 16))
                },
                ? if ? == GTE_EXT_OBS_ACC_SIZE8 => {
                    __WriteMemory(AccType_NORMAL, None(), 1, addr, slice(addr, 0, 56), slice(_GTEExtObsData[i], 0, 8))
                },
                _ => {
                    ok = false
                }
              };
              if ok then {
                  _GTEExtObsResult[i] = GTE_ST_REQUEST_GRANTED
              } else {
                  _GTEExtObsResult[i] = GTE_ST_REQUEST_FAIL
              }
          },
          _ => {
              _GTEExtObsResult[i] = GTE_ST_REQUEST_FAIL
          }
        }
    };
    return()
}

val MAP_vPARTID : bits(16) -> (bits(16), bool) effect {rreg, undef}

function MAP_vPARTID vpartid = {
    ret : bits(16) = undefined : bits(16);
    err : bool = undefined : bool;
    virt : int = UInt(vpartid);
    let 'vmprmax = UInt(slice(MPAMIDR_EL1, 18, 3));
    let 'vpartid_max = 4 * vmprmax + 3;
    if virt > vpartid_max then {
        virt = virt % (vpartid_max + 1)
    };
    if [MPAMVPMV_EL2[virt]] == 0b1 then {
        ret = mapvpmw(virt);
        err = false
    } else {
        if [MPAMVPMV_EL2[0]] == 0b1 then {
            ret = slice(MPAMVPM0_EL2, 0, 16);
            err = false
        } else {
            ret = DefaultPARTID;
            err = true
        }
    };
    let 'partid_max = UInt(slice(MPAMIDR_EL1, 0, 16));
    if UInt(ret) > partid_max then {
        ret = DefaultPARTID;
        err = true
    };
    return((ret, err))
}

val GTESetupExtObs64 : unit -> unit effect {rreg, wreg}

function GTESetupExtObs64 () = {
    let 'access_count = UInt(_GTEParam[0]);
    let 'address_data_count = UInt(_GTEParam[1]);
    prerr("GTESetupExtObs64(accesses=(");
    foreach (i from 0 to (access_count - 1) by 1 in inc) {
        prerr(HexStr(UInt(_GTEListParam0[i])) ++ " ")
    };
    prerr("), address_data=(");
    foreach (i from 0 to (address_data_count - 1) by 1 in inc) {
        prerr(HexStr(UInt(_GTEListParam1[i])) ++ " ")
    };
    prerr("))\n");
    if access_count == 0 then {
        prerr("  access list empty\n");
        _GTEStatus = Ones(64);
        return()
    };
    let 'num_addresses = UInt(slice(_GTEListParam0[0], 0, 8));
    if address_data_count < num_addresses * 2 then {
        prerr("address/data list too short\n");
        _GTEStatus = Ones(64);
        return()
    };
    if access_count * 4 - 1 < num_addresses then {
        prerr("  access list too short\n");
        _GTEStatus = Ones(64);
        return()
    };
    let 'observer = GTEAllocExtObs();
    if observer == negate(1) then {
        _GTEStatus = Ones(64);
        return()
    };
    let 'ibase = NUM_GTE_EXT_OBS_OBSERVATIONS_PER_OBSERVER * observer;
    ai : int = 8;
    foreach (i from 0 to (num_addresses - 1) by 1 in inc) {
        let access_lo : bits(8) = slice(_GTEListParam0[shr_int(ai, 6)], ai % 64, 8);
        ai = ai + 8;
        let access_hi : bits(8) = slice(_GTEListParam0[shr_int(ai, 6)], ai % 64, 8);
        ai = ai + 8;
        _GTEExtObsAccess[ibase + i] = access_hi @ access_lo;
        _GTEExtObsAddress[ibase + i] = _GTEListParam1[i * 2];
        _GTEExtObsData[ibase + i] = _GTEListParam1[i * 2 + 1]
    };
    _GTEExtObsCount[observer] = num_addresses;
    _GTEExtObsIndex[observer] = ibase;
    _GTEExtObsResultIndex[observer] = ibase;
    _GTEExtObsResultIsAddress[observer] = true;
    _GTEStatus = __GetSlice_int(64, 1, 0);
    return()
}

val GTESetupExtObs : unit -> unit effect {rreg, wreg}

function GTESetupExtObs () = {
    let 'address_data_count = UInt(_GTEParam[0]);
    let 'access_count = UInt(_GTEParam[1]);
    prerr("GTESetupExtObs(address_data=(");
    foreach (i from 0 to (address_data_count - 1) by 1 in inc) {
        prerr(HexStr(UInt(slice(_GTEListParam0[i], 0, 32))) ++ " ")
    };
    prerr("), accesses=(");
    foreach (i from 0 to (access_count - 1) by 1 in inc) {
        prerr(HexStr(UInt(slice(_GTEListParam1[i], 0, 32))) ++ " ")
    };
    prerr("))\n");
    if access_count == 0 then {
        prerr("   ERROR: zero accesses provided\n");
        _GTEStatus = Ones(64);
        return()
    };
    let 'num_addresses = UInt(slice(_GTEListParam1[0], 0, 8));
    if address_data_count < num_addresses * 2 then {
        prerr("    ERROR: address/data count mismatch\n");
        _GTEStatus = Ones(64);
        return()
    };
    if access_count * 4 - 1 < num_addresses then {
        prerr("    ERROR: address/count mismatch\n");
        _GTEStatus = Ones(64);
        return()
    };
    let 'observer = GTEAllocExtObs();
    if observer == negate(1) then {
        prerr("    no more observers\n");
        _GTEStatus = Ones(64);
        return()
    };
    let 'ibase = NUM_GTE_EXT_OBS_OBSERVATIONS_PER_OBSERVER * observer;
    ai : int = 8;
    foreach (i from 0 to (num_addresses - 1) by 1 in inc) {
        let access : bits(8) = slice(_GTEListParam1[shr_int(ai, 5)], ai % 32, 8);
        ai = ai + 8;
        _GTEExtObsAccess[ibase + i] = Zeros(8) @ access;
        _GTEExtObsAddress[ibase + i] = _GTEListParam0[i * 2];
        _GTEExtObsData[ibase + i] = _GTEListParam0[i * 2 + 1]
    };
    _GTEExtObsCount[observer] = num_addresses;
    _GTEExtObsIndex[observer] = ibase;
    _GTEExtObsResultIndex[observer] = ibase;
    _GTEExtObsResultIsAddress[observer] = true;
    _GTEStatus = Zeros(64);
    return()
}

val Align__0 : forall ('x : Int) ('y : Int). (int('x), int('y)) -> int

val Align__1 : forall ('N : Int) ('y : Int). (bits('N), int('y)) -> bits('N)

overload Align = {Align__0, Align__1}

function Align__0 (x, y) = y * (x / y)

function Align__1 (x, y) = {
  assert(length(x) > 0 & y > 0);
  align_bits(x, y)
}

val aset_ELR__0 : (bits(2), bits(64)) -> unit effect {escape, wreg}

val aset_ELR__1 : bits(64) -> unit effect {escape, rreg, wreg}

overload aset_ELR = {aset_ELR__0, aset_ELR__1}

overload ELR = {aset_ELR__0, aset_ELR__1}

function aset_ELR__0 (el, value_name) = let r : bits(64) = value_name in {
    match el {
      ? if ? == EL1 => ELR_EL1 = r,
      ? if ? == EL2 => ELR_EL2 = r,
      ? if ? == EL3 => ELR_EL3 = r,
      _ => Unreachable()
    };
    return()
}

function aset_ELR__1 value_name = {
    assert(PSTATE.EL != EL0);
    aset_ELR(PSTATE.EL, value_name);
    return()
}

val IsSecondStage : FaultRecord -> bool effect {escape}

function IsSecondStage fault = {
    assert(fault.typ != Fault_None);
    fault.secondstage
}

val IsSErrorInterrupt__0 : Fault -> bool effect {escape}

val IsSErrorInterrupt__1 : FaultRecord -> bool effect {escape}

overload IsSErrorInterrupt = {IsSErrorInterrupt__0, IsSErrorInterrupt__1}

function IsSErrorInterrupt__0 typ = {
    assert(typ != Fault_None);
    typ == Fault_AsyncExternal | typ == Fault_AsyncParity
}

function IsSErrorInterrupt__1 fault = {
    IsSErrorInterrupt(fault.typ)
}

val IsFault : AddressDescriptor -> bool

function IsFault addrdesc = {
    addrdesc.fault.typ != Fault_None
}

val CombineS1S2Desc : (AddressDescriptor, AddressDescriptor) -> AddressDescriptor effect {rreg, undef}

function CombineS1S2Desc (s1desc, s2desc) = {
    result : AddressDescriptor = undefined : AddressDescriptor;
    result.fault = AArch64_NoFault();
    result.paddress = s2desc.paddress;
    if IsFault(s1desc) | IsFault(s2desc) then {
        result = if IsFault(s1desc) then s1desc else s2desc
    } else {
        if s2desc.memattrs.typ == MemType_Device | s1desc.memattrs.typ == MemType_Device then {
            __tc1 : MemoryAttributes = result.memattrs;
            __tc1.typ = MemType_Device;
            result.memattrs = __tc1;
            if s1desc.memattrs.typ == MemType_Normal then {
                __tc2 : MemoryAttributes = result.memattrs;
                __tc2.device = s2desc.memattrs.device;
                result.memattrs = __tc2
            } else {
                if s2desc.memattrs.typ == MemType_Normal then {
                    __tc3 : MemoryAttributes = result.memattrs;
                    __tc3.device = s1desc.memattrs.device;
                    result.memattrs = __tc3
                } else {
                    __tc4 : MemoryAttributes = result.memattrs;
                    __tc4.device = CombineS1S2Device(s1desc.memattrs.device, s2desc.memattrs.device);
                    result.memattrs = __tc4
                }
            };
            __tc5 : MemoryAttributes = result.memattrs;
            __tc5.tagged = false;
            result.memattrs = __tc5
        } else {
            __tc6 : MemoryAttributes = result.memattrs;
            __tc6.typ = MemType_Normal;
            result.memattrs = __tc6;
            __tc7 : MemoryAttributes = result.memattrs;
            __tc7.device = undefined : DeviceType;
            result.memattrs = __tc7;
            __tc8 : MemoryAttributes = result.memattrs;
            __tc8.inner = CombineS1S2AttrHints(s1desc.memattrs.inner, s2desc.memattrs.inner);
            result.memattrs = __tc8;
            __tc9 : MemoryAttributes = result.memattrs;
            __tc9.outer = CombineS1S2AttrHints(s1desc.memattrs.outer, s2desc.memattrs.outer);
            result.memattrs = __tc9;
            __tc10 : MemoryAttributes = result.memattrs;
            __tc10.shareable = s1desc.memattrs.shareable | s2desc.memattrs.shareable;
            result.memattrs = __tc10;
            __tc11 : MemoryAttributes = result.memattrs;
            __tc11.outershareable = s1desc.memattrs.outershareable | s2desc.memattrs.outershareable;
            result.memattrs = __tc11;
            __tc12 : MemoryAttributes = result.memattrs;
            __tc12.tagged = (((s1desc.memattrs.tagged & result.memattrs.inner.attrs == MemAttr_WB) & result.memattrs.inner.hints == MemHint_RWA) & result.memattrs.outer.attrs == MemAttr_WB) & result.memattrs.outer.hints == MemHint_RWA;
            result.memattrs = __tc12
        }
    };
    result.memattrs = MemAttrDefaults(result.memattrs);
    result
}

val IsExternalSyncAbort__0 : Fault -> bool effect {escape}

val IsExternalSyncAbort__1 : FaultRecord -> bool effect {escape}

overload IsExternalSyncAbort = {IsExternalSyncAbort__0, IsExternalSyncAbort__1}

function IsExternalSyncAbort__0 typ = {
    assert(typ != Fault_None);
    typ == Fault_SyncExternal | typ == Fault_SyncParity | typ == Fault_SyncExternalOnWalk | typ == Fault_SyncParityOnWalk
}

function IsExternalSyncAbort__1 fault = {
    IsExternalSyncAbort(fault.typ)
}

val IsExternalAbort__0 : Fault -> bool effect {escape}

val IsExternalAbort__1 : FaultRecord -> bool effect {escape}

overload IsExternalAbort = {IsExternalAbort__0, IsExternalAbort__1}

function IsExternalAbort__0 typ = {
    assert(typ != Fault_None);
    typ == Fault_SyncExternal | typ == Fault_SyncParity | typ == Fault_SyncExternalOnWalk | typ == Fault_SyncParityOnWalk | typ == Fault_AsyncExternal | typ == Fault_AsyncParity
}

function IsExternalAbort__1 fault = {
    IsExternalAbort(fault.typ)
}

val IsDebugException : FaultRecord -> bool effect {escape}

function IsDebugException fault = {
    assert(fault.typ != Fault_None);
    fault.typ == Fault_Debug
}

val IsAsyncAbort__0 : Fault -> bool effect {escape}

val IsAsyncAbort__1 : FaultRecord -> bool effect {escape}

overload IsAsyncAbort = {IsAsyncAbort__0, IsAsyncAbort__1}

function IsAsyncAbort__0 typ = {
    assert(typ != Fault_None);
    typ == Fault_AsyncExternal | typ == Fault_AsyncParity
}

function IsAsyncAbort__1 fault = {
    IsAsyncAbort(fault.typ)
}

val IPAValid : FaultRecord -> bool effect {escape}

function IPAValid fault = {
    assert(fault.typ != Fault_None);
    if fault.s2fs1walk then {
        return(fault.typ == Fault_AccessFlag | fault.typ == Fault_Permission | fault.typ == Fault_Translation | fault.typ == Fault_AddressSize)
    } else {
        if fault.secondstage then {
            return(fault.typ == Fault_AccessFlag | fault.typ == Fault_Translation | fault.typ == Fault_AddressSize)
        } else {
            return(false)
        }
    }
}

val HaveEL : bits(2) -> bool effect {escape}

function HaveEL el = {
    if el == EL1 | el == EL0 then {
        return(true)
    } else {
        if el == EL2 then {
            return(CFG_ID_AA64PFR0_EL1_EL2 != 0x0)
        } else {
            if el == EL3 then {
                return(CFG_ID_AA64PFR0_EL1_EL3 != 0x0)
            } else {
                assert(false);
                false
            }
        }
    }
}

val aget_SCR_GEN : unit -> bits(32) effect {escape, rreg, undef}

function aget_SCR_GEN () = {
    assert(HaveEL(EL3));
    r : bits(32) = undefined : bits(32);
    if HighestELUsingAArch32() then {
        r = get_SCR()
    } else {
        r = SCR_EL3
    };
    r
}

overload SCR_GEN = {aget_SCR_GEN}

val HighestEL : unit -> bits(2) effect {escape}

function HighestEL () = {
    if HaveEL(EL3) then {
        return(EL3)
    } else {
        if HaveEL(EL2) then {
            return(EL2)
        } else {
            return(EL1)
        }
    }
}

val MPAMisEnabled : unit -> bool effect {escape, rreg}

function MPAMisEnabled () = {
    let el = HighestEL();
    match el {
      ? if ? == EL3 => {
          return([MPAM3_EL3[63]] == 0b1)
      },
      ? if ? == EL2 => {
          return([MPAM2_EL2[63]] == 0b1)
      },
      ? if ? == EL1 => {
          return([MPAM1_EL1[63]] == 0b1)
      }
    }
}

val Have16bitVMID : unit -> bool effect {escape}

function Have16bitVMID () = {
    HaveEL(EL2) & __IMPDEF_boolean("")
}

val GTEOnesTerminatedListParam : unit -> unit effect {rreg, wreg}

function GTEOnesTerminatedListParam () = {
    if _GTEParamType != GTEParam_LIST then {
        _GTEParamType = GTEParam_LIST;
        _GTEListParamIndex = 0;
        _GTEListParamTerminator = Ones(64);
        _GTEListParamTerminators = 1;
        _GTEListParamTerminatorCount = 0
    }
}

val GTEListParam : unit -> unit effect {rreg, wreg}

function GTEListParam () = {
    if _GTEParamType != GTEParam_LIST then {
        _GTEParamType = GTEParam_LIST;
        _GTEListParamIndex = 0;
        _GTEListParamTerminator = Zeros(64);
        _GTEListParamTerminators = 1;
        _GTEListParamTerminatorCount = 0
    }
}

val GTEExtObsAddrDataListParam : unit -> unit effect {rreg, wreg}

function GTEExtObsAddrDataListParam () = {
    if _GTEParamType != GTEParam_LIST then {
        _GTEParamType = GTEParam_LIST;
        _GTEListParamIndex = 0;
        _GTEListParamTerminator = Zeros(64);
        _GTEListParamTerminators = 1;
        _GTEListParamTerminatorCount = 0
    }
}

val GTEExtObsAccessListParam : unit -> unit effect {rreg, wreg}

function GTEExtObsAccessListParam () = {
    if _GTEParamType != GTEParam_EOACCESS then {
        prerr("** starting EOACCESS list\n");
        _GTEParamType = GTEParam_EOACCESS;
        _GTEListParamIndex = 0;
        _GTEListParamTerminator = Zeros(64)
    }
}

val GTEChkAccessSensitiveBEH : unit -> unit effect {rreg, wreg}

function GTEChkAccessSensitiveBEH () = {
    let 'list_count = UInt(_GTEParam[0]);
    let 'address_count = list_count / 3;
    prerr("GTEChkAccessSensitiveBEH(");
    foreach (i from 0 to (address_count - 1) by 1 in inc) {
        prerr("( address=" ++ HexStr(UInt(_GTEListParam0[i * 3])));
        prerr(", access=" ++ HexStr(UInt(_GTEListParam0[i * 3 + 1])));
        prerr(", data=" ++ HexStr(UInt(_GTEListParam0[i * 3 + 2])));
        prerr("), ")
    };
    prerr(")\n");
    foreach (i from 0 to (address_count - 1) by 1 in inc) {
        if ((i >= _GTE_AS_AccessCount | _GTE_AS_RecordedAddress[i] != _GTEListParam0[i * 3]) | _GTE_AS_RecordedAccess[i] != slice(_GTEListParam0[i * 3 + 1], 0, 32)) | _GTE_AS_RecordedData[i] != _GTEListParam0[i * 3 + 2] then {
            _GTEStatus = __SetSlice_bits(64, 1, _GTEStatus, i, 0b1)
        }
    };
    _GTE_AS_AccessCount = 0;
    _GTEStatus = __SetSlice_bits(64, negate(address_count) + 64, _GTEStatus, address_count, Zeros());
    return()
}

val EffectiveTCF : bits(2) -> bits(2) effect {rreg, undef}

function EffectiveTCF el = {
    tcf : bits(2) = undefined : bits(2);
    if el == EL3 then {
        tcf = slice(SCTLR_EL3, 40, 2)
    } else {
        if el == EL2 then {
            tcf = slice(SCTLR_EL2, 40, 2)
        } else {
            if el == EL1 then {
                tcf = slice(SCTLR_EL1, 40, 2)
            } else {
                if el == EL0 & (HCR_EL2[34 .. 34] @ HCR_EL2[27 .. 27]) == 0b11 then {
                    tcf = slice(SCTLR_EL2, 38, 2)
                } else {
                    if el == EL0 & (HCR_EL2[34 .. 34] @ HCR_EL2[27 .. 27]) != 0b11 then {
                        tcf = slice(SCTLR_EL1, 38, 2)
                    }
                }
            }
        }
    };
    tcf
}

val AllocationTagAccessIsEnabled : unit -> bool effect {rreg}

function AllocationTagAccessIsEnabled () = {
    if [SCR_EL3[26]] == 0b0 & (PSTATE.EL == EL0 | PSTATE.EL == EL1 | PSTATE.EL == EL2) then {
        return(false)
    } else {
        if ([HCR_EL2[56]] == 0b0 & (HCR_EL2[34 .. 34] @ HCR_EL2[27 .. 27]) != 0b11) & (PSTATE.EL == EL0 | PSTATE.EL == EL1) then {
            return(false)
        } else {
            if [SCTLR_EL3[43]] == 0b0 & PSTATE.EL == EL3 then {
                return(false)
            } else {
                if [SCTLR_EL2[43]] == 0b0 & PSTATE.EL == EL2 then {
                    return(false)
                } else {
                    if [SCTLR_EL1[43]] == 0b0 & PSTATE.EL == EL1 then {
                        return(false)
                    } else {
                        if ([SCTLR_EL2[42]] == 0b0 & (HCR_EL2[34 .. 34] @ HCR_EL2[27 .. 27]) == 0b11) & PSTATE.EL == EL0 then {
                            return(false)
                        } else {
                            if ([SCTLR_EL1[42]] == 0b0 & (HCR_EL2[34 .. 34] @ HCR_EL2[27 .. 27]) != 0b11) & PSTATE.EL == EL0 then {
                                return(false)
                            } else {
                                return(true)
                            }
                        }
                    }
                }
            }
        }
    }
}

val AArch32_FaultStatusSD : forall ('d_side : Bool).
  (bool('d_side), FaultRecord) -> bits(32) effect {escape, undef}

function AArch32_FaultStatusSD (d_side, fault) = {
    assert(fault.typ != Fault_None);
    fsr : bits(32) = Zeros();
    if HaveRASExt() & IsAsyncAbort(fault) then {
        fsr = __SetSlice_bits(32, 2, fsr, 14, fault.errortype)
    };
    if d_side then {
        if fault.acctype == AccType_DC | fault.acctype == AccType_IC | fault.acctype == AccType_AT then {
            fsr = __SetSlice_bits(32, 1, fsr, 13, 0b1);
            fsr = __SetSlice_bits(32, 1, fsr, 11, 0b1)
        } else {
            fsr = __SetSlice_bits(32, 1, fsr, 11, if fault.write then 0b1 else 0b0)
        }
    };
    if IsExternalAbort(fault) then {
        fsr = __SetSlice_bits(32, 1, fsr, 12, fault.extflag)
    };
    fsr = __SetSlice_bits(32, 1, fsr, 9, 0b0);
    (fsr[10 .. 10] @ fsr[3 .. 0]) = EncodeSDFSC(fault.typ, fault.level);
    if d_side then {
        fsr = __SetSlice_bits(32, 4, fsr, 4, fault.domain)
    };
    fsr
}

val AArch32_FaultStatusLD : forall ('d_side : Bool).
  (bool('d_side), FaultRecord) -> bits(32) effect {escape, undef}

function AArch32_FaultStatusLD (d_side, fault) = {
    assert(fault.typ != Fault_None);
    fsr : bits(32) = Zeros();
    if HaveRASExt() & IsAsyncAbort(fault) then {
        fsr = __SetSlice_bits(32, 2, fsr, 14, fault.errortype)
    };
    if d_side then {
        if fault.acctype == AccType_DC | fault.acctype == AccType_IC | fault.acctype == AccType_AT then {
            fsr = __SetSlice_bits(32, 1, fsr, 13, 0b1);
            fsr = __SetSlice_bits(32, 1, fsr, 11, 0b1)
        } else {
            fsr = __SetSlice_bits(32, 1, fsr, 11, if fault.write then 0b1 else 0b0)
        }
    };
    if IsExternalAbort(fault) then {
        fsr = __SetSlice_bits(32, 1, fsr, 12, fault.extflag)
    };
    fsr = __SetSlice_bits(32, 1, fsr, 9, 0b1);
    let fsr = __SetSlice_bits(32, 6, fsr, 0, EncodeLDFSC(fault.typ, fault.level));
    fsr
}

val AArch32_DomainValid : forall ('level : Int).
  (Fault, int('level)) -> bool effect {escape}

function AArch32_DomainValid (typ, level) = {
    assert(typ != Fault_None);
    match typ {
      Fault_Domain => {
          return(true)
      },
      Fault_Translation => {
          return(level == 2)
      },
      Fault_AccessFlag => {
          return(level == 2)
      },
      Fault_SyncExternalOnWalk => {
          return(level == 2)
      },
      Fault_SyncParityOnWalk => {
          return(level == 2)
      },
      _ => {
          return(false)
      }
    }
}

val AArch32_AccessIsPrivileged : AccType -> bool effect {rreg, undef}

function AArch32_AccessIsPrivileged acctype = {
    let el : bits(2) = AArch32_AccessUsesEL(acctype);
    ispriv : bool = undefined : bool;
    if el == EL0 then {
        ispriv = false
    } else {
        if el != EL1 then {
            ispriv = true
        } else {
            ispriv = acctype != AccType_UNPRIV
        }
    };
    ispriv
}

val UsingAArch32 : unit -> bool effect {escape, rreg}

function UsingAArch32 () = {
    let aarch32 = PSTATE.nRW == 0b1;
    if ~(HaveAnyAArch32()) then {
        assert(~(aarch32))
    };
    if HighestELUsingAArch32() then {
        assert(aarch32)
    };
    aarch32
}

val aset_SPSR : bits(32) -> unit effect {escape, rreg, wreg}

function aset_SPSR value_name = {
    if UsingAArch32() then {
        match PSTATE.M {
          ? if ? == M32_FIQ => {
              SPSR_fiq = value_name
          },
          ? if ? == M32_IRQ => {
              SPSR_irq = value_name
          },
          ? if ? == M32_Svc => {
              set_SPSR_svc(value_name)
          },
          ? if ? == M32_Monitor => {
              set_SPSR_mon(value_name)
          },
          ? if ? == M32_Abort => {
              SPSR_abt = value_name
          },
          ? if ? == M32_Hyp => {
              set_SPSR_hyp(value_name)
          },
          ? if ? == M32_Undef => {
              SPSR_und = value_name
          },
          _ => {
              Unreachable()
          }
        }
    } else {
        match PSTATE.EL {
          ? if ? == EL1 => {
              SPSR_EL1 = value_name
          },
          ? if ? == EL2 => {
              SPSR_EL2 = value_name
          },
          ? if ? == EL3 => {
              SPSR_EL3 = value_name
          },
          _ => {
              Unreachable()
          }
        }
    };
    return()
}

overload SPSR = {aset_SPSR}

val ThisInstrAddr : forall ('N : Int).
  implicit('N) -> bits('N) effect {escape, rreg}

function ThisInstrAddr N = {
    assert('N == 64 | 'N == 32 & UsingAArch32());
    slice(_PC, 0, 'N)
}

val IsNonTagCheckedInstruction : unit -> bool effect {escape, rreg}

function IsNonTagCheckedInstruction () = {
    let here : bits(64) = ThisInstrAddr();
    sp_rel_access_pc == here
}

val CurrentInstrSet : unit -> InstrSet effect {escape, rreg, undef}

function CurrentInstrSet () = {
    result : InstrSet = undefined : InstrSet;
    if UsingAArch32() then {
        result = if PSTATE.T == 0b0 then InstrSet_A32 else InstrSet_T32
    } else {
        result = InstrSet_A64
    };
    result
}

val AArch32_ExecutingLSMInstr : unit -> bool effect {escape, rreg, undef}

function AArch32_ExecutingLSMInstr () = {
    let instr = ThisInstr();
    let instr_set = CurrentInstrSet();
    assert(instr_set == InstrSet_A32 | instr_set == InstrSet_T32);
    if instr_set == InstrSet_A32 then {
        return(slice(instr, 28, 4) != 0xF & slice(instr, 25, 3) == 0b100)
    } else {
        if ThisInstrLength() == 16 then {
            return(slice(instr, 12, 4) == 0xC)
        } else {
            return(slice(instr, 25, 7) == 0b1110100 & [instr[22]] == 0b0)
        }
    }
}

val IsSecureBelowEL3 : unit -> bool effect {escape, rreg, undef}

function IsSecureBelowEL3 () = {
    if HaveEL(EL3) then {
        return([SCR_GEN()[0]] == 0b0)
    } else {
        if HaveEL(EL2) & (~(HaveSecureEL2Ext()) | HighestELUsingAArch32()) then {
            return(false)
        } else {
            return(__IMPDEF_boolean("Secure-only implementation"))
        }
    }
}

val IsSecure : unit -> bool effect {escape, rreg, undef}

function IsSecure () = {
    if (HaveEL(EL3) & ~(UsingAArch32())) & PSTATE.EL == EL3 then {
        return(true)
    } else {
        if (HaveEL(EL3) & UsingAArch32()) & PSTATE.M == M32_Monitor then {
            return(true)
        }
    };
    IsSecureBelowEL3()
}

val IsGTEPPUMatch : (FullAddress, bits(1)) -> bool effect {escape, rreg}

function IsGTEPPUMatch (fullAddress, read) = {
    if ~(_GTEActive) then {
        return(false)
    };
    let address : bits(64) = ZeroExtend(fullAddress.address);
    let ns : bits(1) = fullAddress.NS;
    let priv : bits(1) = 0b1;
    generate_abort : bool = false;
    let 'ns_access_bit : {|1, 0|} = if ns == 0b1 then 1 else 0;
    let 'prot_access_bit : int = 4 + (if ns == 0b1 then 4 else 0) + (if priv == 0b1 then 2 else 0) + (if read == 0b1 then 1 else 0);
    let 'log_or_abort_bit : {'n, 'n == 31. int('n)} = 31;
    foreach (i from 0 to (NUM_GTE_REGIONS - 1) by 1 in inc) {
        let 'size : int = UInt(slice(_GTE_PPU_SizeEn[i], 1, 7)) + 1;
        assert(constraint(- 'size + 64 >= 0));
        if [_GTE_PPU_SizeEn[i][0]] == 0b1 & slice(address, size, negate(size) + 64) == slice(_GTE_PPU_Address[i], size, negate(size) + 64) then {
            prerr("GTE_PPU[" ++ DecStr(i) ++ "] matched address " ++ HexStr(UInt(address)));
            if ns == 0b1 then {
                prerr("_ns")
            } else {
                prerr("_s")
            };
            prerr("\n");
            if [_GTE_PPU_Access[i][ns_access_bit]] == 0b1 then {
                generate_abort = true
            };
            if [_GTE_PPU_Access[i][prot_access_bit]] != [_GTE_PPU_Access[i][prot_access_bit - 4]] then {
                prerr("TODO: GTE_PPU match needs privilege information\n")
            };
            if [_GTE_PPU_Access[i][prot_access_bit]] == 0b1 then {
                generate_abort = true
            };
            if [_GTE_PPU_Access[i][log_or_abort_bit]] == 0b1 then {
                prerr("GTE_PPU logged a matched address access violation");
                generate_abort = false
            }
        }
    };
    generate_abort
}

val HaveMTEExt : unit -> bool effect {escape}

function HaveMTEExt () = {
    if ~(HasArchVersion(ARMv8p5)) then {
        return(false)
    };
    __IMPDEF_boolean("Has MTE extension")
}

val GetPSRFromPSTATE : unit -> bits(32) effect {escape, rreg}

function GetPSRFromPSTATE () = {
    spsr : bits(32) = Zeros();
    spsr = __SetSlice_bits(32, 4, spsr, 28, PSTATE.N @ (PSTATE.Z @ (PSTATE.C @ PSTATE.V)));
    if HaveDITExt() then {
        spsr = __SetSlice_bits(32, 1, spsr, 24, PSTATE.DIT)
    };
    if HavePANExt() then {
        spsr = __SetSlice_bits(32, 1, spsr, 22, PSTATE.PAN)
    };
    spsr = __SetSlice_bits(32, 1, spsr, 21, PSTATE.SS);
    spsr = __SetSlice_bits(32, 1, spsr, 20, PSTATE.IL);
    if PSTATE.nRW == 0b1 then {
        spsr = __SetSlice_bits(32, 1, spsr, 27, PSTATE.Q);
        spsr = __SetSlice_bits(32, 2, spsr, 25, slice(PSTATE.IT, 0, 2));
        spsr = __SetSlice_bits(32, 4, spsr, 16, PSTATE.GE);
        spsr = __SetSlice_bits(32, 6, spsr, 10, slice(PSTATE.IT, 2, 6));
        spsr = __SetSlice_bits(32, 1, spsr, 9, PSTATE.E);
        spsr = __SetSlice_bits(32, 3, spsr, 6, PSTATE.A @ (PSTATE.I @ PSTATE.F));
        spsr = __SetSlice_bits(32, 1, spsr, 5, PSTATE.T);
        assert([PSTATE.M[4]] == PSTATE.nRW);
        spsr = __SetSlice_bits(32, 5, spsr, 0, PSTATE.M)
    } else {
        if HaveUAOExt() then {
            spsr = __SetSlice_bits(32, 1, spsr, 23, PSTATE.UAO)
        };
        if HaveMTEExt() then {
            spsr = __SetSlice_bits(32, 1, spsr, 25, PSTATE.TCO)
        };
        if HaveBTIExt() then {
            spsr = __SetSlice_bits(32, 2, spsr, 10, PSTATE.BTYPE)
        };
        spsr = __SetSlice_bits(32, 4, spsr, 6, PSTATE.D @ (PSTATE.A @ (PSTATE.I @ PSTATE.F)));
        spsr = __SetSlice_bits(32, 1, spsr, 4, PSTATE.nRW);
        spsr = __SetSlice_bits(32, 2, spsr, 2, PSTATE.EL);
        spsr = __SetSlice_bits(32, 1, spsr, 0, PSTATE.SP)
    };
    spsr
}

val HaveDoubleLock : unit -> bool effect {escape}

function HaveDoubleLock () = {
    ~(HasArchVersion(ARMv8p4)) | __IMPDEF_boolean("OS Double Lock is implemented")
}

val HaveAArch32EL : bits(2) -> bool effect {escape, rreg}

function HaveAArch32EL el = {
    if ~(HaveEL(el)) then {
        return(false)
    } else {
        if ~(HaveAnyAArch32()) then {
            return(false)
        } else {
            if HighestELUsingAArch32() then {
                return(true)
            } else {
                if el == HighestEL() then {
                    return(false)
                } else {
                    if el == EL0 then {
                        return(true)
                    } else {
                        match el {
                          ? if ? == EL0 => {
                              return(CFG_ID_AA64PFR0_EL1_EL0 == 0x2)
                          },
                          ? if ? == EL1 => {
                              return(CFG_ID_AA64PFR0_EL1_EL1 == 0x2)
                          },
                          ? if ? == EL2 => {
                              return(CFG_ID_AA64PFR0_EL1_EL2 == 0x2)
                          },
                          ? if ? == EL3 => {
                              return(CFG_ID_AA64PFR0_EL1_EL3 == 0x2)
                          }
                        }
                    }
                }
            }
        }
    }
}

val Halted : unit -> bool effect {rreg}

function Halted () = {
    ~(slice(EDSCR, 0, 6) == 0b000001 | slice(EDSCR, 0, 6) == 0b000010)
}

val GTEIsExtObsActive : forall ('observer : Int).
  int('observer) -> bool effect {rreg}

function GTEIsExtObsActive observer = {
    if observer >= NUM_GTE_EXT_OBS_OBSERVERS then {
        prerr("    ERROR handle out of range\n");
        return(false)
    };
    if ~(_GTEExtObsActive[observer]) then {
        prerr("    ERROR observer not active\n");
        return(false)
    };
    true
}

val GTEReturnObsData : unit -> unit effect {rreg, wreg}

function GTEReturnObsData () = {
    prerr("GTEReturnObsData(" ++ DecStr(UInt(slice(_GTEParam[0], 0, 32))) ++ ")\n");
    let 'observer = UInt(slice(_GTEParam[0], 0, 32));
    if ~(GTEIsExtObsActive(observer)) then {
        _GTEStatus = GTE_ST_REQUEST_FAIL;
        return()
    };
    if _GTEExtObsResultIndex[observer] == _GTEExtObsIndex[observer] + _GTEExtObsCount[observer] then {
        _GTEStatus = Ones(64);
        return()
    };
    let 'index = _GTEExtObsResultIndex[observer];
    if _GTEExtObsResultIsAddress[observer] then {
        _GTEStatus = _GTEExtObsAddress[_GTEExtObsResultIndex[observer]]
    } else {
        _GTEStatus = _GTEExtObsResult[_GTEExtObsResultIndex[observer]];
        _GTEExtObsResultIndex[observer] = _GTEExtObsResultIndex[observer] + 1
    };
    _GTEExtObsResultIsAddress[observer] = ~(_GTEExtObsResultIsAddress[observer]);
    return()
}

val GTEReleaseExtObs : unit -> unit effect {rreg, wreg}

function GTEReleaseExtObs () = {
    prerr("GTEReleaseExtObs(" ++ DecStr(UInt(slice(_GTEParam[0], 0, 32))) ++ ")\n");
    let 'observer = UInt(slice(_GTEParam[0], 0, 32));
    if ~(GTEIsExtObsActive(observer)) then {
        _GTEStatus = GTE_ST_REQUEST_FAIL;
        return()
    };
    _GTEExtObsActive[observer] = false;
    _GTEStatus = GTE_ST_REQUEST_GRANTED;
    return()
}

val GTEPerformExtObs64 : unit -> unit effect {rmem, rreg, undef, wmem, wreg}

function GTEPerformExtObs64 () = {
    prerr("GTEPerformExtObs64(" ++ DecStr(UInt(slice(_GTEParam[0], 0, 32))) ++ ")\n");
    let 'observer = UInt(slice(_GTEParam[0], 0, 32));
    if ~(GTEIsExtObsActive(observer)) then {
        _GTEStatus = GTE_ST_REQUEST_FAIL;
        return()
    };
    GTEPerformExtObsCommon(observer);
    _GTEStatus = GTE_ST_REQUEST_GRANTED;
    return()
}

val GTEPerformExtObs : unit -> unit effect {rmem, rreg, undef, wmem, wreg}

function GTEPerformExtObs () = {
    prerr("GTEPerformExtObs(" ++ DecStr(UInt(slice(_GTEParam[0], 0, 32))) ++ ")\n");
    let 'observer = UInt(slice(_GTEParam[0], 0, 32));
    if ~(GTEIsExtObsActive(observer)) then {
        _GTEStatus = GTE_ST_REQUEST_FAIL;
        return()
    };
    GTEPerformExtObsCommon(observer);
    _GTEStatus = GTE_EXT_OBS_RESULTS_ADDRESS;
    return()
}

val GTEEnableExtObs : unit -> unit effect {rreg, wreg}

function GTEEnableExtObs () = {
    prerr("GTEEnableExtObs(" ++ DecStr(UInt(slice(_GTEParam[0], 0, 32))) ++ ")\n");
    let 'observer = UInt(slice(_GTEParam[0], 0, 32));
    if ~(GTEIsExtObsActive(observer)) then {
        _GTEStatus = GTE_ST_REQUEST_FAIL;
        return()
    };
    _GTEExtObsResultIndex[observer] = _GTEExtObsIndex[observer];
    _GTEExtObsResultIsAddress[observer] = true;
    _GTEStatus = GTE_ST_REQUEST_GRANTED;
    return()
}

val GTEProcessParam : unit -> unit effect {rmem, rreg, undef, wmem, wreg}

function GTEProcessParam () = {
    match _GTECurrentAPI {
      ? if ? == VAL_EVENTGEN_SETUP => {
          if _GTEParamCount == 2 then {
              GTEListParam()
          } else {
              if _GTEParamCount == 3 then {
                  _GTEParamsComplete = true;
                  GTEEventGenSetup()
              }
          }
      },
      ? if ? == VAL_EVENTGEN_PRIME => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEEventGenPrime()
          }
      },
      ? if ? == VAL_EVENTGEN_CLEAR => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEEventGenClear()
          }
      },
      ? if ? == VAL_EVENTGEN_QUERY => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEEventGenQuery()
          }
      },
      ? if ? == VAL_EVENTGEN_DISABLE => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEEventGenDisable()
          }
      },
      ? if ? == VAL_EVENTGEN_FREE => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEEventGenFree()
          }
      },
      ? if ? == VAL_ASSERT => {
          if _GTEParamCount == 0 then {
              GTEListParam()
          } else {
              if _GTEParamCount == 2 then {
                  _GTEParamsComplete = true;
                  GTEAssert()
              }
          }
      },
      ? if ? == VAL_DEASSERT => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEDeassert()
          }
      },
      ? if ? == VAL_GET_PPU_ID => {
          _GTEParamsComplete = true;
          GTEGetPPUID()
      },
      ? if ? == VAL_SET_PPU_REGION => {
          if _GTEParamCount == 4 then {
              _GTEParamsComplete = true;
              GTESetPPURegion()
          }
      },
      ? if ? == VAL_GET_PPU_REGION => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEGetPPURegion()
          }
      },
      ? if ? == VAL_PPU_CONTROL => {
          if _GTEParamCount == 2 then {
              _GTEParamsComplete = true;
              GTEPPUControl()
          }
      },
      ? if ? == VAL_SETUP_EXT_OBS => {
          if _GTEParamCount == 0 then {
              GTEExtObsAddrDataListParam()
          } else {
              if _GTEParamCount == 1 then {
                  GTEListParam()
              } else {
                  if _GTEParamCount == 2 then {
                      _GTEParamsComplete = true;
                      GTESetupExtObs()
                  }
              }
          }
      },
      ? if ? == VAL_ENABLE_EXT_OBS => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEEnableExtObs()
          }
      },
      ? if ? == VAL_PERFORM_EXT_OBS => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEPerformExtObs()
          }
      },
      ? if ? == VAL_RELEASE_EXT_OBS => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEReleaseExtObs()
          }
      },
      ? if ? == VAL_SET_CRITICAL_EVENT => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTESetCriticalEvent()
          }
      },
      ? if ? == VAL_CRITICAL_SECTION_START => {
          if _GTEParamCount == 0 then {
              _GTEParamsComplete = true;
              GTECriticalSectionStart()
          }
      },
      ? if ? == VAL_CRITICAL_SECTION_END => {
          if _GTEParamCount == 0 then {
              _GTEParamsComplete = true;
              GTECriticalSectionEnd()
          }
      },
      ? if ? == VAL_RANDNUM => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTERandNum()
          }
      },
      ? if ? == VAL_DEFINE_NO_ABORTING_REGIONS => {
          prerr("Unhandled Trickbox GTE function VAL_DEFINE_NO_ABORTING_REGIONS\n")
      },
      ? if ? == VAL_OBSERVER_PIN_VALUE => {
          prerr("Unhandled Trickbox GTE function VAL_OBSERVER_PIN_VALUE\n")
      },
      ? if ? == VAL_EN_ACCESS_SENSITIVE_BEH => {
          if _GTEParamCount == 3 then {
              GTEEnAccessSensitiveBEH()
          }
      },
      ? if ? == VAL_CHK_ACCESS_SENSITIVE_BEH => {
          if _GTEParamCount == 0 then {
              GTEOnesTerminatedListParam()
          } else {
              if _GTEParamCount == 1 then {
                  GTEChkAccessSensitiveBEH()
              }
          }
      },
      ? if ? == VAL_SETUP_EXT_OBS_64 => {
          if _GTEParamCount == 0 then {
              GTEExtObsAccessListParam()
          } else {
              if _GTEParamCount == 1 then {
                  GTEOnesTerminatedListParam()
              } else {
                  if _GTEParamCount == 2 then {
                      _GTEParamsComplete = true;
                      GTESetupExtObs64()
                  }
              }
          }
      },
      ? if ? == VAL_ENABLE_EXT_OBS_64 => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEEnableExtObs()
          }
      },
      ? if ? == VAL_PERFORM_EXT_OBS_64 => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEPerformExtObs64()
          }
      },
      ? if ? == VAL_RETURN_OBS_DATA_64 => {
          if _GTEParamCount == 1 then {
              _GTEParamsComplete = true;
              GTEReturnObsData()
          }
      },
      _ => {
          prerr("Unknown Trickbox GTE function" ++ HexStr(UInt(_GTECurrentAPI)) ++ "\n")
      }
    };
    return()
}

val set_GTE_API : bits(32) -> unit effect {rmem, rreg, undef, wmem, wreg}

function set_GTE_API val_name = {
    _GTEActive = true;
    _GTEParamCount = 0;
    _GTEParamType = GTEParam_WORD;
    _GTEListParam = 0;
    _GTEParamsComplete = false;
    _GTEHaveParamLo = false;
    _GTECurrentAPI = val_name;
    GTEProcessParam();
    return()
}

val GTENextParam : bits(64) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function GTENextParam val_name__arg = {
    val_name = val_name__arg;
    if _GTEParamType == GTEParam_LIST then {
        if val_name == _GTEListParamTerminator then {
            _GTEListParamTerminatorCount = _GTEListParamTerminatorCount + 1
        } else {
            _GTEListParamTerminatorCount = 0
        };
        if _GTEListParamTerminatorCount == _GTEListParamTerminators then {
            _GTEParamType = GTEParam_WORD;
            _GTEListParam = _GTEListParam + 1;
            val_name = __GetSlice_int(64, _GTEListParamIndex, 0);
            _GTEListParamIndex = 0
        } else {
            GTEAddListParam(val_name);
            return()
        }
    };
    if _GTEParamType == GTEParam_EOACCESS then {
        if _GTEListParamIndex == 0 then {
            let 'num_access = UInt(slice(val_name, 0, 8));
            _GTEListParamTerminatorCount = 1 + shr_int(num_access, 2)
        };
        if val_name == _GTEListParamTerminator & _GTEListParamIndex >= _GTEListParamTerminatorCount then {
            _GTEParamType = GTEParam_WORD;
            _GTEListParam = _GTEListParam + 1;
            val_name = __GetSlice_int(64, _GTEListParamIndex, 0);
            _GTEListParamIndex = 0
        } else {
            GTEAddListParam(val_name);
            return()
        }
    };
    _GTEParam[_GTEParamCount] = val_name;
    _GTEParamCount = _GTEParamCount + 1;
    GTEProcessParam();
    return()
}

val set_GTE_API_PARAM_64_HI : bits(32) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function set_GTE_API_PARAM_64_HI val_name = {
    let val64_name : bits(64) = slice(val_name, 0, 32) @ _GTEParamLo;
    GTENextParam(val64_name)
}

val set_GTE_API_PARAM : bits(32) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function set_GTE_API_PARAM val_name = {
    GTENextParam(Zeros(32) @ val_name)
}

val _WriteTrickbox : forall 'address ('UNP : Bool) ('UP : Bool) ('PNP : Bool) ('PP : Bool).
  (int('address), bool('UNP), bool('UP), bool('PNP), bool('PP), bits(32)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function _WriteTrickbox (address, UNP, UP, PNP, PP, val_name) = {
    match address {
      0 if ((UNP | PNP) | UP) | PP => {
          set_TUBE(val_name)
      },
      8 if ((UNP | PNP) | UP) | PP => {
          set_ScheduleFIQ(val_name)
      },
      12 if ((UNP | PNP) | UP) | PP => {
          set_ScheduleIRQ(val_name)
      },
      16 if ((UNP | PNP) | UP) | PP => {
          set_ClearFIQ(val_name)
      },
      20 if ((UNP | PNP) | UP) | PP => {
          set_ClearIRQ(val_name)
      },
      252 if ((UNP | PNP) | UP) | PP => {
          set_TargetCPU(val_name)
      },
      256 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Lo1 = val_name
      },
      260 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Lo1_Hi = val_name
      },
      264 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Hi1 = val_name
      },
      268 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Hi1_Hi = val_name
      },
      272 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Lo2 = val_name
      },
      276 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Lo2_Hi = val_name
      },
      280 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Hi2 = val_name
      },
      284 if ((UNP | PNP) | UP) | PP => {
          AbortRgn64Hi2_Hi = val_name
      },
      1280 if ((UNP | PNP) | UP) | PP => {
          set_AXIAbortCtl(val_name)
      },
      2560 if ((UNP | PNP) | UP) | PP => {
          let GTE_API = undefined : bits(32);
          set_GTE_API(val_name)
      },
      2564 if ((UNP | PNP) | UP) | PP => {
          set_GTE_API_PARAM(val_name)
      },
      2600 if ((UNP | PNP) | UP) | PP => {
          set_GTE_API_PARAM_64(val_name)
      },
      2604 if ((UNP | PNP) | UP) | PP => {
          set_GTE_API_PARAM_64_HI(val_name)
      },
      _ => {
          prerr("Undefined trickbox write at offset " ++ HexStr(address) ++ " with value " ++ HexStr(UInt(val_name)) ++ "\n");
          return()
      }
    }
}

val GTECheckAccessSensitiveAccess : forall ('size : Int), 0 <= 'size.
  (bits(52), int('size), bits(8 * 'size), bool) -> unit effect {escape, rreg, wreg}

function GTECheckAccessSensitiveAccess (address, size, data, isRead) = {
    if (~(_GTEActive) | _GTE_AS_Size == 0) | _GTE_AS_Access == 0 then {
        return()
    };
    if (_GTE_AS_AccessCount < NUM_GTE_AS_ACCESSES & UInt(address) >= UInt(_GTE_AS_Address)) & UInt(address) < UInt(_GTE_AS_Address + _GTE_AS_Size) then {
        let access_dir : bits(2) = if isRead then 0b01 else 0b10;
        let access : bits(32) = (Zeros(26) @ __GetSlice_int(4, size, 0)) @ access_dir;
        prerr("Access sensitive " ++ (if isRead then "read" else "write") ++ " at " ++ HexStr(UInt(address)) ++ " size " ++ DecStr(size));
        if (_GTE_AS_Access & access) == access then {
            prerr(" access match\n");
            let return_size : bits(2) = match size {
              1 => 0b01,
              2 => 0b10,
              4 => 0b00,
              8 => 0b11
            };
            _GTE_AS_RecordedAddress[_GTE_AS_AccessCount] = ZeroExtend(address);
            _GTE_AS_RecordedData[_GTE_AS_AccessCount] = ZeroExtend(data);
            __tc1 : bits(32) = _GTE_AS_RecordedAccess[_GTE_AS_AccessCount];
            __tc1 = __SetSlice_bits(32, 2, __tc1, 2, return_size);
            _GTE_AS_RecordedAccess[_GTE_AS_AccessCount] = __tc1;
            __tc2 : bits(32) = _GTE_AS_RecordedAccess[_GTE_AS_AccessCount];
            __tc2 = __SetSlice_bits(32, 2, __tc2, 0, access_dir);
            _GTE_AS_RecordedAccess[_GTE_AS_AccessCount] = __tc2;
            _GTE_AS_AccessCount = _GTE_AS_AccessCount + 1
        } else {
            prerr(" no access match\n")
        }
    };
    return()
}

val ExternalSecureDebugEnabled : unit -> bool effect {escape, rreg, undef}

function ExternalSecureDebugEnabled () = {
    if ~(HaveEL(EL3)) & ~(IsSecure()) then {
        return(false)
    };
    ExternalDebugEnabled() & SPIDEN == HIGH
}

val ELStateUsingAArch32K : forall ('secure : Bool).
  (bits(2), bool('secure)) -> (bool, bool) effect {escape, rreg, undef}

function ELStateUsingAArch32K (el, secure) = {
    aarch32 : bool = undefined : bool;
    known : bool = undefined : bool;
    known = true;
    aarch32_at_el1 : bool = undefined : bool;
    aarch32_below_el3 : bool = undefined : bool;
    if ~(HaveAArch32EL(el)) then {
        aarch32 = false
    } else {
        if HighestELUsingAArch32() then {
            aarch32 = true
        } else {
            aarch32_below_el3 = HaveEL(EL3) & [SCR_EL3[10]] == 0b0;
            aarch32_at_el1 = aarch32_below_el3 | ((HaveEL(EL2) & (HaveSecureEL2Ext() & [SCR_EL3[18]] == 0b1 | ~(secure))) & [HCR_EL2[31]] == 0b0) & ~(([HCR_EL2[34]] == 0b1 & [HCR_EL2[27]] == 0b1) & HaveVirtHostExt());
            if el == EL0 & ~(aarch32_at_el1) then {
                if PSTATE.EL == EL0 then {
                    aarch32 = PSTATE.nRW == 0b1
                } else {
                    known = false
                }
            } else {
                aarch32 = aarch32_below_el3 & el != EL3 | aarch32_at_el1 & (el == EL1 | el == EL0)
            }
        }
    };
    if ~(known) then {
        aarch32 = undefined : bool
    };
    return((known, aarch32))
}

val ELStateUsingAArch32 : forall ('secure : Bool).
  (bits(2), bool('secure)) -> bool effect {escape, rreg, undef}

function ELStateUsingAArch32 (el, secure) = {
    aarch32 : bool = undefined : bool;
    known : bool = undefined : bool;
    (known, aarch32) = ELStateUsingAArch32K(el, secure);
    assert(known);
    aarch32
}

val ELUsingAArch32 : bits(2) -> bool effect {escape, rreg, undef}

function ELUsingAArch32 el = {
    ELStateUsingAArch32(el, IsSecureBelowEL3())
}

val set_IFSR : bits(32) -> unit effect {escape, rreg, undef, wreg}

function set_IFSR val_name = {
    let r : bits(32) = val_name;
    if ELUsingAArch32(EL3) & IsSecure() then {
        IFSR_S = r
    } else {
        set_IFSR_NS(r)
    };
    return()
}

val set_IFAR : bits(32) -> unit effect {escape, rreg, undef, wreg}

function set_IFAR val_name = {
    let r : bits(32) = val_name;
    if ELUsingAArch32(EL3) & IsSecure() then {
        set_IFAR_S(r)
    } else {
        set_IFAR_NS(r)
    };
    return()
}

val set_DFSR : bits(32) -> unit effect {escape, rreg, undef, wreg}

function set_DFSR val_name = {
    let r : bits(32) = val_name;
    if ELUsingAArch32(EL3) & IsSecure() then {
        DFSR_S = r
    } else {
        set_DFSR_NS(r)
    };
    return()
}

val set_DFAR : bits(32) -> unit effect {escape, rreg, undef, wreg}

function set_DFAR val_name = {
    let r : bits(32) = val_name;
    if ELUsingAArch32(EL3) & IsSecure() then {
        set_DFAR_S(r)
    } else {
        set_DFAR_NS(r)
    };
    return()
}

val get_VBAR : unit -> bits(32) effect {escape, rreg, undef}

function get_VBAR () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = VBAR_S
    } else {
        r = get_VBAR_NS()
    };
    r
}

val get_TTBR1 : unit -> bits(64) effect {escape, rreg, undef}

function get_TTBR1 () = {
    r : bits(64) = undefined : bits(64);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = TTBR1_S
    } else {
        r = get_TTBR1_NS()
    };
    r
}

val get_TTBR0 : unit -> bits(64) effect {escape, rreg, undef}

function get_TTBR0 () = {
    r : bits(64) = undefined : bits(64);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = TTBR0_S
    } else {
        r = get_TTBR0_NS()
    };
    r
}

val get_TTBCR2 : unit -> bits(32) effect {escape, rreg, undef}

function get_TTBCR2 () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = TTBCR2_S
    } else {
        r = get_TTBCR2_NS()
    };
    r
}

val get_TTBCR : unit -> bits(32) effect {escape, rreg, undef}

function get_TTBCR () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = TTBCR_S
    } else {
        r = get_TTBCR_NS()
    };
    r
}

val get_CONTEXTIDR_NS : unit -> bits(32) effect {rreg, undef}

function get_CONTEXTIDR_NS () = {
    r : bits(32) = undefined : bits(32);
    let r = __SetSlice_bits(32, 32, r, 0, slice(CONTEXTIDR_EL1, 0, 32));
    r
}

register CONTEXTIDR_S : bits(32)

val get_SCTLR : unit -> bits(32) effect {escape, rreg, undef}

function get_SCTLR () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = SCTLR_S
    } else {
        r = get_SCTLR_NS()
    };
    r
}

val ExcVectorBase : unit -> bits(32) effect {escape, rreg, undef}

function ExcVectorBase () = {
    if [get_SCTLR()[13]] == 0b1 then {
        return(Ones(16) @ Zeros(16))
    } else {
        return(slice(get_VBAR(), 5, 27) @ Zeros(5))
    }
}

val get_PRRR : unit -> bits(32) effect {escape, rreg, undef}

function get_PRRR () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = PRRR_S
    } else {
        r = get_PRRR_NS()
    };
    r
}

val get_NMRR : unit -> bits(32) effect {escape, rreg, undef}

function get_NMRR () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = NMRR_S
    } else {
        r = get_NMRR_NS()
    };
    r
}

val get_MAIR1 : unit -> bits(32) effect {escape, rreg, undef}

function get_MAIR1 () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = MAIR1_S
    } else {
        r = get_MAIR1_NS()
    };
    r
}

val get_MAIR0 : unit -> bits(32) effect {escape, rreg, undef}

function get_MAIR0 () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = MAIR0_S
    } else {
        r = get_MAIR0_NS()
    };
    r
}

val get_DACR : unit -> bits(32) effect {escape, rreg, undef}

function get_DACR () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = DACR_S
    } else {
        r = get_DACR_NS()
    };
    r
}

val get_CONTEXTIDR : unit -> bits(32) effect {escape, rreg, undef}

function get_CONTEXTIDR () = {
    r : bits(32) = undefined : bits(32);
    if ELUsingAArch32(EL3) & IsSecure() then {
        r = CONTEXTIDR_S
    } else {
        r = get_CONTEXTIDR_NS()
    };
    r
}

val S2CacheDisabled : AccType -> bool effect {escape, rreg, undef}

function S2CacheDisabled acctype = {
    disable : bits(1) = undefined : bits(1);
    if ELUsingAArch32(EL2) then {
        disable = if acctype == AccType_IFETCH then [get_HCR2()[1]] else [get_HCR2()[0]]
    } else {
        disable = if acctype == AccType_IFETCH then [HCR_EL2[33]] else [HCR_EL2[32]]
    };
    disable == 0b1
}

val S2ConvertAttrsHints : (bits(2), AccType) -> MemAttrHints effect {escape, rreg, undef}

function S2ConvertAttrsHints (attr, acctype) = {
    assert(~(IsZero(attr)));
    result : MemAttrHints = undefined : MemAttrHints;
    if S2CacheDisabled(acctype) then {
        result.attrs = MemAttr_NC;
        result.hints = MemHint_No
    } else {
        match attr {
          0b01 => {
              result.attrs = MemAttr_NC;
              result.hints = MemHint_No
          },
          0b10 => {
              result.attrs = MemAttr_WT;
              result.hints = MemHint_RWA
          },
          0b11 => {
              result.attrs = MemAttr_WB;
              result.hints = MemHint_RWA
          }
        }
    };
    result.transient = false;
    result
}

val S2AttrDecode : (bits(2), bits(4), AccType) -> MemoryAttributes effect {escape, rreg, undef}

function S2AttrDecode (SH, attr, acctype) = {
    memattrs : MemoryAttributes = undefined : MemoryAttributes;
    let apply_force_writeback = HaveStage2MemAttrControl() & [HCR_EL2[46]] == 0b1;
    if apply_force_writeback & [attr[2]] == 0b0 | slice(attr, 2, 2) == 0b00 then {
        memattrs.typ = MemType_Device;
        match slice(attr, 0, 2) {
          0b00 => {
              memattrs.device = DeviceType_nGnRnE
          },
          0b01 => {
              memattrs.device = DeviceType_nGnRE
          },
          0b10 => {
              memattrs.device = DeviceType_nGRE
          },
          0b11 => {
              memattrs.device = DeviceType_GRE
          }
        }
    } else {
        if slice(attr, 0, 2) != 0b00 then {
            memattrs.typ = MemType_Normal;
            if apply_force_writeback then {
                memattrs.outer = S2ConvertAttrsHints(slice(attr, 0, 2), acctype)
            } else {
                memattrs.outer = S2ConvertAttrsHints(slice(attr, 2, 2), acctype)
            };
            memattrs.inner = S2ConvertAttrsHints(slice(attr, 0, 2), acctype);
            memattrs.shareable = [SH[1]] == 0b1;
            memattrs.outershareable = SH == 0b10
        } else {
            memattrs = undefined : MemoryAttributes
        }
    };
    MemAttrDefaults(memattrs)
}

val IsSecureEL2Enabled : unit -> bool effect {escape, rreg, undef}

function IsSecureEL2Enabled () = {
    ((HaveSecureEL2Ext() & HaveEL(EL2)) & ~(ELUsingAArch32(EL2))) & ((HaveEL(EL3) & ~(ELUsingAArch32(EL3))) & [SCR_EL3[18]] == 0b1 | ~(HaveEL(EL3)) & IsSecure())
}

val UpdateEDSCRFields : unit -> unit effect {escape, rreg, undef, wreg}

function UpdateEDSCRFields () = {
    if ~(Halted()) then {
        EDSCR = __SetSlice_bits(32, 2, EDSCR, 8, 0b00);
        EDSCR = __SetSlice_bits(32, 1, EDSCR, 18, undefined : bits(1));
        EDSCR = __SetSlice_bits(32, 4, EDSCR, 10, 0xF)
    } else {
        EDSCR = __SetSlice_bits(32, 2, EDSCR, 8, PSTATE.EL);
        EDSCR = __SetSlice_bits(32, 1, EDSCR, 18, if IsSecure() then 0b0 else 0b1);
        RW : bits(4) = undefined : bits(4);
        RW = __SetSlice_bits(4, 1, RW, 1, if ELUsingAArch32(EL1) then 0b0 else 0b1);
        if PSTATE.EL != EL0 then {
            RW = __SetSlice_bits(4, 1, RW, 0, [RW[1]])
        } else {
            RW = __SetSlice_bits(4, 1, RW, 0, if UsingAArch32() then 0b0 else 0b1)
        };
        if ~(HaveEL(EL2)) | (HaveEL(EL3) & [SCR_GEN()[0]] == 0b0) & ~(IsSecureEL2Enabled()) then {
            RW = __SetSlice_bits(4, 1, RW, 2, [RW[1]])
        } else {
            RW = __SetSlice_bits(4, 1, RW, 2, if ELUsingAArch32(EL2) then 0b0 else 0b1)
        };
        if ~(HaveEL(EL3)) then {
            RW = __SetSlice_bits(4, 1, RW, 3, [RW[2]])
        } else {
            RW = __SetSlice_bits(4, 1, RW, 3, if ELUsingAArch32(EL3) then 0b0 else 0b1)
        };
        if [RW[3]] == 0b0 then {
            RW = __SetSlice_bits(4, 3, RW, 0, undefined : bits(3))
        } else {
            if [RW[2]] == 0b0 then {
                RW = __SetSlice_bits(4, 2, RW, 0, undefined : bits(2))
            } else {
                if [RW[1]] == 0b0 then {
                    RW = __SetSlice_bits(4, 1, RW, 0, undefined : bits(1))
                }
            }
        };
        EDSCR = __SetSlice_bits(32, 4, EDSCR, 10, RW)
    };
    return()
}

val Halt : bits(6) -> unit effect {escape, rreg, undef, wreg}

function Halt reason = {
    CTI_SignalEvent(CrossTriggerIn_CrossHalt);
    if UsingAArch32() then {
        set_DLR(ThisInstrAddr());
        set_DSPSR(GetPSRFromPSTATE());
        __tc1 : bits(32) = get_DSPSR();
        __tc1 = __SetSlice_bits(32, 1, __tc1, 21, PSTATE.SS);
        set_DSPSR(__tc1)
    } else {
        DLR_EL0 = ThisInstrAddr();
        DSPSR_EL0 = GetPSRFromPSTATE();
        DSPSR_EL0 = __SetSlice_bits(32, 1, DSPSR_EL0, 21, PSTATE.SS)
    };
    EDSCR = __SetSlice_bits(32, 1, EDSCR, 24, 0b1);
    EDSCR = __SetSlice_bits(32, 1, EDSCR, 28, 0b0);
    if IsSecure() then {
        EDSCR = __SetSlice_bits(32, 1, EDSCR, 16, 0b0)
    } else {
        if HaveEL(EL3) then {
            EDSCR = __SetSlice_bits(32, 1, EDSCR, 16, if ExternalSecureDebugEnabled() then 0b0 else 0b1)
        } else {
            assert([EDSCR[16]] == 0b1)
        }
    };
    EDSCR = __SetSlice_bits(32, 1, EDSCR, 20, 0b0);
    if UsingAArch32() then {
        (PSTATE.SS @ PSTATE.A @ PSTATE.I @ PSTATE.F) = undefined : bits(4);
        PSTATE.IT = 0x00;
        PSTATE.T = 0b1
    } else {
        (PSTATE.SS @ PSTATE.D @ PSTATE.A @ PSTATE.I @ PSTATE.F) = undefined : bits(5)
    };
    PSTATE.IL = 0b0;
    StopInstructionPrefetchAndEnableITR();
    EDSCR = __SetSlice_bits(32, 6, EDSCR, 0, reason);
    UpdateEDSCRFields();
    return()
}

val HaveDoubleFaultExt : unit -> bool effect {escape, rreg, undef}

function HaveDoubleFaultExt () = {
    ((HasArchVersion(ARMv8p4) & HaveEL(EL3)) & ~(ELUsingAArch32(EL3))) & HaveIESB()
}

val ELIsInHost : bits(2) -> bool effect {escape, rreg, undef}

function ELIsInHost el = {
    ((((IsSecureEL2Enabled() | ~(IsSecureBelowEL3())) & HaveVirtHostExt()) & ~(ELUsingAArch32(EL2))) & [HCR_EL2[34]] == 0b1) & (el == EL2 | el == EL0 & [HCR_EL2[27]] == 0b1)
}

val S1TranslationRegime__0 : bits(2) -> bits(2) effect {escape, rreg, undef}

val S1TranslationRegime__1 : unit -> bits(2) effect {escape, rreg, undef}

overload S1TranslationRegime = {S1TranslationRegime__0, S1TranslationRegime__1}

function S1TranslationRegime__0 el = {
    if el != EL0 then {
        return(el)
    } else {
        if (HaveEL(EL3) & ELUsingAArch32(EL3)) & [get_SCR()[0]] == 0b0 then {
            return(EL3)
        } else {
            if HaveVirtHostExt() & ELIsInHost(el) then {
                return(EL2)
            } else {
                return(EL1)
            }
        }
    }
}

function S1TranslationRegime__1 () = {
    S1TranslationRegime(PSTATE.EL)
}

val aset_FAR__0 : (bits(2), bits(64)) -> unit effect {escape, wreg}

val aset_FAR__1 : bits(64) -> unit effect {escape, wreg, rreg, undef}

overload aset_FAR = {aset_FAR__0, aset_FAR__1}

overload FAR = {aset_FAR__0, aset_FAR__1}

function aset_FAR__0 (regime, value_name) = {
    let r : bits(64) = value_name;
    match regime {
      ? if ? == EL1 => {
          FAR_EL1 = r
      },
      ? if ? == EL2 => {
          FAR_EL2 = r
      },
      ? if ? == EL3 => {
          FAR_EL3 = r
      },
      _ => {
          Unreachable()
      }
    };
    return()
}

function aset_FAR__1 value_name = {
    aset_FAR(S1TranslationRegime(), value_name);
    return()
}

val aset_ESR__0 : (bits(2), bits(32)) -> unit effect {escape, wreg}

val aset_ESR__1 : bits(32) -> unit effect {escape, wreg, rreg, undef}

overload aset_ESR = {aset_ESR__0, aset_ESR__1}

overload ESR = {aset_ESR__0, aset_ESR__1}

function aset_ESR__0 (regime, value_name) = {
    let r : bits(32) = value_name;
    match regime {
      ? if ? == EL1 => {
          ESR_EL1 = r
      },
      ? if ? == EL2 => {
          ESR_EL2 = r
      },
      ? if ? == EL3 => {
          ESR_EL3 = r
      },
      _ => {
          Unreachable()
      }
    };
    return()
}

function aset_ESR__1 value_name = {
    aset_ESR(S1TranslationRegime(), value_name)
}

val aget_VBAR__0 : bits(2) -> bits(64) effect {escape, rreg, undef}

val aget_VBAR__1 : unit -> bits(64) effect {escape, rreg, undef}

overload aget_VBAR = {aget_VBAR__0, aget_VBAR__1}

overload VBAR = {aget_VBAR__0, aget_VBAR__1}

function aget_VBAR__0 regime = {
    r : bits(64) = undefined : bits(64);
    match regime {
      ? if ? == EL1 => {
          r = VBAR_EL1
      },
      ? if ? == EL2 => {
          r = VBAR_EL2
      },
      ? if ? == EL3 => {
          r = VBAR_EL3
      },
      _ => {
          Unreachable()
      }
    };
    r
}

function aget_VBAR__1 () = {
    VBAR(S1TranslationRegime())
}

val aget_SCTLR__0 : bits(2) -> bits(64) effect {escape, rreg, undef}

val aget_SCTLR__1 : unit -> bits(64) effect {escape, rreg, undef}

overload aget_SCTLR = {aget_SCTLR__0, aget_SCTLR__1}

overload SCTLR = {aget_SCTLR__0, aget_SCTLR__1}

function aget_SCTLR__0 regime = {
    r : bits(64) = undefined : bits(64);
    match regime {
      ? if ? == EL1 => {
          r = SCTLR_EL1
      },
      ? if ? == EL2 => {
          r = SCTLR_EL2
      },
      ? if ? == EL3 => {
          r = SCTLR_EL3
      },
      _ => {
          Unreachable()
      }
    };
    r
}

function aget_SCTLR__1 () = {
    SCTLR(S1TranslationRegime())
}

val aget_MAIR__0 : bits(2) -> bits(64) effect {escape, rreg, undef}

val aget_MAIR__1 : unit -> bits(64) effect {escape, rreg, undef}

overload aget_MAIR = {aget_MAIR__0, aget_MAIR__1}

overload MAIR = {aget_MAIR__0, aget_MAIR__1}

function aget_MAIR__0 regime = {
    r : bits(64) = undefined : bits(64);
    match regime {
      ? if ? == EL1 => {
          r = MAIR_EL1
      },
      ? if ? == EL2 => {
          r = MAIR_EL2
      },
      ? if ? == EL3 => {
          r = MAIR_EL3
      },
      _ => {
          Unreachable()
      }
    };
    r
}

function aget_MAIR__1 () = {
    MAIR(S1TranslationRegime())
}

val S1CacheDisabled : AccType -> bool effect {escape, rreg, undef}

function S1CacheDisabled acctype = {
    enable : bits(1) = undefined : bits(1);
    if ELUsingAArch32(S1TranslationRegime()) then {
        if PSTATE.EL == EL2 then {
            enable = if acctype == AccType_IFETCH then [get_HSCTLR()[12]] else [get_HSCTLR()[2]]
        } else {
            enable = if acctype == AccType_IFETCH then [get_SCTLR()[12]] else [get_SCTLR()[2]]
        }
    } else {
        enable = if acctype == AccType_IFETCH then [SCTLR()[12]] else [SCTLR()[2]]
    };
    enable == 0b0
}

val ShortConvertAttrsHints : forall ('secondstage : Bool).
  (bits(2), AccType, bool('secondstage)) -> MemAttrHints effect {escape, rreg, undef}

function ShortConvertAttrsHints (RGN, acctype, secondstage) = {
    result : MemAttrHints = undefined : MemAttrHints;
    if ~(secondstage) & S1CacheDisabled(acctype) | secondstage & S2CacheDisabled(acctype) then {
        result.attrs = MemAttr_NC;
        result.hints = MemHint_No
    } else {
        match RGN {
          0b00 => {
              result.attrs = MemAttr_NC;
              result.hints = MemHint_No
          },
          0b01 => {
              result.attrs = MemAttr_WB;
              result.hints = MemHint_RWA
          },
          0b10 => {
              result.attrs = MemAttr_WT;
              result.hints = MemHint_RA
          },
          0b11 => {
              result.attrs = MemAttr_WB;
              result.hints = MemHint_RA
          }
        }
    };
    result.transient = false;
    result
}

val WalkAttrDecode : forall ('secondstage : Bool).
  (bits(2), bits(2), bits(2), bool('secondstage)) -> MemoryAttributes effect {escape, rreg, undef}

function WalkAttrDecode (SH, ORGN, IRGN, secondstage) = {
    memattrs : MemoryAttributes = undefined : MemoryAttributes;
    let acctype = AccType_NORMAL;
    memattrs.typ = MemType_Normal;
    memattrs.inner = ShortConvertAttrsHints(IRGN, acctype, secondstage);
    memattrs.outer = ShortConvertAttrsHints(ORGN, acctype, secondstage);
    memattrs.shareable = [SH[1]] == 0b1;
    memattrs.outershareable = SH == 0b10;
    memattrs.tagged = false;
    MemAttrDefaults(memattrs)
}

val AArch32_RemappedTEXDecode : (bits(3), bits(1), bits(1), bits(1), AccType) -> MemoryAttributes effect {escape, rreg, undef}

function AArch32_RemappedTEXDecode (TEX, C, B, S, acctype) = {
    memattrs : MemoryAttributes = undefined : MemoryAttributes;
    let region = UInt(([TEX[0]] @ C) @ B);
    __anon1 : Constraint = undefined : Constraint;
    attrfield : bits(2) = undefined : bits(2);
    base : int = undefined : int;
    s_bit : bits(1) = undefined : bits(1);
    if region == 6 then {
        memattrs = undefined
    } else {
        base = 2 * region;
        attrfield = slice(get_PRRR(), base, 2);
        if attrfield == 0b11 then {
            (__anon1, attrfield) = ConstrainUnpredictableBits(Unpredictable_RESPRRR)
        };
        match attrfield {
          0b00 => {
              memattrs.typ = MemType_Device;
              memattrs.device = DeviceType_nGnRnE
          },
          0b01 => {
              memattrs.typ = MemType_Device;
              memattrs.device = DeviceType_nGnRE
          },
          0b10 => {
              memattrs.typ = MemType_Normal;
              memattrs.inner = ShortConvertAttrsHints(slice(get_NMRR(), base, 2), acctype, false);
              memattrs.outer = ShortConvertAttrsHints(slice(get_NMRR(), base + 16, 2), acctype, false);
              s_bit = if S == 0b0 then [get_PRRR()[18]] else [get_PRRR()[19]];
              memattrs.shareable = s_bit == 0b1;
              memattrs.outershareable = s_bit == 0b1 & [get_PRRR()[region + 24]] == 0b0
          },
          0b11 => {
              Unreachable()
          }
        }
    };
    __tc1 : MemAttrHints = memattrs.inner;
    __tc1.transient = false;
    memattrs.inner = __tc1;
    __tc2 : MemAttrHints = memattrs.outer;
    __tc2.transient = false;
    memattrs.outer = __tc2;
    memattrs.tagged = false;
    MemAttrDefaults(memattrs)
}

val AArch32_DefaultTEXDecode : (bits(3), bits(1), bits(1), bits(1), AccType) -> MemoryAttributes effect {escape, rreg, undef}

function AArch32_DefaultTEXDecode (TEX__arg, C__arg, B__arg, S, acctype) = {
    B = B__arg;
    C = C__arg;
    TEX = TEX__arg;
    memattrs : MemoryAttributes = undefined : MemoryAttributes;
    __anon1 : Constraint = undefined : Constraint;
    if (TEX == 0b001 & (C @ B) == 0b01 | TEX == 0b010 & (C @ B) != 0b00) | TEX == 0b011 then {
        texcb : bits(5) = undefined : bits(5);
        (__anon1, texcb) = ConstrainUnpredictableBits(Unpredictable_RESTEXCB);
        TEX = slice(texcb, 2, 3);
        C = [texcb[1]];
        B = [texcb[0]]
    };
    match (TEX @ C) @ B {
      0b00000 => {
          memattrs.typ = MemType_Device;
          memattrs.device = DeviceType_nGnRnE
      },
      0b00001 => {
          memattrs.typ = MemType_Device;
          memattrs.device = DeviceType_nGnRE
      },
      0b01000 => {
          memattrs.typ = MemType_Device;
          memattrs.device = DeviceType_nGnRE
      },
      0b00010 => {
          memattrs.typ = MemType_Normal;
          memattrs.inner = ShortConvertAttrsHints(C @ B, acctype, false);
          memattrs.outer = ShortConvertAttrsHints(C @ B, acctype, false);
          memattrs.shareable = S == 0b1
      },
      0b00011 => {
          memattrs.typ = MemType_Normal;
          memattrs.inner = ShortConvertAttrsHints(C @ B, acctype, false);
          memattrs.outer = ShortConvertAttrsHints(C @ B, acctype, false);
          memattrs.shareable = S == 0b1
      },
      0b00100 => {
          memattrs.typ = MemType_Normal;
          memattrs.inner = ShortConvertAttrsHints(C @ B, acctype, false);
          memattrs.outer = ShortConvertAttrsHints(C @ B, acctype, false);
          memattrs.shareable = S == 0b1
      },
      0b00110 => {
          memattrs = undefined
      },
      0b00111 => {
          memattrs.typ = MemType_Normal;
          memattrs.inner = ShortConvertAttrsHints(0b01, acctype, false);
          memattrs.outer = ShortConvertAttrsHints(0b01, acctype, false);
          memattrs.shareable = S == 0b1
      },
      [bitone] @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) => {
          memattrs.typ = MemType_Normal;
          memattrs.inner = ShortConvertAttrsHints(C @ B, acctype, false);
          memattrs.outer = ShortConvertAttrsHints(slice(TEX, 0, 2), acctype, false);
          memattrs.shareable = S == 0b1
      },
      _ => {
          Unreachable()
      }
    };
    __tc1 : MemAttrHints = memattrs.inner;
    __tc1.transient = false;
    memattrs.inner = __tc1;
    __tc2 : MemAttrHints = memattrs.outer;
    __tc2.transient = false;
    memattrs.outer = __tc2;
    memattrs.outershareable = memattrs.shareable;
    memattrs.tagged = false;
    MemAttrDefaults(memattrs)
}

val LongConvertAttrsHints : (bits(4), AccType) -> MemAttrHints effect {escape, rreg, undef}

function LongConvertAttrsHints (attrfield, acctype) = {
    assert(~(IsZero(attrfield)));
    result : MemAttrHints = undefined : MemAttrHints;
    if S1CacheDisabled(acctype) then {
        result.attrs = MemAttr_NC;
        result.hints = MemHint_No
    } else {
        if slice(attrfield, 2, 2) == 0b00 then {
            result.attrs = MemAttr_WT;
            result.hints = slice(attrfield, 0, 2);
            result.transient = true
        } else {
            if slice(attrfield, 0, 4) == 0x4 then {
                result.attrs = MemAttr_NC;
                result.hints = MemHint_No;
                result.transient = false
            } else {
                if slice(attrfield, 2, 2) == 0b01 then {
                    result.attrs = MemAttr_WB;
                    result.hints = slice(attrfield, 0, 2);
                    result.transient = true
                } else {
                    result.attrs = slice(attrfield, 2, 2);
                    result.hints = slice(attrfield, 0, 2);
                    result.transient = false
                }
            }
        }
    };
    result
}

val IsInHost : unit -> bool effect {escape, rreg, undef}

function IsInHost () = {
    ELIsInHost(PSTATE.EL)
}

val EffectiveTCMA : (bits(64), bits(2)) -> bits(1) effect {escape, rreg, undef}

function EffectiveTCMA (address, el) = {
    assert(HaveEL(el));
    let regime = S1TranslationRegime(el);
    assert(~(ELUsingAArch32(regime)));
    tcma : bits(1) = undefined : bits(1);
    match regime {
      ? if ? == EL1 => {
          tcma = if [address[55]] == 0b1 then [TCR_EL1[58]] else [TCR_EL1[57]]
      },
      ? if ? == EL2 => {
          if HaveVirtHostExt() & ELIsInHost(el) then {
              tcma = if [address[55]] == 0b1 then [TCR_EL2[58]] else [TCR_EL2[57]]
          } else {
              tcma = [TCR_EL2[30]]
          }
      },
      ? if ? == EL3 => {
          tcma = [TCR_EL3[30]]
      }
    };
    tcma
}

val EffectiveTBI : forall ('IsInstr : Bool).
  (bits(64), bool('IsInstr), bits(2)) -> bits(1) effect {escape, rreg, undef}

function EffectiveTBI (address, IsInstr, el) = {
    assert(HaveEL(el));
    let regime = S1TranslationRegime(el);
    assert(~(ELUsingAArch32(regime)));
    tbi : bits(1) = undefined : bits(1);
    tbid : bits(1) = undefined : bits(1);
    match regime {
      ? if ? == EL1 => {
          tbi = if [address[55]] == 0b1 then [TCR_EL1[38]] else [TCR_EL1[37]];
          if HavePACExt() then {
              tbid = if [address[55]] == 0b1 then [TCR_EL1[52]] else [TCR_EL1[51]]
          }
      },
      ? if ? == EL2 => {
          if HaveVirtHostExt() & ELIsInHost(el) then {
              tbi = if [address[55]] == 0b1 then [TCR_EL2[38]] else [TCR_EL2[37]];
              if HavePACExt() then {
                  tbid = if [address[55]] == 0b1 then [TCR_EL2[52]] else [TCR_EL2[51]]
              }
          } else {
              tbi = [TCR_EL2[20]];
              if HavePACExt() then {
                  tbid = [TCR_EL2[29]]
              }
          }
      },
      ? if ? == EL3 => {
          tbi = [TCR_EL3[20]];
          if HavePACExt() then {
              tbid = [TCR_EL3[29]]
          }
      }
    };
    if tbi == 0b1 & ((~(HavePACExt()) | tbid == 0b0) | ~(IsInstr)) then 0b1 else 0b0
}

val EL2Enabled : unit -> bool effect {escape, rreg, undef}

function EL2Enabled () = {
    IsSecureEL2Enabled() | HaveEL(EL2) & ~(IsSecure())
}

val VMID_opt : unit -> option(bits(16)) effect {rreg}

function VMID_opt() = {
    if EL2Enabled() then {
        Some(VTTBR_EL2[63 .. 48])
    } else {
        None()
    }
}

val getMPAM_PMG : forall ('MPAMn : Int) ('InD : Bool).
  (int('MPAMn), bool('InD)) -> bits(8) effect {escape, rreg, undef}

function getMPAM_PMG (MPAMn, InD) = {
    pmg : bits(8) = undefined : bits(8);
    let el2avail = EL2Enabled();
    if InD then {
        match MPAMn {
          3 => {
              pmg = slice(MPAM3_EL3, 32, 8)
          },
          2 => {
              pmg = if el2avail then slice(MPAM2_EL2, 32, 8) else Zeros()
          },
          1 => {
              pmg = slice(MPAM1_EL1, 32, 8)
          },
          0 => {
              pmg = slice(MPAM0_EL1, 32, 8)
          },
          _ => {
              pmg = undefined : bits(8)
          }
        }
    } else {
        match MPAMn {
          3 => {
              pmg = slice(MPAM3_EL3, 40, 8)
          },
          2 => {
              pmg = if el2avail then slice(MPAM2_EL2, 40, 8) else Zeros()
          },
          1 => {
              pmg = slice(MPAM1_EL1, 40, 8)
          },
          0 => {
              pmg = slice(MPAM0_EL1, 40, 8)
          },
          _ => {
              pmg = undefined : bits(8)
          }
        }
    };
    pmg
}

val genPMG : forall ('el : Int) ('InD : Bool) ('partid_err : Bool).
  (int('el), bool('InD), bool('partid_err)) -> bits(8) effect {escape, rreg, undef}

function genPMG (el, InD, partid_err) = {
    let 'pmg_max = UInt(slice(MPAMIDR_EL1, 32, 8));
    if partid_err then {
        return(DefaultPMG)
    };
    let groupel = getMPAM_PMG(el, InD);
    if UInt(groupel) <= pmg_max then {
        return(groupel)
    };
    DefaultPMG
}

val getMPAM_PARTID : forall ('MPAMn : Int) ('InD : Bool).
  (int('MPAMn), bool('InD)) -> bits(16) effect {escape, rreg, undef}

function getMPAM_PARTID (MPAMn, InD) = {
    partid : bits(16) = undefined : bits(16);
    let el2avail = EL2Enabled();
    if InD then {
        match MPAMn {
          3 => {
              partid = slice(MPAM3_EL3, 0, 16)
          },
          2 => {
              partid = if el2avail then slice(MPAM2_EL2, 0, 16) else Zeros()
          },
          1 => {
              partid = slice(MPAM1_EL1, 0, 16)
          },
          0 => {
              partid = slice(MPAM0_EL1, 0, 16)
          },
          _ => {
              partid = undefined : bits(16)
          }
        }
    } else {
        match MPAMn {
          3 => {
              partid = slice(MPAM3_EL3, 16, 16)
          },
          2 => {
              partid = if el2avail then slice(MPAM2_EL2, 16, 16) else Zeros()
          },
          1 => {
              partid = slice(MPAM1_EL1, 16, 16)
          },
          0 => {
              partid = slice(MPAM0_EL1, 16, 16)
          },
          _ => {
              partid = undefined : bits(16)
          }
        }
    };
    partid
}

val MPAMisVirtual : forall ('el : Int).
  int('el) -> bool effect {escape, rreg, undef}

function MPAMisVirtual el = {
    ([MPAMIDR_EL1[17]] == 0b1 & EL2Enabled()) & (el == 0 & [MPAMHCR_EL2[0]] == 0b1 | el == 1 & [MPAMHCR_EL2[1]] == 0b1)
}

val genPARTID : forall ('el : Int) ('InD : Bool).
  (int('el), bool('InD)) -> (bits(16), bool) effect {escape, rreg, undef}

function genPARTID (el, InD) = {
    let partidel = getMPAM_PARTID(el, InD);
    let 'partid_max = UInt(slice(MPAMIDR_EL1, 0, 16));
    if UInt(partidel) > partid_max then {
        return((DefaultPARTID, true))
    };
    if MPAMisVirtual(el) then {
        return(MAP_vPARTID(partidel))
    } else {
        return((partidel, false))
    }
}

val genMPAM : forall ('el : Int) ('InD : Bool) ('secure : Bool).
  (int('el), bool('InD), bool('secure)) -> MPAMinfo effect {escape, rreg, undef}

function genMPAM (el, InD, secure) = {
    returnInfo : MPAMinfo = undefined : MPAMinfo;
    partidel : bits(16) = undefined : bits(16);
    perr : bool = undefined : bool;
    let gstplk = ((el == 0 & EL2Enabled()) & [MPAMHCR_EL2[8]] == 0b1) & [HCR_EL2[27]] == 0b0;
    let 'eff_el = if gstplk then 1 else el;
    (partidel, perr) = genPARTID(eff_el, InD);
    let groupel : bits(8) = genPMG(eff_el, InD, perr);
    returnInfo.mpam_ns = if secure then 0b0 else 0b1;
    returnInfo.partid = partidel;
    returnInfo.pmg = groupel;
    returnInfo
}

val HasS2Translation : unit -> bool effect {escape, rreg, undef}

function HasS2Translation () = {
    (EL2Enabled() & ~(IsInHost())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)
}

val AArch64_PendingUnmaskedVirtualInterrupts : bits(3) -> (bool, bool, bool) effect {escape, rreg, undef}

function AArch64_PendingUnmaskedVirtualInterrupts mask = {
    pending : bits(3) = undefined : bits(3);
    if (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & [HCR_EL2[27]] == 0b0 then {
        pending = (HCR_EL2[8 .. 8] @ (HCR_EL2[7 .. 7] @ HCR_EL2[6 .. 6])) & (HCR_EL2[5 .. 5] @ (HCR_EL2[4 .. 4] @ HCR_EL2[3 .. 3]))
    } else {
        pending = 0b000
    };
    let unmasked_pending : bits(3) = pending & ~(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

val DoubleLockStatus : unit -> bool effect {escape, rreg, undef}

function DoubleLockStatus () = {
    if ~(HaveDoubleLock()) then {
        return(false)
    } else {
        if ELUsingAArch32(EL1) then {
            return(([get_DBGOSDLR()[0]] == 0b1 & [get_DBGPRCR()[0]] == 0b0) & ~(Halted()))
        } else {
            return(([OSDLR_EL1[0]] == 0b1 & [DBGPRCR_EL1[0]] == 0b0) & ~(Halted()))
        }
    }
}

val HaltingAllowed : unit -> bool effect {escape, rreg, undef}

function HaltingAllowed () = {
    if Halted() | DoubleLockStatus() then {
        return(false)
    } else {
        if IsSecure() then {
            return(ExternalSecureDebugEnabled())
        } else {
            return(ExternalDebugEnabled())
        }
    }
}

val HaltOnBreakpointOrWatchpoint : unit -> bool effect {escape, rreg, undef}

function HaltOnBreakpointOrWatchpoint () = {
    (HaltingAllowed() & [EDSCR[14]] == 0b1) & [OSLSR_EL1[1]] == 0b0
}

val DebugTargetFrom : forall ('secure : Bool).
  bool('secure) -> bits(2) effect {escape, rreg, undef}

function DebugTargetFrom secure = {
    route_to_el2 : bool = undefined : bool;
    if HaveEL(EL2) & ~(secure) then {
        if ELUsingAArch32(EL2) then {
            route_to_el2 = [get_HDCR()[8]] == 0b1 | [get_HCR()[27]] == 0b1
        } else {
            route_to_el2 = [MDCR_EL2[8]] == 0b1 | [HCR_EL2[27]] == 0b1
        }
    } else {
        route_to_el2 = false
    };
    target : bits(2) = undefined : bits(2);
    if route_to_el2 then {
        target = EL2
    } else {
        if (HaveEL(EL3) & HighestELUsingAArch32()) & secure then {
            target = EL3
        } else {
            target = EL1
        }
    };
    target
}

val DebugTarget : unit -> bits(2) effect {escape, rreg, undef}

function DebugTarget () = {
    let secure = IsSecure();
    DebugTargetFrom(secure)
}

val BadMode : bits(5) -> bool effect {escape, rreg, undef}

function BadMode mode = {
    valid_name : bool = undefined : bool;
    match mode {
      ? if ? == M32_Monitor => {
          valid_name = HaveAArch32EL(EL3)
      },
      ? if ? == M32_Hyp => {
          valid_name = HaveAArch32EL(EL2)
      },
      ? if ? == M32_FIQ => {
          valid_name = HaveAArch32EL(EL1)
      },
      ? if ? == M32_IRQ => {
          valid_name = HaveAArch32EL(EL1)
      },
      ? if ? == M32_Svc => {
          valid_name = HaveAArch32EL(EL1)
      },
      ? if ? == M32_Abort => {
          valid_name = HaveAArch32EL(EL1)
      },
      ? if ? == M32_Undef => {
          valid_name = HaveAArch32EL(EL1)
      },
      ? if ? == M32_System => {
          valid_name = HaveAArch32EL(EL1)
      },
      ? if ? == M32_User => {
          valid_name = HaveAArch32EL(EL0)
      },
      _ => {
          valid_name = false
      }
    };
    let valid_name = valid_name;
    ~(valid_name)
}

val aset_Rmode : forall ('n : Int), ('n >= 0 & 'n <= 14).
  (int('n), bits(5), bits(32)) -> unit effect {escape, rreg, undef, wreg}

function aset_Rmode (n, mode, value_name) = {
    assert(n >= 0 & n <= 14);
    if ~(IsSecure()) then {
        assert(mode != M32_Monitor)
    };
    assert(~(BadMode(mode)));
    if mode == M32_Monitor then {
        if n == 13 then {
            SP_mon = value_name
        } else {
            if n == 14 then {
                LR_mon = value_name
            } else {
                __tc1 : bits(64) = _R(n);
                __tc1 = __SetSlice_bits(64, 32, __tc1, 0, value_name);
                _R(n) = __tc1
            }
        }
    } else {
        if ~(HighestELUsingAArch32()) & ConstrainUnpredictableBool(Unpredictable_ZEROUPPER) then {
            _R(LookUpRIndex(n, mode)) = ZeroExtend(value_name)
        } else {
            __tc2 : bits(64) = _R(LookUpRIndex(n, mode));
            __tc2 = __SetSlice_bits(64, 32, __tc2, 0, value_name);
            _R(LookUpRIndex(n, mode)) = __tc2
        }
    };
    return()
}

overload Rmode = {aset_Rmode}

val aset_R : forall ('n : Int), ('n >= 0 & 'n <= 14).
  (int('n), bits(32)) -> unit effect {escape, rreg, undef, wreg}

function aset_R (n, value_name) = {
    Rmode(n, PSTATE.M) = value_name;
    return()
}

overload R = {aset_R}

val ELFromM32 : bits(5) -> (bool, bits(2)) effect {escape, rreg, undef}

function ELFromM32 mode = {
    el : bits(2) = undefined : bits(2);
    valid_name : bool = ~(BadMode(mode));
    match mode {
      ? if ? == M32_Monitor => {
          el = EL3
      },
      ? if ? == M32_Hyp => {
          el = EL2;
          valid_name = valid_name & (~(HaveEL(EL3)) | [SCR_GEN()[0]] == 0b1)
      },
      ? if ? == M32_FIQ => {
          el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [get_SCR()[0]] == 0b0 then EL3 else EL1
      },
      ? if ? == M32_IRQ => {
          el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [get_SCR()[0]] == 0b0 then EL3 else EL1
      },
      ? if ? == M32_Svc => {
          el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [get_SCR()[0]] == 0b0 then EL3 else EL1
      },
      ? if ? == M32_Abort => {
          el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [get_SCR()[0]] == 0b0 then EL3 else EL1
      },
      ? if ? == M32_Undef => {
          el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [get_SCR()[0]] == 0b0 then EL3 else EL1
      },
      ? if ? == M32_System => {
          el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [get_SCR()[0]] == 0b0 then EL3 else EL1
      },
      ? if ? == M32_User => {
          el = EL0
      },
      _ => {
          valid_name = false
      }
    };
    if ~(valid_name) then {
        el = undefined : bits(2)
    };
    return((valid_name, el))
}

val GenMPAMcurEL : forall ('InD : Bool).
  bool('InD) -> MPAMinfo effect {escape, rreg, undef}

function GenMPAMcurEL InD = {
    mpamel : bits(2) = undefined : bits(2);
    validEL_name : bool = undefined : bool;
    let secure = IsSecure();
    if HaveMPAMExt() & MPAMisEnabled() then {
        if UsingAArch32() then {
            (validEL_name, mpamel) = ELFromM32(PSTATE.M)
        } else {
            validEL_name = true;
            mpamel = PSTATE.EL
        };
        if validEL_name then {
            return(genMPAM(UInt(mpamel), InD, secure))
        }
    };
    DefaultMPAMinfo(secure)
}

val CreateAccessDescriptorPTW : forall ('secondstage : Bool) ('s2fs1walk : Bool) 'level.
  (AccType, bool('secondstage), bool('s2fs1walk), int('level)) -> AccessDescriptor effect {escape, rreg, undef}

function CreateAccessDescriptorPTW (acctype, secondstage, s2fs1walk, level) = {
    accdesc : AccessDescriptor = undefined : AccessDescriptor;
    accdesc.acctype = acctype;
    accdesc.mpam = GenMPAMcurEL(acctype == AccType_IFETCH | acctype == AccType_IC);
    accdesc.page_table_walk = true;
    accdesc.secondstage = s2fs1walk;
    accdesc.secondstage = secondstage;
    accdesc.level = level;
    accdesc
}

val CreateAccessDescriptor : AccType -> AccessDescriptor effect {escape, rreg, undef}

function CreateAccessDescriptor acctype = {
    accdesc : AccessDescriptor = undefined : AccessDescriptor;
    accdesc.acctype = acctype;
    accdesc.mpam = GenMPAMcurEL(acctype == AccType_IFETCH | acctype == AccType_IC);
    accdesc.page_table_walk = false;
    accdesc
}

val AArch32_WriteMode : bits(5) -> unit effect {escape, rreg, undef, wreg}

function AArch32_WriteMode mode = {
    el : bits(2) = undefined : bits(2);
    valid_name : bool = undefined : bool;
    (valid_name, el) = ELFromM32(mode);
    assert(valid_name);
    PSTATE.M = mode;
    PSTATE.EL = el;
    PSTATE.nRW = 0b1;
    PSTATE.SP = if mode == M32_User | mode == M32_System then 0b0 else 0b1;
    return()
}

val AddrTop : forall ('IsInstr : Bool).
  (bits(64), bool('IsInstr), bits(2)) -> int effect {escape, rreg, undef}

function AddrTop (address, IsInstr, el) = {
    assert(HaveEL(el));
    let regime = S1TranslationRegime(el);
    tbi : bits(1) = undefined : bits(1);
    tbid : bits(1) = undefined : bits(1);
    if ELUsingAArch32(regime) then {
        return(31)
    } else {
        match regime {
          ? if ? == EL1 => {
              tbi = if [address[55]] == 0b1 then [TCR_EL1[38]] else [TCR_EL1[37]];
              if HavePACExt() then {
                  tbid = if [address[55]] == 0b1 then [TCR_EL1[52]] else [TCR_EL1[51]]
              }
          },
          ? if ? == EL2 => {
              if HaveVirtHostExt() & ELIsInHost(el) then {
                  tbi = if [address[55]] == 0b1 then [TCR_EL2[38]] else [TCR_EL2[37]];
                  if HavePACExt() then {
                      tbid = if [address[55]] == 0b1 then [TCR_EL2[52]] else [TCR_EL2[51]]
                  }
              } else {
                  tbi = [TCR_EL2[20]];
                  if HavePACExt() then {
                      tbid = [TCR_EL2[29]]
                  }
              }
          },
          ? if ? == EL3 => {
              tbi = [TCR_EL3[20]];
              if HavePACExt() then {
                  tbid = [TCR_EL3[29]]
              }
          }
        }
    };
    if tbi == 0b1 & ((~(HavePACExt()) | tbid == 0b0) | ~(IsInstr)) then 55 else 63
}

val getTLBContext : forall ('secondstage : Bool).
  (bits(64), bool('secondstage), bits(1), AccType) -> TLBContext effect {escape, rreg, undef}

function getTLBContext (inputaddr, secondstage, s1_nonsecure, acctype) = {
    context : TLBContext = undefined : TLBContext;
    context.secondstage = secondstage;
    context.twostage = HasS2Translation();
    context.el = PSTATE.EL;
    secure : bool = undefined : bool;
    asidregister : bits(64) = undefined : bits(64);
    granule : bits(2) = undefined : bits(2);
    t_sz : bits(6) = undefined : bits(6);
    secure = IsSecure();
    let top = AddrTop(inputaddr, acctype == AccType_IFETCH, PSTATE.EL);
    if ~(secondstage) then {
        if PSTATE.nRW == 0b1 then {
            if PSTATE.EL == EL2 then {
                asidregister = Zeros();
                t_sz = ZeroExtend(slice(get_HTCR(), 0, 3))
            } else {
                asidregister = if [get_TTBCR()[22]] == 0b0 then get_TTBR0() else get_TTBR1();
                t_sz = ZeroExtend(slice(get_TTBCR(), 0, 3))
            };
            granule = 0b00
        } else {
            if PSTATE.EL == EL3 then {
                asidregister = TTBR0_EL3;
                granule = slice(TCR_EL3, 14, 2);
                t_sz = slice(TCR_EL3, 0, 6)
            } else {
                if IsInHost() then {
                    asidregister = if [TCR_EL2[22]] == 0b0 then TTBR0_EL2 else TTBR1_EL2;
                    if [inputaddr[top]] == 0b0 then {
                        granule = slice(TCR_EL2, 14, 2);
                        t_sz = slice(TCR_EL2, 0, 6)
                    } else {
                        granule = GranuleSizeTG0(slice(TCR_EL2, 30, 2));
                        t_sz = slice(TCR_EL2, 16, 6)
                    }
                } else {
                    if PSTATE.EL == EL2 then {
                        asidregister = TTBR0_EL2;
                        granule = slice(TCR_EL2, 14, 2);
                        t_sz = slice(TCR_EL2, 0, 6)
                    } else {
                        asidregister = if [TCR_EL1[22]] == 0b0 then TTBR0_EL1 else TTBR1_EL1;
                        if [inputaddr[top]] == 0b0 then {
                            granule = slice(TCR_EL1, 14, 2);
                            t_sz = slice(TCR_EL1, 0, 6)
                        } else {
                            granule = GranuleSizeTG0(slice(TCR_EL1, 30, 2));
                            t_sz = slice(TCR_EL1, 16, 6)
                        }
                    }
                }
            }
        }
    } else {
        if PSTATE.nRW == 0b1 then {
            asidregister = get_VTTBR();
            granule = 0b00;
            t_sz = ZeroExtend(slice(get_VTCR(), 0, 4))
        } else {
            secure = if IsSecureEL2Enabled() & IsSecure() then s1_nonsecure == 0b0 else false;
            if secure then {
                asidregister = VSTTBR_EL2;
                granule = slice(VSTCR_EL2, 14, 2);
                t_sz = slice(VSTCR_EL2, 0, 6)
            } else {
                asidregister = VTTBR_EL2;
                granule = slice(VTCR_EL2, 14, 2);
                t_sz = slice(VTCR_EL2, 0, 6)
            }
        }
    };
    context.secure = secure;
    context.asid = slice(asidregister, 48, 16);
    context.vmid = VTTBR_EL2[56 .. 49] @ VTTBR_EL2[48 .. 41];
    context.t_sz = t_sz;
    if granule == 0b00 then {
        context.granule_size = 12
    } else {
        if granule == 0b10 then {
            context.granule_size = 14
        } else {
            context.granule_size = 16
        }
    };
    context
}

val TLBLookup : (bits(64), bool, bits(1), AccType) -> TLBLine effect {escape, rreg, undef, wreg}

function TLBLookup (address, secondstage, s1_nonsecure, acctype) = {
    let context : TLBContext = getTLBContext(address, secondstage, s1_nonsecure, acctype);
    let 'idx = UInt(TLBIndex(address, context));
    let 'granule_size = context.granule_size;
    assert(constraint((- 'granule_size + 52 >= 0 & 'granule_size >= 0)));
    result : TLBLine = undefined : TLBLine;
    result = _TLB[idx];
    if (~(result.valid_name) | slice(result.address, granule_size, negate(granule_size) + 64) != slice(address, granule_size, negate(granule_size) + 64)) | ~(TLBContextMatch(result.context, context)) then {
        TLBMisses = TLBMisses + 1;
        result.valid_name = false
    } else {
        TLBHits = TLBHits + 1;
        __tc1 : FullAddress = result.data.addrdesc.paddress;
        __tc1.address = slice(result.data.addrdesc.paddress.address, granule_size, negate(granule_size) + 52) @ slice(address, 0, granule_size);
        __tc2 : AddressDescriptor = result.data.addrdesc;
        __tc2.paddress = __tc1;
        __tc3 : TLBRecord = result.data;
        __tc3.addrdesc = __tc2;
        result.data = __tc3
    };
    result
}

val TLBCache : forall ('secondstage : Bool).
  (bits(64), bool('secondstage), bits(1), AccType, TLBRecord) -> unit effect {escape, rreg, undef, wreg}

function TLBCache (address, secondstage, s1_nonsecure, acctype, data) = {
    let context = getTLBContext(address, secondstage, s1_nonsecure, acctype);
    let idx = UInt(TLBIndex(address, context));
    __tc1 : TLBLine = _TLB[idx];
    __tc1.address = address;
    _TLB[idx] = __tc1;
    __tc2 : TLBLine = _TLB[idx];
    __tc2.context = context;
    _TLB[idx] = __tc2;
    __tc3 : TLBLine = _TLB[idx];
    __tc3.data = data;
    _TLB[idx] = __tc3;
    __tc4 : DescriptorUpdate = _TLB[idx].data.descupdate;
    __tc4.AF = false;
    __tc5 : TLBRecord = _TLB[idx].data;
    __tc5.descupdate = __tc4;
    __tc6 : TLBLine = _TLB[idx];
    __tc6.data = __tc5;
    _TLB[idx] = __tc6;
    __tc7 : TLBLine = _TLB[idx];
    __tc7.valid_name = true;
    _TLB[idx] = __tc7
}

val AccessIsTagChecked : (bits(64), AccType) -> bool effect {escape, rreg, undef}

function AccessIsTagChecked (vaddr, acctype) = {
    if [PSTATE.M[4]] == 0b1 then {
        return(false)
    };
    if EffectiveTBI(vaddr, false, PSTATE.EL) == 0b0 then {
        return(false)
    };
    if EffectiveTCMA(vaddr, PSTATE.EL) == 0b1 & (slice(vaddr, 55, 5) == 0b00000 | slice(vaddr, 55, 5) == 0b11111) then {
        return(false)
    };
    if ~(AllocationTagAccessIsEnabled()) then {
        return(false)
    };
    if acctype == AccType_IFETCH | acctype == AccType_PTW then {
        return(false)
    };
    if acctype == AccType_NV2REGISTER then {
        return(false)
    };
    if PSTATE.TCO == 0b1 then {
        return(false)
    };
    if IsNonTagCheckedInstruction() then {
        return(false)
    };
    true
}

val AArch64_WatchpointByteMatch : forall ('n : Int).
  (int('n), AccType, bits(64)) -> bool effect {escape, rreg, undef}

function AArch64_WatchpointByteMatch (n, acctype, vaddress) = {
    let el : bits(2) = if HaveNV2Ext() & acctype == AccType_NV2REGISTER then EL2 else PSTATE.EL;
    let 'top = AddrTop(vaddress, false, el);
    bottom : int = undefined : int;
    bottom = if [DBGWVR_EL1[n][2]] == 0b1 then 2 else 3;
    let 'bottom_fixed = bottom;
    assert(constraint('bottom_fixed in {2, 3}));
    byte_select_match : bool = undefined : bool;
    byte_select_match = [slice(DBGWCR_EL1[n], 5, 8)[UInt(slice(vaddress, 0, bottom_fixed))]] != 0b0;
    mask : int = undefined : int;
    mask = UInt(slice(DBGWCR_EL1[n], 24, 5));
    LSB : bits(8) = undefined : bits(8);
    MSB : bits(8) = undefined : bits(8);
    if mask > 0 & ~(IsOnes(slice(DBGWCR_EL1[n], 5, 8))) then {
        byte_select_match = ConstrainUnpredictableBool(Unpredictable_WPMASKANDBAS)
    } else {
        LSB = slice(DBGWCR_EL1[n], 5, 8) & ~(slice(DBGWCR_EL1[n], 5, 8) - 1);
        MSB = slice(DBGWCR_EL1[n], 5, 8) + LSB;
        if ~(IsZero(MSB & MSB - 1)) then {
            byte_select_match = ConstrainUnpredictableBool(Unpredictable_WPBASCONTIGUOUS);
            bottom = 3
        }
    };
    c : Constraint = undefined : Constraint;
    if mask > 0 & mask <= 2 then {
        (c, mask) = ConstrainUnpredictableInteger(3, 31, Unpredictable_RESWPMASK);
        assert(c == Constraint_DISABLED | c == Constraint_NONE | c == Constraint_UNKNOWN);
        match c {
          Constraint_DISABLED => {
              return(false)
          },
          Constraint_NONE => {
              mask = 0
          }
        }
    };
    WVR_match : bool = undefined : bool;
    let 'bottom = bottom;
    assert(constraint('bottom in {2, 3}));
    if mask > bottom then {
        let 'mask = mask;
        assert(constraint(('top - 'mask + 1 >= 0 & 'mask - 'bottom >= 0)));
        WVR_match = slice(vaddress, mask, top - mask + 1) == slice(DBGWVR_EL1[n], mask, top - mask + 1);
        if WVR_match & ~(IsZero(slice(DBGWVR_EL1[n], bottom, mask - bottom))) then {
            WVR_match = ConstrainUnpredictableBool(Unpredictable_WPMASKEDBITS)
        }
    } else {
        let 'mask = mask;
        assert(constraint('top - 'bottom + 1 >= 0));
        WVR_match = slice(vaddress, bottom, top - bottom + 1) == slice(DBGWVR_EL1[n], bottom, top - bottom + 1)
    };
    WVR_match & byte_select_match
}

val AArch64_TranslateAddressS1Off : (bits(64), AccType, bool) -> TLBRecord effect {escape, rreg, undef}

function AArch64_TranslateAddressS1Off (vaddress, acctype, iswrite) = {
    assert(~(ELUsingAArch32(S1TranslationRegime())));
    result : TLBRecord = undefined : TLBRecord;
    result.descupdate.AF = false;
    result.descupdate.AP = false;
    let 'Top = AddrTop(vaddress, acctype == AccType_IFETCH, PSTATE.EL);
    ipaddress : bits(52) = undefined : bits(52);
    level : int = undefined : int;
    s2fs1walk : bool = undefined : bool;
    secondstage : bool = undefined : bool;
    let 'pa_max = PAMax();
    assert(constraint('Top + 1 - 'pa_max >= 0));
    if ~(IsZero(slice(vaddress, pa_max, Top + 1 - pa_max))) then {
        level = 0;
        ipaddress = undefined : bits(52);
        secondstage = false;
        s2fs1walk = false;
        __tc1 : AddressDescriptor = result.addrdesc;
        __tc1.fault = AArch64_AddressSizeFault(ipaddress, undefined : bits(1), level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc1;
        return(result)
    };
    let default_cacheable : bool = HasS2Translation() & [HCR_EL2[12]] == 0b1;
    cacheable : bool = undefined : bool;
    if default_cacheable then {
        __tc2 : MemoryAttributes = result.addrdesc.memattrs;
        __tc2.typ = MemType_Normal;
        __tc3 : AddressDescriptor = result.addrdesc;
        __tc3.memattrs = __tc2;
        result.addrdesc = __tc3;
        __tc4 : MemAttrHints = result.addrdesc.memattrs.inner;
        __tc4.attrs = MemAttr_WB;
        __tc5 : MemoryAttributes = result.addrdesc.memattrs;
        __tc5.inner = __tc4;
        __tc6 : AddressDescriptor = result.addrdesc;
        __tc6.memattrs = __tc5;
        result.addrdesc = __tc6;
        __tc7 : MemAttrHints = result.addrdesc.memattrs.inner;
        __tc7.hints = MemHint_RWA;
        __tc8 : MemoryAttributes = result.addrdesc.memattrs;
        __tc8.inner = __tc7;
        __tc9 : AddressDescriptor = result.addrdesc;
        __tc9.memattrs = __tc8;
        result.addrdesc = __tc9;
        __tc10 : MemoryAttributes = result.addrdesc.memattrs;
        __tc10.shareable = false;
        __tc11 : AddressDescriptor = result.addrdesc;
        __tc11.memattrs = __tc10;
        result.addrdesc = __tc11;
        __tc12 : MemoryAttributes = result.addrdesc.memattrs;
        __tc12.outershareable = false;
        __tc13 : AddressDescriptor = result.addrdesc;
        __tc13.memattrs = __tc12;
        result.addrdesc = __tc13;
        __tc14 : MemoryAttributes = result.addrdesc.memattrs;
        __tc14.tagged = [HCR_EL2[57]] == 0b1;
        __tc15 : AddressDescriptor = result.addrdesc;
        __tc15.memattrs = __tc14;
        result.addrdesc = __tc15
    } else {
        if acctype != AccType_IFETCH then {
            __tc16 : MemoryAttributes = result.addrdesc.memattrs;
            __tc16.typ = MemType_Device;
            __tc17 : AddressDescriptor = result.addrdesc;
            __tc17.memattrs = __tc16;
            result.addrdesc = __tc17;
            __tc18 : MemoryAttributes = result.addrdesc.memattrs;
            __tc18.device = DeviceType_nGnRnE;
            __tc19 : AddressDescriptor = result.addrdesc;
            __tc19.memattrs = __tc18;
            result.addrdesc = __tc19;
            __tc20 : MemoryAttributes = result.addrdesc.memattrs;
            __tc20.inner = undefined : MemAttrHints;
            __tc21 : AddressDescriptor = result.addrdesc;
            __tc21.memattrs = __tc20;
            result.addrdesc = __tc21;
            __tc22 : MemoryAttributes = result.addrdesc.memattrs;
            __tc22.tagged = false;
            __tc23 : AddressDescriptor = result.addrdesc;
            __tc23.memattrs = __tc22;
            result.addrdesc = __tc23
        } else {
            cacheable = [aget_SCTLR()[12]] == 0b1;
            __tc24 : MemoryAttributes = result.addrdesc.memattrs;
            __tc24.typ = MemType_Normal;
            __tc25 : AddressDescriptor = result.addrdesc;
            __tc25.memattrs = __tc24;
            result.addrdesc = __tc25;
            if cacheable then {
                __tc26 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc26.attrs = MemAttr_WT;
                __tc27 : MemoryAttributes = result.addrdesc.memattrs;
                __tc27.inner = __tc26;
                __tc28 : AddressDescriptor = result.addrdesc;
                __tc28.memattrs = __tc27;
                result.addrdesc = __tc28;
                __tc29 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc29.hints = MemHint_RA;
                __tc30 : MemoryAttributes = result.addrdesc.memattrs;
                __tc30.inner = __tc29;
                __tc31 : AddressDescriptor = result.addrdesc;
                __tc31.memattrs = __tc30;
                result.addrdesc = __tc31
            } else {
                __tc32 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc32.attrs = MemAttr_NC;
                __tc33 : MemoryAttributes = result.addrdesc.memattrs;
                __tc33.inner = __tc32;
                __tc34 : AddressDescriptor = result.addrdesc;
                __tc34.memattrs = __tc33;
                result.addrdesc = __tc34;
                __tc35 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc35.hints = MemHint_No;
                __tc36 : MemoryAttributes = result.addrdesc.memattrs;
                __tc36.inner = __tc35;
                __tc37 : AddressDescriptor = result.addrdesc;
                __tc37.memattrs = __tc36;
                result.addrdesc = __tc37
            };
            __tc38 : MemoryAttributes = result.addrdesc.memattrs;
            __tc38.shareable = true;
            __tc39 : AddressDescriptor = result.addrdesc;
            __tc39.memattrs = __tc38;
            result.addrdesc = __tc39;
            __tc40 : MemoryAttributes = result.addrdesc.memattrs;
            __tc40.outershareable = true;
            __tc41 : AddressDescriptor = result.addrdesc;
            __tc41.memattrs = __tc40;
            result.addrdesc = __tc41;
            __tc42 : MemoryAttributes = result.addrdesc.memattrs;
            __tc42.tagged = false;
            __tc43 : AddressDescriptor = result.addrdesc;
            __tc43.memattrs = __tc42;
            result.addrdesc = __tc43
        }
    };
    __tc44 : MemoryAttributes = result.addrdesc.memattrs;
    __tc44.outer = result.addrdesc.memattrs.inner;
    __tc45 : AddressDescriptor = result.addrdesc;
    __tc45.memattrs = __tc44;
    result.addrdesc = __tc45;
    __tc46 : AddressDescriptor = result.addrdesc;
    __tc46.memattrs = MemAttrDefaults(result.addrdesc.memattrs);
    result.addrdesc = __tc46;
    __tc47 : Permissions = result.perms;
    __tc47.ap = undefined : bits(3);
    result.perms = __tc47;
    __tc48 : Permissions = result.perms;
    __tc48.xn = 0b0;
    result.perms = __tc48;
    __tc49 : Permissions = result.perms;
    __tc49.pxn = 0b0;
    result.perms = __tc49;
    result.nG = undefined : bits(1);
    result.contiguous = undefined : bool;
    result.domain = undefined : bits(4);
    result.level = undefined : int;
    result.blocksize = undefined : int;
    __tc50 : FullAddress = result.addrdesc.paddress;
    __tc50.address = slice(vaddress, 0, 52);
    __tc51 : AddressDescriptor = result.addrdesc;
    __tc51.paddress = __tc50;
    result.addrdesc = __tc51;
    __tc52 : FullAddress = result.addrdesc.paddress;
    __tc52.NS = if IsSecure() then 0b0 else 0b1;
    __tc53 : AddressDescriptor = result.addrdesc;
    __tc53.paddress = __tc52;
    result.addrdesc = __tc53;
    __tc54 : AddressDescriptor = result.addrdesc;
    __tc54.fault = AArch64_NoFault();
    result.addrdesc = __tc54;
    result
}

val AArch64_S1AttrDecode : (bits(2), bits(3), AccType) -> MemoryAttributes effect {escape, rreg, undef}

function AArch64_S1AttrDecode (SH, attr, acctype) = {
    memattrs : MemoryAttributes = undefined : MemoryAttributes;
    let mair = MAIR();
    let index = 8 * UInt(attr);
    attrfield : bits(8) = undefined : bits(8);
    attrfield = slice(mair, index, 8);
    memattrs.tagged = false;
    __anon1 : Constraint = undefined : Constraint;
    if (slice(attrfield, 4, 4) != 0x0 & slice(attrfield, 4, 4) != 0xF) & slice(attrfield, 0, 4) == 0x0 | slice(attrfield, 4, 4) == 0x0 & (slice(attrfield, 0, 4) & 0x3) != 0x0 then {
        (__anon1, attrfield) = ConstrainUnpredictableBits(Unpredictable_RESMAIR)
    };
    __anon2 : Constraint = undefined : Constraint;
    if (~(HaveMTEExt()) & slice(attrfield, 4, 4) == 0xF) & slice(attrfield, 0, 4) == 0x0 then {
        (__anon2, attrfield) = ConstrainUnpredictableBits(Unpredictable_RESMAIR)
    };
    if slice(attrfield, 4, 4) == 0x0 then {
        memattrs.typ = MemType_Device;
        match slice(attrfield, 0, 4) {
          0x0 => {
              memattrs.device = DeviceType_nGnRnE
          },
          0x4 => {
              memattrs.device = DeviceType_nGnRE
          },
          0x8 => {
              memattrs.device = DeviceType_nGRE
          },
          0xC => {
              memattrs.device = DeviceType_GRE
          },
          _ => {
              Unreachable()
          }
        }
    } else {
        if slice(attrfield, 0, 4) != 0x0 then {
            memattrs.typ = MemType_Normal;
            memattrs.outer = LongConvertAttrsHints(slice(attrfield, 4, 4), acctype);
            memattrs.inner = LongConvertAttrsHints(slice(attrfield, 0, 4), acctype);
            memattrs.shareable = [SH[1]] == 0b1;
            memattrs.outershareable = SH == 0b10
        } else {
            if HaveMTEExt() & attrfield == 0xF0 then {
                memattrs.tagged = true;
                memattrs.typ = MemType_Normal;
                __tc1 : MemAttrHints = memattrs.outer;
                __tc1.attrs = MemAttr_WB;
                memattrs.outer = __tc1;
                __tc2 : MemAttrHints = memattrs.inner;
                __tc2.attrs = MemAttr_WB;
                memattrs.inner = __tc2;
                __tc3 : MemAttrHints = memattrs.outer;
                __tc3.hints = MemHint_RWA;
                memattrs.outer = __tc3;
                __tc4 : MemAttrHints = memattrs.inner;
                __tc4.hints = MemHint_RWA;
                memattrs.inner = __tc4;
                memattrs.shareable = [SH[1]] == 0b1;
                memattrs.outershareable = SH == 0b10
            } else {
                Unreachable()
            }
        }
    };
    MemAttrDefaults(memattrs)
}

val AArch64_PendingUnmaskedPhysicalInterrupts : bits(3) -> (bool, bool, bool) effect {escape, rreg, undef}

function AArch64_PendingUnmaskedPhysicalInterrupts mask__arg = {
    mask = mask__arg;
    let se_pending = if IsPhysicalSErrorPending() then 0b1 else 0b0;
    let irq_pending = if IRQPending() then 0b1 else 0b0;
    let fiq_pending = if FIQPending() then 0b1 else 0b0;
    let pending : bits(3) = (se_pending @ irq_pending) @ fiq_pending;
    mask_override : bits(3) = undefined : bits(3);
    if EL2Enabled() then {
        if (HaveVirtHostExt() & [HCR_EL2[34]] == 0b1) & [HCR_EL2[27]] == 0b1 then {
            mask_override = 0b000
        } else {
            if [HCR_EL2[27]] == 0b1 then {
                mask_override = 0b111
            } else {
                mask_override = HCR_EL2[5 .. 5] @ (HCR_EL2[4 .. 4] @ HCR_EL2[3 .. 3])
            }
        };
        if PSTATE.EL == EL1 | PSTATE.EL == EL0 then {
            mask = mask & ~(mask_override)
        } else {
            if ~(ELUsingAArch32(EL2)) & [HCR_EL2[27]] == 0b0 then {
                mask = mask | ~(mask_override)
            }
        }
    };
    if HaveEL(EL3) then {
        if PSTATE.EL != EL3 then {
            mask = mask & ~(SCR_EL3[3 .. 3] @ (SCR_EL3[1 .. 1] @ SCR_EL3[2 .. 2]))
        } else {
            mask = mask | ~(SCR_EL3[3 .. 3] @ (SCR_EL3[1 .. 1] @ SCR_EL3[2 .. 2]))
        }
    };
    let unmasked_pending : bits(3) = pending & ~(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

val AArch64_MaybeZeroRegisterUppers : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_MaybeZeroRegisterUppers () = {
    assert(UsingAArch32());
    let first = 0;
    include_R15_name : bool = undefined : bool;
    last : int = undefined : int;
    if PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1)) then {
        last = 14;
        include_R15_name = false
    } else {
        if ((PSTATE.EL == EL0 | PSTATE.EL == EL1) & EL2Enabled()) & ~(ELUsingAArch32(EL2)) then {
            last = 30;
            include_R15_name = false
        } else {
            last = 30;
            include_R15_name = true
        }
    };
    let 'last = last;
    assert(constraint('last <= 30));
    foreach (n from first to last by 1 in inc) {
        if (n != 15 | include_R15_name) & ConstrainUnpredictableBool(Unpredictable_ZEROUPPER) then {
            __tc1 : bits(64) = _R(n);
            __tc1 = __SetSlice_bits(64, 32, __tc1, 32, Zeros());
            _R(n) = __tc1
        }
    };
    return()
}

val AArch64_GenerateDebugExceptionsFrom : forall ('secure : Bool).
  (bits(2), bool('secure), bits(1)) -> bool effect {escape, rreg, undef}

function AArch64_GenerateDebugExceptionsFrom (from, secure, mask) = {
    if ([OSLSR_EL1[1]] == 0b1 | DoubleLockStatus()) | Halted() then {
        return(false)
    };
    let route_to_el2 = (HaveEL(EL2) & ~(secure)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
    let target : bits(2) = if route_to_el2 then EL2 else EL1;
    enabled : bool = undefined : bool;
    enabled = (~(HaveEL(EL3)) | ~(secure)) | [MDCR_EL3[16]] == 0b0;
    if from == target then {
        enabled = (enabled & [MDSCR_EL1[13]] == 0b1) & mask == 0b0
    } else {
        enabled = enabled & UInt(target) > UInt(from)
    };
    enabled
}

val AArch64_GenerateDebugExceptions : unit -> bool effect {escape, rreg, undef}

function AArch64_GenerateDebugExceptions () = {
    AArch64_GenerateDebugExceptionsFrom(PSTATE.EL, IsSecure(), PSTATE.D)
}

val AArch64_FaultSyndrome : forall ('d_side : Bool).
  (bool('d_side), FaultRecord) -> bits(25) effect {escape, rreg, undef}

function AArch64_FaultSyndrome (d_side, fault) = {
    assert(fault.typ != Fault_None);
    iss : bits(25) = Zeros();
    if HaveRASExt() & IsExternalSyncAbort(fault) then {
        iss = __SetSlice_bits(25, 2, iss, 11, fault.errortype)
    };
    if d_side then {
        if IsSecondStage(fault) & ~(fault.s2fs1walk) then {
            iss = __SetSlice_bits(25, 11, iss, 14, LSInstructionSyndrome())
        };
        if HaveNV2Ext() & fault.acctype == AccType_NV2REGISTER then {
            iss = __SetSlice_bits(25, 1, iss, 13, 0b1)
        };
        if fault.acctype == AccType_DC | fault.acctype == AccType_DC_UNPRIV | fault.acctype == AccType_IC | fault.acctype == AccType_AT then {
            iss = __SetSlice_bits(25, 1, iss, 8, 0b1);
            iss = __SetSlice_bits(25, 1, iss, 6, 0b1)
        } else {
            iss = __SetSlice_bits(25, 1, iss, 6, if fault.write then 0b1 else 0b0)
        }
    };
    if IsExternalAbort(fault) then {
        iss = __SetSlice_bits(25, 1, iss, 9, fault.extflag)
    };
    iss = __SetSlice_bits(25, 1, iss, 7, if fault.s2fs1walk then 0b1 else 0b0);
    let iss = __SetSlice_bits(25, 6, iss, 0, EncodeLDFSC(fault.typ, fault.level));
    iss
}

val AArch64_AbortSyndrome : (Exception, FaultRecord, bits(64)) -> ExceptionRecord effect {escape, rreg, undef}

function AArch64_AbortSyndrome (typ, fault, vaddress) = {
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(typ);
    let d_side = typ == Exception_DataAbort | typ == Exception_NV2DataAbort | typ == Exception_Watchpoint;
    exception.syndrome = AArch64_FaultSyndrome(d_side, fault);
    exception.vaddress = ZeroExtend(vaddress);
    if IPAValid(fault) then {
        exception.ipavalid = true;
        exception.NS = fault.ipaddress.NS;
        exception.ipaddress = fault.ipaddress.address
    } else {
        exception.ipavalid = false
    };
    exception
}

val AArch64_ExecutingATS1xPInstr : unit -> bool effect {rreg, undef}

function AArch64_ExecutingATS1xPInstr () = {
    if ~(HavePrivATExt()) then {
        return(false)
    };
    let instr = ThisInstr();
    CRm : bits(4) = undefined : bits(4);
    CRn : bits(4) = undefined : bits(4);
    op1 : bits(3) = undefined : bits(3);
    op2 : bits(3) = undefined : bits(3);
    if slice(instr, 22, 10) == 0b1101010100 then {
        op1 = slice(instr, 16, 3);
        CRn = slice(instr, 12, 4);
        CRm = slice(instr, 8, 4);
        op2 = slice(instr, 5, 3);
        return(((op1 == 0b000 & CRn == 0x7) & CRm == 0x9) & (op2 == 0b000 | op2 == 0b001))
    } else {
        return(false)
    }
}

val AArch64_ExceptionClass : (Exception, bits(2)) -> (int, bits(1)) effect {escape, rreg, undef}

function AArch64_ExceptionClass (typ, target_el) = {
    il : bits(1) = undefined : bits(1);
    il = if ThisInstrLength() == 32 then 0b1 else 0b0;
    let from_32 = UsingAArch32();
    assert(from_32 | il == 0b1);
    ec : int = undefined : int;
    match typ {
      Exception_Uncategorized => {
          ec = 0;
          il = 0b1
      },
      Exception_WFxTrap => {
          ec = 1
      },
      Exception_CP15RTTrap => {
          ec = 3;
          assert(from_32)
      },
      Exception_CP15RRTTrap => {
          ec = 4;
          assert(from_32)
      },
      Exception_CP14RTTrap => {
          ec = 5;
          assert(from_32)
      },
      Exception_CP14DTTrap => {
          ec = 6;
          assert(from_32)
      },
      Exception_AdvSIMDFPAccessTrap => {
          ec = 7
      },
      Exception_FPIDTrap => {
          ec = 8
      },
      Exception_PACTrap => {
          ec = 9
      },
      Exception_CP14RRTTrap => {
          ec = 12;
          assert(from_32)
      },
      Exception_BranchTarget => {
          ec = 13
      },
      Exception_IllegalState => {
          ec = 14;
          il = 0b1
      },
      Exception_SupervisorCall => {
          ec = 17
      },
      Exception_HypervisorCall => {
          ec = 18
      },
      Exception_MonitorCall => {
          ec = 19
      },
      Exception_SystemRegisterTrap => {
          ec = 24;
          assert(~(from_32))
      },
      Exception_ERetTrap => {
          ec = 26
      },
      Exception_InstructionAbort => {
          ec = 32;
          il = 0b1
      },
      Exception_PCAlignment => {
          ec = 34;
          il = 0b1
      },
      Exception_DataAbort => {
          ec = 36
      },
      Exception_NV2DataAbort => {
          ec = 37
      },
      Exception_SPAlignment => {
          ec = 38;
          il = 0b1;
          assert(~(from_32))
      },
      Exception_FPTrappedException => {
          ec = 40
      },
      Exception_SError => {
          ec = 47;
          il = 0b1
      },
      Exception_Breakpoint => {
          ec = 48;
          il = 0b1
      },
      Exception_SoftwareStep => {
          ec = 50;
          il = 0b1
      },
      Exception_Watchpoint => {
          ec = 52;
          il = 0b1
      },
      Exception_SoftwareBreakpoint => {
          ec = 56
      },
      Exception_VectorCatch => {
          ec = 58;
          il = 0b1;
          assert(from_32)
      },
      _ => {
          Unreachable()
      }
    };
    if (ec == 32 | ec == 36 | ec == 48 | ec == 50 | ec == 52) & target_el == PSTATE.EL then {
        ec = ec + 1
    };
    if (ec == 17 | ec == 18 | ec == 19 | ec == 40 | ec == 56) & ~(from_32) then {
        ec = ec + 4
    };
    return((ec, il))
}

val AArch64_ReportException : (ExceptionRecord, bits(2)) -> unit effect {escape, rreg, undef, wreg}

function AArch64_ReportException (exception, target_el) = {
    let typ = exception.typ;
    ec : int = undefined : int;
    il : bits(1) = undefined : bits(1);
    (ec, il) = AArch64_ExceptionClass(typ, target_el);
    let iss = exception.syndrome;
    if (ec == 36 | ec == 37) & [iss[24]] == 0b0 then {
        il = 0b1
    };
    ESR(target_el) = (__GetSlice_int(6, ec, 0) @ il) @ iss;
    if typ == Exception_InstructionAbort | typ == Exception_PCAlignment | typ == Exception_DataAbort | typ == Exception_NV2DataAbort | typ == Exception_Watchpoint then {
        FAR(target_el) = exception.vaddress
    } else {
        FAR(target_el) = undefined : bits(64)
    };
    if target_el == EL2 then {
        if exception.ipavalid then {
            HPFAR_EL2 = __SetSlice_bits(64, 40, HPFAR_EL2, 4, slice(exception.ipaddress, 12, 40));
            if HaveSecureEL2Ext() then {
                if IsSecureEL2Enabled() then {
                    HPFAR_EL2 = __SetSlice_bits(64, 1, HPFAR_EL2, 63, exception.NS)
                } else {
                    HPFAR_EL2 = __SetSlice_bits(64, 1, HPFAR_EL2, 63, 0b0)
                }
            }
        } else {
            HPFAR_EL2 = __SetSlice_bits(64, 40, HPFAR_EL2, 4, undefined : bits(40))
        }
    };
    return()
}

val AArch64_CheckS2Permission : forall 'level ('iswrite : Bool) ('s2fs1walk : Bool) ('hwupdatewalk : Bool).
  (Permissions, bits(64), bits(52), int('level), AccType, bool('iswrite), bits(1), bool('s2fs1walk), bool('hwupdatewalk)) -> FaultRecord effect {escape, rreg, undef}

function AArch64_CheckS2Permission (perms, vaddress, ipaddress, level, acctype, iswrite, NS, s2fs1walk, hwupdatewalk) = {
    assert((IsSecureEL2Enabled() | (HaveEL(EL2) & ~(IsSecure())) & ~(ELUsingAArch32(EL2))) & HasS2Translation());
    let r = [perms.ap[1]] == 0b1;
    let w = [perms.ap[2]] == 0b1;
    xn : bool = undefined : bool;
    if HaveExtendedExecuteNeverExt() then {
        match perms.xn @ perms.xxn {
          0b00 => {
              xn = false
          },
          0b01 => {
              xn = PSTATE.EL == EL1
          },
          0b10 => {
              xn = true
          },
          0b11 => {
              xn = PSTATE.EL == EL0
          }
        }
    } else {
        xn = perms.xn == 0b1
    };
    fail : bool = undefined : bool;
    failedread : bool = undefined : bool;
    if acctype == AccType_IFETCH /* & ~(s2fs1walk) */ then {
        fail = xn;
        failedread = true
    } else {
        if (acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW | acctype == AccType_ORDEREDATOMICRW) & ~(s2fs1walk) then {
            fail = ~(r) | ~(w);
            failedread = ~(r)
        } else {
            if iswrite & ~(s2fs1walk) then {
                fail = ~(w);
                failedread = false
            } else {
                if (acctype == AccType_DC & PSTATE.EL != EL0) & ~(s2fs1walk) then {
                    fail = false
                } else {
                    if hwupdatewalk then {
                        fail = ~(w);
                        failedread = ~(iswrite)
                    } else {
                        fail = ~(r);
                        failedread = ~(iswrite)
                    }
                }
            }
        }
    };
    domain : bits(4) = undefined : bits(4);
    secondstage : bool = undefined : bool;
    if fail then {
        domain = undefined : bits(4);
        secondstage = true;
        return(AArch64_PermissionFault(ipaddress, NS, level, acctype, ~(failedread), secondstage, s2fs1walk))
    } else {
        return(AArch64_NoFault())
    }
}

val AArch64_SecondStageTranslate : forall ('iswrite : Bool) ('wasaligned : Bool) ('s2fs1walk : Bool) 'size ('hwupdatewalk : Bool).
  (AddressDescriptor, bits(64), AccType, bool('iswrite), bool('wasaligned), bool('s2fs1walk), int('size), bool('hwupdatewalk)) -> (AddressDescriptor, option(TranslationInfo)) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_SecondStageTranslate (S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size, hwupdatewalk) = {
    assert(HasS2Translation());
    let s2_enabled = [HCR_EL2[0]] == 0b1 | [HCR_EL2[12]] == 0b1;
    let secondstage = true;
    NS : bits(1) = undefined : bits(1);
    S2 : TLBRecord = undefined : TLBRecord;
    translation_info : option(TranslationInfo) = None();
    ipaddress : bits(52) = undefined : bits(52);
    result : AddressDescriptor = undefined : AddressDescriptor;
    if s2_enabled then {
        ipaddress = slice(S1.paddress.address, 0, 52);
        NS = S1.paddress.NS;
        (S2, translation_info) = AArch64_TranslationTableWalk(ipaddress, NS, vaddress, acctype, iswrite, secondstage, s2fs1walk, size);
        if ((~(wasaligned) & acctype != AccType_IFETCH | acctype == AccType_DCZVA) & S2.addrdesc.memattrs.typ == MemType_Device) & ~(IsFault(S2.addrdesc)) then {
            __tc1 : AddressDescriptor = S2.addrdesc;
            __tc1.fault = AArch64_AlignmentFault(acctype, iswrite, secondstage);
            S2.addrdesc = __tc1
        };
        if ~(IsFault(S2.addrdesc)) then {
            __tc2 : AddressDescriptor = S2.addrdesc;
            __tc2.fault = AArch64_CheckS2Permission(S2.perms, vaddress, ipaddress, S2.level, acctype, iswrite, NS, s2fs1walk, hwupdatewalk);
            S2.addrdesc = __tc2
        };
        if ((~(s2fs1walk) & ~(IsFault(S2.addrdesc))) & S2.addrdesc.memattrs.typ == MemType_Device) & acctype == AccType_IFETCH then {
            S2.addrdesc = AArch64_InstructionDevice(S2.addrdesc, vaddress, ipaddress, S2.level, acctype, iswrite, secondstage, s2fs1walk)
        };
        if ((s2fs1walk & ~(IsFault(S2.addrdesc))) & [HCR_EL2[2]] == 0b1) & S2.addrdesc.memattrs.typ == MemType_Device then {
            __tc3 : AddressDescriptor = S2.addrdesc;
            __tc3.fault = AArch64_PermissionFault(ipaddress, S1.paddress.NS, S2.level, acctype, iswrite, secondstage, s2fs1walk);
            S2.addrdesc = __tc3
        };
        __tc4 : AddressDescriptor = S2.addrdesc;
        __tc4.fault = AArch64_CheckAndUpdateDescriptor(S2.descupdate, S2.addrdesc.fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk);
        S2.addrdesc = __tc4;
        result = CombineS1S2Desc(S1, S2.addrdesc)
    } else {
        result = S1
    };
    (result, translation_info)
}

val AArch64_SecondStageWalk : forall ('iswrite : Bool) 'size ('hwupdatewalk : Bool).
  (AddressDescriptor, bits(64), AccType, bool('iswrite), int('size), bool('hwupdatewalk)) -> (AddressDescriptor, option(TranslationInfo)) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_SecondStageWalk (S1, vaddress, acctype, iswrite, size, hwupdatewalk) = {
    assert(HasS2Translation());
    let s2fs1walk = true;
    let wasaligned = true;
    AArch64_SecondStageTranslate(S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size, hwupdatewalk)
}

val AArch64_BreakpointValueMatch : forall ('n : Int).
  (int('n), bits(64), bool) -> bool effect {escape, rreg, undef}

function AArch64_BreakpointValueMatch (n__arg, vaddress, linked_to) = {
    n : int = n__arg;
    c : Constraint = undefined : Constraint;
    if n > UInt(slice(ID_AA64DFR0_EL1, 12, 4)) then {
        (c, n) = ConstrainUnpredictableInteger(0, UInt(slice(ID_AA64DFR0_EL1, 12, 4)), Unpredictable_BPNOTIMPL);
        assert(c == Constraint_DISABLED | c == Constraint_UNKNOWN);
        if c == Constraint_DISABLED then {
            return(false)
        }
    };
    if [DBGBCR_EL1[n][0]] == 0b0 then {
        return(false)
    };
    let context_aware : bool = n >= UInt(slice(ID_AA64DFR0_EL1, 12, 4)) - UInt(slice(ID_AA64DFR0_EL1, 28, 4));
    typ : bits(4) = undefined : bits(4);
    typ = slice(DBGBCR_EL1[n], 20, 4);
    if ((((typ & 0xE) == 0x6 | (typ & 0xC) == 0xC) & ~(HaveVirtHostExt()) | (typ & 0xE) == 0x4) | (typ & 0xA) != 0x0 & ~(context_aware)) | (typ & 0x8) == 0x8 & ~(HaveEL(EL2)) then {
        (c, typ) = ConstrainUnpredictableBits(Unpredictable_RESBPTYPE);
        assert(c == Constraint_DISABLED | c == Constraint_UNKNOWN);
        if c == Constraint_DISABLED then {
            return(false)
        }
    };
    let match_addr : bool = (typ & 0xA) == 0x0;
    let match_vmid : bool = (typ & 0xC) == 0x8;
    let match_cid : bool = (typ & 0xE) == 0x2;
    let match_cid1 : bool = (typ & 0xE) == 0xA | (typ & 0x6) == 0x6;
    let match_cid2 : bool = (typ & 0xC) == 0xC;
    let linked : bool = (typ & 0x1) == 0x1;
    if linked_to & (~(linked) | match_addr) then {
        return(false)
    };
    if (~(linked_to) & linked) & ~(match_addr) then {
        return(false)
    };
    BVR_match : bool = undefined : bool;
    byte : int = undefined : int;
    byte_select_match : bool = undefined : bool;
    if match_addr then {
        byte = UInt(slice(vaddress, 0, 2));
        if HaveAnyAArch32() then {
            assert(byte == 0 | byte == 2);
            byte_select_match = [slice(DBGBCR_EL1[n], 5, 4)[byte]] == 0b1
        } else {
            assert(byte == 0);
            byte_select_match = true
        };
        let 'top = AddrTop(vaddress, true, PSTATE.EL);
        assert(constraint('top - 1 >= 0));
        BVR_match = slice(vaddress, 2, top - 1) == slice(DBGBVR_EL1[n], 2, top - 1) & byte_select_match
    } else {
        if match_cid then {
            if IsInHost() then {
                BVR_match = CONTEXTIDR_EL2 == slice(DBGBVR_EL1[n], 0, 32)
            } else {
                BVR_match = (PSTATE.EL == EL0 | PSTATE.EL == EL1) & CONTEXTIDR_EL1 == slice(DBGBVR_EL1[n], 0, 32)
            }
        } else {
            if match_cid1 then {
                BVR_match = ((PSTATE.EL == EL0 | PSTATE.EL == EL1) & ~(IsInHost())) & CONTEXTIDR_EL1 == slice(DBGBVR_EL1[n], 0, 32)
            }
        }
    };
    BXVR_match : bool = undefined : bool;
    bvr_vmid : bits(16) = undefined : bits(16);
    vmid : bits(16) = undefined : bits(16);
    if match_vmid then {
        if ~(Have16bitVMID()) | [VTCR_EL2[19]] == 0b0 then {
            vmid = ZeroExtend(slice(VTTBR_EL2[56 .. 49] @ VTTBR_EL2[48 .. 41], 0, 8), 16);
            bvr_vmid = ZeroExtend(slice(DBGBVR_EL1[n], 32, 8), 16)
        } else {
            vmid = VTTBR_EL2[56 .. 49] @ VTTBR_EL2[48 .. 41];
            bvr_vmid = slice(DBGBVR_EL1[n], 32, 16)
        };
        BXVR_match = ((EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ~(IsInHost())) & vmid == bvr_vmid
    } else {
        if match_cid2 then {
            BXVR_match = (~(IsSecure()) & HaveVirtHostExt()) & slice(DBGBVR_EL1[n], 32, 32) == CONTEXTIDR_EL2
        }
    };
    let bvr_match_valid : bool = (match_addr | match_cid) | match_cid1;
    let bxvr_match_valid : bool = match_vmid | match_cid2;
    let val_match : bool = (~(bxvr_match_valid) | BXVR_match) & (~(bvr_match_valid) | BVR_match);
    val_match
}

val AArch64_StateMatch : forall ('linked : Bool) ('isbreakpnt : Bool) ('ispriv : Bool).
  (bits(2), bits(1), bits(2), bool('linked), bits(4), bool('isbreakpnt), AccType, bool('ispriv)) -> bool effect {escape, rreg, undef}

function AArch64_StateMatch (SSC__arg, HMC__arg, PxC__arg, linked__arg, LBN, isbreakpnt, acctype, ispriv) = {
    HMC = HMC__arg;
    PxC = PxC__arg;
    SSC = SSC__arg;
    linked : bool = linked__arg;
    c : Constraint = undefined : Constraint;
    if (((((((HMC @ SSC) @ PxC) & 0b11100) == 0b01100 | (((HMC @ SSC) @ PxC) & 0b11101) == 0b10000 | (((HMC @ SSC) @ PxC) & 0b11101) == 0b10100 | ((HMC @ SSC) @ PxC) == 0b11010 | ((HMC @ SSC) @ PxC) == 0b11101 | (((HMC @ SSC) @ PxC) & 0b11110) == 0b11110) | (HMC == 0b0 & PxC == 0b00) & (~(isbreakpnt) | ~(HaveAArch32EL(EL1)))) | (SSC == 0b01 | SSC == 0b10) & ~(HaveEL(EL3))) | (((HMC @ SSC) != 0b000 & (HMC @ SSC) != 0b111) & ~(HaveEL(EL3))) & ~(HaveEL(EL2))) | ((HMC @ SSC) @ PxC) == 0b11100 & ~(HaveEL(EL2)) then {
        __tc1 : bits(5) = undefined : bits(5);
        (c, __tc1) = ConstrainUnpredictableBits(Unpredictable_RESBPWPCTRL);
        let __tc2 : bits(5) = __tc1;
        HMC = [__tc2[4]];
        let __tc3 : bits(4) = slice(__tc2, 0, 4);
        SSC = slice(__tc3, 2, 2);
        PxC = slice(__tc3, 0, 2);
        assert(c == Constraint_DISABLED | c == Constraint_UNKNOWN);
        if c == Constraint_DISABLED then {
            return(false)
        }
    };
    let EL3_match : bool = (HaveEL(EL3) & HMC == 0b1) & [SSC[0]] == 0b0;
    let EL2_match : bool = HaveEL(EL2) & HMC == 0b1;
    let EL1_match : bool = [PxC[0]] == 0b1;
    let EL0_match : bool = [PxC[1]] == 0b1;
    let el : bits(2) = if HaveNV2Ext() & acctype == AccType_NV2REGISTER then EL2 else PSTATE.EL;
    priv_match : bool = undefined : bool;
    if ~(ispriv) & ~(isbreakpnt) then {
        priv_match = EL0_match
    } else {
        match el {
          ? if ? == EL3 => {
              priv_match = EL3_match
          },
          ? if ? == EL2 => {
              priv_match = EL2_match
          },
          ? if ? == EL1 => {
              priv_match = EL1_match
          },
          ? if ? == EL0 => {
              priv_match = EL0_match
          }
        }
    };
    security_state_match : bool = undefined : bool;
    match SSC {
      0b00 => {
          security_state_match = true
      },
      0b01 => {
          security_state_match = ~(IsSecure())
      },
      0b10 => {
          security_state_match = IsSecure()
      },
      0b11 => {
          security_state_match = true
      }
    };
    first_ctx_cmp : int = undefined : int;
    last_ctx_cmp : int = undefined : int;
    lbn : int = undefined : int;
    if linked then {
        lbn = UInt(LBN);
        first_ctx_cmp = UInt(slice(ID_AA64DFR0_EL1, 12, 4)) - UInt(slice(ID_AA64DFR0_EL1, 28, 4));
        last_ctx_cmp = UInt(slice(ID_AA64DFR0_EL1, 12, 4));
        if lbn < first_ctx_cmp | lbn > last_ctx_cmp then {
            (c, lbn) = ConstrainUnpredictableInteger(first_ctx_cmp, last_ctx_cmp, Unpredictable_BPNOTCTXCMP);
            assert(c == Constraint_DISABLED | c == Constraint_NONE | c == Constraint_UNKNOWN);
            match c {
              Constraint_DISABLED => {
                  return(false)
              },
              Constraint_NONE => {
                  linked = false
              }
            }
        }
    };
    linked_match : bool = undefined : bool;
    linked_to : bool = undefined : bool;
    vaddress : bits(64) = undefined : bits(64);
    if linked then {
        vaddress = undefined : bits(64);
        linked_to = true;
        linked_match = AArch64_BreakpointValueMatch(lbn, vaddress, linked_to)
    };
    (priv_match & security_state_match) & (~(linked) | linked_match)
}

val AArch64_WatchpointMatch : forall 'n 'size ('ispriv : Bool) ('iswrite : Bool).
  (int('n), bits(64), int('size), bool('ispriv), AccType, bool('iswrite)) -> bool effect {escape, rreg, undef}

function AArch64_WatchpointMatch (n, vaddress, size, ispriv, acctype, iswrite) = {
    assert(~(ELUsingAArch32(S1TranslationRegime())));
    assert(n <= UInt(slice(ID_AA64DFR0_EL1, 20, 4)));
    let enabled = [DBGWCR_EL1[n][0]] == 0b1;
    let linked = [DBGWCR_EL1[n][20]] == 0b1;
    let isbreakpnt = false;
    let state_match : bool = AArch64_StateMatch(slice(DBGWCR_EL1[n], 14, 2), [DBGWCR_EL1[n][13]], slice(DBGWCR_EL1[n], 1, 2), linked, slice(DBGWCR_EL1[n], 16, 4), isbreakpnt, acctype, ispriv);
    let ls_match = [slice(DBGWCR_EL1[n], 3, 2)[if iswrite then 1 else 0]] == 0b1;
    value_match_name : bool = undefined : bool;
    value_match_name = false;
    foreach (byte from 0 to (size - 1) by 1 in inc) {
        value_match_name = value_match_name | AArch64_WatchpointByteMatch(n, acctype, vaddress + byte)
    };
    ((value_match_name & state_match) & ls_match) & enabled
}

val AArch64_BreakpointMatch : forall ('n : Int) ('size : Int).
  (int('n), bits(64), AccType, int('size)) -> bool effect {escape, rreg, undef}

function AArch64_BreakpointMatch (n, vaddress, acctype, size) = {
    assert(~(ELUsingAArch32(S1TranslationRegime())));
    assert(n <= UInt(slice(ID_AA64DFR0_EL1, 12, 4)));
    let enabled = [DBGBCR_EL1[n][0]] == 0b1;
    let ispriv = PSTATE.EL != EL0;
    let linked = (slice(DBGBCR_EL1[n], 20, 4) & 0xB) == 0x1;
    let isbreakpnt = true;
    let linked_to = false;
    let state_match : bool = AArch64_StateMatch(slice(DBGBCR_EL1[n], 14, 2), [DBGBCR_EL1[n][13]], slice(DBGBCR_EL1[n], 1, 2), linked, slice(DBGBCR_EL1[n], 16, 4), isbreakpnt, acctype, ispriv);
    value_match_name : bool = undefined : bool;
    value_match_name = AArch64_BreakpointValueMatch(n, vaddress, linked_to);
    match_i : bool = undefined : bool;
    if HaveAnyAArch32() & size == 4 then {
        match_i = AArch64_BreakpointValueMatch(n, vaddress + 2, linked_to);
        if ~(value_match_name) & match_i then {
            value_match_name = ConstrainUnpredictableBool(Unpredictable_BPMATCHHALF)
        }
    };
    if [vaddress[1]] == 0b1 & slice(DBGBCR_EL1[n], 5, 4) == 0xF then {
        if value_match_name then {
            value_match_name = ConstrainUnpredictableBool(Unpredictable_BPMATCHHALF)
        }
    };
    let val_match : bool = (value_match_name & state_match) & enabled;
    val_match
}

val AArch64_CheckBreakpoint : forall ('size : Int).
  (bits(64), AccType, int('size)) -> FaultRecord effect {escape, rreg, undef, wreg}

function AArch64_CheckBreakpoint (vaddress, acctype__arg, size) = {
    acctype = acctype__arg;
    assert(~(ELUsingAArch32(S1TranslationRegime())));
    assert(UsingAArch32() & (size == 2 | size == 4) | size == 4);
    val_match : bool = undefined : bool;
    val_match = false;
    match_i : bool = undefined : bool;
    foreach (i from 0 to UInt(slice(ID_AA64DFR0_EL1, 12, 4)) by 1 in inc) {
        match_i = AArch64_BreakpointMatch(i, vaddress, acctype, size);
        val_match = val_match | match_i
    };
    iswrite : bool = undefined : bool;
    reason : bits(6) = undefined : bits(6);
    if val_match & HaltOnBreakpointOrWatchpoint() then {
        reason = DebugHalt_Breakpoint;
        Halt(reason);
        return(AArch64_NoFault())
    } else {
        if (val_match & [MDSCR_EL1[15]] == 0b1) & AArch64_GenerateDebugExceptions() then {
            acctype = AccType_IFETCH;
            iswrite = false;
            return(AArch64_DebugFault(acctype, iswrite))
        } else {
            return(AArch64_NoFault())
        }
    }
}

val AArch64_BranchAddr : bits(64) -> bits(64) effect {escape, rreg, undef}

function AArch64_BranchAddr vaddress = {
    assert(~(UsingAArch32()));
    let msbit = AddrTop(vaddress, true, PSTATE.EL);
    assert(msbit + 1 >= 0);
    if msbit == 63 then {
        return(vaddress)
    } else {
        if ((PSTATE.EL == EL0 | PSTATE.EL == EL1) | IsInHost()) & [vaddress[msbit]] == 0b1 then {
            return(SignExtend(slice(vaddress, 0, msbit + 1)))
        } else {
            return(ZeroExtend(slice(vaddress, 0, msbit + 1)))
        }
    }
}

val BranchTo : forall ('N : Int), 'N >= 0.
  (bits('N), BranchType) -> unit effect {escape, rreg, undef, wreg}

function BranchTo (target, branch_type) = {
    Hint_Branch(branch_type);
    if 'N == 32 then {
        assert(UsingAArch32());
        sail_branch_announce(64, ZeroExtend(64, target));
        _PC = ZeroExtend(target)
    } else {
        assert('N == 64 & ~(UsingAArch32()));
        sail_branch_announce(64, slice(target, 0, 64));
        _PC = AArch64_BranchAddr(slice(target, 0, 64))
    };
    __PC_changed = true;
    return()
}

val AArch64_TakeException : forall ('vect_offset : Int).
  (bits(2), ExceptionRecord, bits(64), int('vect_offset)) -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakeException (target_el, exception, preferred_exception_return, vect_offset__arg) = {
    vect_offset : int = vect_offset__arg;
    assert((HaveEL(target_el) & ~(ELUsingAArch32(target_el))) & UInt(target_el) >= UInt(PSTATE.EL));
    sync_errors : bool = undefined : bool;
    sync_errors = HaveIESB() & [aget_SCTLR()[21]] == 0b1;
    if HaveDoubleFaultExt() then {
        sync_errors = sync_errors | ([SCR_EL3[3]] == 0b1 & [SCR_EL3[20]] == 0b1) & PSTATE.EL == EL3
    };
    iesb_req : bool = undefined : bool;
    if sync_errors & InsertIESBBeforeException(target_el) then {
        SynchronizeErrors();
        iesb_req = false;
        sync_errors = false;
        TakeUnmaskedPhysicalSErrorInterrupts(iesb_req)
    };
    SynchronizeContext();
    let from_32 : bool = UsingAArch32();
    if from_32 then {
        AArch64_MaybeZeroRegisterUppers()
    };
    if UInt(target_el) > UInt(PSTATE.EL) then {
        lower_32 : bool = undefined : bool;
        if target_el == EL3 then {
            if EL2Enabled() then {
                lower_32 = ELUsingAArch32(EL2)
            } else {
                lower_32 = ELUsingAArch32(EL1)
            }
        } else {
            if (IsInHost() & PSTATE.EL == EL0) & target_el == EL2 then {
                lower_32 = ELUsingAArch32(EL0)
            } else {
                lower_32 = ELUsingAArch32(target_el - 1)
            }
        };
        vect_offset = vect_offset + (if lower_32 then 1536 else 1024)
    } else {
        if PSTATE.SP == 0b1 then {
            vect_offset = vect_offset + 512
        }
    };
    spsr : bits(32) = undefined : bits(32);
    spsr = GetPSRFromPSTATE();
    if (((PSTATE.EL == EL1 & target_el == EL1) & HaveNVExt()) & EL2Enabled()) & (HCR_EL2[42 .. 42] @ HCR_EL2[43 .. 43]) == 0b10 then {
        spsr = __SetSlice_bits(32, 2, spsr, 2, 0b10)
    };
    if HaveUAOExt() then {
        PSTATE.UAO = 0b0
    };
    if ~(exception.typ == Exception_IRQ | exception.typ == Exception_FIQ) then {
        AArch64_ReportException(exception, target_el)
    };
    PSTATE.EL = target_el;
    PSTATE.nRW = 0b0;
    PSTATE.SP = 0b1;
    spsr_btype : bits(2) = undefined : bits(2);
    if HaveBTIExt() then {
        if exception.typ == Exception_SError | exception.typ == Exception_IRQ | exception.typ == Exception_FIQ | exception.typ == Exception_SoftwareStep | exception.typ == Exception_PCAlignment | exception.typ == Exception_InstructionAbort | exception.typ == Exception_SoftwareBreakpoint | exception.typ == Exception_IllegalState | exception.typ == Exception_BranchTarget then {
            spsr_btype = PSTATE.BTYPE
        } else {
            spsr_btype = if ConstrainUnpredictableBool(Unpredictable_ZEROBTYPE) then 0b00 else PSTATE.BTYPE
        };
        spsr = __SetSlice_bits(32, 2, spsr, 10, spsr_btype)
    };
    aset_SPSR(spsr);
    aset_ELR(preferred_exception_return);
    if HaveBTIExt() then {
        PSTATE.BTYPE = 0b00
    };
    PSTATE.SS = 0b0;
    (PSTATE.D @ PSTATE.A @ PSTATE.I @ PSTATE.F) = 0xF;
    PSTATE.IL = 0b0;
    if from_32 then {
        PSTATE.IT = 0x00;
        PSTATE.T = 0b0
    };
    if (HavePANExt() & (PSTATE.EL == EL1 | PSTATE.EL == EL2 & ELIsInHost(EL0))) & [aget_SCTLR()[23]] == 0b0 then {
        PSTATE.PAN = 0b1
    };
    if HaveMTEExt() then {
        PSTATE.TCO = 0b1
    };
    BranchTo(slice(aget_VBAR(), 11, 53) @ __GetSlice_int(11, vect_offset, 0), BranchType_EXCEPTION);
    if sync_errors then {
        SynchronizeErrors();
        iesb_req = true;
        TakeUnmaskedPhysicalSErrorInterrupts(iesb_req)
    };
    EndOfInstruction()
}

val TagCheckFault : forall ('write : Bool).
  (bits(64), bool('write)) -> unit effect {escape, rreg, undef, wreg}

function TagCheckFault (va, write) = {
    target_el : bits(2) = undefined : bits(2);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let 'vect_offset = 0;
    if PSTATE.EL == EL0 then {
        target_el = if [HCR_EL2[27]] == 0 then EL1 else EL2
    } else {
        target_el = PSTATE.EL
    };
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(Exception_DataAbort);
    __tc1 : bits(25) = exception.syndrome;
    let __tc1 = __SetSlice_bits(25, 6, __tc1, 0, 0b010001);
    exception.syndrome = __tc1;
    if write then {
        __tc2 : bits(25) = exception.syndrome;
        __tc2 = __SetSlice_bits(25, 1, __tc2, 6, 0b1);
        exception.syndrome = __tc2
    };
    exception.vaddress = va;
    AArch64_TakeException(target_el, exception, preferred_exception_return, vect_offset)
}

val TagCheckFail : forall ('iswrite : Bool).
  (bits(64), bool('iswrite)) -> unit effect {escape, rreg, undef, wreg}

function TagCheckFail (vaddress, iswrite) = {
    let tcf = EffectiveTCF(PSTATE.EL);
    if tcf == 0b01 then {
        TagCheckFault(vaddress, iswrite)
    } else {
        if tcf == 0b10 then {
            ReportTagCheckFail(PSTATE.EL, [vaddress[55]])
        }
    }
}

val AArch64_WatchpointException : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_WatchpointException (vaddress, fault) = {
    assert(PSTATE.EL != EL3);
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 0;
    let exception = AArch64_AbortSyndrome(Exception_Watchpoint, fault, vaddress);
    if PSTATE.EL == EL2 | route_to_el2 then {
        AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
    } else {
        AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
    }
}

val AArch64_VectorCatchException : FaultRecord -> unit effect {escape, rreg, undef, wreg}

function AArch64_VectorCatchException fault = {
    assert(PSTATE.EL != EL2);
    assert(EL2Enabled() & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1));
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 0;
    let vaddress = undefined : bits(64);
    let exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_VectorCatch, fault, vaddress);
    AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
}

val AArch64_TakeVirtualSErrorException : forall ('impdef_syndrome : Bool).
  (bool('impdef_syndrome), bits(24)) -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakeVirtualSErrorException (impdef_syndrome, syndrome) = {
    assert(EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1));
    assert([HCR_EL2[27]] == 0b0 & [HCR_EL2[5]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 384;
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(Exception_SError);
    if HaveRASExt() then {
        __tc1 : bits(25) = exception.syndrome;
        __tc1 = __SetSlice_bits(25, 1, __tc1, 24, [VSESR_EL2[24]]);
        exception.syndrome = __tc1;
        __tc2 : bits(25) = exception.syndrome;
        __tc2 = __SetSlice_bits(25, 24, __tc2, 0, slice(VSESR_EL2, 0, 24));
        exception.syndrome = __tc2
    } else {
        __tc3 : bits(25) = exception.syndrome;
        __tc3 = __SetSlice_bits(25, 1, __tc3, 24, if impdef_syndrome then 0b1 else 0b0);
        exception.syndrome = __tc3;
        if impdef_syndrome then {
            __tc4 : bits(25) = exception.syndrome;
            __tc4 = __SetSlice_bits(25, 24, __tc4, 0, syndrome);
            exception.syndrome = __tc4
        }
    };
    ClearPendingVirtualSError();
    AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_TakeVirtualIRQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakeVirtualIRQException () = {
    assert(EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1));
    assert([HCR_EL2[27]] == 0b0 & [HCR_EL2[4]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 128;
    let exception = ExceptionSyndrome(Exception_IRQ);
    AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_TakeVirtualFIQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakeVirtualFIQException () = {
    assert(EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1));
    assert([HCR_EL2[27]] == 0b0 & [HCR_EL2[3]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 256;
    let exception = ExceptionSyndrome(Exception_FIQ);
    AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_TakePhysicalSErrorException : forall ('impdef_syndrome : Bool).
  (bool('impdef_syndrome), bits(24)) -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakePhysicalSErrorException (impdef_syndrome, syndrome) = {
    let route_to_el3 = HaveEL(EL3) & [SCR_EL3[3]] == 0b1;
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | ~(IsInHost()) & [HCR_EL2[5]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 384;
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(Exception_SError);
    __tc1 : bits(25) = exception.syndrome;
    let __tc1 = __SetSlice_bits(25, 1, __tc1, 24, if impdef_syndrome then 0b1 else 0b0);
    exception.syndrome = __tc1;
    __tc2 : bits(25) = exception.syndrome;
    let __tc2 = __SetSlice_bits(25, 24, __tc2, 0, syndrome);
    exception.syndrome = __tc2;
    ClearPendingPhysicalSError();
    if PSTATE.EL == EL3 | route_to_el3 then {
        AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_el2 then {
            AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
        } else {
            AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
        }
    }
}

val AArch64_TakePhysicalIRQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakePhysicalIRQException () = {
    let route_to_el3 = HaveEL(EL3) & [SCR_EL3[1]] == 0b1;
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [HCR_EL2[4]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 128;
    let exception = ExceptionSyndrome(Exception_IRQ);
    if route_to_el3 then {
        AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_el2 then {
            assert(PSTATE.EL != EL3);
            AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
        } else {
            assert(PSTATE.EL == EL0 | PSTATE.EL == EL1);
            AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
        }
    }
}

val AArch64_TakePhysicalFIQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakePhysicalFIQException () = {
    let route_to_el3 = HaveEL(EL3) & [SCR_EL3[2]] == 0b1;
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [HCR_EL2[3]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 256;
    let exception = ExceptionSyndrome(Exception_FIQ);
    if route_to_el3 then {
        AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_el2 then {
            assert(PSTATE.EL != EL3);
            AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
        } else {
            assert(PSTATE.EL == EL0 | PSTATE.EL == EL1);
            AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
        }
    }
}

val AArch64_SoftwareStepException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_SoftwareStepException () = {
    assert(PSTATE.EL != EL3);
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 0;
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(Exception_SoftwareStep);
    if SoftwareStep_DidNotStep() then {
        __tc1 : bits(25) = exception.syndrome;
        __tc1 = __SetSlice_bits(25, 1, __tc1, 24, 0b0);
        exception.syndrome = __tc1
    } else {
        __tc2 : bits(25) = exception.syndrome;
        __tc2 = __SetSlice_bits(25, 1, __tc2, 24, 0b1);
        exception.syndrome = __tc2;
        __tc3 : bits(25) = exception.syndrome;
        __tc3 = __SetSlice_bits(25, 1, __tc3, 6, if SoftwareStep_SteppedEX() then 0b1 else 0b0);
        exception.syndrome = __tc3
    };
    if PSTATE.EL == EL2 | route_to_el2 then {
        AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
    } else {
        AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
    }
}

val CheckSoftwareStep : unit -> unit effect {escape, rreg, undef, wreg}

function CheckSoftwareStep () = {
    if ~(ELUsingAArch32(DebugTarget())) & AArch64_GenerateDebugExceptions() then {
        if [MDSCR_EL1[0]] == 0b1 & PSTATE.SS == 0b0 then {
            AArch64_SoftwareStepException()
        }
    }
}

val AArch64_PCAlignmentFault : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_PCAlignmentFault () = {
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 0;
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(Exception_PCAlignment);
    exception.vaddress = ThisInstrAddr();
    if UInt(PSTATE.EL) > UInt(EL1) then {
        AArch64_TakeException(PSTATE.EL, exception, preferred_exception_return, vect_offset)
    } else {
        if EL2Enabled() & [HCR_EL2[27]] == 0b1 then {
            AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
        } else {
            AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
        }
    }
}

val AArch64_CheckPCAlignment : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_CheckPCAlignment () = {
    let pc : bits(64) = ThisInstrAddr();
    if slice(pc, 0, 2) != 0b00 then {
        AArch64_PCAlignmentFault()
    }
}

val AArch64_InstructionAbort : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_InstructionAbort (vaddress, fault) = {
    if HaveDoubleFaultExt() then {
        assert(fault.typ != Fault_AsyncExternal)
    };
    let route_to_el3 = (HaveEL(EL3) & [SCR_EL3[3]] == 0b1) & IsExternalAbort(fault);
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & (([HCR_EL2[27]] == 0b1 | IsSecondStage(fault)) | (HaveRASExt() & [HCR_EL2[37]] == 0b1) & IsExternalAbort(fault));
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 0;
    let exception = AArch64_AbortSyndrome(Exception_InstructionAbort, fault, vaddress);
    if PSTATE.EL == EL3 | route_to_el3 then {
        AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_el2 then {
            AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
        } else {
            AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
        }
    }
}

val AArch64_DataAbort : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_DataAbort (vaddress, fault) = {
    let route_to_el3 = (HaveEL(EL3) & [SCR_EL3[3]] == 0b1) & IsExternalAbort(fault);
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ((([HCR_EL2[27]] == 0b1 | (HaveRASExt() & [HCR_EL2[37]] == 0b1) & IsExternalAbort(fault)) | HaveNV2Ext() & fault.acctype == AccType_NV2REGISTER) | IsSecondStage(fault));
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    vect_offset : int = undefined : int;
    if ((HaveDoubleFaultExt() & (PSTATE.EL == EL3 | route_to_el3)) & IsExternalAbort(fault)) & [SCR_EL3[19]] == 0b1 then {
        vect_offset = 384
    } else {
        vect_offset = 0
    };
    exception : ExceptionRecord = undefined : ExceptionRecord;
    if HaveNV2Ext() & fault.acctype == AccType_NV2REGISTER then {
        exception = AArch64_AbortSyndrome(Exception_NV2DataAbort, fault, vaddress)
    } else {
        exception = AArch64_AbortSyndrome(Exception_DataAbort, fault, vaddress)
    };
    if PSTATE.EL == EL3 | route_to_el3 then {
        AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_el2 then {
            AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
        } else {
            AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
        }
    }
}

val AArch64_CheckIllegalState : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_CheckIllegalState () = {
    exception : ExceptionRecord = undefined : ExceptionRecord;
    route_to_el2 : bool = undefined : bool;
    vect_offset : int = undefined : int;
    if PSTATE.IL == 0b1 then {
        route_to_el2 = (EL2Enabled() & PSTATE.EL == EL0) & [HCR_EL2[27]] == 0b1;
        let preferred_exception_return : bits(64) = ThisInstrAddr();
        vect_offset = 0;
        exception = ExceptionSyndrome(Exception_IllegalState);
        if UInt(PSTATE.EL) > UInt(EL1) then {
            AArch64_TakeException(PSTATE.EL, exception, preferred_exception_return, vect_offset)
        } else {
            if route_to_el2 then {
                AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
            } else {
                AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
            }
        }
    }
}

val AArch64_BreakpointException : FaultRecord -> unit effect {escape, rreg, undef, wreg}

function AArch64_BreakpointException fault = {
    assert(PSTATE.EL != EL3);
    let route_to_el2 = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
    let preferred_exception_return : bits(64) = ThisInstrAddr();
    let vect_offset = 0;
    let vaddress = undefined : bits(64);
    let exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_Breakpoint, fault, vaddress);
    if PSTATE.EL == EL2 | route_to_el2 then {
        AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
    } else {
        AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
    }
}

function AArch64_Abort (vaddress, fault) = {
    if IsDebugException(fault) then {
        if fault.acctype == AccType_IFETCH then {
            if UsingAArch32() & fault.debugmoe == DebugException_VectorCatch then {
                AArch64_VectorCatchException(fault)
            } else {
                AArch64_BreakpointException(fault)
            }
        } else {
            AArch64_WatchpointException(vaddress, fault)
        }
    } else {
        if fault.acctype == AccType_IFETCH then {
            AArch64_InstructionAbort(vaddress, fault)
        } else {
            AArch64_DataAbort(vaddress, fault)
        }
    }
}

val AArch32_EnterMode : forall ('lr_offset : Int) ('vect_offset : Int).
  (bits(5), bits(32), int('lr_offset), int('vect_offset)) -> unit effect {escape, rreg, undef, wreg}

function AArch32_EnterMode (target_mode, preferred_exception_return, lr_offset, vect_offset) = {
    SynchronizeContext();
    assert(ELUsingAArch32(EL1) & PSTATE.EL != EL2);
    let spsr = GetPSRFromPSTATE();
    if PSTATE.M == M32_Monitor then {
        __tc1 : bits(32) = get_SCR();
        __tc1 = __SetSlice_bits(32, 1, __tc1, 0, 0b0);
        set_SCR(__tc1)
    };
    AArch32_WriteMode(target_mode);
    SPSR() = spsr;
    R(14) = preferred_exception_return + lr_offset;
    PSTATE.T = [get_SCTLR()[30]];
    PSTATE.SS = 0b0;
    if target_mode == M32_FIQ then {
        (PSTATE.A @ PSTATE.I @ PSTATE.F) = 0b111
    } else {
        if target_mode == M32_Abort | target_mode == M32_IRQ then {
            (PSTATE.A @ PSTATE.I) = 0b11
        } else {
            PSTATE.I = 0b1
        }
    };
    PSTATE.E = [get_SCTLR()[25]];
    PSTATE.IL = 0b0;
    PSTATE.IT = 0x00;
    if HavePANExt() & [get_SCTLR()[23]] == 0b0 then {
        PSTATE.PAN = 0b1
    };
    BranchTo(slice(ExcVectorBase(), 5, 27) @ __GetSlice_int(5, vect_offset, 0), BranchType_EXCEPTION);
    EndOfInstruction()
}

val AArch64_AccessIsPrivileged : AccType -> bool effect {escape, rreg, undef}

function AArch64_AccessIsPrivileged acctype = {
    let el : bits(2) = AArch64_AccessUsesEL(acctype);
    ispriv : bool = undefined : bool;
    if el == EL0 then {
        ispriv = false
    } else {
        if el == EL3 then {
            ispriv = true
        } else {
            if el == EL2 & (~(IsInHost()) | [HCR_EL2[27]] == 0b0) then {
                ispriv = true
            } else {
                if HaveUAOExt() & PSTATE.UAO == 0b1 then {
                    ispriv = true
                } else {
                    ispriv = acctype != AccType_UNPRIV
                }
            }
        }
    };
    ispriv
}

val AArch64_CheckWatchpoint : forall ('size : Int).
  (bits(64), AccType, bool, int('size)) -> FaultRecord effect {escape, rreg, undef, wreg}

function AArch64_CheckWatchpoint (vaddress, acctype, iswrite, size) = {
    assert(~(ELUsingAArch32(S1TranslationRegime())));
    val_match : bool = undefined : bool;
    val_match = false;
    let ispriv : bool = AArch64_AccessIsPrivileged(acctype);
    foreach (i from 0 to UInt(slice(ID_AA64DFR0_EL1, 20, 4)) by 1 in inc) {
        val_match = val_match | AArch64_WatchpointMatch(i, vaddress, size, ispriv, acctype, iswrite)
    };
    reason : bits(6) = undefined : bits(6);
    if val_match & HaltOnBreakpointOrWatchpoint() then {
        reason = DebugHalt_Watchpoint;
        Halt(reason);
        AArch64_NoFault()
    } else {
        if (val_match & [MDSCR_EL1[15]] == 0b1) & AArch64_GenerateDebugExceptions() then {
            return(AArch64_DebugFault(acctype, iswrite))
        } else {
            return(AArch64_NoFault())
        }
    }
}

val AArch64_CheckDebug : forall ('iswrite : Bool) ('size : Int).
  (bits(64), AccType, bool('iswrite), int('size)) -> FaultRecord effect {escape, rreg, undef, wreg}

function AArch64_CheckDebug (vaddress, acctype, iswrite, size) = {
    fault : FaultRecord = AArch64_NoFault();
    let d_side = acctype != AccType_IFETCH;
    let generate_exception = AArch64_GenerateDebugExceptions() & [MDSCR_EL1[15]] == 0b1;
    let halt = HaltOnBreakpointOrWatchpoint();
    if generate_exception | halt then {
        if d_side then {
            fault = AArch64_CheckWatchpoint(vaddress, acctype, iswrite, size)
        } else {
            fault = AArch64_CheckBreakpoint(vaddress, acctype, size)
        }
    };
    fault
}

val AArch64_CheckPermission : forall ('level : Int) ('iswrite : Bool).
  (Permissions, bits(64), int('level), bits(1), AccType, bool('iswrite)) -> FaultRecord effect {escape, rreg, undef}

function AArch64_CheckPermission (perms, vaddress, level, NS, acctype, iswrite) = {
    assert(~(ELUsingAArch32(S1TranslationRegime())));
    let wxn = [SCTLR()[19]] == 0b1;
    is_ats1xp : bool = undefined : bool;
    is_ldst : bool = undefined : bool;
    ispriv : bool = undefined : bool;
    pan : bits(1) = undefined : bits(1);
    priv_r : bool = undefined : bool;
    priv_w : bool = undefined : bool;
    priv_xn : bool = undefined : bool;
    r : bool = undefined : bool;
    user_r : bool = undefined : bool;
    user_w : bool = undefined : bool;
    user_xn : bool = undefined : bool;
    w : bool = undefined : bool;
    xn : bool = undefined : bool;
    if ((PSTATE.EL == EL0 | IsInHost()) | PSTATE.EL == EL1 & ~(HaveNV2Ext())) | (PSTATE.EL == EL1 & HaveNV2Ext()) & (acctype != AccType_NV2REGISTER | ~(ELIsInHost(EL2))) then {
        priv_r = true;
        priv_w = [perms.ap[2]] == 0b0;
        user_r = [perms.ap[1]] == 0b1;
        user_w = slice(perms.ap, 1, 2) == 0b01;
        ispriv = AArch64_AccessIsPrivileged(acctype);
        pan = if HavePANExt() then PSTATE.PAN else 0b0;
        if EL2Enabled() & ((PSTATE.EL == EL1 & HaveNVExt()) & (HCR_EL2[42 .. 42] @ HCR_EL2[43 .. 43]) == 0b11 | (HaveNV2Ext() & acctype == AccType_NV2REGISTER) & [HCR_EL2[45]] == 0b1) then {
            pan = 0b0
        };
        is_ldst = ~(acctype == AccType_DC | acctype == AccType_DC_UNPRIV | acctype == AccType_AT | acctype == AccType_IFETCH);
        is_ats1xp = acctype == AccType_AT & AArch64_ExecutingATS1xPInstr();
        if ((pan == 0b1 & user_r) & ispriv) & (is_ldst | is_ats1xp) then {
            priv_r = false;
            priv_w = false
        };
        user_xn = perms.xn == 0b1 | user_w & wxn;
        priv_xn = (perms.pxn == 0b1 | priv_w & wxn) | user_w;
        if ispriv then {
            (r, w, xn) = (priv_r, priv_w, priv_xn)
        } else {
            (r, w, xn) = (user_r, user_w, user_xn)
        }
    } else {
        r = true;
        w = [perms.ap[2]] == 0b0;
        xn = perms.xn == 0b1 | w & wxn
    };
    if ((HaveEL(EL3) & IsSecure()) & NS == 0b1) & [SCR_EL3[9]] == 0b1 then {
        xn = true
    };
    fail : bool = undefined : bool;
    failedread : bool = undefined : bool;
    if acctype == AccType_IFETCH then {
        fail = xn;
        failedread = true
    } else {
        if acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW | acctype == AccType_ORDEREDATOMICRW then {
            fail = ~(r) | ~(w);
            failedread = ~(r)
        } else {
            if iswrite then {
                fail = ~(w);
                failedread = false
            } else {
                if acctype == AccType_DC & PSTATE.EL != EL0 then {
                    fail = false
                } else {
                    fail = ~(r);
                    failedread = true
                }
            }
        }
    };
    ipaddress : bits(52) = undefined : bits(52);
    s2fs1walk : bool = undefined : bool;
    secondstage : bool = undefined : bool;
    if fail then {
        secondstage = false;
        s2fs1walk = false;
        ipaddress = undefined : bits(52);
        return(AArch64_PermissionFault(ipaddress, undefined : bits(1), level, acctype, ~(failedread), secondstage, s2fs1walk))
    } else {
        return(AArch64_NoFault())
    }
}

val AArch64_FirstStageTranslate : forall ('iswrite : Bool) ('wasaligned : Bool) 'size.
  (bits(64), AccType, bool('iswrite), bool('wasaligned), int('size)) -> (AddressDescriptor, option(TranslationInfo)) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_FirstStageTranslate (vaddress, acctype, iswrite, wasaligned, size) = {
    s1_enabled : bool = undefined : bool;
    if HaveNV2Ext() & acctype == AccType_NV2REGISTER then {
        s1_enabled = [SCTLR_EL2[0]] == 0b1
    } else {
        if HasS2Translation() then {
            s1_enabled = ([HCR_EL2[27]] == 0b0 & [HCR_EL2[12]] == 0b0) & [SCTLR_EL1[0]] == 0b1
        } else {
            s1_enabled = [SCTLR()[0]] == 0b1
        }
    };
    let ipaddress = undefined : bits(52);
    let secondstage = false;
    s2fs1walk : bool = undefined : bool;
    s2fs1walk = false;
    S1 : TLBRecord = undefined : TLBRecord;
    S1.descupdate.AF = false;
    S1.descupdate.AP = false;
    translation_info : option(TranslationInfo) = None();
    nTLSMD : bits(1) = undefined : bits(1);
    permissioncheck : bool = undefined : bool;
    if s1_enabled then {
        (S1, translation_info) = AArch64_TranslationTableWalk(ipaddress, 0b1, vaddress, acctype, iswrite, secondstage, s2fs1walk, size);
        permissioncheck = true;
        if acctype == AccType_IFETCH then {
            InGuardedPage = S1.GP == 0b1
        }
    } else {
        S1 = AArch64_TranslateAddressS1Off(vaddress, acctype, iswrite);
        permissioncheck = false;
        if (UsingAArch32() & HaveTrapLoadStoreMultipleDeviceExt()) & AArch32_ExecutingLSMInstr() then {
            if S1.addrdesc.memattrs.typ == MemType_Device & S1.addrdesc.memattrs.device != DeviceType_GRE then {
                nTLSMD = if S1TranslationRegime() == EL2 then [SCTLR_EL2[28]] else [SCTLR_EL1[28]];
                if nTLSMD == 0b0 then {
                    __tc1 : AddressDescriptor = S1.addrdesc;
                    __tc1.fault = AArch64_AlignmentFault(acctype, iswrite, secondstage);
                    S1.addrdesc = __tc1
                }
            }
        }
    };
    if ((~(wasaligned) & acctype != AccType_IFETCH | acctype == AccType_DCZVA) & ~(IsFault(S1.addrdesc)) & S1.addrdesc.memattrs.typ == MemType_Device)  then {
        __tc2 : AddressDescriptor = S1.addrdesc;
        __tc2.fault = AArch64_AlignmentFault(acctype, iswrite, secondstage);
        S1.addrdesc = __tc2
    };
    if ~(IsFault(S1.addrdesc)) & permissioncheck then {
        __tc3 : AddressDescriptor = S1.addrdesc;
        __tc3.fault = AArch64_CheckPermission(S1.perms, vaddress, S1.level, S1.addrdesc.paddress.NS, acctype, iswrite);
        S1.addrdesc = __tc3
    };
    if (~(IsFault(S1.addrdesc)) & S1.addrdesc.memattrs.typ == MemType_Device) & acctype == AccType_IFETCH then {
        S1.addrdesc = AArch64_InstructionDevice(S1.addrdesc, vaddress, ipaddress, S1.level, acctype, iswrite, secondstage, s2fs1walk)
    };
    let hwupdatewalk = false;
    let s2fs1walk = false;
    __tc4 : AddressDescriptor = S1.addrdesc;
    __tc4.fault = AArch64_CheckAndUpdateDescriptor(S1.descupdate, S1.addrdesc.fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk);
    S1.addrdesc = __tc4;
    (S1.addrdesc, translation_info)
}

val AArch64_FullTranslate : forall ('iswrite : Bool) ('wasaligned : Bool) 'size.
  (bits(64), AccType, bool('iswrite), bool('wasaligned), int('size)) -> (AddressDescriptor, option(TranslationInfo)) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_FullTranslate (vaddress, acctype, iswrite, wasaligned, size) = {
    let (S1, translation_info) = AArch64_FirstStageTranslate(vaddress, acctype, iswrite, wasaligned, size);
    hwupdatewalk : bool = undefined : bool;
    s2fs1walk : bool = undefined : bool;
    if (~(IsFault(S1)) & ~(HaveNV2Ext() & acctype == AccType_NV2REGISTER)) & HasS2Translation() then {
        s2fs1walk = false;
        hwupdatewalk = false;
        AArch64_SecondStageTranslate(S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size, hwupdatewalk)
    } else {
        (S1, translation_info)
    }
}

val AArch64_TranslateAddress : forall ('iswrite : Bool) ('wasaligned : Bool) 'size.
  (bits(64), AccType, bool('iswrite), bool('wasaligned), int('size)) -> (AddressDescriptor, option(TranslationInfo)) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_TranslateAddress (vaddress, acctype, iswrite, wasaligned, size) = {
    result : AddressDescriptor = undefined : AddressDescriptor;
    let (desc, translation_info) = AArch64_FullTranslate(vaddress, acctype, iswrite, wasaligned, size);
    result = desc;
    if ~(acctype == AccType_PTW | acctype == AccType_IC | acctype == AccType_AT) & ~(IsFault(result)) then {
        result.fault = AArch64_CheckDebug(vaddress, acctype, iswrite, size)
    };
    result.vaddress = ZeroExtend(vaddress);
    (result, translation_info)
}

val aget_MemTag : bits(64) -> bits(4) effect {escape, rmem, rreg, undef, wmem, wreg}

function aget_MemTag address = {
    memaddrdesc : AddressDescriptor = undefined : AddressDescriptor;
    let value_name = undefined : bits(4);
    let iswrite = false;
    let (memaddrdesc, _) = AArch64_TranslateAddress(address, AccType_NORMAL, iswrite, true, TAG_GRANULE);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(address, memaddrdesc.fault)
    };
    if AllocationTagAccessIsEnabled() then {
        return(_MemTag(memaddrdesc))
    } else {
        return(0x0)
    }
}

overload MemTag = {aget_MemTag}

val CheckTag : forall ('write : Bool).
  (AddressDescriptor, bits(4), bool('write)) -> bool effect {escape, rmem, rreg, undef, wmem, wreg}

function CheckTag (memaddrdesc, ptag, write) = {
    if memaddrdesc.memattrs.tagged then {
        let paddress : bits(64) = ZeroExtend(memaddrdesc.paddress.address);
        return(ptag == MemTag(paddress))
    } else {
        return(true)
    }
}

val AArch32_WatchpointByteMatch : forall ('n : Int).
  (int('n), bits(32)) -> bool effect {escape, rreg, undef}

function AArch32_WatchpointByteMatch (n, vaddress) = {
    bottom : int = undefined : int;
    bottom = if [DBGWVR[n][2]] == 0b1 then 2 else 3;
    let bottom_fixed = bottom;
    assert(bottom_fixed == 2 | bottom_fixed == 3);
    byte_select_match : bool = undefined : bool;
    byte_select_match = [slice(DBGWCR[n], 5, 8)[UInt(slice(vaddress, 0, bottom_fixed))]] != 0b0;
    mask : int = undefined : int;
    mask = UInt(slice(DBGWCR[n], 24, 5));
    LSB : bits(8) = undefined : bits(8);
    MSB : bits(8) = undefined : bits(8);
    if mask > 0 & ~(IsOnes(slice(DBGWCR[n], 5, 8))) then {
        byte_select_match = ConstrainUnpredictableBool(Unpredictable_WPMASKANDBAS)
    } else {
        LSB = slice(DBGWCR[n], 5, 8) & ~(slice(DBGWCR[n], 5, 8) - 1);
        MSB = slice(DBGWCR[n], 5, 8) + LSB;
        if ~(IsZero(MSB & MSB - 1)) then {
            byte_select_match = ConstrainUnpredictableBool(Unpredictable_WPBASCONTIGUOUS);
            bottom = 3
        }
    };
    c : Constraint = undefined : Constraint;
    if mask > 0 & mask <= 2 then {
        (c, mask) = ConstrainUnpredictableInteger(3, 31, Unpredictable_RESWPMASK);
        assert(c == Constraint_DISABLED | c == Constraint_NONE | c == Constraint_UNKNOWN);
        match c {
          Constraint_DISABLED => {
              return(false)
          },
          Constraint_NONE => {
              mask = 0
          }
        }
    };
    WVR_match : bool = undefined : bool;
    let bottom_fixed = bottom;
    let mask_fixed = mask;
    assert(bottom_fixed == 2 | bottom_fixed == 3);
    assert(negate(mask_fixed) + 32 >= 0 & mask_fixed >= 0);
    if mask_fixed > bottom_fixed then {
        WVR_match = slice(vaddress, mask_fixed, negate(mask_fixed) + 32) == slice(DBGWVR[n], mask_fixed, negate(mask_fixed) + 32);
        if WVR_match & ~(IsZero(slice(DBGWVR[n], bottom_fixed, mask_fixed - bottom_fixed))) then {
            WVR_match = ConstrainUnpredictableBool(Unpredictable_WPMASKEDBITS)
        }
    } else {
        WVR_match = slice(vaddress, bottom_fixed, negate(bottom_fixed) + 32) == slice(DBGWVR[n], bottom_fixed, negate(bottom_fixed) + 32)
    };
    WVR_match & byte_select_match
}

val AArch32_VCRMatch : bits(32) -> bool effect {escape, rreg, undef}

function AArch32_VCRMatch vaddress = {
    mask : bits(32) = undefined : bits(32);
    val_match : bool = undefined : bool;
    match_word : bits(32) = undefined : bits(32);
    if ((UsingAArch32() & ELUsingAArch32(EL1)) & IsZero(slice(vaddress, 0, 2))) & PSTATE.EL != EL2 then {
        match_word = Zeros(32);
        if slice(vaddress, 5, 27) == slice(ExcVectorBase(), 5, 27) then {
            if HaveEL(EL3) & ~(IsSecure()) then {
                match_word = __SetSlice_bits(32, 1, match_word, UInt(slice(vaddress, 2, 3)) + 24, 0b1)
            } else {
                match_word = __SetSlice_bits(32, 1, match_word, UInt(slice(vaddress, 2, 3)) + 0, 0b1)
            }
        };
        if ((HaveEL(EL3) & ELUsingAArch32(EL3)) & IsSecure()) & slice(vaddress, 5, 27) == slice(MVBAR, 5, 27) then {
            match_word = __SetSlice_bits(32, 1, match_word, UInt(slice(vaddress, 2, 3)) + 8, 0b1)
        };
        if ~(HaveEL(EL3)) then {
            mask = ((0x00 @ 0x00) @ 0x00) @ 0xDE
        } else {
            if ~(ELUsingAArch32(EL3)) then {
                mask = ((0xDE @ 0x00) @ 0x00) @ 0xDE
            } else {
                mask = ((0xDE @ 0x00) @ 0xDC) @ 0xDE
            }
        };
        match_word = (match_word & get_DBGVCR()) & mask;
        val_match = ~(IsZero(match_word));
        if ~(IsZero(match_word[27 .. 26] @ (match_word[11 .. 10] @ match_word[3 .. 2]))) & DebugTarget() == PSTATE.EL then {
            val_match = ConstrainUnpredictableBool(Unpredictable_VCMATCHDAPA)
        }
    } else {
        val_match = false
    };
    val_match
}

val AArch32_TakeVirtualIRQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch32_TakeVirtualIRQException () = {
    assert(EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1));
    if ELUsingAArch32(EL2) then {
        assert([get_HCR()[27]] == 0b0 & [get_HCR()[4]] == 0b1)
    } else {
        assert([HCR_EL2[27]] == 0b0 & [HCR_EL2[4]] == 0b1)
    };
    if PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1)) then {
        AArch64_TakeVirtualIRQException()
    };
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 24;
    let lr_offset = 4;
    AArch32_EnterMode(M32_IRQ, preferred_exception_return, lr_offset, vect_offset)
}

val AArch32_TakeVirtualFIQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch32_TakeVirtualFIQException () = {
    assert(EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1));
    if ELUsingAArch32(EL2) then {
        assert([get_HCR()[27]] == 0b0 & [get_HCR()[3]] == 0b1)
    } else {
        assert([HCR_EL2[27]] == 0b0 & [HCR_EL2[3]] == 0b1)
    };
    if PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1)) then {
        AArch64_TakeVirtualFIQException()
    };
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 28;
    let lr_offset = 4;
    AArch32_EnterMode(M32_FIQ, preferred_exception_return, lr_offset, vect_offset)
}

val AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled : unit -> bool effect {escape, rreg, undef}

function AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled () = {
    if ~(HaveEL(EL3)) & ~(IsSecure()) then {
        return(false)
    };
    DBGEN == HIGH & SPIDEN == HIGH
}

val AArch32_S1AttrDecode : (bits(2), bits(3), AccType) -> MemoryAttributes effect {escape, rreg, undef}

function AArch32_S1AttrDecode (SH, attr, acctype) = {
    memattrs : MemoryAttributes = undefined : MemoryAttributes;
    mair : bits(64) = undefined : bits(64);
    if PSTATE.EL == EL2 then {
        mair = get_HMAIR1() @ get_HMAIR0()
    } else {
        mair = get_MAIR1() @ get_MAIR0()
    };
    let index = 8 * UInt(attr);
    attrfield : bits(8) = undefined : bits(8);
    attrfield = slice(mair, index, 8);
    memattrs.tagged = false;
    __anon1 : Constraint = undefined : Constraint;
    if (slice(attrfield, 4, 4) != 0x0 & slice(attrfield, 4, 4) != 0xF) & slice(attrfield, 0, 4) == 0x0 | slice(attrfield, 4, 4) == 0x0 & (slice(attrfield, 0, 4) & 0x3) != 0x0 then {
        (__anon1, attrfield) = ConstrainUnpredictableBits(Unpredictable_RESMAIR)
    };
    __anon2 : Constraint = undefined : Constraint;
    if (~(HaveMTEExt()) & slice(attrfield, 4, 4) == 0xF) & slice(attrfield, 0, 4) == 0x0 then {
        (__anon2, attrfield) = ConstrainUnpredictableBits(Unpredictable_RESMAIR)
    };
    if slice(attrfield, 4, 4) == 0x0 then {
        memattrs.typ = MemType_Device;
        match slice(attrfield, 0, 4) {
          0x0 => {
              memattrs.device = DeviceType_nGnRnE
          },
          0x4 => {
              memattrs.device = DeviceType_nGnRE
          },
          0x8 => {
              memattrs.device = DeviceType_nGRE
          },
          0xC => {
              memattrs.device = DeviceType_GRE
          },
          _ => {
              Unreachable()
          }
        }
    } else {
        if slice(attrfield, 0, 4) != 0x0 then {
            memattrs.typ = MemType_Normal;
            memattrs.outer = LongConvertAttrsHints(slice(attrfield, 4, 4), acctype);
            memattrs.inner = LongConvertAttrsHints(slice(attrfield, 0, 4), acctype);
            memattrs.shareable = [SH[1]] == 0b1;
            memattrs.outershareable = SH == 0b10
        } else {
            if HaveMTEExt() & attrfield == 0xF0 then {
                memattrs.tagged = true;
                memattrs.typ = MemType_Normal;
                __tc1 : MemAttrHints = memattrs.outer;
                __tc1.attrs = MemAttr_WB;
                memattrs.outer = __tc1;
                __tc2 : MemAttrHints = memattrs.inner;
                __tc2.attrs = MemAttr_WB;
                memattrs.inner = __tc2;
                __tc3 : MemAttrHints = memattrs.outer;
                __tc3.hints = MemHint_RWA;
                memattrs.outer = __tc3;
                __tc4 : MemAttrHints = memattrs.inner;
                __tc4.hints = MemHint_RWA;
                memattrs.inner = __tc4;
                memattrs.shareable = [SH[1]] == 0b1;
                memattrs.outershareable = SH == 0b10
            } else {
                Unreachable()
            }
        }
    };
    MemAttrDefaults(memattrs)
}

val AArch32_ReportPrefetchAbort : forall ('route_to_monitor : Bool).
  (bool('route_to_monitor), FaultRecord, bits(32)) -> unit effect {escape, rreg, undef, wreg}

function AArch32_ReportPrefetchAbort (route_to_monitor, fault, vaddress) = {
    long_format : bool = undefined : bool;
    long_format = false;
    if route_to_monitor & ~(IsSecure()) then {
        long_format = ([TTBCR_S[31]] == 0b1 | PSTATE.EL == EL2) | [get_TTBCR()[31]] == 0b1
    } else {
        long_format = [get_TTBCR()[31]] == 0b1
    };
    let d_side = false;
    fsr : bits(32) = undefined : bits(32);
    if long_format then {
        fsr = AArch32_FaultStatusLD(d_side, fault)
    } else {
        fsr = AArch32_FaultStatusSD(d_side, fault)
    };
    if route_to_monitor then {
        IFSR_S = fsr;
        set_IFAR_S(vaddress)
    } else {
        set_IFSR(fsr);
        set_IFAR(vaddress)
    };
    return()
}

val AArch32_ReportDataAbort : forall ('route_to_monitor : Bool).
  (bool('route_to_monitor), FaultRecord, bits(32)) -> unit effect {escape, rreg, undef, wreg}

function AArch32_ReportDataAbort (route_to_monitor, fault, vaddress) = {
    long_format : bool = undefined : bool;
    long_format = false;
    if route_to_monitor & ~(IsSecure()) then {
        long_format = [TTBCR_S[31]] == 0b1;
        if ~(IsSErrorInterrupt(fault)) & ~(long_format) then {
            long_format = PSTATE.EL == EL2 | [get_TTBCR()[31]] == 0b1
        }
    } else {
        long_format = [get_TTBCR()[31]] == 0b1
    };
    let d_side = true;
    syndrome : bits(32) = undefined : bits(32);
    if long_format then {
        syndrome = AArch32_FaultStatusLD(d_side, fault)
    } else {
        syndrome = AArch32_FaultStatusSD(d_side, fault)
    };
    i_syndrome : bits(32) = undefined : bits(32);
    if fault.acctype == AccType_IC then {
        if ~(long_format) & __IMPDEF_boolean("Report I-cache maintenance fault in IFSR") then {
            i_syndrome = syndrome;
            (syndrome[10 .. 10] @ syndrome[3 .. 0]) = EncodeSDFSC(Fault_ICacheMaint, 1)
        } else {
            i_syndrome = undefined : bits(32)
        };
        if route_to_monitor then {
            IFSR_S = i_syndrome
        } else {
            set_IFSR(i_syndrome)
        }
    };
    if route_to_monitor then {
        DFSR_S = syndrome;
        set_DFAR_S(vaddress)
    } else {
        set_DFSR(syndrome);
        set_DFAR(vaddress)
    };
    return()
}

val AArch32_PendingUnmaskedVirtualInterrupts : unit -> (bool, bool, bool) effect {escape, rreg, undef}

function AArch32_PendingUnmaskedVirtualInterrupts () = {
    if HaveEL(EL2) & ~(ELUsingAArch32(EL2)) | HaveEL(EL3) & ~(ELUsingAArch32(EL3)) then {
        return(AArch64_PendingUnmaskedVirtualInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F)))
    };
    let mask = PSTATE.A @ (PSTATE.I @ PSTATE.F);
    pending : bits(3) = undefined : bits(3);
    if (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & [get_HCR()[27]] == 0b0 then {
        pending = (get_HCR()[8 .. 8] @ (get_HCR()[7 .. 7] @ get_HCR()[6 .. 6])) & (get_HCR()[5 .. 5] @ (get_HCR()[4 .. 4] @ get_HCR()[3 .. 3]))
    } else {
        pending = 0b000
    };
    let unmasked_pending : bits(3) = pending & ~(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

val AArch32_PendingUnmaskedPhysicalInterrupts : unit -> (bool, bool, bool) effect {escape, rreg, undef}

function AArch32_PendingUnmaskedPhysicalInterrupts () = {
    if HaveEL(EL3) & ~(ELUsingAArch32(EL3)) then {
        return(AArch64_PendingUnmaskedPhysicalInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F)))
    };
    let se_pending = if IsPhysicalSErrorPending() then 0b1 else 0b0;
    let irq_pending = if IRQPending() then 0b1 else 0b0;
    let fiq_pending = if FIQPending() then 0b1 else 0b0;
    let pending : bits(3) = (se_pending @ irq_pending) @ fiq_pending;
    mask : bits(3) = undefined : bits(3);
    mask = PSTATE.A @ (PSTATE.I @ PSTATE.F);
    mask_override : bits(3) = undefined : bits(3);
    if (PSTATE.EL == EL1 | PSTATE.EL == EL0) & EL2Enabled() then {
        mask_override = if [get_HCR()[27]] == 0b1 then 0b111 else get_HCR()[5 .. 5] @ (get_HCR()[4 .. 4] @ get_HCR()[3 .. 3]);
        mask = mask & ~(mask_override)
    };
    if HaveEL(EL3) then {
        if PSTATE.EL != EL3 then {
            if [get_SCR()[2]] == 0b1 & ([get_SCR()[4]] == 0b0 | [get_HCR()[3]] == 0b1) then {
                mask = __SetSlice_bits(3, 1, mask, 0, 0b0)
            };
            if [get_SCR()[1]] == 0b1 & [get_HCR()[4]] == 0b1 then {
                mask = __SetSlice_bits(3, 1, mask, 1, 0b0)
            };
            if [get_SCR()[3]] == 0b1 & ([get_SCR()[5]] == 0b0 | [get_HCR()[5]] == 0b1) then {
                mask = __SetSlice_bits(3, 1, mask, 2, 0b0)
            }
        }
    };
    let unmasked_pending : bits(3) = pending & ~(mask);
    return(([unmasked_pending[2]] == 0b1, [unmasked_pending[1]] == 0b1, [unmasked_pending[0]] == 0b1))
}

val AArch32_GenerateDebugExceptionsFrom : forall ('secure : Bool).
  (bits(2), bool('secure)) -> bool effect {escape, rreg, undef}

function AArch32_GenerateDebugExceptionsFrom (from, secure) = {
    mask : bits(1) = undefined : bits(1);
    if from == EL0 & ~(ELStateUsingAArch32(EL1, secure)) then {
        mask = undefined : bits(1);
        return(AArch64_GenerateDebugExceptionsFrom(from, secure, mask))
    };
    if ([get_DBGOSLSR()[1]] == 0b1 | DoubleLockStatus()) | Halted() then {
        return(false)
    };
    enabled : bool = undefined : bool;
    spd : bits(2) = undefined : bits(2);
    if HaveEL(EL3) & secure then {
        spd = if ELUsingAArch32(EL3) then slice(get_SDCR(), 14, 2) else slice(MDCR_EL3, 14, 2);
        if [spd[1]] == 0b1 then {
            enabled = [spd[0]] == 0b1
        } else {
            enabled = AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled()
        };
        if from == EL0 then {
            enabled = enabled | [get_SDER()[0]] == 0b1
        }
    } else {
        enabled = from != EL2
    };
    enabled
}

val AArch32_GenerateDebugExceptions : unit -> bool effect {escape, rreg, undef}

function AArch32_GenerateDebugExceptions () = {
    AArch32_GenerateDebugExceptionsFrom(PSTATE.EL, IsSecure())
}

val AArch32_GeneralExceptionsToAArch64 : unit -> bool effect {escape, rreg, undef}

function AArch32_GeneralExceptionsToAArch64 () = {
    PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1)) | (EL2Enabled() & ~(ELUsingAArch32(EL2))) & [HCR_EL2[27]] == 0b1
}

val AArch32_FaultSyndrome : forall ('d_side : Bool).
  (bool('d_side), FaultRecord) -> bits(25) effect {escape, rreg, undef}

function AArch32_FaultSyndrome (d_side, fault) = {
    assert(fault.typ != Fault_None);
    iss : bits(25) = Zeros();
    if HaveRASExt() & IsAsyncAbort(fault) then {
        iss = __SetSlice_bits(25, 2, iss, 10, fault.errortype)
    };
    if d_side then {
        if IsSecondStage(fault) & ~(fault.s2fs1walk) then {
            iss = __SetSlice_bits(25, 11, iss, 14, LSInstructionSyndrome())
        };
        if fault.acctype == AccType_DC | fault.acctype == AccType_DC_UNPRIV | fault.acctype == AccType_IC | fault.acctype == AccType_AT then {
            iss = __SetSlice_bits(25, 1, iss, 8, 0b1);
            iss = __SetSlice_bits(25, 1, iss, 6, 0b1)
        } else {
            iss = __SetSlice_bits(25, 1, iss, 6, if fault.write then 0b1 else 0b0)
        }
    };
    if IsExternalAbort(fault) then {
        iss = __SetSlice_bits(25, 1, iss, 9, fault.extflag)
    };
    iss = __SetSlice_bits(25, 1, iss, 7, if fault.s2fs1walk then 0b1 else 0b0);
    let iss = __SetSlice_bits(25, 6, iss, 0, EncodeLDFSC(fault.typ, fault.level));
    iss
}

val AArch32_AbortSyndrome : (Exception, FaultRecord, bits(32)) -> ExceptionRecord effect {escape, rreg, undef}

function AArch32_AbortSyndrome (typ, fault, vaddress) = {
    exception : ExceptionRecord = undefined : ExceptionRecord;
    exception = ExceptionSyndrome(typ);
    let d_side = typ == Exception_DataAbort;
    exception.syndrome = AArch32_FaultSyndrome(d_side, fault);
    exception.vaddress = ZeroExtend(vaddress);
    if IPAValid(fault) then {
        exception.ipavalid = true;
        exception.NS = fault.ipaddress.NS;
        exception.ipaddress = ZeroExtend(fault.ipaddress.address)
    } else {
        exception.ipavalid = false
    };
    exception
}

val AArch32_ExecutingATS1xPInstr : unit -> bool effect {rreg, undef}

function AArch32_ExecutingATS1xPInstr () = {
    if ~(HavePrivATExt()) then {
        return(false)
    };
    let instr = ThisInstr();
    CRm : bits(4) = undefined : bits(4);
    CRn : bits(4) = undefined : bits(4);
    op1 : bits(3) = undefined : bits(3);
    op2 : bits(3) = undefined : bits(3);
    if slice(instr, 24, 4) == 0xE & slice(instr, 8, 4) == 0xE then {
        op1 = slice(instr, 21, 3);
        CRn = slice(instr, 16, 4);
        CRm = slice(instr, 0, 4);
        op2 = slice(instr, 5, 3);
        return(((op1 == 0b000 & CRn == 0x7) & CRm == 0x9) & (op2 == 0b000 | op2 == 0b001))
    } else {
        return(false)
    }
}

val AArch32_EnterMonitorMode : forall ('lr_offset : Int) ('vect_offset : Int).
  (bits(32), int('lr_offset), int('vect_offset)) -> unit effect {escape, rreg, undef, wreg}

function AArch32_EnterMonitorMode (preferred_exception_return, lr_offset, vect_offset) = {
    SynchronizeContext();
    assert(HaveEL(EL3) & ELUsingAArch32(EL3));
    let from_secure = IsSecure();
    let spsr = GetPSRFromPSTATE();
    if PSTATE.M == M32_Monitor then {
        __tc1 : bits(32) = get_SCR();
        __tc1 = __SetSlice_bits(32, 1, __tc1, 0, 0b0);
        set_SCR(__tc1)
    };
    AArch32_WriteMode(M32_Monitor);
    SPSR() = spsr;
    R(14) = preferred_exception_return + lr_offset;
    PSTATE.T = [get_SCTLR()[30]];
    PSTATE.SS = 0b0;
    (PSTATE.A @ PSTATE.I @ PSTATE.F) = 0b111;
    PSTATE.E = [get_SCTLR()[25]];
    PSTATE.IL = 0b0;
    PSTATE.IT = 0x00;
    if HavePANExt() then {
        if ~(from_secure) then {
            PSTATE.PAN = 0b0
        } else {
            if [get_SCTLR()[23]] == 0b0 then {
                PSTATE.PAN = 0b1
            }
        }
    };
    BranchTo(slice(MVBAR, 5, 27) @ __GetSlice_int(5, vect_offset, 0), BranchType_EXCEPTION);
    EndOfInstruction()
}

val AArch32_EnterHypMode : forall ('vect_offset : Int).
  (ExceptionRecord, bits(32), int('vect_offset)) -> unit effect {escape, rreg, undef, wreg}

function AArch32_EnterHypMode (exception, preferred_exception_return, vect_offset) = {
    SynchronizeContext();
    assert((HaveEL(EL2) & ~(IsSecure())) & ELUsingAArch32(EL2));
    let spsr = GetPSRFromPSTATE();
    if ~(exception.typ == Exception_IRQ | exception.typ == Exception_FIQ) then {
        AArch32_ReportHypEntry(exception)
    };
    AArch32_WriteMode(M32_Hyp);
    SPSR() = spsr;
    set_ELR_hyp(preferred_exception_return);
    PSTATE.T = [get_HSCTLR()[30]];
    PSTATE.SS = 0b0;
    if ~(HaveEL(EL3)) | [SCR_GEN()[3]] == 0b0 then {
        PSTATE.A = 0b1
    };
    if ~(HaveEL(EL3)) | [SCR_GEN()[1]] == 0b0 then {
        PSTATE.I = 0b1
    };
    if ~(HaveEL(EL3)) | [SCR_GEN()[2]] == 0b0 then {
        PSTATE.F = 0b1
    };
    PSTATE.E = [get_HSCTLR()[25]];
    PSTATE.IL = 0b0;
    PSTATE.IT = 0x00;
    BranchTo(slice(get_HVBAR(), 5, 27) @ __GetSlice_int(5, vect_offset, 0), BranchType_EXCEPTION);
    EndOfInstruction()
}

val AArch32_TakeUndefInstrException__0 : unit -> unit effect {escape, rreg, undef, wreg}

val AArch32_TakeUndefInstrException__1 : ExceptionRecord -> unit effect {escape, rreg, undef, wreg}

overload AArch32_TakeUndefInstrException = {
  AArch32_TakeUndefInstrException__0,
  AArch32_TakeUndefInstrException__1
}

function AArch32_TakeUndefInstrException__0 () = {
    let exception = ExceptionSyndrome(Exception_Uncategorized);
    AArch32_TakeUndefInstrException(exception)
}

function AArch32_TakeUndefInstrException__1 exception = {
    let route_to_hyp = (EL2Enabled() & PSTATE.EL == EL0) & [get_HCR()[27]] == 0b1;
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 4;
    let lr_offset = if CurrentInstrSet() == InstrSet_A32 then 4 else 2;
    if PSTATE.EL == EL2 then {
        AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset)
    } else {
        if route_to_hyp then {
            AArch32_EnterHypMode(exception, preferred_exception_return, 20)
        } else {
            AArch32_EnterMode(M32_Undef, preferred_exception_return, lr_offset, vect_offset)
        }
    }
}

val AArch32_TakePhysicalIRQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch32_TakePhysicalIRQException () = {
    route_to_aarch64 : bool = undefined : bool;
    route_to_aarch64 = PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1));
    if (~(route_to_aarch64) & EL2Enabled()) & ~(ELUsingAArch32(EL2)) then {
        route_to_aarch64 = [HCR_EL2[27]] == 0b1 | [HCR_EL2[4]] == 0b1 & ~(IsInHost())
    };
    if (~(route_to_aarch64) & HaveEL(EL3)) & ~(ELUsingAArch32(EL3)) then {
        route_to_aarch64 = [SCR_EL3[1]] == 0b1
    };
    if route_to_aarch64 then {
        AArch64_TakePhysicalIRQException()
    };
    let route_to_monitor = HaveEL(EL3) & [get_SCR()[1]] == 0b1;
    let route_to_hyp = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([get_HCR()[27]] == 0b1 | [get_HCR()[4]] == 0b1);
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 24;
    let lr_offset = 4;
    exception : ExceptionRecord = undefined : ExceptionRecord;
    if route_to_monitor then {
        AArch32_EnterMonitorMode(preferred_exception_return, lr_offset, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_hyp then {
            exception = ExceptionSyndrome(Exception_IRQ);
            AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset)
        } else {
            AArch32_EnterMode(M32_IRQ, preferred_exception_return, lr_offset, vect_offset)
        }
    }
}

val AArch32_TakePhysicalFIQException : unit -> unit effect {escape, rreg, undef, wreg}

function AArch32_TakePhysicalFIQException () = {
    route_to_aarch64 : bool = undefined : bool;
    route_to_aarch64 = PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1));
    if (~(route_to_aarch64) & EL2Enabled()) & ~(ELUsingAArch32(EL2)) then {
        route_to_aarch64 = [HCR_EL2[27]] == 0b1 | [HCR_EL2[3]] == 0b1 & ~(IsInHost())
    };
    if (~(route_to_aarch64) & HaveEL(EL3)) & ~(ELUsingAArch32(EL3)) then {
        route_to_aarch64 = [SCR_EL3[2]] == 0b1
    };
    if route_to_aarch64 then {
        AArch64_TakePhysicalFIQException()
    };
    let route_to_monitor = HaveEL(EL3) & [get_SCR()[2]] == 0b1;
    let route_to_hyp = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([get_HCR()[27]] == 0b1 | [get_HCR()[3]] == 0b1);
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 28;
    let lr_offset = 4;
    exception : ExceptionRecord = undefined : ExceptionRecord;
    if route_to_monitor then {
        AArch32_EnterMonitorMode(preferred_exception_return, lr_offset, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_hyp then {
            exception = ExceptionSyndrome(Exception_FIQ);
            AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset)
        } else {
            AArch32_EnterMode(M32_FIQ, preferred_exception_return, lr_offset, vect_offset)
        }
    }
}

val AArch32_InstructionAbort : (bits(32), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch32_InstructionAbort (vaddress, fault) = {
    let route_to_monitor = (HaveEL(EL3) & [get_SCR()[3]] == 0b1) & IsExternalAbort(fault);
    let route_to_hyp = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ((([get_HCR()[27]] == 0b1 | IsSecondStage(fault)) | (HaveRASExt() & [get_HCR2()[5]] == 0b1) & IsExternalAbort(fault)) | IsDebugException(fault) & [get_HDCR()[8]] == 0b1);
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 12;
    let lr_offset = 4;
    if IsDebugException(fault) then {
        __tc1 : bits(32) = get_DBGDSCRext();
        __tc1 = __SetSlice_bits(32, 4, __tc1, 2, fault.debugmoe);
        set_DBGDSCRext(__tc1)
    };
    exception : ExceptionRecord = undefined : ExceptionRecord;
    if route_to_monitor then {
        AArch32_ReportPrefetchAbort(route_to_monitor, fault, vaddress);
        AArch32_EnterMonitorMode(preferred_exception_return, lr_offset, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_hyp then {
            if fault.typ == Fault_Alignment then {
                exception = ExceptionSyndrome(Exception_PCAlignment);
                exception.vaddress = ThisInstrAddr()
            } else {
                exception = AArch32_AbortSyndrome(Exception_InstructionAbort, fault, vaddress)
            };
            if PSTATE.EL == EL2 then {
                AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset)
            } else {
                AArch32_EnterHypMode(exception, preferred_exception_return, 20)
            }
        } else {
            AArch32_ReportPrefetchAbort(route_to_monitor, fault, vaddress);
            AArch32_EnterMode(M32_Abort, preferred_exception_return, lr_offset, vect_offset)
        }
    }
}

val AArch32_CheckIllegalState : unit -> unit effect {escape, rreg, undef, wreg}

function AArch32_CheckIllegalState () = {
    exception : ExceptionRecord = undefined : ExceptionRecord;
    route_to_hyp : bool = undefined : bool;
    vect_offset : int = undefined : int;
    if AArch32_GeneralExceptionsToAArch64() then {
        AArch64_CheckIllegalState()
    } else {
        if PSTATE.IL == 0b1 then {
            route_to_hyp = (EL2Enabled() & PSTATE.EL == EL0) & [get_HCR()[27]] == 0b1;
            let preferred_exception_return : bits(32) = ThisInstrAddr();
            vect_offset = 4;
            if PSTATE.EL == EL2 | route_to_hyp then {
                exception = ExceptionSyndrome(Exception_IllegalState);
                if PSTATE.EL == EL2 then {
                    AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset)
                } else {
                    AArch32_EnterHypMode(exception, preferred_exception_return, 20)
                }
            } else {
                AArch32_TakeUndefInstrException()
            }
        }
    }
}

val AArch32_DataAbort : (bits(32), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch32_DataAbort (vaddress, fault) = {
    let route_to_monitor = (HaveEL(EL3) & [get_SCR()[3]] == 0b1) & IsExternalAbort(fault);
    let route_to_hyp = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ((([get_HCR()[27]] == 0b1 | IsSecondStage(fault)) | (HaveRASExt() & [get_HCR2()[5]] == 0b1) & IsExternalAbort(fault)) | IsDebugException(fault) & [get_HDCR()[8]] == 0b1);
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 16;
    let lr_offset = 8;
    if IsDebugException(fault) then {
        __tc1 : bits(32) = get_DBGDSCRext();
        __tc1 = __SetSlice_bits(32, 4, __tc1, 2, fault.debugmoe);
        set_DBGDSCRext(__tc1)
    };
    exception : ExceptionRecord = undefined : ExceptionRecord;
    if route_to_monitor then {
        AArch32_ReportDataAbort(route_to_monitor, fault, vaddress);
        AArch32_EnterMonitorMode(preferred_exception_return, lr_offset, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_hyp then {
            exception = AArch32_AbortSyndrome(Exception_DataAbort, fault, vaddress);
            if PSTATE.EL == EL2 then {
                AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset)
            } else {
                AArch32_EnterHypMode(exception, preferred_exception_return, 20)
            }
        } else {
            AArch32_ReportDataAbort(route_to_monitor, fault, vaddress);
            AArch32_EnterMode(M32_Abort, preferred_exception_return, lr_offset, vect_offset)
        }
    }
}

val AArch32_CreateFaultRecord : forall 'level ('write : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (Fault, bits(40), bits(4), int('level), AccType, bool('write), bits(1), bits(4), bits(2), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_CreateFaultRecord (typ, ipaddress, domain, level, acctype, write, extflag, debugmoe, errortype, secondstage, s2fs1walk) = {
    fault : FaultRecord = undefined : FaultRecord;
    fault.typ = typ;
    if ((((typ != Fault_None & PSTATE.EL != EL2) & [get_TTBCR()[31]] == 0b0) & ~(secondstage)) & ~(s2fs1walk)) & AArch32_DomainValid(typ, level) then {
        fault.domain = domain
    } else {
        fault.domain = undefined : bits(4)
    };
    fault.debugmoe = debugmoe;
    fault.errortype = errortype;
    __tc1 : FullAddress = fault.ipaddress;
    __tc1.NS = undefined : bits(1);
    fault.ipaddress = __tc1;
    __tc2 : FullAddress = fault.ipaddress;
    __tc2.address = ZeroExtend(ipaddress);
    fault.ipaddress = __tc2;
    fault.level = level;
    fault.acctype = acctype;
    fault.write = write;
    fault.extflag = extflag;
    fault.secondstage = secondstage;
    fault.s2fs1walk = s2fs1walk;
    fault
}

val _SyncExternalFault : (bits(52), AccessDescriptor, bits(1), bits(1)) -> FaultRecord effect {escape, rreg, undef}

function _SyncExternalFault (paddress, accdesc, read, extflag) = {
    let write = read == 0b0;
    let secondstage = accdesc.secondstage;
    let s2fs1walk = accdesc.s2fs1walk;
    let level = accdesc.level;
    let errortype = undefined : bits(2);
    debugmoe : bits(4) = undefined : bits(4);
    domain : bits(4) = undefined : bits(4);
    if UsingAArch32() then {
        debugmoe = undefined : bits(4);
        domain = undefined : bits(4);
        assert(slice(paddress, 40, 8) == 0x00);
        assert(slice(paddress, 40, 12) == Zeros(52 - 40));
        return(AArch32_CreateFaultRecord(Fault_SyncExternal, slice(paddress, 0, 40), domain, level, accdesc.acctype, write, extflag, debugmoe, errortype, secondstage, s2fs1walk))
    } else {
        return(AArch64_CreateFaultRecord(Fault_SyncExternal, paddress, undefined : bits(1), level, accdesc.acctype, write, extflag, errortype, secondstage, s2fs1walk))
    }
}

val AArch32_TranslationFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(40), bits(4), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_TranslationFault (ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let debugmoe = undefined : bits(4);
    let errortype = undefined : bits(2);
    AArch32_CreateFaultRecord(Fault_Translation, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_PermissionFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(40), bits(4), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_PermissionFault (ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let debugmoe = undefined : bits(4);
    let errortype = undefined : bits(2);
    AArch32_CreateFaultRecord(Fault_Permission, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_InstructionDevice : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (AddressDescriptor, bits(32), bits(40), int('level), bits(4), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> AddressDescriptor effect {escape, rreg, undef}

function AArch32_InstructionDevice (addrdesc__arg, vaddress, ipaddress, level, domain, acctype, iswrite, secondstage, s2fs1walk) = {
    addrdesc = addrdesc__arg;
    let c = ConstrainUnpredictable(Unpredictable_INSTRDEVICE);
    assert(c == Constraint_NONE | c == Constraint_FAULT);
    if c == Constraint_FAULT then {
        addrdesc.fault = AArch32_PermissionFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk)
    } else {
        __tc1 : MemoryAttributes = addrdesc.memattrs;
        __tc1.typ = MemType_Normal;
        addrdesc.memattrs = __tc1;
        __tc2 : MemAttrHints = addrdesc.memattrs.inner;
        __tc2.attrs = MemAttr_NC;
        __tc3 : MemoryAttributes = addrdesc.memattrs;
        __tc3.inner = __tc2;
        addrdesc.memattrs = __tc3;
        __tc4 : MemAttrHints = addrdesc.memattrs.inner;
        __tc4.hints = MemHint_No;
        __tc5 : MemoryAttributes = addrdesc.memattrs;
        __tc5.inner = __tc4;
        addrdesc.memattrs = __tc5;
        __tc6 : MemoryAttributes = addrdesc.memattrs;
        __tc6.outer = addrdesc.memattrs.inner;
        addrdesc.memattrs = __tc6;
        __tc7 : MemoryAttributes = addrdesc.memattrs;
        __tc7.tagged = false;
        addrdesc.memattrs = __tc7;
        addrdesc.memattrs = MemAttrDefaults(addrdesc.memattrs)
    };
    addrdesc
}

val AArch32_NoFault : unit -> FaultRecord effect {escape, rreg, undef}

function AArch32_NoFault () = {
    let ipaddress = undefined : bits(40);
    let domain = undefined : bits(4);
    let level = undefined : int;
    let acctype = AccType_NORMAL;
    let iswrite = undefined : bool;
    let extflag = undefined : bits(1);
    let debugmoe = undefined : bits(4);
    let errortype = undefined : bits(2);
    let secondstage = false;
    let s2fs1walk = false;
    AArch32_CreateFaultRecord(Fault_None, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_TranslateAddressS1Off : forall ('iswrite : Bool).
  (bits(32), AccType, bool('iswrite)) -> TLBRecord effect {escape, rreg, undef}

function AArch32_TranslateAddressS1Off (vaddress, acctype, iswrite) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    result : TLBRecord = undefined : TLBRecord;
    let default_cacheable = HasS2Translation() & (if ELUsingAArch32(EL2) then [get_HCR()[12]] else [HCR_EL2[12]]) == 0b1;
    cacheable : bool = undefined : bool;
    if default_cacheable then {
        __tc1 : MemoryAttributes = result.addrdesc.memattrs;
        __tc1.typ = MemType_Normal;
        __tc2 : AddressDescriptor = result.addrdesc;
        __tc2.memattrs = __tc1;
        result.addrdesc = __tc2;
        __tc3 : MemAttrHints = result.addrdesc.memattrs.inner;
        __tc3.attrs = MemAttr_WB;
        __tc4 : MemoryAttributes = result.addrdesc.memattrs;
        __tc4.inner = __tc3;
        __tc5 : AddressDescriptor = result.addrdesc;
        __tc5.memattrs = __tc4;
        result.addrdesc = __tc5;
        __tc6 : MemAttrHints = result.addrdesc.memattrs.inner;
        __tc6.hints = MemHint_RWA;
        __tc7 : MemoryAttributes = result.addrdesc.memattrs;
        __tc7.inner = __tc6;
        __tc8 : AddressDescriptor = result.addrdesc;
        __tc8.memattrs = __tc7;
        result.addrdesc = __tc8;
        __tc9 : MemoryAttributes = result.addrdesc.memattrs;
        __tc9.shareable = false;
        __tc10 : AddressDescriptor = result.addrdesc;
        __tc10.memattrs = __tc9;
        result.addrdesc = __tc10;
        __tc11 : MemoryAttributes = result.addrdesc.memattrs;
        __tc11.outershareable = false;
        __tc12 : AddressDescriptor = result.addrdesc;
        __tc12.memattrs = __tc11;
        result.addrdesc = __tc12;
        __tc13 : MemoryAttributes = result.addrdesc.memattrs;
        __tc13.tagged = [HCR_EL2[57]] == 0b1;
        __tc14 : AddressDescriptor = result.addrdesc;
        __tc14.memattrs = __tc13;
        result.addrdesc = __tc14
    } else {
        if acctype != AccType_IFETCH then {
            __tc15 : MemoryAttributes = result.addrdesc.memattrs;
            __tc15.typ = MemType_Device;
            __tc16 : AddressDescriptor = result.addrdesc;
            __tc16.memattrs = __tc15;
            result.addrdesc = __tc16;
            __tc17 : MemoryAttributes = result.addrdesc.memattrs;
            __tc17.device = DeviceType_nGnRnE;
            __tc18 : AddressDescriptor = result.addrdesc;
            __tc18.memattrs = __tc17;
            result.addrdesc = __tc18;
            __tc19 : MemoryAttributes = result.addrdesc.memattrs;
            __tc19.inner = undefined : MemAttrHints;
            __tc20 : AddressDescriptor = result.addrdesc;
            __tc20.memattrs = __tc19;
            result.addrdesc = __tc20;
            __tc21 : MemoryAttributes = result.addrdesc.memattrs;
            __tc21.tagged = false;
            __tc22 : AddressDescriptor = result.addrdesc;
            __tc22.memattrs = __tc21;
            result.addrdesc = __tc22
        } else {
            if PSTATE.EL == EL2 then {
                cacheable = [get_HSCTLR()[12]] == 0b1
            } else {
                cacheable = [get_SCTLR()[12]] == 0b1
            };
            __tc23 : MemoryAttributes = result.addrdesc.memattrs;
            __tc23.typ = MemType_Normal;
            __tc24 : AddressDescriptor = result.addrdesc;
            __tc24.memattrs = __tc23;
            result.addrdesc = __tc24;
            if cacheable then {
                __tc25 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc25.attrs = MemAttr_WT;
                __tc26 : MemoryAttributes = result.addrdesc.memattrs;
                __tc26.inner = __tc25;
                __tc27 : AddressDescriptor = result.addrdesc;
                __tc27.memattrs = __tc26;
                result.addrdesc = __tc27;
                __tc28 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc28.hints = MemHint_RA;
                __tc29 : MemoryAttributes = result.addrdesc.memattrs;
                __tc29.inner = __tc28;
                __tc30 : AddressDescriptor = result.addrdesc;
                __tc30.memattrs = __tc29;
                result.addrdesc = __tc30
            } else {
                __tc31 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc31.attrs = MemAttr_NC;
                __tc32 : MemoryAttributes = result.addrdesc.memattrs;
                __tc32.inner = __tc31;
                __tc33 : AddressDescriptor = result.addrdesc;
                __tc33.memattrs = __tc32;
                result.addrdesc = __tc33;
                __tc34 : MemAttrHints = result.addrdesc.memattrs.inner;
                __tc34.hints = MemHint_No;
                __tc35 : MemoryAttributes = result.addrdesc.memattrs;
                __tc35.inner = __tc34;
                __tc36 : AddressDescriptor = result.addrdesc;
                __tc36.memattrs = __tc35;
                result.addrdesc = __tc36
            };
            __tc37 : MemoryAttributes = result.addrdesc.memattrs;
            __tc37.shareable = true;
            __tc38 : AddressDescriptor = result.addrdesc;
            __tc38.memattrs = __tc37;
            result.addrdesc = __tc38;
            __tc39 : MemoryAttributes = result.addrdesc.memattrs;
            __tc39.outershareable = true;
            __tc40 : AddressDescriptor = result.addrdesc;
            __tc40.memattrs = __tc39;
            result.addrdesc = __tc40;
            __tc41 : MemoryAttributes = result.addrdesc.memattrs;
            __tc41.tagged = false;
            __tc42 : AddressDescriptor = result.addrdesc;
            __tc42.memattrs = __tc41;
            result.addrdesc = __tc42
        }
    };
    __tc43 : MemoryAttributes = result.addrdesc.memattrs;
    __tc43.outer = result.addrdesc.memattrs.inner;
    __tc44 : AddressDescriptor = result.addrdesc;
    __tc44.memattrs = __tc43;
    result.addrdesc = __tc44;
    __tc45 : AddressDescriptor = result.addrdesc;
    __tc45.memattrs = MemAttrDefaults(result.addrdesc.memattrs);
    result.addrdesc = __tc45;
    __tc46 : Permissions = result.perms;
    __tc46.ap = undefined : bits(3);
    result.perms = __tc46;
    __tc47 : Permissions = result.perms;
    __tc47.xn = 0b0;
    result.perms = __tc47;
    __tc48 : Permissions = result.perms;
    __tc48.pxn = 0b0;
    result.perms = __tc48;
    result.nG = undefined : bits(1);
    result.contiguous = undefined : bool;
    result.domain = undefined : bits(4);
    result.level = undefined : int;
    result.blocksize = undefined : int;
    __tc49 : FullAddress = result.addrdesc.paddress;
    __tc49.address = ZeroExtend(vaddress);
    __tc50 : AddressDescriptor = result.addrdesc;
    __tc50.paddress = __tc49;
    result.addrdesc = __tc50;
    __tc51 : FullAddress = result.addrdesc.paddress;
    __tc51.NS = if IsSecure() then 0b0 else 0b1;
    __tc52 : AddressDescriptor = result.addrdesc;
    __tc52.paddress = __tc51;
    result.addrdesc = __tc52;
    __tc53 : AddressDescriptor = result.addrdesc;
    __tc53.fault = AArch32_NoFault();
    result.addrdesc = __tc53;
    result
}

val AArch32_DomainFault : forall ('level : Int) ('iswrite : Bool).
  (bits(4), int('level), AccType, bool('iswrite)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_DomainFault (domain, level, acctype, iswrite) = {
    let ipaddress = undefined : bits(40);
    let extflag = undefined : bits(1);
    let debugmoe = undefined : bits(4);
    let errortype = undefined : bits(2);
    let secondstage = false;
    let s2fs1walk = false;
    AArch32_CreateFaultRecord(Fault_Domain, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_CheckDomain : forall ('level : Int) ('iswrite : Bool).
  (bits(4), bits(32), int('level), AccType, bool('iswrite)) -> (bool, FaultRecord) effect {escape, rreg, undef}

function AArch32_CheckDomain (domain, vaddress, level, acctype, iswrite) = {
    let index = 2 * UInt(domain);
    attrfield : bits(2) = undefined : bits(2);
    attrfield = slice(get_DACR(), index, 2);
    __anon1 : Constraint = undefined : Constraint;
    if attrfield == 0b10 then {
        (__anon1, attrfield) = ConstrainUnpredictableBits(Unpredictable_RESDACR)
    };
    fault : FaultRecord = undefined : FaultRecord;
    if attrfield == 0b00 then {
        fault = AArch32_DomainFault(domain, level, acctype, iswrite)
    } else {
        fault = AArch32_NoFault()
    };
    let permissioncheck : bool = attrfield == 0b01;
    return((permissioncheck, fault))
}

val AArch32_DebugFault : forall ('iswrite : Bool).
  (AccType, bool('iswrite), bits(4)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_DebugFault (acctype, iswrite, debugmoe) = {
    let ipaddress = undefined : bits(40);
    let domain = undefined : bits(4);
    let errortype = undefined : bits(2);
    let level = undefined : int;
    let extflag = undefined : bits(1);
    let secondstage = false;
    let s2fs1walk = false;
    AArch32_CreateFaultRecord(Fault_Debug, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_AsynchExternalAbort : forall ('parity : Bool).
  (bool('parity), bits(2), bits(1)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_AsynchExternalAbort (parity, errortype, extflag) = {
    let typ = if parity then Fault_AsyncParity else Fault_AsyncExternal;
    let ipaddress = undefined : bits(40);
    let domain = undefined : bits(4);
    let level = undefined : int;
    let acctype = AccType_NORMAL;
    let iswrite = undefined : bool;
    let debugmoe = undefined : bits(4);
    let secondstage = false;
    let s2fs1walk = false;
    AArch32_CreateFaultRecord(typ, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_TakeVirtualSErrorException : forall ('impdef_syndrome : Bool).
  (bits(1), bits(2), bool('impdef_syndrome), bits(24)) -> unit effect {escape, rreg, undef, wreg}

function AArch32_TakeVirtualSErrorException (extflag, errortype, impdef_syndrome, full_syndrome) = {
    assert(EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1));
    if ELUsingAArch32(EL2) then {
        assert([get_HCR()[27]] == 0b0 & [get_HCR()[5]] == 0b1)
    } else {
        assert([HCR_EL2[27]] == 0b0 & [HCR_EL2[5]] == 0b1)
    };
    if PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1)) then {
        AArch64_TakeVirtualSErrorException(impdef_syndrome, full_syndrome)
    };
    let route_to_monitor = false;
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 16;
    let lr_offset = 8;
    let vaddress = undefined : bits(32);
    let parity = false;
    fault : FaultRecord = undefined : FaultRecord;
    if HaveRASExt() then {
        if ELUsingAArch32(EL2) then {
            fault = AArch32_AsynchExternalAbort(false, slice(get_VDFSR(), 14, 2), [get_VDFSR()[12]])
        } else {
            fault = AArch32_AsynchExternalAbort(false, slice(VSESR_EL2, 14, 2), [VSESR_EL2[12]])
        }
    } else {
        fault = AArch32_AsynchExternalAbort(parity, errortype, extflag)
    };
    ClearPendingVirtualSError();
    AArch32_ReportDataAbort(route_to_monitor, fault, vaddress);
    AArch32_EnterMode(M32_Abort, preferred_exception_return, lr_offset, vect_offset)
}

val AArch32_TakePhysicalSErrorException : forall ('parity : Bool) ('impdef_syndrome : Bool).
  (bool('parity), bits(1), bits(2), bool('impdef_syndrome), bits(24)) -> unit effect {escape, rreg, undef, wreg}

function AArch32_TakePhysicalSErrorException (parity, extflag, errortype, impdef_syndrome, full_syndrome) = {
    ClearPendingPhysicalSError();
    route_to_aarch64 : bool = undefined : bool;
    route_to_aarch64 = PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1));
    if (~(route_to_aarch64) & EL2Enabled()) & ~(ELUsingAArch32(EL2)) then {
        route_to_aarch64 = [HCR_EL2[27]] == 0b1 | ~(IsInHost()) & [HCR_EL2[5]] == 0b1
    };
    if (~(route_to_aarch64) & HaveEL(EL3)) & ~(ELUsingAArch32(EL3)) then {
        route_to_aarch64 = [SCR_EL3[3]] == 0b1
    };
    if route_to_aarch64 then {
        AArch64_TakePhysicalSErrorException(impdef_syndrome, full_syndrome)
    };
    let route_to_monitor = HaveEL(EL3) & [get_SCR()[3]] == 0b1;
    let route_to_hyp = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([get_HCR()[27]] == 0b1 | [get_HCR()[5]] == 0b1);
    let preferred_exception_return : bits(32) = ThisInstrAddr();
    let vect_offset = 16;
    let lr_offset = 8;
    let fault = AArch32_AsynchExternalAbort(parity, errortype, extflag);
    let vaddress = undefined : bits(32);
    exception : ExceptionRecord = undefined : ExceptionRecord;
    if route_to_monitor then {
        AArch32_ReportDataAbort(route_to_monitor, fault, vaddress);
        AArch32_EnterMonitorMode(preferred_exception_return, lr_offset, vect_offset)
    } else {
        if PSTATE.EL == EL2 | route_to_hyp then {
            exception = AArch32_AbortSyndrome(Exception_DataAbort, fault, vaddress);
            if PSTATE.EL == EL2 then {
                AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset)
            } else {
                AArch32_EnterHypMode(exception, preferred_exception_return, 20)
            }
        } else {
            AArch32_ReportDataAbort(route_to_monitor, fault, vaddress);
            AArch32_EnterMode(M32_Abort, preferred_exception_return, lr_offset, vect_offset)
        }
    }
}

function TakePendingInterrupts interrupt_req = {
    AA : bool = undefined : bool;
    FIQ : bool = undefined : bool;
    IRQ : bool = undefined : bool;
    SE : bool = undefined : bool;
    interrupt_taken : bool = undefined : bool;
    syndrome : bits(25) = undefined : bits(25);
    syndrome32 : AArch32_SErrorSyndrome = undefined : AArch32_SErrorSyndrome;
    syndrome64 : bits(25) = undefined : bits(25);
    vAA : bool = undefined : bool;
    vFIQ : bool = undefined : bool;
    vIRQ : bool = undefined : bool;
    vSE : bool = undefined : bool;
    if UsingAArch32() then {
        (vAA, vIRQ, vFIQ) = AArch32_PendingUnmaskedVirtualInterrupts();
        (AA, IRQ, FIQ) = AArch32_PendingUnmaskedPhysicalInterrupts();
        if ~(interrupt_req.take_SE) then {
            AA = false
        };
        if ~(interrupt_req.take_vSE) then {
            vAA = false
        };
        if ~(interrupt_req.take_IRQ) then {
            IRQ = false
        };
        if ~(interrupt_req.take_vIRQ) then {
            vIRQ = false
        };
        if ~(interrupt_req.take_FIQ) then {
            FIQ = false
        };
        if ~(interrupt_req.take_vFIQ) then {
            vFIQ = false
        };
        if ((((AA | FIQ) | IRQ) | vAA) | vFIQ) | vIRQ then {
            interrupt_taken = true
        } else {
            interrupt_taken = false
        };
        if vFIQ then {
            AArch32_TakeVirtualFIQException()
        } else {
            if vIRQ then {
                AArch32_TakeVirtualIRQException()
            } else {
                if vAA then {
                    AArch32_TakeVirtualSErrorException([get_VDFSR()[12]], slice(get_VDFSR(), 14, 2), [get_VDFSR()[24]] == 0b1, slice(get_VDFSR(), 0, 24))
                } else {
                    if FIQ then {
                        AArch32_TakePhysicalFIQException()
                    } else {
                        if IRQ then {
                            AArch32_TakePhysicalIRQException()
                        } else {
                            if AA then {
			        throw(Error_SError(interrupt_req.iesb_req));
                            }
                        }
                    }
                }
            }
        }
    } else {
        (vSE, vIRQ, vFIQ) = AArch64_PendingUnmaskedVirtualInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F));
        (SE, IRQ, FIQ) = AArch64_PendingUnmaskedPhysicalInterrupts(PSTATE.A @ (PSTATE.I @ PSTATE.F));
        if ~(interrupt_req.take_SE) then {
            SE = false
        };
        if ~(interrupt_req.take_vSE) then {
            vSE = false
        };
        if ~(interrupt_req.take_IRQ) then {
            IRQ = false
        };
        if ~(interrupt_req.take_vIRQ) then {
            vIRQ = false
        };
        if ~(interrupt_req.take_FIQ) then {
            FIQ = false
        };
        if ~(interrupt_req.take_vFIQ) then {
            vFIQ = false
        };
        if ((((SE | FIQ) | IRQ) | vSE) | vFIQ) | vIRQ then {
            interrupt_taken = true
        } else {
            interrupt_taken = false
        };
        if vFIQ then {
            AArch64_TakeVirtualFIQException()
        } else {
            if vIRQ then {
                AArch64_TakeVirtualIRQException()
            } else {
                if vSE then {
                    AArch64_TakeVirtualSErrorException([VSESR_EL2[24]] == 0b1, slice(VSESR_EL2, 0, 24))
                } else {
                    if FIQ then {
                        AArch64_TakePhysicalFIQException()
                    } else {
                        if IRQ then {
                            AArch64_TakePhysicalIRQException()
                        } else {
                            if SE then {
			        throw(Error_SError(interrupt_req.iesb_req));
                            }
                        }
                    }
                }
            }
        }
    };
    interrupt_taken
}

function TakeSError(iesb_req) = {
    if UsingAArch32() then {
        let syndrome32 : AArch32_SErrorSyndrome = AArch32_PhysicalSErrorSyndrome();
        let syndrome64 = AArch64_PhysicalSErrorSyndrome(iesb_req);
        AArch32_TakePhysicalSErrorException(false, syndrome32.ExT, syndrome32.AET, [syndrome64[24]] == 0b1, slice(syndrome64, 0, 24))
    } else {
        let syndrome = AArch64_PhysicalSErrorSyndrome(iesb_req);
        AArch64_TakePhysicalSErrorException([syndrome[24]] == 0b1, slice(syndrome, 0, 24))
    }
}

val AArch32_AlignmentFault : forall ('iswrite : Bool) ('secondstage : Bool).
  (AccType, bool('iswrite), bool('secondstage)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_AlignmentFault (acctype, iswrite, secondstage) = {
    let ipaddress = undefined : bits(40);
    let domain = undefined : bits(4);
    let level = undefined : int;
    let extflag = undefined : bits(1);
    let debugmoe = undefined : bits(4);
    let errortype = undefined : bits(2);
    let s2fs1walk = undefined : bool;
    AArch32_CreateFaultRecord(Fault_Alignment, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_AddressSizeFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(40), bits(4), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_AddressSizeFault (ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let debugmoe = undefined : bits(4);
    let errortype = undefined : bits(2);
    AArch32_CreateFaultRecord(Fault_AddressSize, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_AccessFlagFault : forall 'level ('iswrite : Bool) ('secondstage : Bool) ('s2fs1walk : Bool).
  (bits(40), bits(4), int('level), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_AccessFlagFault (ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk) = {
    let extflag = undefined : bits(1);
    let debugmoe = undefined : bits(4);
    let errortype = undefined : bits(2);
    AArch32_CreateFaultRecord(Fault_AccessFlag, ipaddress, domain, level, acctype, iswrite, extflag, debugmoe, errortype, secondstage, s2fs1walk)
}

val AArch32_CheckVectorCatch : forall ('size : Int).
  (bits(32), int('size)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_CheckVectorCatch (vaddress, size) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    val_match : bool = undefined : bool;
    val_match = AArch32_VCRMatch(vaddress);
    if (size == 4 & ~(val_match)) & AArch32_VCRMatch(vaddress + 2) then {
        val_match = ConstrainUnpredictableBool(Unpredictable_VCMATCHHALF)
    };
    acctype : AccType = undefined : AccType;
    debugmoe : bits(4) = undefined : bits(4);
    iswrite : bool = undefined : bool;
    if (val_match & [get_DBGDSCRext()[15]] == 0b1) & AArch32_GenerateDebugExceptions() then {
        acctype = AccType_IFETCH;
        iswrite = false;
        debugmoe = DebugException_VectorCatch;
        return(AArch32_DebugFault(acctype, iswrite, debugmoe))
    } else {
        return(AArch32_NoFault())
    }
}

val AArch32_CheckS2Permission : forall 'level ('iswrite : Bool) ('s2fs1walk : Bool).
  (Permissions, bits(32), bits(40), int('level), AccType, bool('iswrite), bool('s2fs1walk)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_CheckS2Permission (perms, vaddress, ipaddress, level, acctype, iswrite, s2fs1walk) = {
    assert(((HaveEL(EL2) & ~(IsSecure())) & ELUsingAArch32(EL2)) & HasS2Translation());
    let r = [perms.ap[1]] == 0b1;
    let w = [perms.ap[2]] == 0b1;
    xn : bool = undefined : bool;
    if HaveExtendedExecuteNeverExt() then {
        match perms.xn @ perms.xxn {
          0b00 => {
              xn = ~(r)
          },
          0b01 => {
              xn = ~(r) | PSTATE.EL == EL1
          },
          0b10 => {
              xn = true
          },
          0b11 => {
              xn = ~(r) | PSTATE.EL == EL0
          }
        }
    } else {
        xn = ~(r) | perms.xn == 0b1
    };
    fail : bool = undefined : bool;
    failedread : bool = undefined : bool;
    if acctype == AccType_IFETCH & ~(s2fs1walk) then {
        fail = xn;
        failedread = true
    } else {
        if (acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW | acctype == AccType_ORDEREDATOMICRW) & ~(s2fs1walk) then {
            fail = ~(r) | ~(w);
            failedread = ~(r)
        } else {
            if acctype == AccType_DC & ~(s2fs1walk) then {
                fail = false
            } else {
                if iswrite & ~(s2fs1walk) then {
                    fail = ~(w);
                    failedread = false
                } else {
                    fail = ~(r);
                    failedread = ~(iswrite)
                }
            }
        }
    };
    domain : bits(4) = undefined : bits(4);
    secondstage : bool = undefined : bool;
    if fail then {
        domain = undefined : bits(4);
        secondstage = true;
        return(AArch32_PermissionFault(ipaddress, domain, level, acctype, ~(failedread), secondstage, s2fs1walk))
    } else {
        return(AArch32_NoFault())
    }
}

val AArch32_SecondStageTranslate : forall ('iswrite : Bool) ('wasaligned : Bool) ('s2fs1walk : Bool) 'size.
  (AddressDescriptor, bits(32), AccType, bool('iswrite), bool('wasaligned), bool('s2fs1walk), int('size)) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch32_SecondStageTranslate (S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size) = {
    assert(HasS2Translation());
    assert(IsZero(slice(S1.paddress.address, 40, 8)));
    let hwupdatewalk = false;
    if ~(ELUsingAArch32(EL2)) then {
        let (result, _) = AArch64_SecondStageTranslate(S1, ZeroExtend(vaddress, 64), acctype, iswrite, wasaligned, s2fs1walk, size, hwupdatewalk);
        return result
    };
    let s2_enabled = [get_HCR()[0]] == 0b1 | [get_HCR()[12]] == 0b1;
    let secondstage = true;
    S2 : TLBRecord = undefined : TLBRecord;
    domain : bits(4) = undefined : bits(4);
    ipaddress : bits(40) = undefined : bits(40);
    result : AddressDescriptor = undefined : AddressDescriptor;
    if s2_enabled then {
        ipaddress = slice(S1.paddress.address, 0, 40);
        S2 = AArch32_TranslationTableWalk(ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, size);
        if ((~(wasaligned) & acctype != AccType_IFETCH | acctype == AccType_DCZVA) & S2.addrdesc.memattrs.typ == MemType_Device) & ~(IsFault(S2.addrdesc)) then {
            __tc1 : AddressDescriptor = S2.addrdesc;
            __tc1.fault = AArch32_AlignmentFault(acctype, iswrite, secondstage);
            S2.addrdesc = __tc1
        };
        if ~(IsFault(S2.addrdesc)) then {
            __tc2 : AddressDescriptor = S2.addrdesc;
            __tc2.fault = AArch32_CheckS2Permission(S2.perms, vaddress, ipaddress, S2.level, acctype, iswrite, s2fs1walk);
            S2.addrdesc = __tc2
        };
        if ((~(s2fs1walk) & ~(IsFault(S2.addrdesc))) & S2.addrdesc.memattrs.typ == MemType_Device) & acctype == AccType_IFETCH then {
            domain = undefined : bits(4);
            S2.addrdesc = AArch32_InstructionDevice(S2.addrdesc, vaddress, ipaddress, S2.level, domain, acctype, iswrite, secondstage, s2fs1walk)
        };
        if ((s2fs1walk & ~(IsFault(S2.addrdesc))) & [get_HCR()[2]] == 0b1) & S2.addrdesc.memattrs.typ == MemType_Device then {
            domain = undefined : bits(4);
            __tc3 : AddressDescriptor = S2.addrdesc;
            __tc3.fault = AArch32_PermissionFault(ipaddress, domain, S2.level, acctype, iswrite, secondstage, s2fs1walk);
            S2.addrdesc = __tc3
        };
        result = CombineS1S2Desc(S1, S2.addrdesc)
    } else {
        result = S1
    };
    result
}

val AArch32_SecondStageWalk : forall ('iswrite : Bool) ('size : Int).
  (AddressDescriptor, bits(32), AccType, bool('iswrite), int('size)) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch32_SecondStageWalk (S1, vaddress, acctype, iswrite, size) = {
    assert(HasS2Translation());
    let s2fs1walk = true;
    let wasaligned = true;
    AArch32_SecondStageTranslate(S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size)
}

val AArch32_CheckPermission : forall ('level : Int) ('iswrite : Bool).
  (Permissions, bits(32), int('level), bits(4), bits(1), AccType, bool('iswrite)) -> FaultRecord effect {escape, rreg, undef}

function AArch32_CheckPermission (perms, vaddress, level, domain, NS, acctype, iswrite) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    is_ats1xp : bool = undefined : bool;
    is_ldst : bool = undefined : bool;
    ispriv : bool = undefined : bool;
    pan : bits(1) = undefined : bits(1);
    priv_r : bool = undefined : bool;
    priv_w : bool = undefined : bool;
    priv_xn : bool = undefined : bool;
    r : bool = undefined : bool;
    user_r : bool = undefined : bool;
    user_w : bool = undefined : bool;
    user_xn : bool = undefined : bool;
    uwxn : bool = undefined : bool;
    w : bool = undefined : bool;
    wxn : bool = undefined : bool;
    xn : bool = undefined : bool;
    if PSTATE.EL != EL2 then {
        wxn = [get_SCTLR()[19]] == 0b1;
        if ([get_TTBCR()[31]] == 0b1 | [get_SCTLR()[29]] == 0b1) | [perms.ap[0]] == 0b1 then {
            priv_r = true;
            priv_w = [perms.ap[2]] == 0b0;
            user_r = [perms.ap[1]] == 0b1;
            user_w = slice(perms.ap, 1, 2) == 0b01
        } else {
            priv_r = slice(perms.ap, 1, 2) != 0b00;
            priv_w = slice(perms.ap, 1, 2) == 0b01;
            user_r = [perms.ap[1]] == 0b1;
            user_w = false
        };
        uwxn = [get_SCTLR()[20]] == 0b1;
        ispriv = AArch32_AccessIsPrivileged(acctype);
        pan = if HavePANExt() then PSTATE.PAN else 0b0;
        is_ldst = ~(acctype == AccType_DC | acctype == AccType_DC_UNPRIV | acctype == AccType_AT | acctype == AccType_IFETCH);
        is_ats1xp = acctype == AccType_AT & AArch32_ExecutingATS1xPInstr();
        if ((pan == 0b1 & user_r) & ispriv) & (is_ldst | is_ats1xp) then {
            priv_r = false;
            priv_w = false
        };
        user_xn = (~(user_r) | perms.xn == 0b1) | user_w & wxn;
        priv_xn = (((~(priv_r) | perms.xn == 0b1) | perms.pxn == 0b1) | priv_w & wxn) | user_w & uwxn;
        if ispriv then {
            (r, w, xn) = (priv_r, priv_w, priv_xn)
        } else {
            (r, w, xn) = (user_r, user_w, user_xn)
        }
    } else {
        wxn = [get_HSCTLR()[19]] == 0b1;
        r = true;
        w = [perms.ap[2]] == 0b0;
        xn = perms.xn == 0b1 | w & wxn
    };
    secure_instr_fetch : bits(1) = undefined : bits(1);
    if (HaveEL(EL3) & IsSecure()) & NS == 0b1 then {
        secure_instr_fetch = if ELUsingAArch32(EL3) then [get_SCR()[9]] else [SCR_EL3[9]];
        if secure_instr_fetch == 0b1 then {
            xn = true
        }
    };
    fail : bool = undefined : bool;
    failedread : bool = undefined : bool;
    if acctype == AccType_IFETCH then {
        fail = xn;
        failedread = true
    } else {
        if acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW | acctype == AccType_ORDEREDATOMICRW then {
            fail = ~(r) | ~(w);
            failedread = ~(r)
        } else {
            if acctype == AccType_DC then {
                fail = false
            } else {
                if iswrite then {
                    fail = ~(w);
                    failedread = false
                } else {
                    fail = ~(r);
                    failedread = true
                }
            }
        }
    };
    ipaddress : bits(40) = undefined : bits(40);
    s2fs1walk : bool = undefined : bool;
    secondstage : bool = undefined : bool;
    if fail then {
        secondstage = false;
        s2fs1walk = false;
        ipaddress = undefined : bits(40);
        return(AArch32_PermissionFault(ipaddress, domain, level, acctype, ~(failedread), secondstage, s2fs1walk))
    } else {
        return(AArch32_NoFault())
    }
}

val AArch32_BreakpointValueMatch : forall ('n : Int).
  (int('n), bits(32), bool) -> (bool, bool) effect {escape, rreg, undef}

function AArch32_BreakpointValueMatch (n__arg, vaddress, linked_to) = {
    n : int = n__arg;
    c : Constraint = undefined : Constraint;
    if n > UInt(slice(DBGDIDR, 24, 4)) then {
        (c, n) = ConstrainUnpredictableInteger(0, UInt(slice(DBGDIDR, 24, 4)), Unpredictable_BPNOTIMPL);
        assert(c == Constraint_DISABLED | c == Constraint_UNKNOWN);
        if c == Constraint_DISABLED then {
            return((false, false))
        }
    };
    if [DBGBCR[n][0]] == 0b0 then {
        return((false, false))
    };
    let context_aware : bool = n >= UInt(slice(DBGDIDR, 24, 4)) - UInt(slice(DBGDIDR, 20, 4));
    typ : bits(4) = undefined : bits(4);
    typ = slice(DBGBCR[n], 20, 4);
    if ((((typ & 0xE) == 0x6 | (typ & 0xC) == 0xC) & ~(HaveVirtHostExt()) | (typ & 0xE) == 0x4 & HaltOnBreakpointOrWatchpoint()) | (typ & 0xA) != 0x0 & ~(context_aware)) | (typ & 0x8) == 0x8 & ~(HaveEL(EL2)) then {
        (c, typ) = ConstrainUnpredictableBits(Unpredictable_RESBPTYPE);
        assert(c == Constraint_DISABLED | c == Constraint_UNKNOWN);
        if c == Constraint_DISABLED then {
            return((false, false))
        }
    };
    let match_addr : bool = (typ & 0xA) == 0x0;
    let mismatch : bool = (typ & 0xE) == 0x4;
    let match_vmid : bool = (typ & 0xC) == 0x8;
    let match_cid1 : bool = (typ & 0x2) == 0x2;
    let match_cid2 : bool = (typ & 0xC) == 0xC;
    let linked : bool = (typ & 0x1) == 0x1;
    if linked_to & (~(linked) | match_addr) then {
        return((false, false))
    };
    if (~(linked_to) & linked) & ~(match_addr) then {
        return((false, false))
    };
    BVR_match : bool = undefined : bool;
    byte : int = undefined : int;
    byte_select_match : bool = undefined : bool;
    if match_addr then {
        byte = UInt(slice(vaddress, 0, 2));
        assert(byte == 0 | byte == 2);
        byte_select_match = [slice(DBGBCR[n], 5, 4)[byte]] == 0b1;
        BVR_match = slice(vaddress, 2, 30) == slice(DBGBVR[n], 2, 30) & byte_select_match
    } else {
        if match_cid1 then {
            BVR_match = PSTATE.EL != EL2 & get_CONTEXTIDR() == slice(DBGBVR[n], 0, 32)
        }
    };
    BXVR_match : bool = undefined : bool;
    bvr_vmid : bits(16) = undefined : bits(16);
    vmid : bits(16) = undefined : bits(16);
    if match_vmid then {
        if ELUsingAArch32(EL2) then {
            vmid = ZeroExtend(slice(get_VTTBR(), 48, 8), 16);
            bvr_vmid = ZeroExtend(slice(DBGBXVR[n], 0, 8), 16)
        } else {
            if ~(Have16bitVMID()) | [VTCR_EL2[19]] == 0b0 then {
                vmid = ZeroExtend(slice(VTTBR_EL2[56 .. 49] @ VTTBR_EL2[48 .. 41], 0, 8), 16);
                bvr_vmid = ZeroExtend(slice(DBGBXVR[n], 0, 8), 16)
            } else {
                vmid = VTTBR_EL2[56 .. 49] @ VTTBR_EL2[48 .. 41];
                bvr_vmid = slice(DBGBXVR[n], 0, 16)
            }
        };
        BXVR_match = (EL2Enabled() & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & vmid == bvr_vmid
    } else {
        if match_cid2 then {
            BXVR_match = ((~(IsSecure()) & HaveVirtHostExt()) & ~(ELUsingAArch32(EL2))) & slice(DBGBXVR[n], 0, 32) == CONTEXTIDR_EL2
        }
    };
    let bvr_match_valid : bool = match_addr | match_cid1;
    let bxvr_match_valid : bool = match_vmid | match_cid2;
    let val_match : bool = (~(bxvr_match_valid) | BXVR_match) & (~(bvr_match_valid) | BVR_match);
    return((val_match & ~(mismatch), ~(val_match) & mismatch))
}

val AArch32_StateMatch : forall ('linked : Bool) ('isbreakpnt : Bool) ('ispriv : Bool).
  (bits(2), bits(1), bits(2), bool('linked), bits(4), bool('isbreakpnt), bool('ispriv)) -> bool effect {escape, rreg, undef}

function AArch32_StateMatch (SSC__arg, HMC__arg, PxC__arg, linked__arg, LBN, isbreakpnt, ispriv) = {
    HMC = HMC__arg;
    PxC = PxC__arg;
    SSC = SSC__arg;
    linked : bool = linked__arg;
    c : Constraint = undefined : Constraint;
    if ((((((((HMC @ SSC) @ PxC) & 0b11100) == 0b01100 | (((HMC @ SSC) @ PxC) & 0b11101) == 0b10000 | (((HMC @ SSC) @ PxC) & 0b11101) == 0b10100 | ((HMC @ SSC) @ PxC) == 0b11010 | ((HMC @ SSC) @ PxC) == 0b11101 | (((HMC @ SSC) @ PxC) & 0b11110) == 0b11110) | (HMC == 0b0 & PxC == 0b00) & ~(isbreakpnt)) | (SSC == 0b01 | SSC == 0b10) & ~(HaveEL(EL3))) | ((HMC @ SSC) @ PxC) == 0b11000 & ELUsingAArch32(EL3)) | (((HMC @ SSC) != 0b000 & (HMC @ SSC) != 0b111) & ~(HaveEL(EL3))) & ~(HaveEL(EL2))) | ((HMC @ SSC) @ PxC) == 0b11100 & ~(HaveEL(EL2)) then {
        __tc1 : bits(5) = undefined : bits(5);
        (c, __tc1) = ConstrainUnpredictableBits(Unpredictable_RESBPWPCTRL);
        let __tc2 : bits(5) = __tc1;
        HMC = [__tc2[4]];
        let __tc3 : bits(4) = slice(__tc2, 0, 4);
        SSC = slice(__tc3, 2, 2);
        PxC = slice(__tc3, 0, 2);
        assert(c == Constraint_DISABLED | c == Constraint_UNKNOWN);
        if c == Constraint_DISABLED then {
            return(false)
        }
    };
    let PL2_match : bool = HaveEL(EL2) & HMC == 0b1;
    let PL1_match : bool = [PxC[0]] == 0b1;
    let PL0_match : bool = [PxC[1]] == 0b1;
    let SSU_match : bool = ((isbreakpnt & HMC == 0b0) & PxC == 0b00) & SSC != 0b11;
    let el : bits(2) = PSTATE.EL;
    priv_match : bool = undefined : bool;
    if ~(ispriv) & ~(isbreakpnt) then {
        priv_match = PL0_match
    } else {
        if SSU_match then {
            priv_match = PSTATE.M == M32_User | PSTATE.M == M32_Svc | PSTATE.M == M32_System
        } else {
            match el {
              ? if ? == EL3 => {
                  priv_match = PL1_match
              },
              ? if ? == EL2 => {
                  priv_match = PL2_match
              },
              ? if ? == EL1 => {
                  priv_match = PL1_match
              },
              ? if ? == EL0 => {
                  priv_match = PL0_match
              }
            }
        }
    };
    security_state_match : bool = undefined : bool;
    match SSC {
      0b00 => {
          security_state_match = true
      },
      0b01 => {
          security_state_match = ~(IsSecure())
      },
      0b10 => {
          security_state_match = IsSecure()
      },
      0b11 => {
          security_state_match = true
      }
    };
    first_ctx_cmp : int = undefined : int;
    last_ctx_cmp : int = undefined : int;
    lbn : int = undefined : int;
    if linked then {
        lbn = UInt(LBN);
        first_ctx_cmp = UInt(slice(DBGDIDR, 24, 4)) - UInt(slice(DBGDIDR, 20, 4));
        last_ctx_cmp = UInt(slice(DBGDIDR, 24, 4));
        if lbn < first_ctx_cmp | lbn > last_ctx_cmp then {
            (c, lbn) = ConstrainUnpredictableInteger(first_ctx_cmp, last_ctx_cmp, Unpredictable_BPNOTCTXCMP);
            assert(c == Constraint_DISABLED | c == Constraint_NONE | c == Constraint_UNKNOWN);
            match c {
              Constraint_DISABLED => {
                  return(false)
              },
              Constraint_NONE => {
                  linked = false
              }
            }
        }
    };
    __anon1 : bool = undefined : bool;
    linked_match : bool = undefined : bool;
    linked_to : bool = undefined : bool;
    vaddress : bits(32) = undefined : bits(32);
    if linked then {
        vaddress = undefined : bits(32);
        linked_to = true;
        (linked_match, __anon1) = AArch32_BreakpointValueMatch(lbn, vaddress, linked_to)
    };
    (priv_match & security_state_match) & (~(linked) | linked_match)
}

val AArch32_WatchpointMatch : forall 'n 'size ('ispriv : Bool) ('iswrite : Bool).
  (int('n), bits(32), int('size), bool('ispriv), bool('iswrite)) -> bool effect {escape, rreg, undef}

function AArch32_WatchpointMatch (n, vaddress, size, ispriv, iswrite) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    assert(n <= UInt(slice(DBGDIDR, 28, 4)));
    let enabled = [DBGWCR[n][0]] == 0b1;
    let linked = [DBGWCR[n][20]] == 0b1;
    let isbreakpnt = false;
    let state_match : bool = AArch32_StateMatch(slice(DBGWCR[n], 14, 2), [DBGWCR[n][13]], slice(DBGWCR[n], 1, 2), linked, slice(DBGWCR[n], 16, 4), isbreakpnt, ispriv);
    let ls_match = [slice(DBGWCR[n], 3, 2)[if iswrite then 1 else 0]] == 0b1;
    value_match_name : bool = undefined : bool;
    value_match_name = false;
    foreach (byte from 0 to (size - 1) by 1 in inc) {
        value_match_name = value_match_name | AArch32_WatchpointByteMatch(n, vaddress + byte)
    };
    ((value_match_name & state_match) & ls_match) & enabled
}

val AArch32_CheckWatchpoint : forall ('size : Int).
  (bits(32), AccType, bool, int('size)) -> FaultRecord effect {escape, rreg, undef, wreg}

function AArch32_CheckWatchpoint (vaddress, acctype, iswrite, size) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    val_match : bool = undefined : bool;
    val_match = false;
    let ispriv : bool = AArch32_AccessIsPrivileged(acctype);
    foreach (i from 0 to UInt(slice(DBGDIDR, 28, 4)) by 1 in inc) {
        val_match = val_match | AArch32_WatchpointMatch(i, vaddress, size, ispriv, iswrite)
    };
    debugmoe : bits(4) = undefined : bits(4);
    reason : bits(6) = undefined : bits(6);
    if val_match & HaltOnBreakpointOrWatchpoint() then {
        reason = DebugHalt_Watchpoint;
        Halt(reason);
        AArch32_NoFault()
    } else {
        if (val_match & [get_DBGDSCRext()[15]] == 0b1) & AArch32_GenerateDebugExceptions() then {
            debugmoe = DebugException_Watchpoint;
            return(AArch32_DebugFault(acctype, iswrite, debugmoe))
        } else {
            return(AArch32_NoFault())
        }
    }
}

val AArch32_BreakpointMatch : forall ('n : Int) ('size : Int).
  (int('n), bits(32), int('size)) -> (bool, bool) effect {escape, rreg, undef}

function AArch32_BreakpointMatch (n, vaddress, size) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    assert(n <= UInt(slice(DBGDIDR, 24, 4)));
    let enabled = [DBGBCR[n][0]] == 0b1;
    let ispriv = PSTATE.EL != EL0;
    let linked = (slice(DBGBCR[n], 20, 4) & 0xB) == 0x1;
    let isbreakpnt = true;
    let linked_to = false;
    let state_match : bool = AArch32_StateMatch(slice(DBGBCR[n], 14, 2), [DBGBCR[n][13]], slice(DBGBCR[n], 1, 2), linked, slice(DBGBCR[n], 16, 4), isbreakpnt, ispriv);
    value_match_name : bool = undefined : bool;
    value_mismatch_name : bool = undefined : bool;
    (value_match_name, value_mismatch_name) = AArch32_BreakpointValueMatch(n, vaddress, linked_to);
    match_i : bool = undefined : bool;
    mismatch_i : bool = undefined : bool;
    if size == 4 then {
        (match_i, mismatch_i) = AArch32_BreakpointValueMatch(n, vaddress + 2, linked_to);
        if ~(value_match_name) & match_i then {
            value_match_name = ConstrainUnpredictableBool(Unpredictable_BPMATCHHALF)
        };
        if value_mismatch_name & ~(mismatch_i) then {
            value_mismatch_name = ConstrainUnpredictableBool(Unpredictable_BPMISMATCHHALF)
        }
    };
    if [vaddress[1]] == 0b1 & slice(DBGBCR[n], 5, 4) == 0xF then {
        if value_match_name then {
            value_match_name = ConstrainUnpredictableBool(Unpredictable_BPMATCHHALF)
        };
        if ~(value_mismatch_name) then {
            value_mismatch_name = ConstrainUnpredictableBool(Unpredictable_BPMISMATCHHALF)
        }
    };
    let val_match : bool = (value_match_name & state_match) & enabled;
    let mismatch : bool = (value_mismatch_name & state_match) & enabled;
    return((val_match, mismatch))
}

val AArch32_CheckBreakpoint : forall ('size : Int).
  (bits(32), int('size)) -> FaultRecord effect {escape, rreg, undef, wreg}

function AArch32_CheckBreakpoint (vaddress, size) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    assert(size == 2 | size == 4);
    val_match : bool = undefined : bool;
    val_match = false;
    mismatch : bool = undefined : bool;
    mismatch = false;
    match_i : bool = undefined : bool;
    mismatch_i : bool = undefined : bool;
    foreach (i from 0 to UInt(slice(DBGDIDR, 24, 4)) by 1 in inc) {
        (match_i, mismatch_i) = AArch32_BreakpointMatch(i, vaddress, size);
        val_match = val_match | match_i;
        mismatch = mismatch | mismatch_i
    };
    acctype : AccType = undefined : AccType;
    debugmoe : bits(4) = undefined : bits(4);
    iswrite : bool = undefined : bool;
    reason : bits(6) = undefined : bits(6);
    if val_match & HaltOnBreakpointOrWatchpoint() then {
        reason = DebugHalt_Breakpoint;
        Halt(reason);
        AArch32_NoFault()
    } else {
        if ((val_match | mismatch) & [get_DBGDSCRext()[15]] == 0b1) & AArch32_GenerateDebugExceptions() then {
            acctype = AccType_IFETCH;
            iswrite = false;
            debugmoe = DebugException_Breakpoint;
            return(AArch32_DebugFault(acctype, iswrite, debugmoe))
        } else {
            return(AArch32_NoFault())
        }
    }
}

val AArch32_CheckDebug : forall ('iswrite : Bool) ('size : Int).
  (bits(32), AccType, bool('iswrite), int('size)) -> FaultRecord effect {escape, rreg, undef, wreg}

function AArch32_CheckDebug (vaddress, acctype, iswrite, size) = {
    fault : FaultRecord = AArch32_NoFault();
    let d_side = acctype != AccType_IFETCH;
    let generate_exception = AArch32_GenerateDebugExceptions() & [get_DBGDSCRext()[15]] == 0b1;
    let halt = HaltOnBreakpointOrWatchpoint();
    let vector_catch_first_name = ConstrainUnpredictableBool(Unpredictable_BPVECTORCATCHPRI);
    if (~(d_side) & vector_catch_first_name) & generate_exception then {
        fault = AArch32_CheckVectorCatch(vaddress, size)
    };
    if fault.typ == Fault_None & (generate_exception | halt) then {
        if d_side then {
            fault = AArch32_CheckWatchpoint(vaddress, acctype, iswrite, size)
        } else {
            fault = AArch32_CheckBreakpoint(vaddress, size)
        }
    };
    if ((fault.typ == Fault_None & ~(d_side)) & ~(vector_catch_first_name)) & generate_exception then {
        return(AArch32_CheckVectorCatch(vaddress, size))
    };
    fault
}

val AArch32_Abort : (bits(32), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch32_Abort (vaddress, fault) = {
    route_to_aarch64 : bool = undefined : bool;
    route_to_aarch64 = PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1));
    if (~(route_to_aarch64) & EL2Enabled()) & ~(ELUsingAArch32(EL2)) then {
        route_to_aarch64 = (([HCR_EL2[27]] == 0b1 | IsSecondStage(fault)) | (HaveRASExt() & [get_HCR2()[5]] == 0b1) & IsExternalAbort(fault)) | IsDebugException(fault) & [MDCR_EL2[8]] == 0b1
    };
    if (~(route_to_aarch64) & HaveEL(EL3)) & ~(ELUsingAArch32(EL3)) then {
        route_to_aarch64 = [SCR_EL3[3]] == 0b1 & IsExternalAbort(fault)
    };
    if route_to_aarch64 then {
        AArch64_Abort(ZeroExtend(vaddress), fault)
    } else {
        if fault.acctype == AccType_IFETCH then {
            AArch32_InstructionAbort(vaddress, fault)
        } else {
            AArch32_DataAbort(vaddress, fault)
        }
    }
}

val _CheckAbortRegions : forall ('size : Int).
  (AddressDescriptor, int('size), AccessDescriptor, bits(1)) -> unit effect {escape, rreg, undef, wreg}

function _CheckAbortRegions (desc, size, accdesc, read) = {
    let address = desc.paddress.address;
    let extflag = desc.paddress.NS;
    let AbortRgnBase1 = AbortRgn64Lo1_Hi @ AbortRgn64Lo1;
    let AbortRgnTop1 = AbortRgn64Hi1_Hi @ AbortRgn64Hi1;
    let AbortRgnBase2 = AbortRgn64Lo2_Hi @ AbortRgn64Lo2;
    let AbortRgnTop2 = AbortRgn64Hi2_Hi @ AbortRgn64Hi2;
    let AbortLo1 : bool = UInt(address) >= UInt(slice(AbortRgnBase1, 0, 52));
    let AbortHi1 : bool = UInt(address) < UInt(slice(AbortRgnTop1, 0, 52));
    let AbortLo2 : bool = UInt(address) >= UInt(slice(AbortRgnBase2, 0, 52));
    let AbortHi2 : bool = UInt(address) < UInt(slice(AbortRgnTop2, 0, 52));
    fault : FaultRecord = undefined : FaultRecord;
    sync : bool = undefined : bool;
    if AbortLo1 & AbortHi1 | AbortLo2 & AbortHi2 then {
        let cacheable = desc.memattrs.inner.attrs != MemAttr_NC;
        let normal_access = desc.memattrs.typ == MemType_Normal;
        let device = desc.memattrs.typ == MemType_Device;
        let strongly_ordered = desc.memattrs.device == DeviceType_nGnRnE;
        if accdesc.page_table_walk then {
            sync = cacheable & __syncAbortOnTTWCache | ~(cacheable) & __syncAbortOnTTWNonCache
        } else {
            if accdesc.acctype == AccType_IFETCH then {
                sync = __syncAbortOnPrefetch
            } else {
                if read == 0b1 then {
                    sync = (((normal_access & cacheable) & __syncAbortOnReadNormCache | (normal_access & ~(cacheable)) & __syncAbortOnReadNormNonCache) | device & __syncAbortOnDeviceRead) | strongly_ordered & __syncAbortOnSoRead
                } else {
                    sync = ((device & __syncAbortOnDeviceWrite | (normal_access & cacheable) & __syncAbortOnWriteNormCache) | (normal_access & ~(cacheable)) & __syncAbortOnWriteNormNonCache) | strongly_ordered & __syncAbortOnSoWrite
                }
            }
        };
        if sync then {
            fault = _SyncExternalFault(address, accdesc, read, extflag);
            if UsingAArch32() then {
                AArch32_Abort(slice(desc.vaddress, 0, 32), fault)
            } else {
                AArch64_Abort(desc.vaddress, fault)
            }
        } else {
            SetPendingPhysicalSE(true)
        }
    };
    return()
}

val aset__Mem : forall ('size : Int), 'size >= 0.
  (AddressDescriptor, option(TranslationInfo), int('size), AccessDescriptor, bits(8 * 'size)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aset__Mem (desc, translation_info, size, accdesc, value_name) = {
    let read : bits(1) = 0b0;
    paddress : bits(52) = desc.paddress.address;
    let extflag : bits(1) = desc.paddress.NS;
    if __trickbox_enabled then {
        _CheckAbortRegions(desc, size, accdesc, read)
    };
    fault : FaultRecord = undefined : FaultRecord;
    if __trickbox_enabled & IsGTEPPUMatch(desc.paddress, read) then {
        fault = _SyncExternalFault(paddress, accdesc, read, extflag);
        AArch64_Abort(desc.vaddress, fault)
    };
    lsb : int = undefined : int;
    readValue : unit = undefined : unit;
    regs : int = undefined : int;
    if __trickbox_enabled & (paddress & __trickbox_mask_v8) == __trickbox_base_v8 then {
        if slice(paddress, 0, 16) != Zeros(16) then {
            prerr("Trickbox write " ++ HexStr(UInt(paddress)) ++ " = " ++ HexStr(UInt(value_name)) ++ " (" ++ DecStr(size) ++ ")\n")
        };
        if size == 8 | size == 16 then {
            regs = size / 4;
            foreach (i from 1 to regs by 1 in inc) {
                lsb = (i - 1) * 32;
                let writeValue : bits(32) = slice(value_name, lsb, 32);
                prerr("Multiple trickbox write part:" ++ DecStr(i) ++ " " ++ HexStr(UInt(paddress)) ++ " = " ++ HexStr(UInt(writeValue)) ++ "\n");
                _WriteTrickbox(UInt(slice(paddress, 0, 16)), true, true, true, true, writeValue);
                paddress = paddress + 4
            }
        } else {
            let width = size * 8;
            let writeval : bits(32) = ZeroExtend(slice(value_name, 0, width));
            _WriteTrickbox(UInt(slice(paddress, 0, 16)), true, true, true, true, slice(writeval, 0, 32))
        }
    } else {
        if UInt(__CNTControlBase) != 0 & (paddress & __CNTControlMask) == __CNTControlBase then {
            readValue = __WriteMemoryMappedCounterRegister(UInt(slice(paddress, 0, 12)), ZeroExtend(slice(value_name, 0, 32)))
        } else {
            if __trickbox_enabled then {
                GTECheckAccessSensitiveAccess(paddress, size, value_name, false)
            };
            if size == 16 then {
                __WriteMemory(accdesc.acctype, translation_info, 8, desc.vaddress, ZeroExtend(paddress), slice(value_name, 0, 64));
                __WriteMemory(accdesc.acctype, translation_info, 8, desc.vaddress, ZeroExtend(paddress + 8), slice(value_name, 64, 64))
            } else {
                __WriteMemory(accdesc.acctype, translation_info, size, desc.vaddress, ZeroExtend(paddress), value_name)
            }
        }
    };
    return()
}

overload _Mem = {aset__Mem}

val aget__Mem : forall 'size, 'size > 0.
  (AddressDescriptor, option(TranslationInfo), int('size), AccessDescriptor) -> bits(8 * 'size) effect {escape, rmem, rreg, undef, wreg}

function aget__Mem (desc, translation_info, size, accdesc) = {
    let read = 0b1;
    paddress : bits(52) = desc.paddress.address;
    let extflag = desc.paddress.NS;
    if __trickbox_enabled then {
        _CheckAbortRegions(desc, size, accdesc, read)
    };
    fault : FaultRecord = undefined : FaultRecord;
    if __trickbox_enabled & IsGTEPPUMatch(desc.paddress, read) then {
        fault = _SyncExternalFault(paddress, accdesc, read, extflag);
        AArch64_Abort(desc.vaddress, fault)
    };
    lsb : int = undefined : int;
    readValue : bits(32) = undefined : bits(32);
    regs : int = undefined : int;
    if __trickbox_enabled & (paddress & __trickbox_mask_v8) == __trickbox_base_v8 then {
        if size == 8 | size == 16 then {
            regs = size / 4;
            result : bits(8 * 'size) = undefined : bits(8 * 'size);
            foreach (i from 1 to regs by 1 in inc) {
                lsb = (i - 1) * 32;
                readValue = _ReadTrickbox(UInt(slice(paddress, 0, 16)), true, true, true, true);
                prerr("Multiple trickbox read part:" ++ DecStr(i) ++ " " ++ HexStr(UInt(paddress)) ++ " = " ++ HexStr(UInt(readValue)) ++ "\n");
                result = __SetSlice_bits(8 * size, 32, result, lsb, slice(readValue, 0, 32));
                paddress = paddress + 4
            };
            prerr("Multiple trickbox read result: " ++ " = " ++ HexStr(UInt(result)) ++ "\n");
            return(result)
        } else {
            prerr("Trickbox read " ++ HexStr(UInt(paddress)) ++ " = " ++ HexStr(UInt(readValue)) ++ "\n");
            readValue = _ReadTrickbox(UInt(slice(paddress, 0, 16)), true, true, true, true);
            return(slice(readValue, 0, 8 * size))
        }
    } else {
        if UInt(__CNTControlBase) != 0 & (paddress & __CNTControlMask) == __CNTControlBase then {
            readValue = __ReadMemoryMappedCounterRegister(UInt(slice(paddress, 0, 12)));
            return(slice(readValue, 0, 8 * size))
        } else {
            result : bits(8 * 'size) = undefined : bits(8 * 'size);
            if size == 16 then {
                result = __SetSlice_bits(8 * size, 64, result, 0, __ReadMemory(accdesc.acctype, translation_info, 8, desc.vaddress, ZeroExtend(paddress)));
                result = __SetSlice_bits(8 * size, 64, result, 64, __ReadMemory(accdesc.acctype, translation_info, 8, desc.vaddress, ZeroExtend(paddress + 8)))
            } else {
                result = __ReadMemory(accdesc.acctype, translation_info, size, desc.vaddress, ZeroExtend(paddress))
            };
            if __trickbox_enabled then {
                GTECheckAccessSensitiveAccess(paddress, size, result, true)
            };
            return(result)
        }
    }
}

overload _Mem = {aget__Mem}

val AArch64_aget_MemSingle : forall 'size ('wasaligned : Bool),
  'size in {1, 2, 4, 8, 16}.
  (bits(64), int('size), AccType, bool('wasaligned)) -> bits(8 * 'size) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_aget_MemSingle (address, size, acctype, wasaligned) = {
    assert(size == 1 | size == 2 | size == 4 | size == 8 | size == 16);
    assert(address == Align(address, size));
    memaddrdesc : AddressDescriptor = undefined : AddressDescriptor;
    value_name : bits(8 * 'size) = undefined : bits('size * 8);
    let iswrite = false;
    let (memaddrdesc, translation_info) = AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, size);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(address, memaddrdesc.fault)
    };
    let accdesc = CreateAccessDescriptor(acctype);
    if HaveMTEExt() then {
        if AccessIsTagChecked(ZeroExtend(address, 64), acctype) then {
            let ptag = TransformTag(ZeroExtend(address, 64));
            if ~(CheckTag(memaddrdesc, ptag, iswrite)) then {
                TagCheckFail(ZeroExtend(address, 64), iswrite)
            }
        }
    };
    let value_name = _Mem(memaddrdesc, translation_info, size, accdesc);
    value_name
}

overload MemSingle = {AArch64_aget_MemSingle}

val __fetchA64 : unit -> bits(32) effect {escape, rmem, rreg, undef, wmem, wreg}

function __fetchA64 () = {
    CheckSoftwareStep();
    AArch64_CheckPCAlignment();
    let a64 = MemSingle(PC(), 4, AccType_IFETCH, true);
    AArch64_CheckIllegalState();
    a64
}

function IsZero_slice (xs, i, 'l) = {
    assert(constraint('l >= 0));
    IsZero(slice(xs, i, l))
}

function IsOnes_slice (xs, i, 'l) = {
    assert(constraint('l >= 0));
    IsOnes(slice(xs, i, l))
}

function ZeroExtend_slice_append (o, xs, i, 'l, ys) = {
    assert(l >= 0 & 'm >= 0 & length(ys) + l <= o);
    ZeroExtend(slice(xs, i, l) @ ys)
}

function AArch64_TranslationTableWalk (ipaddress, s1_nonsecure, vaddress, acctype, iswrite, secondstage, s2fs1walk, size) = {
    if ~(secondstage) then {
        assert(~(ELUsingAArch32(S1TranslationRegime())))
    } else {
        assert((IsSecureEL2Enabled() | (HaveEL(EL2) & ~(IsSecure())) & ~(ELUsingAArch32(EL2))) & HasS2Translation())
    };
    result : TLBRecord = undefined : TLBRecord;
    result.descupdate.AF = false;
    result.descupdate.AP = false;
    descaddr : AddressDescriptor = undefined : AddressDescriptor;
    descaddr.fault = AArch64_NoFault();
    baseregister : bits(64) = undefined : bits(64);
    inputaddr : bits(64) = undefined : bits(64);
    if __tlb_enabled then {
        if ~(secondstage) then {
            inputaddr = ZeroExtend(vaddress)
        } else {
            inputaddr = ZeroExtend(ipaddress)
        };
        let cacheline : TLBLine = TLBLookup(ZeroExtend(inputaddr, 64), secondstage, s1_nonsecure, acctype);
        if cacheline.valid_name then {
            return (cacheline.data, None())
        }
    };
    __tc1 : MemoryAttributes = descaddr.memattrs;
    __tc1.typ = MemType_Normal;
    descaddr.memattrs = __tc1;
    basefound : bool = undefined : bool;
    c : Constraint = undefined : Constraint;
    disabled : bool = undefined : bool;
    el : bits(2) = undefined : bits(2);
    firstblocklevel : int = undefined : int;
    grainsize : int = undefined : int;
    hierattrsdisabled : bool = undefined : bool;
    inputsize : int = undefined : int;
    inputsize_max : int = undefined : int;
    inputsize_min : int = undefined : int;
    inputsizecheck : int = undefined : int;
    largegrain : bool = undefined : bool;
    level : int = undefined : int;
    lookupsecure : bool = undefined : bool;
    midgrain : bool = undefined : bool;
    nsaccess : bits(1) = undefined : bits(1);
    nswalk : bits(1) = undefined : bits(1);
    ps : bits(3) = undefined : bits(3);
    reversedescriptors : bool = undefined : bool;
    singlepriv : bool = undefined : bool;
    startlevel : int = undefined : int;
    startsizecheck : int = undefined : int;
    stride : int = undefined : int;
    t0size : bits(6) = undefined : bits(6);
    tg0 : bits(2) = undefined : bits(2);
    top : int = undefined : int;
    update_AF : bool = undefined : bool;
    update_AP : bool = undefined : bool;
    if ~(secondstage) then {
        inputaddr = ZeroExtend(vaddress);
        el = AArch64_AccessUsesEL(acctype);
        top = AddrTop(inputaddr, acctype == AccType_IFETCH, el);
        if el == EL3 then {
            largegrain = slice(TCR_EL3, 14, 2) == 0b01;
            midgrain = slice(TCR_EL3, 14, 2) == 0b10;
            inputsize = 64 - UInt(slice(TCR_EL3, 0, 6));
            inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
            inputsize_min = 64 - (if ~(HaveSmallPageTblExt()) then 39 else if largegrain then 47 else 48);
            if inputsize < inputsize_min then {
                c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
                assert(c == Constraint_FORCE | c == Constraint_FAULT);
                if c == Constraint_FORCE then {
                    inputsize = inputsize_min
                }
            };
            ps = slice(TCR_EL3, 16, 3);
            basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
            disabled = false;
            baseregister = TTBR0_EL3;
            descaddr.memattrs = WalkAttrDecode(slice(TCR_EL3, 12, 2), slice(TCR_EL3, 10, 2), slice(TCR_EL3, 8, 2), secondstage);
            reversedescriptors = [SCTLR_EL3[25]] == 0b1;
            lookupsecure = true;
            singlepriv = true;
            update_AF = HaveAccessFlagUpdateExt() & [TCR_EL3[21]] == 0b1;
            update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL3[22]] == 0b1;
            hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL3[24]] == 0b1
        } else {
            if ELIsInHost(el) then {
                if [inputaddr[top]] == 0b0 then {
                    largegrain = slice(TCR_EL2, 14, 2) == 0b01;
                    midgrain = slice(TCR_EL2, 14, 2) == 0b10;
                    inputsize = 64 - UInt(slice(TCR_EL2, 0, 6));
                    inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
                    inputsize_min = 64 - (if ~(HaveSmallPageTblExt()) then 39 else if largegrain then 47 else 48);
                    if inputsize < inputsize_min then {
                        c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
                        assert(c == Constraint_FORCE | c == Constraint_FAULT);
                        if c == Constraint_FORCE then {
                            inputsize = inputsize_min
                        }
                    };
                    basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
                    disabled = [TCR_EL2[7]] == 0b1 | (PSTATE.EL == EL0 & HaveE0PDExt()) & [TCR_EL2[55]] == 0b1;
                    baseregister = TTBR0_EL2;
                    descaddr.memattrs = WalkAttrDecode(slice(TCR_EL2, 12, 2), slice(TCR_EL2, 10, 2), slice(TCR_EL2, 8, 2), secondstage);
                    hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL2[41]] == 0b1
                } else {
                    inputsize = 64 - UInt(slice(TCR_EL2, 16, 6));
                    largegrain = slice(TCR_EL2, 30, 2) == 0b11;
                    midgrain = slice(TCR_EL2, 30, 2) == 0b01;
                    inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
                    inputsize_min = 64 - (if ~(HaveSmallPageTblExt()) then 39 else if largegrain then 47 else 48);
                    if inputsize < inputsize_min then {
                        c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
                        assert(c == Constraint_FORCE | c == Constraint_FAULT);
                        if c == Constraint_FORCE then {
                            inputsize = inputsize_min
                        }
                    };
                    basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsOnes_slice(inputaddr, inputsize, top - inputsize + 1);
                    disabled = [TCR_EL2[23]] == 0b1 | (PSTATE.EL == EL0 & HaveE0PDExt()) & [TCR_EL2[56]] == 0b1;
                    baseregister = TTBR1_EL2;
                    descaddr.memattrs = WalkAttrDecode(slice(TCR_EL2, 28, 2), slice(TCR_EL2, 26, 2), slice(TCR_EL2, 24, 2), secondstage);
                    hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL2[42]] == 0b1
                };
                ps = slice(TCR_EL2, 32, 3);
                reversedescriptors = [SCTLR_EL2[25]] == 0b1;
                lookupsecure = if IsSecureEL2Enabled() then IsSecure() else false;
                singlepriv = false;
                update_AF = HaveAccessFlagUpdateExt() & [TCR_EL2[if [HCR_EL2[34]] == 0 then 21 else 39]] == 0b1;
                update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL2[if [HCR_EL2[34]] == 0 then 22 else 40]] == 0b1
            } else {
                if el == EL2 then {
                    inputsize = 64 - UInt(slice(TCR_EL2, 0, 6));
                    largegrain = slice(TCR_EL2, 14, 2) == 0b01;
                    midgrain = slice(TCR_EL2, 14, 2) == 0b10;
                    inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
                    inputsize_min = 64 - (if ~(HaveSmallPageTblExt()) then 39 else if largegrain then 47 else 48);
                    if inputsize < inputsize_min then {
                        c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
                        assert(c == Constraint_FORCE | c == Constraint_FAULT);
                        if c == Constraint_FORCE then {
                            inputsize = inputsize_min
                        }
                    };
                    ps = slice(TCR_EL2, 16, 3);
                    basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
                    disabled = false;
                    baseregister = TTBR0_EL2;
                    descaddr.memattrs = WalkAttrDecode(slice(TCR_EL2, 12, 2), slice(TCR_EL2, 10, 2), slice(TCR_EL2, 8, 2), secondstage);
                    reversedescriptors = [SCTLR_EL2[25]] == 0b1;
                    lookupsecure = if IsSecureEL2Enabled() then IsSecure() else false;
                    singlepriv = true;
                    update_AF = HaveAccessFlagUpdateExt() & [TCR_EL2[if [HCR_EL2[34]] == 0 then 21 else 39]] == 0b1;
                    update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL2[if [HCR_EL2[34]] == 0 then 22 else 40]] == 0b1;
                    hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL2[24]] == 0b1
                } else {
                    if [inputaddr[top]] == 0b0 then {
                        inputsize = 64 - UInt(slice(TCR_EL1, 0, 6));
                        largegrain = slice(TCR_EL1, 14, 2) == 0b01;
                        midgrain = slice(TCR_EL1, 14, 2) == 0b10;
                        inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
                        inputsize_min = 64 - (if ~(HaveSmallPageTblExt()) then 39 else if largegrain then 47 else 48);
                        if inputsize < inputsize_min then {
                            c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
                            assert(c == Constraint_FORCE | c == Constraint_FAULT);
                            if c == Constraint_FORCE then {
                                inputsize = inputsize_min
                            }
                        };
                        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
                        disabled = [TCR_EL1[7]] == 0b1 | (PSTATE.EL == EL0 & HaveE0PDExt()) & [TCR_EL1[55]] == 0b1;
                        baseregister = TTBR0_EL1;
                        descaddr.memattrs = WalkAttrDecode(slice(TCR_EL1, 12, 2), slice(TCR_EL1, 10, 2), slice(TCR_EL1, 8, 2), secondstage);
                        hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL1[41]] == 0b1
                    } else {
                        inputsize = 64 - UInt(slice(TCR_EL1, 16, 6));
                        largegrain = slice(TCR_EL1, 30, 2) == 0b11;
                        midgrain = slice(TCR_EL1, 30, 2) == 0b01;
                        inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
                        inputsize_min = 64 - (if ~(HaveSmallPageTblExt()) then 39 else if largegrain then 47 else 48);
                        if inputsize < inputsize_min then {
                            c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
                            assert(c == Constraint_FORCE | c == Constraint_FAULT);
                            if c == Constraint_FORCE then {
                                inputsize = inputsize_min
                            }
                        };
                        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsOnes_slice(inputaddr, inputsize, top - inputsize + 1);
                        disabled = [TCR_EL1[23]] == 0b1 | (PSTATE.EL == EL0 & HaveE0PDExt()) & [TCR_EL1[56]] == 0b1;
                        baseregister = TTBR1_EL1;
                        descaddr.memattrs = WalkAttrDecode(slice(TCR_EL1, 28, 2), slice(TCR_EL1, 26, 2), slice(TCR_EL1, 24, 2), secondstage);
                        hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL1[42]] == 0b1
                    };
                    ps = slice(TCR_EL1, 32, 3);
                    reversedescriptors = [SCTLR_EL1[25]] == 0b1;
                    lookupsecure = IsSecure();
                    singlepriv = false;
                    update_AF = HaveAccessFlagUpdateExt() & [TCR_EL1[39]] == 0b1;
                    update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL1[40]] == 0b1
                }
            }
        };
        if largegrain then {
            grainsize = 16;
            firstblocklevel = if Have52BitPAExt() then 1 else 2
        } else {
            if midgrain then {
                grainsize = 14;
                firstblocklevel = 2
            } else {
                grainsize = 12;
                firstblocklevel = 1
            }
        };
        stride = grainsize - 3;
        level = 4 - cdiv_int(inputsize - grainsize, stride)
    } else {
        inputaddr = ZeroExtend(ipaddress);
        if IsSecureEL2Enabled() & IsSecure() then {
            t0size = if s1_nonsecure == 0b1 then slice(VTCR_EL2, 0, 6) else slice(VSTCR_EL2, 0, 6);
            tg0 = if s1_nonsecure == 0b1 then slice(VTCR_EL2, 14, 2) else slice(VSTCR_EL2, 14, 2);
            nswalk = if s1_nonsecure == 0b1 then [VTCR_EL2[29]] else [VSTCR_EL2[29]];
            if nswalk == 0b1 then {
                nsaccess = 0b1
            } else {
                if s1_nonsecure == 0b0 then {
                    nsaccess = [VSTCR_EL2[30]]
                } else {
                    if [VSTCR_EL2[29]] == 0b1 | [VSTCR_EL2[30]] == 0b1 then {
                        nsaccess = 0b1
                    } else {
                        nsaccess = [VTCR_EL2[30]]
                    }
                }
            }
        } else {
            t0size = slice(VTCR_EL2, 0, 6);
            tg0 = slice(VTCR_EL2, 14, 2);
            nsaccess = 0b1
        };
        inputsize = 64 - UInt(t0size);
        largegrain = tg0 == 0b01;
        midgrain = tg0 == 0b10;
        inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
        inputsize_min = 64 - (if ~(HaveSmallPageTblExt()) then 39 else if largegrain then 47 else 48);
        if inputsize < inputsize_min then {
            c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
            assert(c == Constraint_FORCE | c == Constraint_FAULT);
            if c == Constraint_FORCE then {
                inputsize = inputsize_min
            }
        };
        ps = slice(VTCR_EL2, 16, 3);
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, negate(inputsize) + 64);
        disabled = false;
        descaddr.memattrs = WalkAttrDecode(slice(VTCR_EL2, 8, 2), slice(VTCR_EL2, 10, 2), slice(VTCR_EL2, 12, 2), secondstage);
        reversedescriptors = [SCTLR_EL2[25]] == 0b1;
        singlepriv = true;
        update_AF = HaveAccessFlagUpdateExt() & [VTCR_EL2[21]] == 0b1;
        update_AP = (HaveDirtyBitModifierExt() & update_AF) & [VTCR_EL2[22]] == 0b1;
        lookupsecure = if IsSecureEL2Enabled() then s1_nonsecure == 0b0 else false;
        baseregister = if lookupsecure then VSTTBR_EL2 else VTTBR_EL2;
        startlevel = if lookupsecure then UInt(slice(VSTCR_EL2, 6, 2)) else UInt(slice(VTCR_EL2, 6, 2));
        if largegrain then {
            grainsize = 16;
            level = 3 - startlevel;
            firstblocklevel = if Have52BitPAExt() then 1 else 2
        } else {
            if midgrain then {
                grainsize = 14;
                level = 3 - startlevel;
                firstblocklevel = 2
            } else {
                grainsize = 12;
                if HaveSmallPageTblExt() & startlevel == 3 then {
                    level = startlevel
                } else {
                    level = 2 - startlevel
                };
                firstblocklevel = 1
            }
        };
        stride = grainsize - 3;
        if largegrain then {
            if level == 0 | level == 1 & PAMax() <= 42 then {
                basefound = false
            }
        } else {
            if midgrain then {
                if level == 0 | level == 1 & PAMax() <= 40 then {
                    basefound = false
                }
            } else {
                if level < 0 | level == 0 & PAMax() <= 42 then {
                    basefound = false
                }
            }
        };
        inputsizecheck = inputsize;
        if inputsize > PAMax() & (~(ELUsingAArch32(EL1)) | inputsize > 40) then {
            match ConstrainUnpredictable(Unpredictable_LARGEIPA) {
              Constraint_FORCE => {
                  inputsize = PAMax();
                  inputsizecheck = PAMax()
              },
              Constraint_FORCENOSLCHECK => {
                  inputsize = PAMax()
              },
              Constraint_FAULT => {
                  basefound = false
              },
              _ => {
                  Unreachable()
              }
            }
        };
        startsizecheck = inputsizecheck - ((3 - level) * stride + grainsize);
        if startsizecheck < 1 | startsizecheck > stride + 4 then {
            basefound = false
        }
    };
    if ~(basefound) | disabled then {
        level = 0;
        __tc2 : AddressDescriptor = result.addrdesc;
        __tc2.fault = AArch64_TranslationFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc2;
        return (result, None())
    };
    outputsize : int = undefined : int;
    match ps {
      0b000 => {
          outputsize = 32
      },
      0b001 => {
          outputsize = 36
      },
      0b010 => {
          outputsize = 40
      },
      0b011 => {
          outputsize = 42
      },
      0b100 => {
          outputsize = 44
      },
      0b101 => {
          outputsize = 48
      },
      0b110 => {
          outputsize = if Have52BitPAExt() & largegrain then 52 else 48
      },
      _ => {
          outputsize = __IMPDEF_integer("Reserved Intermediate Physical Address size value")
      }
    };
    if outputsize > PAMax() then {
        outputsize = PAMax()
    };
    if outputsize < 48 & ~(IsZero_slice(baseregister, outputsize, negate(outputsize) + 48)) then {
        level = 0;
        __tc3 : AddressDescriptor = result.addrdesc;
        __tc3.fault = AArch64_AddressSizeFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc3;
        return (result, None())
    };
    let baselowerbound : int = 3 + inputsize - ((3 - level) * stride + grainsize);
    baseaddress : bits(52) = undefined : bits(52);
    if outputsize == 52 then {
        let 'z : int = if baselowerbound < 6 then 6 else baselowerbound;
        assert(constraint(- 'z + 48 >= 0));
        baseaddress = (slice(baseregister, 2, 4) @ slice(baseregister, z, negate(z) + 48)) @ Zeros(z)
    } else {
        baseaddress = ZeroExtend_slice_append(baseregister, baselowerbound, negate(baselowerbound) + 48, Zeros(baselowerbound))
    };
    ns_table : bits(1) = undefined : bits(1);
    ns_table = if lookupsecure then 0b0 else 0b1;
    ap_table : bits(2) = undefined : bits(2);
    ap_table = 0b00;
    xn_table : bits(1) = undefined : bits(1);
    xn_table = 0b0;
    pxn_table : bits(1) = undefined : bits(1);
    pxn_table = 0b0;
    addrselecttop : int = undefined : int;
    addrselecttop = inputsize - 1;
    let apply_nvnv1_effect : bool = (((HaveNVExt() & EL2Enabled()) & (HCR_EL2[42 .. 42] @ HCR_EL2[43 .. 43]) == 0b11) & S1TranslationRegime() == EL1) & ~(secondstage);
    accdesc : AccessDescriptor = undefined : AccessDescriptor;
    addrselectbottom : int = undefined : int;
    blocktranslate : bool = undefined : bool;
    desc : bits(64) = undefined : bits(64);
    descaddr2 : AddressDescriptor = undefined : AddressDescriptor;
    descaddr2.fault = AArch64_NoFault();
    hwupdatewalk : bool = undefined : bool;
    repeat {
        addrselectbottom = (3 - level) * stride + grainsize;
        let index : bits(52) = ZeroExtend_slice_append(inputaddr, addrselectbottom, addrselecttop - addrselectbottom + 1, 0b000);
        __tc4 : FullAddress = descaddr.paddress;
        __tc4.address = baseaddress | index;
        descaddr.paddress = __tc4;
        __tc5 : FullAddress = descaddr.paddress;
        __tc5.NS = ns_table;
        descaddr.paddress = __tc5;
        if (secondstage | ~(HasS2Translation())) | HaveNV2Ext() & acctype == AccType_NV2REGISTER then {
            descaddr2 = descaddr
        } else {
            hwupdatewalk = false;
            let (s2_result, translation_info) = AArch64_SecondStageWalk(descaddr, vaddress, acctype, iswrite, 8, hwupdatewalk);
            descaddr2 = s2_result;
            if IsFault(descaddr2) then {
                __tc6 : AddressDescriptor = result.addrdesc;
                __tc6.fault = descaddr2.fault;
                result.addrdesc = __tc6;
                return (result, translation_info)
            }
        };
        descaddr2.vaddress = ZeroExtend(vaddress);
        accdesc = CreateAccessDescriptorPTW(acctype, secondstage, s2fs1walk, level);
        desc = aget__Mem(descaddr2, None(), 8, accdesc);
        if reversedescriptors then {
            desc = BigEndianReverse(desc)
        };
        if [desc[0]] == 0b0 | slice(desc, 0, 2) == 0b01 & (level == 3 | (HaveBlockBBM() & IsBlockDescriptorNTBitValid()) & [desc[16]] == 0b1) then {
            __tc7 : AddressDescriptor = result.addrdesc;
            __tc7.fault = AArch64_TranslationFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
            result.addrdesc = __tc7;
            return (result, None())
        };
        if slice(desc, 0, 2) == 0b01 | level == 3 then {
            blocktranslate = true
        } else {
            if (outputsize < 52 & largegrain) & ~(IsZero_slice(desc, 12, 4)) | outputsize < 48 & ~(IsZero_slice(desc, outputsize, negate(outputsize) + 48)) then {
                __tc8 : AddressDescriptor = result.addrdesc;
                __tc8.fault = AArch64_AddressSizeFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
                result.addrdesc = __tc8;
                return (result, None())
            };
            if outputsize == 52 then {
                let 'g = grainsize;
                assert(constraint(- 'g + 48 >= 0));
                baseaddress = (slice(desc, 12, 4) @ slice(desc, g, negate(g) + 48)) @ Zeros(g)
            } else {
                baseaddress = ZeroExtend_slice_append(desc, grainsize, negate(grainsize) + 48, Zeros(grainsize))
            };
            if ~(secondstage) then {
                ns_table = ns_table | [desc[63]]
            };
            if ~(secondstage) & ~(hierattrsdisabled) then {
                ap_table = __SetSlice_bits(2, 1, ap_table, 1, [ap_table[1]] | [desc[62]]);
                if apply_nvnv1_effect then {
                    pxn_table = pxn_table | [desc[60]]
                } else {
                    xn_table = xn_table | [desc[60]]
                };
                if ~(singlepriv) then {
                    if ~(apply_nvnv1_effect) then {
                        pxn_table = pxn_table | [desc[59]];
                        ap_table = __SetSlice_bits(2, 1, ap_table, 0, [ap_table[0]] | [desc[61]])
                    }
                }
            };
            level = level + 1;
            addrselecttop = addrselectbottom - 1;
            blocktranslate = false
        }
    } until blocktranslate;
    if level < firstblocklevel then {
        __tc9 : AddressDescriptor = result.addrdesc;
        __tc9.fault = AArch64_TranslationFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc9;
        return (result, None())
    };
    contiguousbitcheck : bool = undefined : bool;
    if largegrain then {
        contiguousbitcheck = level == 2 & inputsize < 34
    } else {
        if midgrain then {
            contiguousbitcheck = level == 2 & inputsize < 30
        } else {
            contiguousbitcheck = level == 1 & inputsize < 34
        }
    };
    if contiguousbitcheck & [desc[52]] == 0b1 then {
        if __IMPDEF_boolean("Translation fault on misprogrammed contiguous bit") then {
            __tc10 : AddressDescriptor = result.addrdesc;
            __tc10.fault = AArch64_TranslationFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
            result.addrdesc = __tc10;
            return (result, None())
        }
    };
    if (outputsize < 52 & largegrain) & ~(IsZero_slice(desc, 12, 4)) | outputsize < 48 & ~(IsZero_slice(desc, outputsize, negate(outputsize) + 48)) then {
        __tc11 : AddressDescriptor = result.addrdesc;
        __tc11.fault = AArch64_AddressSizeFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc11;
        return (result, None())
    };
    outputaddress : bits(52) = undefined : bits(52);
    if outputsize == 52 then {
        let 'asb = addrselectbottom;
        assert(constraint((- 'asb + 48 >= 0 & 'asb >= 0)));
        outputaddress = (slice(desc, 12, 4) @ slice(desc, asb, negate(asb) + 48)) @ slice(inputaddr, 0, asb)
    } else {
        let 'asb = addrselectbottom;
        assert(constraint((- 'asb + 48 >= 0 & 'asb >= 0)));
        outputaddress = ZeroExtend_slice_append(desc, asb, negate(asb) + 48, slice(inputaddr, 0, asb))
    };
    if [desc[10]] == 0b0 then {
        if ~(update_AF) then {
            __tc12 : AddressDescriptor = result.addrdesc;
            __tc12.fault = AArch64_AccessFlagFault(ipaddress, s1_nonsecure, level, acctype, iswrite, secondstage, s2fs1walk);
            result.addrdesc = __tc12;
            return (result, None())
        } else {
            __tc13 : DescriptorUpdate = result.descupdate;
            __tc13.AF = true;
            result.descupdate = __tc13
        }
    };
    if update_AP & [desc[51]] == 0b1 then {
        if ~(secondstage) & [desc[7]] == 0b1 then {
            desc = __SetSlice_bits(64, 1, desc, 7, 0b0);
            __tc14 : DescriptorUpdate = result.descupdate;
            __tc14.AP = true;
            result.descupdate = __tc14
        } else {
            if secondstage & [desc[7]] == 0b0 then {
                desc = __SetSlice_bits(64, 1, desc, 7, 0b1);
                __tc15 : DescriptorUpdate = result.descupdate;
                __tc15.AP = true;
                result.descupdate = __tc15
            }
        }
    };
    __tc16 : DescriptorUpdate = result.descupdate;
    __tc16.descaddr = descaddr;
    result.descupdate = __tc16;
    ap : bits(3) = undefined : bits(3);
    pxn : bits(1) = undefined : bits(1);
    xn : bits(1) = undefined : bits(1);
    if apply_nvnv1_effect then {
        pxn = [desc[54]];
        xn = 0b0;
        ap = [desc[7]] @ 0b01
    } else {
        xn = [desc[54]];
        pxn = [desc[53]];
        ap = slice(desc, 6, 2) @ 0b1
    };
    let contiguousbit : bits(1) = [desc[52]];
    let nG : bits(1) = [desc[11]];
    let sh : bits(2) = slice(desc, 8, 2);
    let memattr : bits(4) = slice(desc, 2, 4);
    result.domain = undefined : bits(4);
    result.level = level;
    result.blocksize = 2 ^ ((3 - level) * stride + grainsize);
    if ~(secondstage) then {
        __tc17 : Permissions = result.perms;
        __tc17.xn = xn | xn_table;
        result.perms = __tc17;
        __tc18 : bits(3) = result.perms.ap;
        __tc18 = __SetSlice_bits(3, 1, __tc18, 2, [ap[2]] | [ap_table[1]]);
        __tc19 : Permissions = result.perms;
        __tc19.ap = __tc18;
        result.perms = __tc19;
        if ~(singlepriv) then {
            __tc20 : bits(3) = result.perms.ap;
            __tc20 = __SetSlice_bits(3, 1, __tc20, 1, [ap[1]] & ~([ap_table[0]]));
            __tc21 : Permissions = result.perms;
            __tc21.ap = __tc20;
            result.perms = __tc21;
            __tc22 : Permissions = result.perms;
            __tc22.pxn = pxn | pxn_table;
            result.perms = __tc22;
            if IsSecure() then {
                result.nG = nG | ns_table
            } else {
                result.nG = nG
            }
        } else {
            __tc23 : bits(3) = result.perms.ap;
            __tc23 = __SetSlice_bits(3, 1, __tc23, 1, 0b1);
            __tc24 : Permissions = result.perms;
            __tc24.ap = __tc23;
            result.perms = __tc24;
            __tc25 : Permissions = result.perms;
            __tc25.pxn = 0b0;
            result.perms = __tc25;
            result.nG = 0b0
        };
        result.GP = [desc[50]];
        __tc26 : bits(3) = result.perms.ap;
        __tc26 = __SetSlice_bits(3, 1, __tc26, 0, 0b1);
        __tc27 : Permissions = result.perms;
        __tc27.ap = __tc26;
        result.perms = __tc27;
        __tc28 : AddressDescriptor = result.addrdesc;
        __tc28.memattrs = AArch64_S1AttrDecode(sh, slice(memattr, 0, 3), acctype);
        result.addrdesc = __tc28;
        __tc29 : FullAddress = result.addrdesc.paddress;
        __tc29.NS = [memattr[3]] | ns_table;
        __tc30 : AddressDescriptor = result.addrdesc;
        __tc30.paddress = __tc29;
        result.addrdesc = __tc30
    } else {
        __tc31 : bits(3) = result.perms.ap;
        __tc31 = __SetSlice_bits(3, 2, __tc31, 1, slice(ap, 1, 2));
        __tc32 : Permissions = result.perms;
        __tc32.ap = __tc31;
        result.perms = __tc32;
        __tc33 : bits(3) = result.perms.ap;
        __tc33 = __SetSlice_bits(3, 1, __tc33, 0, 0b1);
        __tc34 : Permissions = result.perms;
        __tc34.ap = __tc33;
        result.perms = __tc34;
        __tc35 : Permissions = result.perms;
        __tc35.xn = xn;
        result.perms = __tc35;
        if HaveExtendedExecuteNeverExt() then {
            __tc36 : Permissions = result.perms;
            __tc36.xxn = [desc[53]];
            result.perms = __tc36
        };
        __tc37 : Permissions = result.perms;
        __tc37.pxn = 0b0;
        result.perms = __tc37;
        result.nG = 0b0;
        if s2fs1walk then {
            __tc38 : AddressDescriptor = result.addrdesc;
            __tc38.memattrs = S2AttrDecode(sh, memattr, AccType_PTW);
            result.addrdesc = __tc38
        } else {
            __tc39 : AddressDescriptor = result.addrdesc;
            __tc39.memattrs = S2AttrDecode(sh, memattr, acctype);
            result.addrdesc = __tc39
        };
        __tc40 : FullAddress = result.addrdesc.paddress;
        __tc40.NS = nsaccess;
        __tc41 : AddressDescriptor = result.addrdesc;
        __tc41.paddress = __tc40;
        result.addrdesc = __tc41
    };
    __tc42 : FullAddress = result.addrdesc.paddress;
    __tc42.address = outputaddress;
    __tc43 : AddressDescriptor = result.addrdesc;
    __tc43.paddress = __tc42;
    result.addrdesc = __tc43;
    __tc44 : AddressDescriptor = result.addrdesc;
    __tc44.fault = AArch64_NoFault();
    result.addrdesc = __tc44;
    result.contiguous = contiguousbit == 0b1;
    if HaveCommonNotPrivateTransExt() then {
        result.CnP = [baseregister[0]]
    };
    if __tlb_enabled then {
        TLBCache(ZeroExtend(inputaddr, 64), secondstage, s1_nonsecure, acctype, result)
    };
    let translation_info: TranslationInfo = struct {
        regime = PSTATE.EL,
        vmid = VMID_opt(),
        asid = Some(baseregister[63 .. 48]),
        va = vaddress,
        s1level = None(),
        s2info = None(),
        memattrs = result.addrdesc.memattrs,
    };
    (result, Some(translation_info))
}

function AArch64_CheckAndUpdateDescriptor (result, fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk__arg) = {
    hwupdatewalk : bool = hwupdatewalk__arg;
    hw_update_AF : bool = false;
    if result.AF then {
        if fault.typ == Fault_None then {
            hw_update_AF = true
        } else {
            if ConstrainUnpredictable(Unpredictable_AFUPDATE) == Constraint_TRUE then {
                hw_update_AF = true
            } else {
                hw_update_AF = false
            }
        }
    };
    hw_update_AP : bool = undefined : bool;
    write_perm_req : bool = undefined : bool;
    if result.AP & fault.typ == Fault_None then {
        write_perm_req = (iswrite | acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW | acctype == AccType_ORDEREDATOMICRW) & ~(s2fs1walk);
        hw_update_AP = write_perm_req & ~(acctype == AccType_AT | acctype == AccType_DC | acctype == AccType_DC_UNPRIV) | hwupdatewalk
    } else {
        hw_update_AP = false
    };
    accdesc : AccessDescriptor = undefined : AccessDescriptor;
    desc : bits(64) = undefined : bits(64);
    descaddr2 : AddressDescriptor = undefined : AddressDescriptor;
    el : bits(2) = undefined : bits(2);
    reversedescriptors : bool = undefined : bool;
    if hw_update_AF | hw_update_AP then {
        if secondstage | ~(HasS2Translation()) then {
            descaddr2 = result.descaddr
        } else {
            hwupdatewalk = true;
            let (s2_result, _) = AArch64_SecondStageWalk(result.descaddr, vaddress, acctype, iswrite, 8, hwupdatewalk);
            descaddr2 = s2_result;
            if IsFault(descaddr2) then {
                return(descaddr2.fault)
            }
        };
        accdesc = CreateAccessDescriptor(AccType_ATOMICRW);
        desc = _Mem(descaddr2, None(), 8, accdesc);
        el = AArch64_AccessUsesEL(acctype);
        match el {
          ? if ? == EL3 => {
              reversedescriptors = [SCTLR_EL3[25]] == 0b1
          },
          ? if ? == EL2 => {
              reversedescriptors = [SCTLR_EL2[25]] == 0b1
          },
          _ => {
              reversedescriptors = [SCTLR_EL1[25]] == 0b1
          }
        };
        if reversedescriptors then {
            desc = BigEndianReverse(desc)
        };
        if hw_update_AF then {
            desc = __SetSlice_bits(64, 1, desc, 10, 0b1)
        };
        if hw_update_AP then {
            desc = __SetSlice_bits(64, 1, desc, 7, if secondstage then 0b1 else 0b0)
        };
        _Mem(descaddr2, None(), 8, accdesc) = if reversedescriptors then BigEndianReverse(desc) else desc
    };
    fault
}

val AArch32_TranslationTableWalkSD : forall ('size : Int).
  (bits(32), AccType, bool, int('size)) -> TLBRecord effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch32_TranslationTableWalkSD (vaddress, acctype, iswrite, size) = {
    assert(ELUsingAArch32(S1TranslationRegime()));
    if __tlb_enabled then {
        let cacheline : TLBLine = TLBLookup(ZeroExtend(vaddress, 64), false, 0b1, acctype);
        if cacheline.valid_name then {
            return(cacheline.data)
        }
    };
    result : TLBRecord = undefined : TLBRecord;
    l1descaddr : AddressDescriptor = undefined : AddressDescriptor;
    l2descaddr : AddressDescriptor = undefined : AddressDescriptor;
    outputaddress : bits(40) = undefined : bits(40);
    let ipaddress : bits(40) = undefined : bits(40);
    let secondstage : bool = false;
    let s2fs1walk : bool = false;
    NS : bits(1) = undefined : bits(1);
    NS = undefined : bits(1);
    domain : bits(4) = undefined : bits(4);
    domain = undefined : bits(4);
    ttbr : bits(64) = undefined : bits(64);
    n : int = undefined : int;
    n = UInt(slice(get_TTBCR(), 0, 3));
    disabled : bool = undefined : bool;
    if n == 0 | IsZero_slice(vaddress, 32 - n, n) then {
        ttbr = get_TTBR0();
        disabled = [get_TTBCR()[4]] == 0b1
    } else {
        ttbr = get_TTBR1();
        disabled = [get_TTBCR()[5]] == 0b1;
        n = 0
    };
    level : int = undefined : int;
    if disabled then {
        level = 1;
        __tc1 : AddressDescriptor = result.addrdesc;
        __tc1.fault = AArch32_TranslationFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc1;
        return(result)
    };
    __tc2 : FullAddress = l1descaddr.paddress;
    __tc2.address = {
        let 'n = n;
        assert(constraint(('n + 18 >= 0 & - 'n + 12 >= 0)));
        ZeroExtend((slice(ttbr, 14 - n, n + 18) @ slice(vaddress, 20, negate(n) + 12)) @ 0b00)
    };
    l1descaddr.paddress = __tc2;
    __tc3 : FullAddress = l1descaddr.paddress;
    __tc3.NS = if IsSecure() then 0b0 else 0b1;
    l1descaddr.paddress = __tc3;
    let IRGN : bits(2) = [ttbr[0]] @ [ttbr[6]];
    let RGN : bits(2) = slice(ttbr, 3, 2);
    let SH : bits(2) = [ttbr[1]] @ [ttbr[5]];
    l1descaddr.memattrs = WalkAttrDecode(SH, RGN, IRGN, secondstage);
    l1descaddr2 : AddressDescriptor = undefined : AddressDescriptor;
    if ~(HaveEL(EL2)) | IsSecure() & ~(IsSecureEL2Enabled()) then {
        l1descaddr2 = l1descaddr
    } else {
        l1descaddr2 = AArch32_SecondStageWalk(l1descaddr, vaddress, acctype, iswrite, 4);
        if IsFault(l1descaddr2) then {
            __tc4 : AddressDescriptor = result.addrdesc;
            __tc4.fault = l1descaddr2.fault;
            result.addrdesc = __tc4;
            return(result)
        }
    };
    l1descaddr2.vaddress = ZeroExtend(vaddress);
    accdesc : AccessDescriptor = undefined : AccessDescriptor;
    accdesc = CreateAccessDescriptorPTW(acctype, secondstage, s2fs1walk, level);
    l1desc : bits(32) = undefined : bits(32);
    l1desc = aget__Mem(l1descaddr2, None(), 4, accdesc);
    if [get_SCTLR()[25]] == 0b1 then {
        l1desc = BigEndianReverse(l1desc)
    };
    S : bits(1) = undefined : bits(1);
    ap : bits(3) = undefined : bits(3);
    b : bits(1) = undefined : bits(1);
    blocksize : int = undefined : int;
    c : bits(1) = undefined : bits(1);
    l2desc : bits(32) = undefined : bits(32);
    l2descaddr2 : AddressDescriptor = undefined : AddressDescriptor;
    nG : bits(1) = undefined : bits(1);
    pxn : bits(1) = undefined : bits(1);
    tex : bits(3) = undefined : bits(3);
    xn : bits(1) = undefined : bits(1);
    match slice(l1desc, 0, 2) {
      0b00 => {
          level = 1;
          __tc5 : AddressDescriptor = result.addrdesc;
          __tc5.fault = AArch32_TranslationFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
          result.addrdesc = __tc5;
          return(result)
      },
      0b01 => {
          domain = slice(l1desc, 5, 4);
          level = 2;
          pxn = [l1desc[2]];
          NS = [l1desc[3]];
          __tc6 : FullAddress = l2descaddr.paddress;
          __tc6.address = ZeroExtend((slice(l1desc, 10, 22) @ slice(vaddress, 12, 8)) @ 0b00);
          l2descaddr.paddress = __tc6;
          __tc7 : FullAddress = l2descaddr.paddress;
          __tc7.NS = if IsSecure() then 0b0 else 0b1;
          l2descaddr.paddress = __tc7;
          l2descaddr.memattrs = l1descaddr.memattrs;
          if ~(HaveEL(EL2)) | IsSecure() & ~(IsSecureEL2Enabled()) then {
              l2descaddr2 = l2descaddr
          } else {
              l2descaddr2 = AArch32_SecondStageWalk(l2descaddr, vaddress, acctype, iswrite, 4);
              if IsFault(l2descaddr2) then {
                  __tc8 : AddressDescriptor = result.addrdesc;
                  __tc8.fault = l2descaddr2.fault;
                  result.addrdesc = __tc8;
                  return(result)
              }
          };
          l2descaddr2.vaddress = ZeroExtend(vaddress);
          accdesc = CreateAccessDescriptorPTW(acctype, secondstage, s2fs1walk, level);
          l2desc = aget__Mem(l2descaddr2, None(), 4, accdesc);
          if [get_SCTLR()[25]] == 0b1 then {
              l2desc = BigEndianReverse(l2desc)
          };
          if slice(l2desc, 0, 2) == 0b00 then {
              __tc9 : AddressDescriptor = result.addrdesc;
              __tc9.fault = AArch32_TranslationFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
              result.addrdesc = __tc9;
              return(result)
          };
          nG = [l2desc[11]];
          S = [l2desc[10]];
          ap = l2desc[9 .. 9] @ l2desc[4 .. 3];
          if [get_SCTLR()[29]] == 0b1 & [l2desc[4]] == 0b0 then {
              __tc10 : AddressDescriptor = result.addrdesc;
              __tc10.fault = AArch32_AccessFlagFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
              result.addrdesc = __tc10;
              return(result)
          };
          if [l2desc[1]] == 0b0 then {
              xn = [l2desc[15]];
              tex = slice(l2desc, 12, 3);
              c = [l2desc[3]];
              b = [l2desc[2]];
              blocksize = 64;
              outputaddress = ZeroExtend(slice(l2desc, 16, 16) @ slice(vaddress, 0, 16))
          } else {
              tex = slice(l2desc, 6, 3);
              c = [l2desc[3]];
              b = [l2desc[2]];
              xn = [l2desc[0]];
              blocksize = 4;
              outputaddress = ZeroExtend(slice(l2desc, 12, 20) @ slice(vaddress, 0, 12))
          }
      },
      [bitone] @ _ : bits(1) => {
          NS = [l1desc[19]];
          nG = [l1desc[17]];
          S = [l1desc[16]];
          ap = l1desc[15 .. 15] @ l1desc[10 .. 9];
          tex = slice(l1desc, 12, 3);
          xn = [l1desc[4]];
          c = [l1desc[3]];
          b = [l1desc[2]];
          pxn = [l1desc[0]];
          level = 1;
          if [get_SCTLR()[29]] == 0b1 & [l1desc[10]] == 0b0 then {
              __tc11 : AddressDescriptor = result.addrdesc;
              __tc11.fault = AArch32_AccessFlagFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
              result.addrdesc = __tc11;
              return(result)
          };
          if [l1desc[18]] == 0b0 then {
              domain = slice(l1desc, 5, 4);
              blocksize = 1024;
              outputaddress = ZeroExtend(slice(l1desc, 20, 12) @ slice(vaddress, 0, 20))
          } else {
              domain = 0x0;
              blocksize = 16384;
              outputaddress = ((slice(l1desc, 5, 4) @ slice(l1desc, 20, 4)) @ slice(l1desc, 24, 8)) @ slice(vaddress, 0, 24)
          }
      }
    };
    if [get_SCTLR()[28]] == 0b0 then {
        if RemapRegsHaveResetValues() then {
            __tc12 : AddressDescriptor = result.addrdesc;
            __tc12.memattrs = AArch32_DefaultTEXDecode(tex, c, b, S, acctype);
            result.addrdesc = __tc12
        } else {
            __tc13 : AddressDescriptor = result.addrdesc;
            __tc13.memattrs = undefined;
            result.addrdesc = __tc13
        }
    } else {
        __tc14 : AddressDescriptor = result.addrdesc;
        __tc14.memattrs = AArch32_RemappedTEXDecode(tex, c, b, S, acctype);
        result.addrdesc = __tc14
    };
    __tc15 : Permissions = result.perms;
    __tc15.ap = ap;
    result.perms = __tc15;
    __tc16 : Permissions = result.perms;
    __tc16.xn = xn;
    result.perms = __tc16;
    __tc17 : Permissions = result.perms;
    __tc17.pxn = pxn;
    result.perms = __tc17;
    result.nG = nG;
    result.domain = domain;
    result.level = level;
    result.blocksize = blocksize;
    __tc18 : FullAddress = result.addrdesc.paddress;
    __tc18.address = ZeroExtend(outputaddress);
    __tc19 : AddressDescriptor = result.addrdesc;
    __tc19.paddress = __tc18;
    result.addrdesc = __tc19;
    __tc20 : FullAddress = result.addrdesc.paddress;
    __tc20.NS = if IsSecure() then NS else 0b1;
    __tc21 : AddressDescriptor = result.addrdesc;
    __tc21.paddress = __tc20;
    result.addrdesc = __tc21;
    __tc22 : AddressDescriptor = result.addrdesc;
    __tc22.fault = AArch32_NoFault();
    result.addrdesc = __tc22;
    if __tlb_enabled then {
        TLBCache(ZeroExtend(vaddress, 64), false, 0b1, acctype, result)
    };
    result
}

val AArch32_FirstStageTranslate : forall ('iswrite : Bool) ('wasaligned : Bool) 'size.
  (bits(32), AccType, bool('iswrite), bool('wasaligned), int('size)) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch32_FirstStageTranslate (vaddress, acctype, iswrite, wasaligned, size) = {
    dc : bits(1) = undefined : bits(1);
    s1_enabled : bool = undefined : bool;
    tge : bits(1) = undefined : bits(1);
    if PSTATE.EL == EL2 then {
        s1_enabled = [get_HSCTLR()[0]] == 0b1
    } else {
        if EL2Enabled() then {
            tge = if ELUsingAArch32(EL2) then [get_HCR()[27]] else [HCR_EL2[27]];
            dc = if ELUsingAArch32(EL2) then [get_HCR()[12]] else [HCR_EL2[12]];
            s1_enabled = (tge == 0b0 & dc == 0b0) & [get_SCTLR()[0]] == 0b1
        } else {
            s1_enabled = [get_SCTLR()[0]] == 0b1
        }
    };
    let ipaddress = undefined : bits(40);
    let secondstage = false;
    let s2fs1walk = false;
    S1 : TLBRecord = undefined : TLBRecord;
    domaincheck : bool = undefined : bool;
    nTLSMD : bits(1) = undefined : bits(1);
    permissioncheck : bool = undefined : bool;
    use_long_descriptor_format : bool = undefined : bool;
    if s1_enabled then {
        use_long_descriptor_format = PSTATE.EL == EL2 | [get_TTBCR()[31]] == 0b1;
        if use_long_descriptor_format then {
            S1 = AArch32_TranslationTableWalk(ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, size);
            permissioncheck = true;
            domaincheck = false
        } else {
            S1 = AArch32_TranslationTableWalkSD(vaddress, acctype, iswrite, size);
            permissioncheck = true;
            domaincheck = true
        }
    } else {
        S1 = AArch32_TranslateAddressS1Off(vaddress, acctype, iswrite);
        permissioncheck = false;
        domaincheck = false;
        if (UsingAArch32() & HaveTrapLoadStoreMultipleDeviceExt()) & AArch32_ExecutingLSMInstr() then {
            if S1.addrdesc.memattrs.typ == MemType_Device & S1.addrdesc.memattrs.device != DeviceType_GRE then {
                nTLSMD = if S1TranslationRegime() == EL2 then [get_HSCTLR()[3]] else [get_SCTLR()[3]];
                if nTLSMD == 0b0 then {
                    __tc1 : AddressDescriptor = S1.addrdesc;
                    __tc1.fault = AArch32_AlignmentFault(acctype, iswrite, secondstage);
                    S1.addrdesc = __tc1
                }
            }
        }
    };
    if ((~(wasaligned) & acctype != AccType_IFETCH | acctype == AccType_DCZVA) & S1.addrdesc.memattrs.typ == MemType_Device) & ~(IsFault(S1.addrdesc)) then {
        __tc2 : AddressDescriptor = S1.addrdesc;
        __tc2.fault = AArch32_AlignmentFault(acctype, iswrite, secondstage);
        S1.addrdesc = __tc2
    };
    abort : FaultRecord = undefined : FaultRecord;
    if ~(IsFault(S1.addrdesc)) & domaincheck then {
        (permissioncheck, abort) = AArch32_CheckDomain(S1.domain, vaddress, S1.level, acctype, iswrite);
        __tc3 : AddressDescriptor = S1.addrdesc;
        __tc3.fault = abort;
        S1.addrdesc = __tc3
    };
    if ~(IsFault(S1.addrdesc)) & permissioncheck then {
        __tc4 : AddressDescriptor = S1.addrdesc;
        __tc4.fault = AArch32_CheckPermission(S1.perms, vaddress, S1.level, S1.domain, S1.addrdesc.paddress.NS, acctype, iswrite);
        S1.addrdesc = __tc4
    };
    if (~(IsFault(S1.addrdesc)) & S1.addrdesc.memattrs.typ == MemType_Device) & acctype == AccType_IFETCH then {
        S1.addrdesc = AArch32_InstructionDevice(S1.addrdesc, vaddress, ipaddress, S1.level, S1.domain, acctype, iswrite, secondstage, s2fs1walk)
    };
    S1.addrdesc
}

val AArch32_FullTranslate : forall ('iswrite : Bool) ('wasaligned : Bool) 'size.
  (bits(32), AccType, bool('iswrite), bool('wasaligned), int('size)) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch32_FullTranslate (vaddress, acctype, iswrite, wasaligned, size) = {
    let S1 = AArch32_FirstStageTranslate(vaddress, acctype, iswrite, wasaligned, size);
    result : AddressDescriptor = undefined : AddressDescriptor;
    s2fs1walk : bool = undefined : bool;
    if (~(IsFault(S1)) & ~(HaveNV2Ext() & acctype == AccType_NV2REGISTER)) & HasS2Translation() then {
        s2fs1walk = false;
        result = AArch32_SecondStageTranslate(S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size)
    } else {
        result = S1
    };
    result
}

val AArch32_TranslateAddress : forall ('iswrite : Bool) ('wasaligned : Bool) 'size.
  (bits(32), AccType, bool('iswrite), bool('wasaligned), int('size)) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch32_TranslateAddress (vaddress, acctype, iswrite, wasaligned, size) = {
    if ~(ELUsingAArch32(S1TranslationRegime())) then {
        let (result, _) = AArch64_TranslateAddress(ZeroExtend(vaddress, 64), acctype, iswrite, wasaligned, size);
        return result
    };
    result : AddressDescriptor = undefined : AddressDescriptor;
    result = AArch32_FullTranslate(vaddress, acctype, iswrite, wasaligned, size);
    if ~(acctype == AccType_PTW | acctype == AccType_IC | acctype == AccType_AT) & ~(IsFault(result)) then {
        result.fault = AArch32_CheckDebug(vaddress, acctype, iswrite, size)
    };
    result.vaddress = ZeroExtend(vaddress);
    result
}

function AArch32_TranslationTableWalk (ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, size) = {
    if ~(secondstage) then {
        assert(ELUsingAArch32(S1TranslationRegime()))
    } else {
        assert(((HaveEL(EL2) & ~(IsSecure())) & ELUsingAArch32(EL2)) & HasS2Translation())
    };
    result : TLBRecord = undefined : TLBRecord;
    descaddr : AddressDescriptor = undefined : AddressDescriptor;
    baseregister : bits(64) = undefined : bits(64);
    inputaddr : bits(40) = undefined : bits(40);
    if __tlb_enabled then {
        if ~(secondstage) then {
            inputaddr = ZeroExtend(vaddress)
        } else {
            inputaddr = ZeroExtend(ipaddress)
        };
        let cacheline : TLBLine = TLBLookup(ZeroExtend(inputaddr, 64), secondstage, 0b1, acctype);
        if cacheline.valid_name then {
            return(cacheline.data)
        }
    };
    let domain : bits(4) = undefined : bits(4);
    __tc1 : MemoryAttributes = descaddr.memattrs;
    __tc1.typ = MemType_Normal;
    descaddr.memattrs = __tc1;
    let 'grainsize : {'n, 'n == 12. int('n)} = 12;
    let 'stride : {'n, 'n == 'grainsize - 3. int('n)} = grainsize - 3;
    __anon1 : Constraint = undefined : Constraint;
    basefound : bool = undefined : bool;
    disabled : bool = undefined : bool;
    el : bits(2) = undefined : bits(2);
    hierattrsdisabled : bool = undefined : bool;
    inputsize : int = undefined : int;
    level : int = undefined : int;
    lookupsecure : bool = undefined : bool;
    reversedescriptors : bool = undefined : bool;
    singlepriv : bool = undefined : bool;
    startlevel : int = undefined : int;
    startsizecheck : int = undefined : int;
    t0size : int = undefined : int;
    t1size : int = undefined : int;
    if ~(secondstage) then {
        inputaddr = ZeroExtend(vaddress);
        el = AArch32_AccessUsesEL(acctype);
        if el == EL2 then {
            inputsize = 32 - UInt(slice(get_HTCR(), 0, 3));
            basefound = inputsize == 32 | IsZero_slice(inputaddr, inputsize, negate(inputsize) + 32);
            disabled = false;
            baseregister = get_HTTBR();
            descaddr.memattrs = WalkAttrDecode(slice(get_HTCR(), 12, 2), slice(get_HTCR(), 10, 2), slice(get_HTCR(), 8, 2), secondstage);
            reversedescriptors = [get_HSCTLR()[25]] == 0b1;
            lookupsecure = false;
            singlepriv = true;
            hierattrsdisabled = AArch32_HaveHPDExt() & [get_HTCR()[24]] == 0b1
        } else {
            basefound = false;
            disabled = false;
            t0size = UInt(slice(get_TTBCR(), 0, 3));
            if t0size == 0 | IsZero_slice(inputaddr, 32 - t0size, t0size) then {
                inputsize = 32 - t0size;
                basefound = true;
                baseregister = get_TTBR0();
                descaddr.memattrs = WalkAttrDecode(slice(get_TTBCR(), 12, 2), slice(get_TTBCR(), 10, 2), slice(get_TTBCR(), 8, 2), secondstage);
                hierattrsdisabled = (AArch32_HaveHPDExt() & [get_TTBCR()[6]] == 0b1) & [get_TTBCR2()[9]] == 0b1
            };
            t1size = UInt(slice(get_TTBCR(), 16, 3));
            if t1size == 0 & ~(basefound) | t1size > 0 & IsOnes_slice(inputaddr, 32 - t1size, t1size) then {
                inputsize = 32 - t1size;
                basefound = true;
                baseregister = get_TTBR1();
                descaddr.memattrs = WalkAttrDecode(slice(get_TTBCR(), 28, 2), slice(get_TTBCR(), 26, 2), slice(get_TTBCR(), 24, 2), secondstage);
                hierattrsdisabled = (AArch32_HaveHPDExt() & [get_TTBCR()[6]] == 0b1) & [get_TTBCR2()[10]] == 0b1
            };
            reversedescriptors = [get_SCTLR()[25]] == 0b1;
            lookupsecure = IsSecure();
            singlepriv = false
        };
        level = 4 - cdiv_int(inputsize - grainsize, stride)
    } else {
        inputaddr = ipaddress;
        inputsize = 32 - SInt(slice(get_VTCR(), 0, 4));
        if [get_VTCR()[4]] != [slice(get_VTCR(), 0, 4)[3]] then {
            (__anon1, inputsize) = ConstrainUnpredictableInteger(32 - 7, 32 + 8, Unpredictable_RESVTCRS)
        };
        basefound = inputsize == 40 | IsZero_slice(inputaddr, inputsize, negate(inputsize) + 40);
        disabled = false;
        descaddr.memattrs = WalkAttrDecode(slice(get_VTCR(), 8, 2), slice(get_VTCR(), 10, 2), slice(get_VTCR(), 12, 2), secondstage);
        reversedescriptors = [get_HSCTLR()[25]] == 0b1;
        singlepriv = true;
        lookupsecure = false;
        baseregister = get_VTTBR();
        startlevel = UInt(slice(get_VTCR(), 6, 2));
        level = 2 - startlevel;
        if level <= 0 then {
            basefound = false
        };
        startsizecheck = inputsize - ((3 - level) * stride + grainsize);
        if startsizecheck < 1 | startsizecheck > stride + 4 then {
            basefound = false
        }
    };
    if ~(basefound) | disabled then {
        level = 1;
        __tc2 : AddressDescriptor = result.addrdesc;
        __tc2.fault = AArch32_TranslationFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc2;
        return(result)
    };
    if ~(IsZero(slice(baseregister, 40, 8))) then {
        level = 0;
        __tc3 : AddressDescriptor = result.addrdesc;
        __tc3.fault = AArch32_AddressSizeFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc3;
        return(result)
    };
    let baselowerbound : int = 3 + inputsize - ((3 - level) * stride + grainsize);
    baseaddress : bits(40) = undefined : bits(40);
    baseaddress = {
        let 'baselowerbound = baselowerbound;
        assert(constraint(- 'baselowerbound + 40 >= 0));
        slice(baseregister, baselowerbound, negate(baselowerbound) + 40) @ Zeros(baselowerbound)
    };
    ns_table : bits(1) = undefined : bits(1);
    ns_table = if lookupsecure then 0b0 else 0b1;
    ap_table : bits(2) = undefined : bits(2);
    ap_table = 0b00;
    xn_table : bits(1) = undefined : bits(1);
    xn_table = 0b0;
    pxn_table : bits(1) = undefined : bits(1);
    pxn_table = 0b0;
    addrselecttop : int = undefined : int;
    addrselecttop = inputsize - 1;
    accdesc : AccessDescriptor = undefined : AccessDescriptor;
    addrselectbottom : int = undefined : int;
    blocktranslate : bool = undefined : bool;
    desc : bits(64) = undefined : bits(64);
    descaddr2 : AddressDescriptor = undefined : AddressDescriptor;
    repeat {
        addrselectbottom = (3 - level) * stride + grainsize;
        let index : bits(40) = ZeroExtend_slice_append(inputaddr, addrselectbottom, addrselecttop - addrselectbottom + 1, 0b000);
        __tc4 : FullAddress = descaddr.paddress;
        __tc4.address = ZeroExtend(baseaddress | index);
        descaddr.paddress = __tc4;
        __tc5 : FullAddress = descaddr.paddress;
        __tc5.NS = ns_table;
        descaddr.paddress = __tc5;
        if (secondstage | ~(HasS2Translation())) | HaveNV2Ext() & acctype == AccType_NV2REGISTER then {
            descaddr2 = descaddr
        } else {
            descaddr2 = AArch32_SecondStageWalk(descaddr, vaddress, acctype, iswrite, 8);
            if IsFault(descaddr2) then {
                __tc6 : AddressDescriptor = result.addrdesc;
                __tc6.fault = descaddr2.fault;
                result.addrdesc = __tc6;
                return(result)
            }
        };
        descaddr2.vaddress = ZeroExtend(vaddress);
        accdesc = CreateAccessDescriptorPTW(acctype, secondstage, s2fs1walk, level);
        desc = aget__Mem(descaddr2, None(), 8, accdesc);
        if reversedescriptors then {
            desc = BigEndianReverse(desc)
        };
        if [desc[0]] == 0b0 | slice(desc, 0, 2) == 0b01 & level == 3 then {
            __tc7 : AddressDescriptor = result.addrdesc;
            __tc7.fault = AArch32_TranslationFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
            result.addrdesc = __tc7;
            return(result)
        };
        if slice(desc, 0, 2) == 0b01 | level == 3 then {
            blocktranslate = true
        } else {
            if ~(IsZero(slice(desc, 40, 8))) then {
                __tc8 : AddressDescriptor = result.addrdesc;
                __tc8.fault = AArch32_AddressSizeFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
                result.addrdesc = __tc8;
                return(result)
            };
            baseaddress = slice(desc, grainsize, negate(grainsize) + 40) @ Zeros(grainsize);
            if ~(secondstage) then {
                ns_table = ns_table | [desc[63]]
            };
            if ~(secondstage) & ~(hierattrsdisabled) then {
                ap_table = __SetSlice_bits(2, 1, ap_table, 1, [ap_table[1]] | [desc[62]]);
                xn_table = xn_table | [desc[60]];
                if ~(singlepriv) then {
                    pxn_table = pxn_table | [desc[59]];
                    ap_table = __SetSlice_bits(2, 1, ap_table, 0, [ap_table[0]] | [desc[61]])
                }
            };
            level = level + 1;
            addrselecttop = addrselectbottom - 1;
            blocktranslate = false
        }
    } until blocktranslate;
    if ~(IsZero(slice(desc, 40, 8))) then {
        __tc9 : AddressDescriptor = result.addrdesc;
        __tc9.fault = AArch32_AddressSizeFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc9;
        return(result)
    };
    let outputaddress : bits(40) = {
        let 'addrselectbottom = addrselectbottom;
        assert(constraint((- 'addrselectbottom + 40 >= 0 & 'addrselectbottom >= 0)));
        slice(desc, addrselectbottom, negate(addrselectbottom) + 40) @ slice(inputaddr, 0, addrselectbottom)
    };
    if [desc[10]] == 0b0 then {
        __tc10 : AddressDescriptor = result.addrdesc;
        __tc10.fault = AArch32_AccessFlagFault(ipaddress, domain, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tc10;
        return(result)
    };
    let xn : bits(1) = [desc[54]];
    let pxn : bits(1) = [desc[53]];
    let ap : bits(3) = slice(desc, 6, 2) @ 0b1;
    let contiguousbit : bits(1) = [desc[52]];
    let nG : bits(1) = [desc[11]];
    let sh : bits(2) = slice(desc, 8, 2);
    let memattr : bits(4) = slice(desc, 2, 4);
    result.domain = undefined : bits(4);
    result.level = level;
    result.blocksize = 2 ^ ((3 - level) * stride + grainsize);
    if ~(secondstage) then {
        __tc11 : Permissions = result.perms;
        __tc11.xn = xn | xn_table;
        result.perms = __tc11;
        __tc12 : bits(3) = result.perms.ap;
        __tc12 = __SetSlice_bits(3, 1, __tc12, 2, [ap[2]] | [ap_table[1]]);
        __tc13 : Permissions = result.perms;
        __tc13.ap = __tc12;
        result.perms = __tc13;
        if ~(singlepriv) then {
            __tc14 : bits(3) = result.perms.ap;
            __tc14 = __SetSlice_bits(3, 1, __tc14, 1, [ap[1]] & ~([ap_table[0]]));
            __tc15 : Permissions = result.perms;
            __tc15.ap = __tc14;
            result.perms = __tc15;
            __tc16 : Permissions = result.perms;
            __tc16.pxn = pxn | pxn_table;
            result.perms = __tc16;
            if IsSecure() then {
                result.nG = nG | ns_table
            } else {
                result.nG = nG
            }
        } else {
            __tc17 : bits(3) = result.perms.ap;
            __tc17 = __SetSlice_bits(3, 1, __tc17, 1, 0b1);
            __tc18 : Permissions = result.perms;
            __tc18.ap = __tc17;
            result.perms = __tc18;
            __tc19 : Permissions = result.perms;
            __tc19.pxn = 0b0;
            result.perms = __tc19;
            result.nG = 0b0
        };
        result.GP = [desc[50]];
        __tc20 : bits(3) = result.perms.ap;
        __tc20 = __SetSlice_bits(3, 1, __tc20, 0, 0b1);
        __tc21 : Permissions = result.perms;
        __tc21.ap = __tc20;
        result.perms = __tc21;
        __tc22 : AddressDescriptor = result.addrdesc;
        __tc22.memattrs = AArch32_S1AttrDecode(sh, slice(memattr, 0, 3), acctype);
        result.addrdesc = __tc22;
        __tc23 : FullAddress = result.addrdesc.paddress;
        __tc23.NS = [memattr[3]] | ns_table;
        __tc24 : AddressDescriptor = result.addrdesc;
        __tc24.paddress = __tc23;
        result.addrdesc = __tc24
    } else {
        __tc25 : bits(3) = result.perms.ap;
        __tc25 = __SetSlice_bits(3, 2, __tc25, 1, slice(ap, 1, 2));
        __tc26 : Permissions = result.perms;
        __tc26.ap = __tc25;
        result.perms = __tc26;
        __tc27 : bits(3) = result.perms.ap;
        __tc27 = __SetSlice_bits(3, 1, __tc27, 0, 0b1);
        __tc28 : Permissions = result.perms;
        __tc28.ap = __tc27;
        result.perms = __tc28;
        __tc29 : Permissions = result.perms;
        __tc29.xn = xn;
        result.perms = __tc29;
        if HaveExtendedExecuteNeverExt() then {
            __tc30 : Permissions = result.perms;
            __tc30.xxn = [desc[53]];
            result.perms = __tc30
        };
        __tc31 : Permissions = result.perms;
        __tc31.pxn = 0b0;
        result.perms = __tc31;
        result.nG = 0b0;
        if s2fs1walk then {
            __tc32 : AddressDescriptor = result.addrdesc;
            __tc32.memattrs = S2AttrDecode(sh, memattr, AccType_PTW);
            result.addrdesc = __tc32
        } else {
            __tc33 : AddressDescriptor = result.addrdesc;
            __tc33.memattrs = S2AttrDecode(sh, memattr, acctype);
            result.addrdesc = __tc33
        };
        __tc34 : FullAddress = result.addrdesc.paddress;
        __tc34.NS = 0b1;
        __tc35 : AddressDescriptor = result.addrdesc;
        __tc35.paddress = __tc34;
        result.addrdesc = __tc35
    };
    __tc36 : FullAddress = result.addrdesc.paddress;
    __tc36.address = ZeroExtend(outputaddress);
    __tc37 : AddressDescriptor = result.addrdesc;
    __tc37.paddress = __tc36;
    result.addrdesc = __tc37;
    __tc38 : AddressDescriptor = result.addrdesc;
    __tc38.fault = AArch32_NoFault();
    result.addrdesc = __tc38;
    result.contiguous = contiguousbit == 0b1;
    if HaveCommonNotPrivateTransExt() then {
        result.CnP = [baseregister[0]]
    };
    if __tlb_enabled then {
        TLBCache(ZeroExtend(inputaddr, 64), secondstage, 0b1, acctype, result)
    };
    result
}

val AArch32_aget_MemSingle : forall 'size ('wasaligned : Bool),
  'size in {1, 2, 4, 8, 16}.
  (bits(32), int('size), AccType, bool('wasaligned)) -> bits(8 * 'size) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch32_aget_MemSingle (address, size, acctype, wasaligned) = {
    assert(size == 1 | size == 2 | size == 4 | size == 8 | size == 16);
    assert(address == Align(address, size));
    memaddrdesc : AddressDescriptor = undefined : AddressDescriptor;
    value_name : bits(8 * 'size) = undefined : bits('size * 8);
    let iswrite = false;
    let memaddrdesc = AArch32_TranslateAddress(address, acctype, iswrite, wasaligned, size);
    if IsFault(memaddrdesc) then {
        AArch32_Abort(address, memaddrdesc.fault)
    };
    let accdesc = CreateAccessDescriptor(acctype);
    if HaveMTEExt() then {
        if AccessIsTagChecked(ZeroExtend(address, 64), acctype) then {
            let ptag = TransformTag(ZeroExtend(address, 64));
            if ~(CheckTag(memaddrdesc, ptag, iswrite)) then {
                TagCheckFail(ZeroExtend(address, 64), iswrite)
            }
        }
    };
    let value_name = _Mem(memaddrdesc, None(), size, accdesc);
    value_name
}

overload MemSingle = {AArch32_aget_MemSingle}

val AArch32_CheckPCAlignment : unit -> unit effect {escape, rreg, undef, wreg}

function AArch32_CheckPCAlignment () = {
    let pc : bits(32) = ThisInstrAddr();
    acctype : AccType = undefined : AccType;
    iswrite : bool = undefined : bool;
    secondstage : bool = undefined : bool;
    vaddress : bits(32) = undefined : bits(32);
    if CurrentInstrSet() == InstrSet_A32 & [pc[1]] == 0b1 | [pc[0]] == 0b1 then {
        if AArch32_GeneralExceptionsToAArch64() then {
            AArch64_PCAlignmentFault()
        };
        vaddress = pc;
        acctype = AccType_IFETCH;
        iswrite = false;
        secondstage = false;
        AArch32_Abort(vaddress, AArch32_AlignmentFault(acctype, iswrite, secondstage))
    }
}

val __fetchA32 : unit -> bits(32) effect {escape, rmem, rreg, undef, wmem, wreg}

function __fetchA32 () = {
    CheckSoftwareStep();
    AArch32_CheckPCAlignment();
    let a32 = MemSingle(slice(_PC, 0, 32), 4, AccType_IFETCH, true);
    AArch32_CheckIllegalState();
    a32
}
