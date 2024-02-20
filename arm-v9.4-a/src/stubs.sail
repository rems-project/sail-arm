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

function AArch32_IsExclusiveVA (address, processorid, size) = {
    return(__UNKNOWN_boolean())
}

function AArch32_MarkExclusiveVA (address, processorid, size) = {
    return()
}

function AArch32_ReportedInnerAttrs attrs = {
    return(__UNKNOWN_bits(3))
}

function AArch32_ReportedOuterAttrs attrs = {
    return(__UNKNOWN_bits(2))
}

function AArch32_SetLSInstructionSyndrome (size, sign_extend, Rt, acq_rel) = {
    return()
}

function AArch64_CheckNVCondsIfCurrentEL (op0, op1, crn, crm, op2) = {
    return(__UNKNOWN_boolean())
}

function ActionRequired () = {
    return(__UNKNOWN_boolean())
}

function AddressSupportsLS64 paddress = {
    return(__UNKNOWN_boolean())
}

function BPIALL () = {
    return()
}

function BPIALLIS () = {
    return()
}

function BPIMVA val_name = {
    return()
}

function CP15DMB () = {
    return()
}

function CP15DSB () = {
    return()
}

function CP15ISB () = {
    return()
}

function CPYPostSizeChoice (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_bits(64))
}

function CPYPreSizeChoice (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_bits(64))
}

function CPYSizeChoice (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_integer())
}

function CTI_SetEventLevel (id, level) = {
    return()
}

function CTI_SignalEvent id = {
    return()
}

function ChooseRandomNonExcludedTag exclude_in = {
    return(__UNKNOWN_bits(4))
}

function ClearExclusiveByAddress (paddress, processorid, size) = {
    return()
}

function ClearExclusiveLocal processorid = {
    return()
}

function CommitTransactionalWrites () = {
    return()
}

function ComputePACIMPDEF (data, modifier, key0, key1) = {
    return(__UNKNOWN_bits(64))
}

function ConstrainUnpredictable which = {
    return(__UNKNOWN_Constraint())
}

function ConstrainUnpredictableBits (which, width) = {
    return(undefined : (Constraint, bits('width)))
}

function ConstrainUnpredictableBool which = {
    return(__UNKNOWN_boolean())
}

function ConstrainUnpredictableInteger (low, high, which) = {
    return(undefined : (Constraint, int))
}

function ConstrainUnpredictableProcedure which = {
    return()
}

function ConsumptionOfSpeculativeDataBarrier () = {
    return()
}

function DC_CIGDPAPA val_name = {
    return()
}

function DC_CIPAPA val_name = {
    return()
}

function DiscardTransactionalWrites () = {
    return()
}

function EnterLowPowerState () = {
    return()
}

function ErrorIsContained () = {
    return(__UNKNOWN_boolean())
}

function ErrorIsSynchronized () = {
    return(__UNKNOWN_boolean())
}

function FaultIsCorrected () = {
    return(__UNKNOWN_boolean())
}

function GPTTLBCache (pgs, gpt_entry) = {
    return()
}

function GPTTLBLookup (pa, pgs) = {
    return(__UNKNOWN_GPTTLBLine())
}

function GetAccumulatedFPExceptions () = {
    return(__UNKNOWN_bits(8))
}

function GetCacheInfo (level, cachetype) = {
    return(undefined : (int, int, int))
}

function GetLoadStoreType () = {
    return(__UNKNOWN_bits(2))
}

function GetPendingPhysicalSError () = {
    return(__UNKNOWN_FaultRecord())
}

function Hint_Branch hint = {
    return()
}

function Hint_CLRBHB () = {
    return()
}

function Hint_DGH () = {
    return()
}

function Hint_Prefetch (address, hint, target, stream) = {
    return()
}

function Hint_PreloadData address = {
    return()
}

function Hint_PreloadDataForWrite address = {
    return()
}

function Hint_PreloadInstr address = {
    return()
}

function Hint_RangePrefetch (address, length, stride, count, reuse, operation) = {
    return()
}

function Hint_Yield () = {
    return()
}

function IsASEInstruction () = {
    return(__UNKNOWN_boolean())
}

function IsExternalAbortTakenSynchronously (memstatus, iswrite, desc, size, accdesc) = {
    return(__UNKNOWN_boolean())
}

function IsSynchronizablePhysicalSErrorPending () = {
    return(__UNKNOWN_boolean())
}

function LS64InstructionSyndrome () = {
    return(undefined : (bits(24), bits(11)))
}

function LocalTimeoutEvent localtimeout = {
    return(__UNKNOWN_boolean())
}

function MarkExclusiveGlobal (paddress, processorid, size) = {
    return()
}

function MarkExclusiveLocal (paddress, processorid, size) = {
    return()
}

function MemCpyDirectionChoice (fromaddress, toaddress, cpysize) = {
    return(__UNKNOWN_boolean())
}

function MemCpyParametersIllformedE (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_boolean())
}

function MemCpyParametersIllformedM (toaddress, fromaddress, cpysize) = {
    return(__UNKNOWN_boolean())
}

function MemCpyZeroSizeCheck () = {
    return(__UNKNOWN_boolean())
}

function MemSetParametersIllformedE (toaddress, setsize, IsSETGE) = {
    return(__UNKNOWN_boolean())
}

function MemSetParametersIllformedM (toaddress, setsize, IsSETGM) = {
    return(__UNKNOWN_boolean())
}

function MemSetZeroSizeCheck () = {
    return(__UNKNOWN_boolean())
}

function PendSErrorInterrupt fault = {
    return()
}

function ProfilingSynchronizationBarrier () = {
    return()
}

function RemapRegsHaveResetValues () = {
    return(__UNKNOWN_boolean())
}

function ReportErrorAsIMPDEF () = {
    return(__UNKNOWN_boolean())
}

function ReportErrorAsUC () = {
    return(__UNKNOWN_boolean())
}

function ReportErrorAsUER () = {
    return(__UNKNOWN_boolean())
}

function ReportErrorAsUEU () = {
    return(__UNKNOWN_boolean())
}

function ReportErrorAsUncategorized () = {
    return(__UNKNOWN_boolean())
}

function ReportedPARAttrs parattrs = {
    return(__UNKNOWN_bits(8))
}

function ReportedPARShareability sh = {
    return(__UNKNOWN_bits(2))
}

function S1TLBCache tlbrecord = {
    return()
}

function S1TLBLookup tlbcontext = {
    return(__UNKNOWN_TLBLine())
}

function S2TLBCache tlbrecord = {
    return()
}

function S2TLBLookup tlbcontext = {
    return(__UNKNOWN_TLBLine())
}

function SETPostSizeChoice (toaddress, setsize, IsSETGE) = {
    return(__UNKNOWN_bits(64))
}

function SETPreSizeChoice (toaddress, setsize, IsSETGP) = {
    return(__UNKNOWN_bits(64))
}

function SETSizeChoice (toaddress, setsize, AlignSize) = {
    return(__UNKNOWN_integer())
}

function SendEvent () = {
    return()
}

function SetAccumulatedFPExceptions accumulated_exceptions = {
    return()
}

function SetIss2 rs = {
    return()
}

function SetLoadStoreType instr = {
    return()
}

function SetTLBIncludesGPT (context, gpt_range) = {
    return()
}

function SoftwareStep_DidNotStep () = {
    return(__UNKNOWN_boolean())
}

function SoftwareStep_SteppedEX () = {
    return(__UNKNOWN_boolean())
}

function SpeculativeStoreBypassBarrierToPA () = {
    return()
}

function SpeculativeStoreBypassBarrierToVA () = {
    return()
}

function StartTrackingTransactionalReadsWrites () = {
    return()
}

function StateIsRecoverable () = {
    return(__UNKNOWN_boolean())
}

function StopInstructionPrefetchAndEnableITR () = {
    return()
}

function SynchronizeContext () = {
    return()
}

function SynchronizeErrors () = {
    return()
}

function TLBIncludesGPT context = {
    return(__UNKNOWN_boolean())
}

function VirtualFIQPending () = {
    return(__UNKNOWN_boolean())
}

function VirtualIRQPending () = {
    return(__UNKNOWN_boolean())
}

function WaitForEventUntilDelay (delay_enabled, delay) = {
    return(__UNKNOWN_boolean())
}

function _TLBInvalidate () = {
    return()
}

function getNumBreakpoints () = {
    return(__UNKNOWN_integer())
}

function getNumCtxBreakpoints () = {
    return(__UNKNOWN_integer())
}

function getNumWatchpoints () = {
    return(__UNKNOWN_integer())
}
