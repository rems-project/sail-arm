/******************************************************************************/
/*  BSD 3-clause Clear License                                                */
/*                                                                            */
/*  Copyright (c) 2022                                                        */
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

termination_measure Reduce__1(op,input,esize,altfp) = 'N

termination_measure BranchEncCycleCount
  while cc

termination_measure DiscardTransactionalWrites
  while __tm_wset_size
/* Actually
  while __tm_wset_next
but we don't support a register read there. */

termination_measure FloorPow2
  while x - pow2(n)

termination_measure ImplementedSVEVectorLength
  while nbits

termination_measure ImplementedSMEVectorLength
  while nbits, while maxbits - nbits

termination_measure RecipSqrtEstimate
  while pow2(28) - b

termination_measure FPRoundBase__1
  while RoundUp(Real(1) / mantissa), /* should be a base-2 log */
  while RoundUp(mantissa)

termination_measure FPRSqrtEstimate
  while 64 + exp

termination_measure AArch64_ChooseNonExcludedTag
  while 32 - UInt(tag), while UInt(offset), while 32 - UInt(tag)

termination_measure ChooseRandomNonExcludedTag
  while 32 - UInt(tag)

termination_measure FPLogB
  while RoundUp(Real(1) / value_name),
  while RoundUp(value_name)

termination_measure BFRound
  while RoundUp(Real(1) / mantissa), /* should be a base-2 log */
  while RoundUp(mantissa)

termination_measure execute_PNEXT_P_P_P__
  while elements - next

termination_measure execute_aarch64_instrs_memory_mcpymset_cpy
  while abs_int(SInt(stagecpysize)),
  while UInt(stagecpysize)
termination_measure execute_aarch64_instrs_memory_mcpymset_cpyf
  while abs_int(SInt(stagecpysize)),
  while UInt(stagecpysize)
termination_measure execute_aarch64_instrs_memory_mcpymset_set
  while abs_int(SInt(stagesetsize)),
  while UInt(stagesetsize)
termination_measure execute_aarch64_instrs_memory_mcpymset_setg
  while abs_int(SInt(stagesetsize)), while tagstep,
  while UInt(stagesetsize), while tagstep

/* Just put a limit in for now.  Probably 4 is more likely... */
termination_measure AArch64_S2Walk repeat 100
termination_measure AArch64_S2Translate repeat 100
termination_measure AArch64_S1Walk repeat 100
termination_measure AArch64_S1Translate repeat 100
termination_measure AArch32_S2Walk repeat 100
termination_measure AArch32_S1WalkLD repeat 100
termination_measure AArch32_S1WalkSD repeat 100

/* AArch64_TakeException (maybe unroll??) */
/* This is a cheat - it's a plain upper bound to break the cycle */
/*
termination_measure TakeUnmaskedPhysicalSErrorInterrupts(_) = 10
termination_measure TakePendingInterrupts(_) = 10
termination_measure AArch32_TakePhysicalFIQException() = 10
termination_measure AArch64_TakePhysicalFIQException() = 10
termination_measure AArch64_TakeException(_,_,_,_) = 10
termination_measure AArch32_TakePhysicalIRQException() = 10
termination_measure AArch64_TakePhysicalIRQException() = 10
termination_measure AArch32_TakePhysicalSErrorException(_,_,_,_) = 10
termination_measure AArch64_TakePhysicalSErrorException(_) = 10
termination_measure AArch32_TakeVirtualFIQException() = 10
termination_measure AArch64_TakeVirtualFIQException() = 10
termination_measure AArch32_TakeVirtualIRQException() = 10
termination_measure AArch64_TakeVirtualIRQException() = 10
termination_measure AArch32_TakeVirtualSErrorException(_,_,_) = 10
termination_measure AArch64_TakeVirtualSErrorException(_) = 10
*/
