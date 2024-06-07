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

// InitFeatureImpl has to come before TakeReset, if used, but also
// appear if it isn't.  Hence we have two entry points - one that just
// calls that, and one that does a reset too, and then a common function
// for the actual execution.

val isla_reset_registers = "reset_registers" : unit -> unit

val isla_footprint_common : bits(32) -> bool effect {configuration, escape, rmem, rreg, undef, wmem, wreg}

function isla_footprint_common(opcode) = {
  SEE = -1;
  DBGEN = Signal_Low;

  isla_reset_registers();

  __ThisInstr = opcode;
  __ThisInstrEnc = __A64;

  // The first cycle during footprint analysis is reserved for initialization, and ignored.
  check_cycle_count();
  try {
    __DecodeA64(UInt(_PC), opcode);
    true
  } catch {
    _ => false
  }
}

val isla_footprint_no_init : bits(32) -> bool effect {configuration, escape, rmem, rreg, undef, wmem, wreg}

function isla_footprint_no_init(opcode) = {
  InitFeatureImpl();
  isla_footprint_common(opcode)
}

val isla_footprint : bits(32) -> bool effect {configuration, escape, rmem, rreg, undef, wmem, wreg}

function isla_footprint(opcode) = {
  __highest_el_aarch32 = false;
  InitFeatureImpl();
  TakeReset(COLD_RESET);
  AArch64_ResetGeneralRegisters();
  PSTATE.EL = EL0;
  PSTATE.SP = 0b0;

  isla_footprint_common(opcode)
}
