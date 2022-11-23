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

function ThisInstr () = __ThisInstr
function ThisInstrLength () = match __ThisInstrEnc {
  __T16 => 16,
  _ => 32
}
function ThisInstrAddr N = Slice(_PC, 0, N)
function NextInstrAddr N = ThisInstrAddr(N) + DIV(ThisInstrLength(), 8)

val __SetThisInstrEnc : __InstrEnc -> unit

function __SetThisInstrEnc(enc) = {
  __ThisInstrEnc = enc
}

val __FetchNextInstr : unit -> (__InstrEnc, bits(32))

function __FetchNextInstr() = {
  match CurrentInstrSet() {
    InstrSet_A32 => {
      AArch32_CheckPCAlignment();
      AArch32_CheckIllegalState();
      (__A32, AArch32_MemSingle_read(PC_read()[31 .. 0], 4, AccType_IFETCH, true))
    },
    InstrSet_T32 => {
      AArch32_CheckPCAlignment();
      AArch32_CheckIllegalState();
      // Read a half-word first
      let hw1 = AArch32_MemSingle_read(PC_read()[31 .. 0], 2, AccType_IFETCH, true);
      // Check the upper 5 bits to distinguish between T32 and T16,
      // following F3.1 of ARM DDI 0487I.a
      if (hw1[15 .. 13] == 0b111 & hw1[12 .. 11] != 0b00) then {
        let hw2 = AArch32_MemSingle_read(PC_read()[31 .. 0] + 2, 2, AccType_IFETCH, true);
        (__T32, hw1 @ hw2)
      } else {
        (__T16, ZeroExtend(hw1, 32))
      }
    },
    InstrSet_A64 => {
      AArch64_CheckPCAlignment();
      AArch64_CheckIllegalState();
      (__A64, AArch64_MemSingle_read(PC_read(), 4, AccType_IFETCH, true))
    }
  }
}
