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

$include <elf.sail>

let COLD_RESET : bool = true

val main : unit -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

val get_cycle_count = { c: "get_cycle_count" } : unit -> int effect {undef, wreg, rreg, rmem, wmem}
val check_cycle_count = { c: "cycle_count" } : unit -> unit
val __GetVerbosity = {c: "sail_get_verbosity"}: unit -> bits(64) effect {rreg, undef}

val step_model : unit -> unit effect {escape}

function step_model() = {
  SEE = -1;
  __TopLevel();
  __CycleEnd();
  ()
}

// Hook for Isla to do extra initialisation
val isla_main_hook : unit -> unit
function isla_main_hook() = ()

function main() = {
  try {
    let verbosity = __GetVerbosity();
    __InitSystem();
    isla_main_hook();
    check_cycle_count();
    while true do {
      if verbosity[0] == bitone then {
          nzcv = (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V);
          print(concat_str("[Sail] ",
                concat_str(DecStr(get_cycle_count()),
                concat_str(" PC=",
                concat_str(HexStr(UInt(_PC)),
                concat_str(" NZCV=",
                concat_str(HexStr(UInt(nzcv)),
                "\n")))))));
      };
      step_model();
      if verbosity[1] == bitone then {
          print(concat_str("[Sail] Instr=",
                concat_str(HexStr(UInt(__ThisInstr)),
                concat_str(" ESR_EL3=",
                concat_str(HexStr(UInt(ESR_EL3.bits)),
                concat_str(if __BranchTaken then " branch taken" else "",
                "\n"))))));
      };
      check_cycle_count();
    }
  } catch {
    Error_ImplementationDefined(s) => {
      print(concat_str("Unsupported implementation defined behaviour: ", s));
    }
  }
}
