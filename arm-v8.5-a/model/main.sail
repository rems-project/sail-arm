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

$include <elf.sail>
$include <trace.sail>

val "get_time_ns" : unit -> int

val "cycle_count" : unit -> unit

val read_register = "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

//             EL1 physical        EL2 physical        EL3 physical        EL1 virtual,       EL2 virtual
let CNT_CVAL = [ref CNTP_CVAL_EL0, ref CNTHP_CVAL_EL2, ref CNTPS_CVAL_EL1, ref CNTV_CVAL_EL0, ref CNTHV_CVAL_EL2]
let CNT_TVAL = [ref CNTP_TVAL_EL0, ref CNTHP_TVAL_EL2, ref CNTPS_TVAL_EL1, ref CNTV_TVAL_EL0, ref CNTHV_TVAL_EL2]
let CNT_CTL  = [ref CNTP_CTL_EL0,  ref CNTHP_CTL_EL2,  ref CNTPS_CTL_EL1,  ref CNTV_CTL_EL0,  ref CNTHV_CTL_EL2 ]
let CNT_IRQ  = [0x0000_beef,       0x0000_cafe,        0x0000_fee1,        0x0000_000b,       0x0000_dead       ]
//                                                     No IRQ

// SGI Interrupts are 0-15, PPI interrupts are 16-31, and SPI interrupts have an offset of 32.
let PPI_OFFSET = 16

register startTime : int
register instCount : int

let ISTATUS = 0x0000_0004
let IMASK = 0x0000_0002

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem, configuration}

function fetch_and_execute () = {
  while true do {
    // print_bits("PC = ", _PC);

    var prevEL = PSTATE.EL;
    var prevI = PSTATE.I;

    // if (instCount == 1000000) then {
    //   endTime = get_time_ns();
    //   elapsed = endTime - startTime;
    //   inst_1e9 = instCount * 1000000000;
    //   ips = inst_1e9 / elapsed;
    //   print_int("*IPS*: ", ips);
    //   startTime = get_time_ns();
    //   instCount = 0;
    // };
    // instCount = instCount + 1;

    try {
      // Increment the counter
      CNTPCT_EL0 = CNTPCT_EL0 + 1;
      CNTVCT_EL0 = CNTPCT_EL0 - CNTVOFF_EL2;

      // Timer value view for each timer
      foreach (timer from 0 to 4) {
	let CTL = CNT_CTL[timer];
	let ctl = read_register(CTL);

	// If the timer is enabled
	if ctl[0] == bitone then {
	  let TVAL = CNT_TVAL[timer];
	  let nextTVAL = read_register(TVAL) - 1;
	  (*TVAL) = nextTVAL;

	  // If the timer condition is met
	  if nextTVAL == 0x0000_0000 then {
	    prerr_int("[Clock] Tick (TVAL) ", timer);
	    (*CTL) = ctl | ISTATUS // Set the ISTATUS bit
	  };

	  if SInt(nextTVAL) <= 0 then {
	     /* IMASK unset         interrupts unmasked */
	     if ctl[1] == bitzero & PSTATE.I == bitzero then {
	       __GIC_Pending = CNT_IRQ[timer] + PPI_OFFSET;
	       prerr_bits("[Clock] GIC interrupt ", __GIC_Pending);
	       _IRQPending = true;
	       AArch64_TakePhysicalIRQException()
	     }
	  } else {
	    (*CTL) = ctl & ~(ISTATUS)
	  }
	}
      };

      // // Handle the Kernel event stream, if enabled by CNTKCTL_EL1[2].
      // if CNTKCTL_EL1[2] == bitone then {
      // 	let mask = LSL(ZeroExtend(0x1, 64), UInt(CNTKCTL_EL1[7 .. 4]));

      //   // Trigger event stream on either rising bit (0-1, bitzero) or falling (1-0, bitone)
      //   let trigger : bool = if CNTKCTL_EL1[3] == bitzero then {
      //     ((CNTVCT_EL0 - 1) & mask) == Zeros() & (CNTVCT_EL0 & mask) != Zeros()
      //   } else {
      //     ((CNTVCT_EL0 - 1) & mask) != Zeros() & (CNTVCT_EL0 & mask) == Zeros()
      //   };

      // 	if trigger & PSTATE.I == bitzero then {
      // 	  prerr("[Clock] Tick\n");
      // 	  __GIC_Pending = 0x0000_000b + PPI_OFFSET; // This might not be 0x000a...
      // 	  CNTV_CTL_EL0 = CNTV_CTL_EL0 | ISTATUS;
      //     _IRQPending = true;
      //     AArch64_TakePhysicalIRQException()
      //   }
      // };

      // // Handle the Hypervisor event stream, if enabled by CNTHCTL_EL2[2].
      // if CNTHCTL_EL2[2] == bitone then {
      // 	let mask = LSL(ZeroExtend(0x1, 64), UInt(CNTHCTL_EL2[7 .. 4]));

      //   // Trigger event stream on either rising bit (0-1, bitzero) or falling (1-0, bitone)
      //   let trigger : bool = if CNTHCTL_EL2[3] == bitzero then {
      //     ((CNTPCT_EL0 - 1) & mask) == Zeros() & (CNTPCT_EL0 & mask) != Zeros()
      //   } else {
      //     ((CNTPCT_EL0 - 1) & mask) != Zeros() & (CNTPCT_EL0 & mask) == Zeros()
      //   };

      // 	if trigger & PSTATE.I == bitzero then {
      // 	  prerr("[Clock] Tick\n");
      // 	  __GIC_Pending = 0x0000_000a + PPI_OFFSET;
      //     _IRQPending = true;
      //     AArch64_TakePhysicalIRQException()
      //   }
      // };

      // Store the old values of the Counter-timer Kernel/Hypervisor Control
      // registers, as we want to figure out when they changes.
      var prevCNTKCTL_EL1 = CNTKCTL_EL1;
      var prevCNTHCTL_EL2 = CNTHCTL_EL2;

      __currentInstr = __fetchA64();
      // print_bits("__currentInstr = ", __currentInstr);

      // Use a magic instruction to kill the simulator in init
      if __currentInstr == 0xFEE1DEAD then {
	 print("[Sail] Finished Successfully!\n");
	 exit()
      };

      __PC_changed = false;
      ShouldAdvanceIT = (PSTATE.nRW == [bitone]) & (PSTATE.T == [bitone]);
      decode(__currentInstr);
      if ~(__PC_changed) then _PC = _PC + 4 else ();
      if ShouldAdvanceIT then AArch32_ITAdvance() else ();
      SSAdvance();
      __UpdateSystemCounter()

    } catch {
      Error_See(str) if str == "HINT" => (),
      Error_ExceptionTaken(_) => {
	() // prerr_bits("[Sail] Exception taken to ", _PC);
      },
      Error_See(str) => {
	print("[Sail] Failed: See " ++ str ++ "\n");
	print_bits("[Sail] Current instruction: ", __currentInstr);
	exit()
      },
      Error_Undefined(_) => {
	print("[Sail] Failed: Undefined\n");
	print_bits("[Sail] Current instruction: ", __currentInstr);
	exit()
      },
      Error_Implementation_Defined(msg) => {
	prerr("Implementation defined " ++ msg ++ "\n");
      },
      Error_ReservedEncoding(_) => {
	prerr("ReservedEncoding\n");
      }
    };
    // We want to keep track of what exception level we are in for debugging purposes.
    if UInt(prevEL) > UInt(PSTATE.EL) then {
      prerr_bits("[Sail] Exception level dropped to: ", PSTATE.EL);
      prerr_bits("[Sail] _PC is ", _PC)
    };
    if prevI != PSTATE.I then {
      () //prerr_bits("[Sail] PSTATE.I changed to: ", PSTATE.I);
    };

    if __GIC_Pending == 0x0000_03ff then _IRQPending = false else ();
    __EndCycle();
    cycle_count();
  }
}

let BOOTLOADER : string = "bootloader.bin"
let KERNEL : string = "Image"
let DTB : string = "sail.dtb"

let COLD_RESET : bool = true

// Values for the floating point and ASIMD fields of the AA64PFR0 feature register
let FPSIMD = 0b0000 // Floating point and ASMID are implemented
let FPSIMD_WITH_HALF_PRECISION = 0b0001 // Floating point/ASMID with half-precision
let NO_FPSIMD = 0b1111 // Floating point and ASIMD are not implemented

let SVE = 0b0001
let NO_SVE = 0b0000

let RAS = 0b0001
let NO_RAS = 0b0000

val "load_raw" : (bits(64), string) -> unit

val init : unit -> unit effect {escape, undef, rreg, wreg, configuration}

function init() = {
  init_devices();
  __currentInstrLength = 4;
  print("Resetting\n");
  TakeReset(COLD_RESET);

  // Set the feature register. We want to disable as many features as
  // we can get away with, and make sure that everything is AArch64
  // only.
  ID_AA64PFR0_EL1[35 .. 32] = NO_SVE;
  ID_AA64PFR0_EL1[31 .. 28] = NO_RAS; // No RAS Extension
  ID_AA64PFR0_EL1[27 .. 24] = 0b0000; // No System register interface to the GIC is supported

  ID_AA64PFR0_EL1[23 .. 20] = NO_FPSIMD;
  ID_AA64PFR0_EL1[19 .. 16] = NO_FPSIMD;
  ID_AA64PFR0_EL1[15 .. 12] = 0b0001; // EL3 can be executed in AArch64 state only
  ID_AA64PFR0_EL1[11 .. 8] = 0b0001; // EL2 can be executed in AArch64 state only
  ID_AA64PFR0_EL1[7 .. 4] = 0b0001; // EL1 can be executed in AArch64 state only
  ID_AA64PFR0_EL1[3 .. 0] = 0b0001; // EL0 can be executed in AArch64 state only

  foreach (timer from 0 to 4 by 1 in inc) {
    let CTL = CNT_CTL[timer];
    (*CTL) = ZeroExtend(0x0, 32)
  };

  let bootloader = ZeroExtend(0x8000_0000, 64);
  let dtb = ZeroExtend(0x8100_0000, 64);
  let kernel = ZeroExtend(0x8208_0000, 64);
  load_raw(bootloader, BOOTLOADER);
  load_raw(dtb, DTB);
  load_raw(kernel, KERNEL);
  _PC = bootloader;
}

val main : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem, configuration}

function main() = {
  init();
  startTime = get_time_ns();
  fetch_and_execute()
}