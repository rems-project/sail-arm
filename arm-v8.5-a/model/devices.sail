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

register configuration __DEBUG_WRITE : bool = false

val "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)
val "zeros" : forall 'n. atom('n) -> bits('n)

val highest_set_bit : forall ('n : Int), 'n >= 0. bits('n) -> int

function highest_set_bit x = {
  foreach (i from ('n - 1) to 0 by 1 in dec) {
    if [x[i]] == 0b1 then return(i) else ()
  };
  return(negate(1))
}

let UART_BASE = 0x3c00

let GIC_BASE = 0x2c00

// Interrupt Controller Type Register
//                                  SecurityExtn  CPUNumber       ITLinesNumber
// let GICD_TYPER = [zeros(32) with 10 = bitzero, 7 .. 5 = 0b000, 4 .. 0 = 0b00111]
let GICD_TYPER = [[zeros(32) with 10 .. 10 = 0b1] with 4 .. 0 = 0b00111]

// CPU Interface Control Register
register {rmem} {wmem} GICC_CTLR : bits(32)

// CPU Interface Identification Register
// 0x0002 = GICv2, 0x043B = Pretend to be ARM implementation (JEP106 code).
let GICC_IIDR = 0x0002_043B

function gic_readonly(addr : bits(56)) -> unit = {
  prerr_bits("[GIC] Read from RO addr: ", addr);
}

register {rmem} pure __GIC_Pending : bits(32)

val ___WriteRAM_bool = "write_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> bool effect {wmem}

val ___WriteRAM : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit effect {wmem}

function ___WriteRAM(a, b, c, d, e) = {
  let _: bool = ___WriteRAM_bool(a, b, c, d, e);
  ()
}

val __InitRAM : forall 'm. (atom('m), int, bits('m), bits(8)) -> unit

function __InitRAM (_, _, _, _) = ()

val ___ReadRAM = "read_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

// gic_ram() simply forwards a request for a GIC address to memory.
function gic_ram(offset : bits(16)) -> bits(32) =
{
  ___ReadRAM(56, 4, zeros(56), zero_extend(GIC_BASE @ offset, 56))
}

function HighestPendingInterrupt(() : unit) -> bits(32) = {
  let intID = __GIC_Pending;
  __GIC_Pending = 0x0000_03ff;
  intID
}

val __ReadRAM : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

function __ReadRAM(addr_length, bytes, hex_ram, addr) =
{
  // Reading from the GIC
  if constraint('m == 56 & 'n == 4) & addr[31 .. 16] == GIC_BASE then {
    match addr[15 .. 0] {
      // ***** Distributor Interface *****
      0x1004 => GICD_TYPER,

      // Send all interrupts to CPU interface 0
      0x1800 => 0xffffffff,

      0x1C04 => {
	prerr_bits("[GIC] Read 1C04: ", gic_ram(0x1C04));
	gic_ram(0x1C04) // Linux timer
      },

      // ***** CPU Interface 0 *****
      0x2000 => {
	prerr_bits("[GIC] Read GICC_CTLR ", GICC_CTLR);
	GICC_CTLR
      },
      0x200C => {
	 prerr_bits("[GIC] Request for highest pending interrupt ", __GIC_Pending);
	 HighestPendingInterrupt()
      },
      0x20FC => GICC_IIDR,

      _ => {
	prerr_bits("[GIC] Read addr: ", addr);
	zeros(32)
      }
    }
  // Reading from the UART
  } else if constraint('m == 56) & addr[31 .. 16] == UART_BASE then {
    match addr[15 .. 0] {
      _ => {
	prerr_bits("[UART] Unknown read address: ", addr);
	zeros(8 * 'n)
      }
    }
  } else {
    ___ReadRAM(addr_length, bytes, hex_ram, addr)
  }
}

val __TraceMemoryWrite : forall 'n 'm.
  (atom('n), bits('m), bits(8 * 'n)) -> unit

val __WriteRAM : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit effect {wmem}

function __WriteRAM(addr_length, bytes, hex_ram, addr, data) =
{
  // Writing to the GIC
  if constraint('m == 56 & 'n == 4) & addr[31 .. 16] == GIC_BASE then {
    match addr[15 .. 0] {
      // ***** Distributor Interface *****
      0x1004 => gic_readonly(addr),

      0x1100 => {
	prerr_bits("[GIC] Registering interrupts ", data);
	let intID = highest_set_bit(data);
	prerr_int("[GIC] Registering interrupt ", intID)
      },

      0x1800 => gic_readonly(addr),

      // ***** CPU Interface 0 *****
      0x2000 => {
	prerr_bits("[GIC] GICC_CTLR = ", data);
	GICC_CTLR = data
      },
      0x200C => gic_readonly(addr),
      0x20FC => gic_readonly(addr),

      0x2010 => {
	prerr_bits("[GIC] End of interrupt = ", data);
	__GIC_Pending = 0x0000_03ff
      },

      0x3000 => {
	prerr("[GIC] Deactivating interrupt\n");
	__GIC_Pending = 0x0000_03ff
      },

      // We don't exhaustivly model the GIC, so log and forward unrecognised writes to memory
      _ => {
	prerr_bits("[GIC] Unknown write address: ", addr);
	prerr_bits("[GIC] Unknown write data: ", data);
	___WriteRAM(addr_length, bytes, hex_ram, addr, data)
      }
    }
  // Writing to the UART
  } else if constraint('m == 56) & addr[31 .. 16] == UART_BASE then {
    match addr[15 .. 0] {
      0x0000 => {
	putchar(UInt(data[7 .. 0]));
      },

      _ => {
	prerr_bits("[UART] Unknown write address: ", addr);
	prerr_bits("[UART] Unknown write data: ", data);
      }
    }
  // Otherwise write to RAM
  } else {
    ___WriteRAM(addr_length, bytes, hex_ram, addr, data)
  }
}

function __TraceMemoryWrite(bytes, addr, data) =
{
  if constraint('m == 56) then {
    if UInt(addr) >= UInt(0x8ffffffff) then {
      print_bits("above mem: ", addr);
    }
  } else {
    print("ADDR LENGTH NOT 56")
  };

  if constraint('n == 1) & __DEBUG_WRITE then {
    let char = UInt(data);
    if (32 <= char & char <= 126) | char == 10 then {
       putchar(UInt(data))
    }
  }
}

val __TraceMemoryRead : forall 'n 'm. (atom('n), bits('m), bits(8 * 'n)) -> unit

function __TraceMemoryRead(bytes, addr, data) =
{
  if constraint('m == 56) then {
    if addr[31 .. 16] == 0x3c00 then {
      match addr[15 .. 0] {
	0x0018 => (),
	_ => {
	  print_bits("uart read: ", addr)
	}
      }
    } else if UInt(addr) > UInt(0x8ffffffff) then {
      print_bits("above mem: ", addr)
    }
  } else {
    print("ADDR LENGTH NOT 56")
  }
}

val init_devices : unit -> unit effect {configuration}

function init_devices() =
{
  __DEBUG_WRITE = false;
  __GIC_Pending = 0x0000_03ff
}