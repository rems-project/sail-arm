// Keep GPRs at their original values.

val AArch64_ResetGeneralRegisters : unit -> unit
function AArch64_ResetGeneralRegisters () = ()

val AArch32_ResetGeneralRegisters : unit -> unit
function AArch32_ResetGeneralRegisters () = ()

// Avoid a Constrained Unpredictable choice in the SIMD reset.

val AArch64_ResetSIMDFPRegisters : unit -> unit
function AArch64_ResetSIMDFPRegisters () = ()

val AArch32_ResetSIMDFPRegisters : unit -> unit
function AArch32_ResetSIMDFPRegisters () = ()


val isla_reset_registers = "reset_registers" : unit -> unit

val isla_main_hook : unit -> unit

function isla_main_hook() = {
    _PC = elf_entry()[63 .. 0];
    SP_EL0 = ZeroExtend(0x3C00, 64);
    PSTATE.EL = EL0;
    PSTATE.PAN = 0b0;
    __emulator_termination_opcode = Some(0x00000000);
    isla_reset_registers();
}
