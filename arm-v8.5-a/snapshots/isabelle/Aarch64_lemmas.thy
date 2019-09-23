theory Aarch64_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Aarch64
begin

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_def set_regval_def CNTHCTL_EL2_ref_def CPTR_EL2_ref_def
  CCSIDR_EL1_ref_def ACTLR_EL1_ref_def ACTLR_EL2_ref_def ACTLR_EL3_ref_def AFSR0_EL1_ref_def
  AFSR0_EL2_ref_def AFSR0_EL3_ref_def AFSR1_EL1_ref_def AFSR1_EL2_ref_def AFSR1_EL3_ref_def
  AIDR_EL1_ref_def AMAIR_EL1_ref_def AMAIR_EL2_ref_def AMAIR_EL3_ref_def APDAKeyHi_EL1_ref_def
  APDAKeyLo_EL1_ref_def APDBKeyHi_EL1_ref_def APDBKeyLo_EL1_ref_def APGAKeyHi_EL1_ref_def
  APGAKeyLo_EL1_ref_def APIAKeyHi_EL1_ref_def APIAKeyLo_EL1_ref_def APIBKeyHi_EL1_ref_def
  APIBKeyLo_EL1_ref_def BTypeCompatible_ref_def BTypeNext_ref_def CCSIDR2_EL1_ref_def
  CLIDR_EL1_ref_def CNTFRQ_EL0_ref_def CNTHPS_CTL_EL2_ref_def CNTHPS_CVAL_EL2_ref_def
  CNTHPS_TVAL_EL2_ref_def CNTHP_CTL_EL2_ref_def CNTHP_CVAL_EL2_ref_def CNTHP_TVAL_EL2_ref_def
  CNTHVS_CTL_EL2_ref_def CNTHVS_CVAL_EL2_ref_def CNTHVS_TVAL_EL2_ref_def CNTHV_CTL_EL2_ref_def
  CNTHV_CVAL_EL2_ref_def CNTHV_TVAL_EL2_ref_def CNTKCTL_EL1_ref_def CNTPCT_EL0_ref_def
  CNTPS_CTL_EL1_ref_def CNTPS_CVAL_EL1_ref_def CNTPS_TVAL_EL1_ref_def CNTP_CTL_EL0_ref_def
  CNTP_CTL_S_ref_def CNTP_CVAL_EL0_ref_def CNTP_TVAL_EL0_ref_def CNTVCT_EL0_ref_def
  CNTVOFF_EL2_ref_def CNTV_CTL_EL0_ref_def CNTV_CVAL_EL0_ref_def CNTV_TVAL_EL0_ref_def
  CPACR_EL1_ref_def CPTR_EL3_ref_def CSSELR_EL1_ref_def CSSELR_S_ref_def CTR_EL0_ref_def
  DBGAUTHSTATUS_EL1_ref_def DBGCLAIMCLR_EL1_ref_def DBGCLAIMSET_EL1_ref_def DBGDEVID1_ref_def
  DBGDEVID2_ref_def DBGDSCRint_ref_def DBGDTRRX_EL0_ref_def DBGDTRTX_EL0_ref_def DBGDTR_EL0_ref_def
  DBGWFAR_ref_def DCZID_EL0_ref_def DISR_EL1_ref_def EDECCR_ref_def EDECR_ref_def EDESR_ref_def
  EDLSR_ref_def EDPCSR_ref_def EDPFR_ref_def EDPRCR_ref_def EDPRSR_ref_def EDVIDSR_ref_def
  ELR_EL0_ref_def ESP_EL0_ref_def ESR_EL0_ref_def EventRegister_ref_def FAR_EL0_ref_def
  FCSEIDR_ref_def FPCR_ref_def FPEXC32_EL2_ref_def FPSCR_ref_def FPSID_ref_def FPSR_ref_def
  GCR_EL1_ref_def HACR_EL2_ref_def HSTR_EL2_ref_def ICC_AP0R_EL1_ref_def ICC_AP1R_EL1_ref_def
  ICC_ASGI1R_EL1_ref_def ICC_BPR0_EL1_ref_def ICC_BPR1_EL1_NS_ref_def ICC_BPR1_EL1_S_ref_def
  ICC_CTLR_EL1_NS_ref_def ICC_CTLR_EL1_S_ref_def ICC_CTLR_EL3_ref_def ICC_DIR_EL1_ref_def
  ICC_EOIR0_EL1_ref_def ICC_EOIR1_EL1_ref_def ICC_HPPIR0_EL1_ref_def ICC_HPPIR1_EL1_ref_def
  ICC_IAR0_EL1_ref_def ICC_IAR1_EL1_ref_def ICC_IGRPEN0_EL1_ref_def ICC_IGRPEN1_EL1_NS_ref_def
  ICC_IGRPEN1_EL1_S_ref_def ICC_IGRPEN1_EL3_ref_def ICC_PMR_EL1_ref_def ICC_RPR_EL1_ref_def
  ICC_SGI0R_EL1_ref_def ICC_SGI1R_EL1_ref_def ICC_SRE_EL1_NS_ref_def ICC_SRE_EL1_S_ref_def
  ICC_SRE_EL2_ref_def ICC_SRE_EL3_ref_def ICH_AP0R_EL2_ref_def ICH_AP1R_EL2_ref_def
  ICH_EISR_EL2_ref_def ICH_ELRSR_EL2_ref_def ICH_HCR_EL2_ref_def ICH_MISR_EL2_ref_def
  ICH_VMCR_EL2_ref_def ICH_VTR_EL2_ref_def ICV_AP0R_EL1_ref_def ICV_AP1R_EL1_ref_def
  ICV_BPR0_EL1_ref_def ICV_BPR1_EL1_ref_def ICV_CTLR_EL1_ref_def ICV_DIR_EL1_ref_def
  ICV_EOIR0_EL1_ref_def ICV_EOIR1_EL1_ref_def ICV_HPPIR0_EL1_ref_def ICV_HPPIR1_EL1_ref_def
  ICV_IAR0_EL1_ref_def ICV_IAR1_EL1_ref_def ICV_IGRPEN0_EL1_ref_def ICV_IGRPEN1_EL1_ref_def
  ICV_PMR_EL1_ref_def ICV_RPR_EL1_ref_def ID_AA64AFR0_EL1_ref_def ID_AA64AFR1_EL1_ref_def
  ID_AA64DFR1_EL1_ref_def ID_AA64ISAR0_EL1_ref_def ID_AA64ISAR1_EL1_ref_def ID_AA64MMFR0_EL1_ref_def
  ID_AA64MMFR1_EL1_ref_def ID_AA64MMFR2_EL1_ref_def ID_AA64PFR0_EL1_ref_def ID_AA64PFR1_EL1_ref_def
  ID_AFR0_EL1_ref_def ID_DFR0_EL1_ref_def ID_ISAR0_EL1_ref_def ID_ISAR1_EL1_ref_def
  ID_ISAR2_EL1_ref_def ID_ISAR3_EL1_ref_def ID_ISAR4_EL1_ref_def ID_ISAR5_EL1_ref_def
  ID_ISAR6_EL1_ref_def ID_MMFR0_EL1_ref_def ID_MMFR1_EL1_ref_def ID_MMFR2_EL1_ref_def
  ID_MMFR3_EL1_ref_def ID_MMFR4_EL1_ref_def ID_PFR0_EL1_ref_def ID_PFR1_EL1_ref_def
  ID_PFR2_EL1_ref_def ISR_EL1_ref_def LORC_EL1_ref_def LOREA_EL1_ref_def LORID_EL1_ref_def
  LORN_EL1_ref_def LORSA_EL1_ref_def MDCCINT_EL1_ref_def MDCCSR_EL0_ref_def MDRAR_EL1_ref_def
  MIDR_EL1_ref_def MVFR0_EL1_ref_def MVFR1_EL1_ref_def MVFR2_EL1_ref_def NSACR_ref_def
  OSDTRRX_EL1_ref_def OSDTRTX_EL1_ref_def OSECCR_EL1_ref_def OSLAR_EL1_ref_def PAR_EL1_ref_def
  PAR_S_ref_def PMCCFILTR_EL0_ref_def PMCCNTR_EL0_ref_def PMCEID0_EL0_ref_def PMCEID1_EL0_ref_def
  PMCNTENCLR_EL0_ref_def PMCNTENSET_EL0_ref_def PMCR_EL0_ref_def PMEVCNTR_EL0_ref_def
  PMEVTYPER_EL0_ref_def PMINTENCLR_EL1_ref_def PMINTENSET_EL1_ref_def PMLSR_ref_def PMMIR_ref_def
  PMMIR_EL1_ref_def PMOVSCLR_EL0_ref_def PMOVSSET_EL0_ref_def PMPCSR_ref_def PMSELR_EL0_ref_def
  PMSWINC_EL0_ref_def PMUSERENR_EL0_ref_def PMVIDSR_ref_def PMXEVCNTR_EL0_ref_def
  PMXEVTYPER_EL0_ref_def RC_ref_def RD_EL0_ref_def REVIDR_EL1_ref_def RGSR_EL1_ref_def
  RMR_EL1_ref_def RMR_EL2_ref_def RMR_EL3_ref_def RMUID_EL0_ref_def RNDR_ref_def RNDRRS_ref_def
  RVBAR_ref_def RVBAR_EL1_ref_def RVBAR_EL2_ref_def RVBAR_EL3_ref_def SCXTNUM_EL0_ref_def
  SCXTNUM_EL1_ref_def SCXTNUM_EL2_ref_def SCXTNUM_EL3_ref_def SDER32_EL2_ref_def SPSR_EL0_ref_def
  SP_EL0_ref_def SP_EL1_ref_def SP_EL2_ref_def SP_EL3_ref_def ShouldAdvanceIT_ref_def TLBTR_ref_def
  TPIDRRO_EL0_ref_def TPIDR_EL0_ref_def TPIDR_EL1_ref_def TPIDR_EL2_ref_def TPIDR_EL3_ref_def
  TRFCR_EL1_ref_def TRFCR_EL2_ref_def VBAR_EL0_ref_def VDISR_EL2_ref_def VMPIDR_EL2_ref_def
  VNCR_EL2_ref_def VPIDR_EL2_ref_def V_ref_def currentCond_ref_def exclusive_block_address_ref_def
  saved_exception_level_ref_def unconditional_ref_def CONTEXTIDR_S_ref_def GTEExtObsAccess_ref_def
  GTEExtObsAddress_ref_def GTEExtObsData_ref_def GTEExtObsResult_ref_def GTEExtObsActive_ref_def
  GTEExtObsCount_ref_def GTEExtObsIndex_ref_def GTEExtObsResultIndex_ref_def
  GTEExtObsResultIsAddress_ref_def GTEListParam0_ref_def GTEListParam1_ref_def GTEParam_ref_def
  GTE_AS_RecordedAccess_ref_def GTE_AS_RecordedAddress_ref_def GTE_AS_RecordedData_ref_def
  GTE_PPU_Access_ref_def GTE_PPU_Address_ref_def GTE_PPU_SizeEn_ref_def AbortRgn64Hi1_ref_def
  AbortRgn64Hi1_Hi_ref_def AbortRgn64Hi2_ref_def AbortRgn64Hi2_Hi_ref_def AbortRgn64Lo1_ref_def
  AbortRgn64Lo1_Hi_ref_def AbortRgn64Lo2_ref_def AbortRgn64Lo2_Hi_ref_def CNTCR_ref_def
  CNTCV_ref_def CNTFID0_ref_def CNTSR_ref_def CONTEXTIDR_EL1_ref_def CONTEXTIDR_EL2_ref_def
  DACR32_EL2_ref_def DACR_S_ref_def DBGBCR_ref_def DBGBCR_EL1_ref_def DBGBVR_ref_def
  DBGBVR_EL1_ref_def DBGBXVR_ref_def DBGDIDR_ref_def DBGEN_ref_def DBGPRCR_EL1_ref_def
  DBGVCR32_EL2_ref_def DBGWCR_ref_def DBGWCR_EL1_ref_def DBGWVR_ref_def DBGWVR_EL1_ref_def
  DLR_EL0_ref_def DSPSR_EL0_ref_def EDSCR_ref_def DFSR_S_ref_def ELR_EL3_ref_def ELR_EL1_ref_def
  ESR_EL3_ref_def ESR_EL1_ref_def ELR_EL2_ref_def TCR_EL2_ref_def ESR_EL2_ref_def FAR_EL1_ref_def
  FAR_EL2_ref_def FAR_EL3_ref_def HCR_EL2_ref_def HPFAR_EL2_ref_def ID_AA64DFR0_EL1_ref_def
  IFSR32_EL2_ref_def IFSR_S_ref_def InGuardedPage_ref_def LR_mon_ref_def MAIR0_S_ref_def
  MAIR1_S_ref_def MAIR_EL1_ref_def MAIR_EL2_ref_def MAIR_EL3_ref_def MDCR_EL2_ref_def
  MDCR_EL3_ref_def MDSCR_EL1_ref_def MPAM0_EL1_ref_def MPAM1_EL1_ref_def MPAM2_EL2_ref_def
  MPAM3_EL3_ref_def MPAMHCR_EL2_ref_def MPAMIDR_EL1_ref_def MPAMVPM0_EL2_ref_def
  MPAMVPM1_EL2_ref_def MPAMVPM2_EL2_ref_def MPAMVPM3_EL2_ref_def MPAMVPM4_EL2_ref_def
  MPAMVPM5_EL2_ref_def MPAMVPM6_EL2_ref_def MPAMVPM7_EL2_ref_def MPAMVPMV_EL2_ref_def
  MPIDR_EL1_ref_def MVBAR_ref_def NMRR_S_ref_def OSDLR_EL1_ref_def OSLSR_EL1_ref_def PRRR_S_ref_def
  PSTATE_ref_def SCR_EL3_ref_def SCTLR_EL1_ref_def SCTLR_EL2_ref_def SCTLR_EL3_ref_def
  SCTLR_S_ref_def SDER32_EL3_ref_def SPIDEN_ref_def SPSR_EL1_ref_def SPSR_EL2_ref_def
  SPSR_EL3_ref_def SPSR_abt_ref_def SPSR_fiq_ref_def SPSR_irq_ref_def SPSR_und_ref_def
  SP_mon_ref_def ScheduledFIQ_ref_def ScheduledIRQ_ref_def TCR_EL1_ref_def TCR_EL3_ref_def
  TFSRE0_EL1_ref_def TFSR_EL1_ref_def TFSR_EL2_ref_def TFSR_EL3_ref_def TLBHits_ref_def
  TLBMisses_ref_def TTBCR2_S_ref_def TTBCR_S_ref_def TTBR0_EL1_ref_def TTBR0_EL2_ref_def
  TTBR0_EL3_ref_def TTBR0_S_ref_def TTBR1_EL1_ref_def TTBR1_EL2_ref_def TTBR1_S_ref_def
  VBAR_EL1_ref_def VBAR_EL2_ref_def VBAR_EL3_ref_def VBAR_S_ref_def VSESR_EL2_ref_def
  VSTCR_EL2_ref_def VSTTBR_EL2_ref_def VTCR_EL2_ref_def VTTBR_EL2_ref_def AXIAbortCtl_ref_def
  ClearFIQ_ref_def ClearIRQ_ref_def FIQPending_ref_def GTEActive_ref_def GTECurrentAPI_ref_def
  GTEHaveParamLo_ref_def GTEListParam_ref_def GTEListParamIndex_ref_def
  GTEListParamTerminator_ref_def GTEListParamTerminatorCount_ref_def GTEListParamTerminators_ref_def
  GTEParamCount_ref_def GTEParamLo_ref_def GTEParamType_ref_def GTEParamsComplete_ref_def
  GTEStatus_ref_def GTE_AS_Access_ref_def GTE_AS_AccessCount_ref_def GTE_AS_Address_ref_def
  GTE_AS_Size_ref_def IRQPending_ref_def PC_ref_def PPURACR_ref_def PPURBAR_ref_def PPURSER_ref_def
  PendingPhysicalSE_ref_def R_ref_def ScheduleFIQ_ref_def ScheduleIRQ_ref_def TLB_ref_def
  TargetCPU_ref_def CNTControlBase_ref_def LSISyndrome_ref_def PC_changed_ref_def
  currentInstr_ref_def currentInstrLength_ref_def defaultRAM_ref_def highest_el_aarch32_ref_def

lemma regval_GTEParamType[simp]:
  "GTEParamType_of_regval (regval_of_GTEParamType v) = Some v"
  by (auto simp: regval_of_GTEParamType_def)

lemma regval_ProcState[simp]:
  "ProcState_of_regval (regval_of_ProcState v) = Some v"
  by (auto simp: regval_of_ProcState_def)

lemma regval_TLBLine[simp]:
  "TLBLine_of_regval (regval_of_TLBLine v) = Some v"
  by (auto simp: regval_of_TLBLine_def)

lemma regval_bool[simp]:
  "bool_of_regval (regval_of_bool v) = Some v"
  by (auto simp: regval_of_bool_def)

lemma regval_int[simp]:
  "int_of_regval (regval_of_int v) = Some v"
  by (auto simp: regval_of_int_def)

lemma regval_signal[simp]:
  "signal_of_regval (regval_of_signal v) = Some v"
  by (auto simp: regval_of_signal_def)

lemma regval_vector_11_dec_bit[simp]:
  "vector_11_dec_bit_of_regval (regval_of_vector_11_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_11_dec_bit_def)

lemma regval_vector_128_dec_bit[simp]:
  "vector_128_dec_bit_of_regval (regval_of_vector_128_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_128_dec_bit_def)

lemma regval_vector_16_dec_bit[simp]:
  "vector_16_dec_bit_of_regval (regval_of_vector_16_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_16_dec_bit_def)

lemma regval_vector_1_dec_bit[simp]:
  "vector_1_dec_bit_of_regval (regval_of_vector_1_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_1_dec_bit_def)

lemma regval_vector_2_dec_bit[simp]:
  "vector_2_dec_bit_of_regval (regval_of_vector_2_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_2_dec_bit_def)

lemma regval_vector_32_dec_bit[simp]:
  "vector_32_dec_bit_of_regval (regval_of_vector_32_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_32_dec_bit_def)

lemma regval_vector_4_dec_bit[simp]:
  "vector_4_dec_bit_of_regval (regval_of_vector_4_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_4_dec_bit_def)

lemma regval_vector_52_dec_bit[simp]:
  "vector_52_dec_bit_of_regval (regval_of_vector_52_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_52_dec_bit_def)

lemma regval_vector_56_dec_bit[simp]:
  "vector_56_dec_bit_of_regval (regval_of_vector_56_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_56_dec_bit_def)

lemma regval_vector_64_dec_bit[simp]:
  "vector_64_dec_bit_of_regval (regval_of_vector_64_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_64_dec_bit_def)

lemma vector_of_rv_rv_of_vector[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "vector_of_regval of_rv (regval_of_vector rv_of len is_inc v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  then show ?thesis by (auto simp: vector_of_regval_def regval_of_vector_def)
qed

lemma option_of_rv_rv_of_option[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "option_of_regval of_rv (regval_of_option rv_of v) = Some v"
  using assms by (cases v) (auto simp: option_of_regval_def regval_of_option_def)

lemma list_of_rv_rv_of_list[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "list_of_regval of_rv (regval_of_list rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  with assms show ?thesis by (induction v) (auto simp: list_of_regval_def regval_of_list_def)
qed

lemma liftS_read_reg_CNTHCTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHCTL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHCTL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHCTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHCTL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHCTL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL2_ref\<rbrakk>\<^sub>S = readS (CPTR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CPTR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CCSIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CCSIDR_EL1_ref\<rbrakk>\<^sub>S = readS (CCSIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CCSIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CCSIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CCSIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ACTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL1_ref\<rbrakk>\<^sub>S = readS (ACTLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ACTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ACTLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ACTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL2_ref\<rbrakk>\<^sub>S = readS (ACTLR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ACTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ACTLR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ACTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL3_ref\<rbrakk>\<^sub>S = readS (ACTLR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ACTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ACTLR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AFSR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL1_ref\<rbrakk>\<^sub>S = readS (AFSR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AFSR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AFSR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AFSR0_EL2[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL2_ref\<rbrakk>\<^sub>S = readS (AFSR0_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AFSR0_EL2[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AFSR0_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AFSR0_EL3[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL3_ref\<rbrakk>\<^sub>S = readS (AFSR0_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AFSR0_EL3[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AFSR0_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AFSR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL1_ref\<rbrakk>\<^sub>S = readS (AFSR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AFSR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AFSR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AFSR1_EL2[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL2_ref\<rbrakk>\<^sub>S = readS (AFSR1_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AFSR1_EL2[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AFSR1_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AFSR1_EL3[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL3_ref\<rbrakk>\<^sub>S = readS (AFSR1_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AFSR1_EL3[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AFSR1_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg AIDR_EL1_ref\<rbrakk>\<^sub>S = readS (AIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg AIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AMAIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL1_ref\<rbrakk>\<^sub>S = readS (AMAIR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AMAIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AMAIR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AMAIR_EL2[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL2_ref\<rbrakk>\<^sub>S = readS (AMAIR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AMAIR_EL2[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AMAIR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AMAIR_EL3[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL3_ref\<rbrakk>\<^sub>S = readS (AMAIR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AMAIR_EL3[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AMAIR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APDAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDAKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APDAKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDAKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APDAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDAKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APDAKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDAKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APDBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDBKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APDBKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDBKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDBKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APDBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDBKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APDBKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDBKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDBKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APGAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APGAKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APGAKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APGAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APGAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APGAKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APGAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APGAKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APGAKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APGAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APGAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APGAKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIAKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APIAKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIAKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIAKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APIAKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIAKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIBKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APIBKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIBKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIBKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIBKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APIBKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIBKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIBKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_BTypeCompatible[liftState_simp]:
  "\<lbrakk>read_reg BTypeCompatible_ref\<rbrakk>\<^sub>S = readS (BTypeCompatible \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_BTypeCompatible[liftState_simp]:
  "\<lbrakk>write_reg BTypeCompatible_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (BTypeCompatible_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_BTypeNext[liftState_simp]:
  "\<lbrakk>read_reg BTypeNext_ref\<rbrakk>\<^sub>S = readS (BTypeNext \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_BTypeNext[liftState_simp]:
  "\<lbrakk>write_reg BTypeNext_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (BTypeNext_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CCSIDR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg CCSIDR2_EL1_ref\<rbrakk>\<^sub>S = readS (CCSIDR2_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CCSIDR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg CCSIDR2_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CCSIDR2_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CLIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CLIDR_EL1_ref\<rbrakk>\<^sub>S = readS (CLIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CLIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CLIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CLIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTFRQ_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTFRQ_EL0_ref\<rbrakk>\<^sub>S = readS (CNTFRQ_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTFRQ_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTFRQ_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTFRQ_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHPS_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_CTL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHPS_CTL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHPS_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_CTL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHPS_CTL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHPS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_CVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHPS_CVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHPS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_CVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHPS_CVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHPS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_TVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHPS_TVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHPS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_TVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHPS_TVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHP_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_CTL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHP_CTL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHP_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_CTL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHP_CTL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHP_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_CVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHP_CVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHP_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_CVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHP_CVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHP_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_TVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHP_TVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHP_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_TVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHP_TVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHVS_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_CTL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHVS_CTL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHVS_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_CTL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHVS_CTL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHVS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_CVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHVS_CVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHVS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_CVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHVS_CVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHVS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_TVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHVS_TVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHVS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_TVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHVS_TVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHV_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_CTL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHV_CTL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHV_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_CTL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHV_CTL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHV_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_CVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHV_CVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHV_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_CVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHV_CVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTHV_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_TVAL_EL2_ref\<rbrakk>\<^sub>S = readS (CNTHV_TVAL_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTHV_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_TVAL_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTHV_TVAL_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTKCTL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTKCTL_EL1_ref\<rbrakk>\<^sub>S = readS (CNTKCTL_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTKCTL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTKCTL_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTKCTL_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTPCT_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTPCT_EL0_ref\<rbrakk>\<^sub>S = readS (CNTPCT_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTPCT_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTPCT_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTPCT_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTPS_CTL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_CTL_EL1_ref\<rbrakk>\<^sub>S = readS (CNTPS_CTL_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTPS_CTL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_CTL_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTPS_CTL_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTPS_CVAL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_CVAL_EL1_ref\<rbrakk>\<^sub>S = readS (CNTPS_CVAL_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTPS_CVAL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_CVAL_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTPS_CVAL_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTPS_TVAL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_TVAL_EL1_ref\<rbrakk>\<^sub>S = readS (CNTPS_TVAL_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTPS_TVAL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_TVAL_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTPS_TVAL_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTP_CTL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CTL_EL0_ref\<rbrakk>\<^sub>S = readS (CNTP_CTL_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTP_CTL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CTL_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTP_CTL_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTP_CTL_S[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CTL_S_ref\<rbrakk>\<^sub>S = readS (CNTP_CTL_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTP_CTL_S[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CTL_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTP_CTL_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTP_CVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CVAL_EL0_ref\<rbrakk>\<^sub>S = readS (CNTP_CVAL_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTP_CVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CVAL_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTP_CVAL_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTP_TVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_TVAL_EL0_ref\<rbrakk>\<^sub>S = readS (CNTP_TVAL_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTP_TVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_TVAL_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTP_TVAL_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTVCT_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTVCT_EL0_ref\<rbrakk>\<^sub>S = readS (CNTVCT_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTVCT_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTVCT_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTVCT_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTVOFF_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTVOFF_EL2_ref\<rbrakk>\<^sub>S = readS (CNTVOFF_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTVOFF_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTVOFF_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTVOFF_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTV_CTL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_CTL_EL0_ref\<rbrakk>\<^sub>S = readS (CNTV_CTL_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTV_CTL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_CTL_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTV_CTL_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTV_CVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_CVAL_EL0_ref\<rbrakk>\<^sub>S = readS (CNTV_CVAL_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTV_CVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_CVAL_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTV_CVAL_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTV_TVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_TVAL_EL0_ref\<rbrakk>\<^sub>S = readS (CNTV_TVAL_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTV_TVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_TVAL_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTV_TVAL_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CPACR_EL1_ref\<rbrakk>\<^sub>S = readS (CPACR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CPACR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CPACR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL3_ref\<rbrakk>\<^sub>S = readS (CPTR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CPTR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CSSELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CSSELR_EL1_ref\<rbrakk>\<^sub>S = readS (CSSELR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CSSELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CSSELR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CSSELR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CSSELR_S[liftState_simp]:
  "\<lbrakk>read_reg CSSELR_S_ref\<rbrakk>\<^sub>S = readS (CSSELR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CSSELR_S[liftState_simp]:
  "\<lbrakk>write_reg CSSELR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CSSELR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg CTR_EL0_ref\<rbrakk>\<^sub>S = readS (CTR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg CTR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CTR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGAUTHSTATUS_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGAUTHSTATUS_EL1_ref\<rbrakk>\<^sub>S = readS (DBGAUTHSTATUS_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGAUTHSTATUS_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGAUTHSTATUS_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGAUTHSTATUS_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGCLAIMCLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGCLAIMCLR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGCLAIMCLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGCLAIMCLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGCLAIMCLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGCLAIMCLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGCLAIMSET_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGCLAIMSET_EL1_ref\<rbrakk>\<^sub>S = readS (DBGCLAIMSET_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGCLAIMSET_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGCLAIMSET_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGCLAIMSET_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGDEVID1[liftState_simp]:
  "\<lbrakk>read_reg DBGDEVID1_ref\<rbrakk>\<^sub>S = readS (DBGDEVID1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGDEVID1[liftState_simp]:
  "\<lbrakk>write_reg DBGDEVID1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGDEVID1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGDEVID2[liftState_simp]:
  "\<lbrakk>read_reg DBGDEVID2_ref\<rbrakk>\<^sub>S = readS (DBGDEVID2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGDEVID2[liftState_simp]:
  "\<lbrakk>write_reg DBGDEVID2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGDEVID2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGDSCRint[liftState_simp]:
  "\<lbrakk>read_reg DBGDSCRint_ref\<rbrakk>\<^sub>S = readS (DBGDSCRint \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGDSCRint[liftState_simp]:
  "\<lbrakk>write_reg DBGDSCRint_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGDSCRint_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGDTRRX_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTRRX_EL0_ref\<rbrakk>\<^sub>S = readS (DBGDTRRX_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGDTRRX_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTRRX_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGDTRRX_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGDTRTX_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTRTX_EL0_ref\<rbrakk>\<^sub>S = readS (DBGDTRTX_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGDTRTX_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTRTX_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGDTRTX_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGDTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTR_EL0_ref\<rbrakk>\<^sub>S = readS (DBGDTR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGDTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGDTR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGWFAR[liftState_simp]:
  "\<lbrakk>read_reg DBGWFAR_ref\<rbrakk>\<^sub>S = readS (DBGWFAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGWFAR[liftState_simp]:
  "\<lbrakk>write_reg DBGWFAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGWFAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DCZID_EL0[liftState_simp]:
  "\<lbrakk>read_reg DCZID_EL0_ref\<rbrakk>\<^sub>S = readS (DCZID_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DCZID_EL0[liftState_simp]:
  "\<lbrakk>write_reg DCZID_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DCZID_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DISR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DISR_EL1_ref\<rbrakk>\<^sub>S = readS (DISR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DISR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DISR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DISR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDECCR[liftState_simp]:
  "\<lbrakk>read_reg EDECCR_ref\<rbrakk>\<^sub>S = readS (EDECCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDECCR[liftState_simp]:
  "\<lbrakk>write_reg EDECCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDECCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDECR[liftState_simp]:
  "\<lbrakk>read_reg EDECR_ref\<rbrakk>\<^sub>S = readS (EDECR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDECR[liftState_simp]:
  "\<lbrakk>write_reg EDECR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDECR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDESR[liftState_simp]:
  "\<lbrakk>read_reg EDESR_ref\<rbrakk>\<^sub>S = readS (EDESR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDESR[liftState_simp]:
  "\<lbrakk>write_reg EDESR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDESR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDLSR[liftState_simp]:
  "\<lbrakk>read_reg EDLSR_ref\<rbrakk>\<^sub>S = readS (EDLSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDLSR[liftState_simp]:
  "\<lbrakk>write_reg EDLSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDLSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDPCSR[liftState_simp]:
  "\<lbrakk>read_reg EDPCSR_ref\<rbrakk>\<^sub>S = readS (EDPCSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDPCSR[liftState_simp]:
  "\<lbrakk>write_reg EDPCSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDPCSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDPFR[liftState_simp]:
  "\<lbrakk>read_reg EDPFR_ref\<rbrakk>\<^sub>S = readS (EDPFR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDPFR[liftState_simp]:
  "\<lbrakk>write_reg EDPFR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDPFR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDPRCR[liftState_simp]:
  "\<lbrakk>read_reg EDPRCR_ref\<rbrakk>\<^sub>S = readS (EDPRCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDPRCR[liftState_simp]:
  "\<lbrakk>write_reg EDPRCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDPRCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDPRSR[liftState_simp]:
  "\<lbrakk>read_reg EDPRSR_ref\<rbrakk>\<^sub>S = readS (EDPRSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDPRSR[liftState_simp]:
  "\<lbrakk>write_reg EDPRSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDPRSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDVIDSR[liftState_simp]:
  "\<lbrakk>read_reg EDVIDSR_ref\<rbrakk>\<^sub>S = readS (EDVIDSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDVIDSR[liftState_simp]:
  "\<lbrakk>write_reg EDVIDSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDVIDSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_EL0[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL0_ref\<rbrakk>\<^sub>S = readS (ELR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_EL0[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESP_EL0[liftState_simp]:
  "\<lbrakk>read_reg ESP_EL0_ref\<rbrakk>\<^sub>S = readS (ESP_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESP_EL0[liftState_simp]:
  "\<lbrakk>write_reg ESP_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESP_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESR_EL0[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL0_ref\<rbrakk>\<^sub>S = readS (ESR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESR_EL0[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EventRegister[liftState_simp]:
  "\<lbrakk>read_reg EventRegister_ref\<rbrakk>\<^sub>S = readS (EventRegister \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EventRegister[liftState_simp]:
  "\<lbrakk>write_reg EventRegister_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EventRegister_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FAR_EL0[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL0_ref\<rbrakk>\<^sub>S = readS (FAR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FAR_EL0[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FAR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FCSEIDR[liftState_simp]:
  "\<lbrakk>read_reg FCSEIDR_ref\<rbrakk>\<^sub>S = readS (FCSEIDR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FCSEIDR[liftState_simp]:
  "\<lbrakk>write_reg FCSEIDR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FCSEIDR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPCR[liftState_simp]:
  "\<lbrakk>read_reg FPCR_ref\<rbrakk>\<^sub>S = readS (FPCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPCR[liftState_simp]:
  "\<lbrakk>write_reg FPCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPEXC32_EL2[liftState_simp]:
  "\<lbrakk>read_reg FPEXC32_EL2_ref\<rbrakk>\<^sub>S = readS (FPEXC32_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPEXC32_EL2[liftState_simp]:
  "\<lbrakk>write_reg FPEXC32_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPEXC32_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPSCR[liftState_simp]:
  "\<lbrakk>read_reg FPSCR_ref\<rbrakk>\<^sub>S = readS (FPSCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPSCR[liftState_simp]:
  "\<lbrakk>write_reg FPSCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPSCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPSID[liftState_simp]:
  "\<lbrakk>read_reg FPSID_ref\<rbrakk>\<^sub>S = readS (FPSID \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPSID[liftState_simp]:
  "\<lbrakk>write_reg FPSID_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPSID_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPSR[liftState_simp]:
  "\<lbrakk>read_reg FPSR_ref\<rbrakk>\<^sub>S = readS (FPSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPSR[liftState_simp]:
  "\<lbrakk>write_reg FPSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg GCR_EL1_ref\<rbrakk>\<^sub>S = readS (GCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg GCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HACR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HACR_EL2_ref\<rbrakk>\<^sub>S = readS (HACR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HACR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HACR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HACR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HSTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HSTR_EL2_ref\<rbrakk>\<^sub>S = readS (HSTR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HSTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HSTR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HSTR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_AP0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP0R_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_AP0R_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_AP0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP0R_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_AP0R_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_AP1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP1R_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_AP1R_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_AP1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP1R_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_AP1R_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_ASGI1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_ASGI1R_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_ASGI1R_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_ASGI1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_ASGI1R_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_ASGI1R_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_BPR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_BPR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_BPR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_BPR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_BPR1_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR1_EL1_NS_ref\<rbrakk>\<^sub>S = readS (ICC_BPR1_EL1_NS \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_BPR1_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR1_EL1_NS_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_BPR1_EL1_NS_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_BPR1_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR1_EL1_S_ref\<rbrakk>\<^sub>S = readS (ICC_BPR1_EL1_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_BPR1_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR1_EL1_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_BPR1_EL1_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_CTLR_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL1_NS_ref\<rbrakk>\<^sub>S = readS (ICC_CTLR_EL1_NS \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_CTLR_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL1_NS_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_CTLR_EL1_NS_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_CTLR_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL1_S_ref\<rbrakk>\<^sub>S = readS (ICC_CTLR_EL1_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_CTLR_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL1_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_CTLR_EL1_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_CTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL3_ref\<rbrakk>\<^sub>S = readS (ICC_CTLR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_CTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_CTLR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_DIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_DIR_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_DIR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_DIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_DIR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_DIR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_EOIR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_EOIR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_EOIR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_EOIR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_EOIR1_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_EOIR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_EOIR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_EOIR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_HPPIR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_HPPIR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_HPPIR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_HPPIR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_HPPIR1_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_HPPIR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_HPPIR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_HPPIR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_IAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IAR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_IAR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_IAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IAR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_IAR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_IAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IAR1_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_IAR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_IAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IAR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_IAR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN0_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_IGRPEN0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_IGRPEN0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL1_NS_ref\<rbrakk>\<^sub>S = readS (ICC_IGRPEN1_EL1_NS \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL1_NS_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_IGRPEN1_EL1_NS_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL1_S_ref\<rbrakk>\<^sub>S = readS (ICC_IGRPEN1_EL1_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL1_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_IGRPEN1_EL1_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL3_ref\<rbrakk>\<^sub>S = readS (ICC_IGRPEN1_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_IGRPEN1_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_PMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_PMR_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_PMR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_PMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_PMR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_PMR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_RPR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_RPR_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_RPR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_RPR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_RPR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_RPR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_SGI0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_SGI0R_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_SGI0R_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_SGI0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_SGI0R_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_SGI0R_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_SGI1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_SGI1R_EL1_ref\<rbrakk>\<^sub>S = readS (ICC_SGI1R_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_SGI1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_SGI1R_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_SGI1R_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_SRE_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL1_NS_ref\<rbrakk>\<^sub>S = readS (ICC_SRE_EL1_NS \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_SRE_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL1_NS_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_SRE_EL1_NS_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_SRE_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL1_S_ref\<rbrakk>\<^sub>S = readS (ICC_SRE_EL1_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_SRE_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL1_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_SRE_EL1_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_SRE_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL2_ref\<rbrakk>\<^sub>S = readS (ICC_SRE_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_SRE_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_SRE_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICC_SRE_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL3_ref\<rbrakk>\<^sub>S = readS (ICC_SRE_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICC_SRE_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICC_SRE_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_AP0R_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_AP0R_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_AP0R_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_AP0R_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_AP0R_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_AP0R_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_AP1R_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_AP1R_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_AP1R_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_AP1R_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_AP1R_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_AP1R_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_EISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_EISR_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_EISR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_EISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_EISR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_EISR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_ELRSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_ELRSR_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_ELRSR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_ELRSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_ELRSR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_ELRSR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_HCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_HCR_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_HCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_HCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_HCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_HCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_MISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_MISR_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_MISR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_MISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_MISR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_MISR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_VMCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_VMCR_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_VMCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_VMCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_VMCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_VMCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICH_VTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_VTR_EL2_ref\<rbrakk>\<^sub>S = readS (ICH_VTR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICH_VTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_VTR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICH_VTR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_AP0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_AP0R_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_AP0R_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_AP0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_AP0R_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_AP0R_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_AP1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_AP1R_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_AP1R_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_AP1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_AP1R_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_AP1R_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_BPR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_BPR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_BPR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_BPR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_BPR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_BPR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_BPR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_BPR1_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_BPR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_BPR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_BPR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_BPR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_CTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_CTLR_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_CTLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_CTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_CTLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_CTLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_DIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_DIR_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_DIR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_DIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_DIR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_DIR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_EOIR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_EOIR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_EOIR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_EOIR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_EOIR1_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_EOIR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_EOIR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_EOIR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_HPPIR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_HPPIR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_HPPIR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_HPPIR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_HPPIR1_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_HPPIR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_HPPIR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_HPPIR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_IAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IAR0_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_IAR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_IAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IAR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_IAR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_IAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IAR1_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_IAR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_IAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IAR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_IAR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IGRPEN0_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_IGRPEN0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IGRPEN0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_IGRPEN0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_IGRPEN1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IGRPEN1_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_IGRPEN1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_IGRPEN1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IGRPEN1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_IGRPEN1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_PMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_PMR_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_PMR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_PMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_PMR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_PMR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ICV_RPR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_RPR_EL1_ref\<rbrakk>\<^sub>S = readS (ICV_RPR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ICV_RPR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_RPR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ICV_RPR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64AFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64AFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64AFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64AFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64AFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64AFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64AFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64AFR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64AFR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64AFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64AFR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64AFR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64DFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64DFR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64DFR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64DFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64DFR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64DFR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64ISAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ISAR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64ISAR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64ISAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ISAR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64ISAR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64ISAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ISAR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64ISAR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64ISAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ISAR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64ISAR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64MMFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64MMFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64MMFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64MMFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64MMFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64MMFR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64MMFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64MMFR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64MMFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR2_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64MMFR2_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64MMFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR2_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64MMFR2_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64PFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64PFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64PFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64PFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64PFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64PFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64PFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64PFR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64PFR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64PFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64PFR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64PFR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_DFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_DFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_DFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_DFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_DFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_DFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_ISAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_ISAR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_ISAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_ISAR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_ISAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_ISAR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_ISAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_ISAR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_ISAR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR2_EL1_ref\<rbrakk>\<^sub>S = readS (ID_ISAR2_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_ISAR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR2_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_ISAR2_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_ISAR3_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR3_EL1_ref\<rbrakk>\<^sub>S = readS (ID_ISAR3_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_ISAR3_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR3_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_ISAR3_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_ISAR4_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR4_EL1_ref\<rbrakk>\<^sub>S = readS (ID_ISAR4_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_ISAR4_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR4_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_ISAR4_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_ISAR5_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR5_EL1_ref\<rbrakk>\<^sub>S = readS (ID_ISAR5_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_ISAR5_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR5_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_ISAR5_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_ISAR6_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR6_EL1_ref\<rbrakk>\<^sub>S = readS (ID_ISAR6_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_ISAR6_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR6_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_ISAR6_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_MMFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_MMFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_MMFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_MMFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_MMFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_MMFR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_MMFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_MMFR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_MMFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR2_EL1_ref\<rbrakk>\<^sub>S = readS (ID_MMFR2_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_MMFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR2_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_MMFR2_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_MMFR3_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR3_EL1_ref\<rbrakk>\<^sub>S = readS (ID_MMFR3_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_MMFR3_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR3_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_MMFR3_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_MMFR4_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR4_EL1_ref\<rbrakk>\<^sub>S = readS (ID_MMFR4_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_MMFR4_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR4_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_MMFR4_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_PFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_PFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_PFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_PFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_PFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR1_EL1_ref\<rbrakk>\<^sub>S = readS (ID_PFR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_PFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_PFR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_PFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR2_EL1_ref\<rbrakk>\<^sub>S = readS (ID_PFR2_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_PFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR2_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_PFR2_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ISR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ISR_EL1_ref\<rbrakk>\<^sub>S = readS (ISR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ISR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ISR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ISR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LORC_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORC_EL1_ref\<rbrakk>\<^sub>S = readS (LORC_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LORC_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORC_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LORC_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LOREA_EL1[liftState_simp]:
  "\<lbrakk>read_reg LOREA_EL1_ref\<rbrakk>\<^sub>S = readS (LOREA_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LOREA_EL1[liftState_simp]:
  "\<lbrakk>write_reg LOREA_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LOREA_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LORID_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORID_EL1_ref\<rbrakk>\<^sub>S = readS (LORID_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LORID_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORID_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LORID_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LORN_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORN_EL1_ref\<rbrakk>\<^sub>S = readS (LORN_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LORN_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORN_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LORN_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LORSA_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORSA_EL1_ref\<rbrakk>\<^sub>S = readS (LORSA_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LORSA_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORSA_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LORSA_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDCCINT_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDCCINT_EL1_ref\<rbrakk>\<^sub>S = readS (MDCCINT_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDCCINT_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDCCINT_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDCCINT_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDCCSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg MDCCSR_EL0_ref\<rbrakk>\<^sub>S = readS (MDCCSR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDCCSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg MDCCSR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDCCSR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDRAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDRAR_EL1_ref\<rbrakk>\<^sub>S = readS (MDRAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDRAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDRAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDRAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MIDR_EL1_ref\<rbrakk>\<^sub>S = readS (MIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MVFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR0_EL1_ref\<rbrakk>\<^sub>S = readS (MVFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MVFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MVFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MVFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR1_EL1_ref\<rbrakk>\<^sub>S = readS (MVFR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MVFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MVFR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MVFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR2_EL1_ref\<rbrakk>\<^sub>S = readS (MVFR2_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MVFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR2_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MVFR2_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_NSACR[liftState_simp]:
  "\<lbrakk>read_reg NSACR_ref\<rbrakk>\<^sub>S = readS (NSACR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_NSACR[liftState_simp]:
  "\<lbrakk>write_reg NSACR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (NSACR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSDTRRX_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDTRRX_EL1_ref\<rbrakk>\<^sub>S = readS (OSDTRRX_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSDTRRX_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDTRRX_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSDTRRX_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSDTRTX_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDTRTX_EL1_ref\<rbrakk>\<^sub>S = readS (OSDTRTX_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSDTRTX_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDTRTX_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSDTRTX_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSECCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSECCR_EL1_ref\<rbrakk>\<^sub>S = readS (OSECCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSECCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSECCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSECCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSLAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSLAR_EL1_ref\<rbrakk>\<^sub>S = readS (OSLAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSLAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSLAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSLAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PAR_EL1_ref\<rbrakk>\<^sub>S = readS (PAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PAR_S[liftState_simp]:
  "\<lbrakk>read_reg PAR_S_ref\<rbrakk>\<^sub>S = readS (PAR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PAR_S[liftState_simp]:
  "\<lbrakk>write_reg PAR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PAR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMCCFILTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCCFILTR_EL0_ref\<rbrakk>\<^sub>S = readS (PMCCFILTR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMCCFILTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCCFILTR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMCCFILTR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMCCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCCNTR_EL0_ref\<rbrakk>\<^sub>S = readS (PMCCNTR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMCCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCCNTR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMCCNTR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMCEID0_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCEID0_EL0_ref\<rbrakk>\<^sub>S = readS (PMCEID0_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMCEID0_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCEID0_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMCEID0_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMCEID1_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCEID1_EL0_ref\<rbrakk>\<^sub>S = readS (PMCEID1_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMCEID1_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCEID1_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMCEID1_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMCNTENCLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCNTENCLR_EL0_ref\<rbrakk>\<^sub>S = readS (PMCNTENCLR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMCNTENCLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCNTENCLR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMCNTENCLR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMCNTENSET_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCNTENSET_EL0_ref\<rbrakk>\<^sub>S = readS (PMCNTENSET_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMCNTENSET_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCNTENSET_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMCNTENSET_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMCR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCR_EL0_ref\<rbrakk>\<^sub>S = readS (PMCR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMCR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMCR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMEVCNTR_EL0_ref\<rbrakk>\<^sub>S = readS (PMEVCNTR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMEVCNTR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMEVCNTR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMEVTYPER_EL0_ref\<rbrakk>\<^sub>S = readS (PMEVTYPER_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMEVTYPER_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMEVTYPER_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMINTENCLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMINTENCLR_EL1_ref\<rbrakk>\<^sub>S = readS (PMINTENCLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMINTENCLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMINTENCLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMINTENCLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMINTENSET_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMINTENSET_EL1_ref\<rbrakk>\<^sub>S = readS (PMINTENSET_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMINTENSET_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMINTENSET_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMINTENSET_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMLSR[liftState_simp]:
  "\<lbrakk>read_reg PMLSR_ref\<rbrakk>\<^sub>S = readS (PMLSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMLSR[liftState_simp]:
  "\<lbrakk>write_reg PMLSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMLSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMMIR[liftState_simp]:
  "\<lbrakk>read_reg PMMIR_ref\<rbrakk>\<^sub>S = readS (PMMIR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMMIR[liftState_simp]:
  "\<lbrakk>write_reg PMMIR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMMIR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMMIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMMIR_EL1_ref\<rbrakk>\<^sub>S = readS (PMMIR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMMIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMMIR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMMIR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMOVSCLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMOVSCLR_EL0_ref\<rbrakk>\<^sub>S = readS (PMOVSCLR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMOVSCLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMOVSCLR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMOVSCLR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMOVSSET_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMOVSSET_EL0_ref\<rbrakk>\<^sub>S = readS (PMOVSSET_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMOVSSET_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMOVSSET_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMOVSSET_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMPCSR[liftState_simp]:
  "\<lbrakk>read_reg PMPCSR_ref\<rbrakk>\<^sub>S = readS (PMPCSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMPCSR[liftState_simp]:
  "\<lbrakk>write_reg PMPCSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMPCSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMSELR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMSELR_EL0_ref\<rbrakk>\<^sub>S = readS (PMSELR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMSELR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMSELR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMSELR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMSWINC_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMSWINC_EL0_ref\<rbrakk>\<^sub>S = readS (PMSWINC_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMSWINC_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMSWINC_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMSWINC_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMUSERENR_EL0_ref\<rbrakk>\<^sub>S = readS (PMUSERENR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMUSERENR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMUSERENR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMVIDSR[liftState_simp]:
  "\<lbrakk>read_reg PMVIDSR_ref\<rbrakk>\<^sub>S = readS (PMVIDSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMVIDSR[liftState_simp]:
  "\<lbrakk>write_reg PMVIDSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMVIDSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMXEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMXEVCNTR_EL0_ref\<rbrakk>\<^sub>S = readS (PMXEVCNTR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMXEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMXEVCNTR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMXEVCNTR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PMXEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMXEVTYPER_EL0_ref\<rbrakk>\<^sub>S = readS (PMXEVTYPER_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PMXEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMXEVTYPER_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PMXEVTYPER_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RC[liftState_simp]:
  "\<lbrakk>read_reg RC_ref\<rbrakk>\<^sub>S = readS (RC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RC[liftState_simp]:
  "\<lbrakk>write_reg RC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RD_EL0[liftState_simp]:
  "\<lbrakk>read_reg RD_EL0_ref\<rbrakk>\<^sub>S = readS (RD_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RD_EL0[liftState_simp]:
  "\<lbrakk>write_reg RD_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RD_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_REVIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg REVIDR_EL1_ref\<rbrakk>\<^sub>S = readS (REVIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_REVIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg REVIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (REVIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RGSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RGSR_EL1_ref\<rbrakk>\<^sub>S = readS (RGSR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RGSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RGSR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RGSR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL1_ref\<rbrakk>\<^sub>S = readS (RMR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RMR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RMR_EL2[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL2_ref\<rbrakk>\<^sub>S = readS (RMR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RMR_EL2[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RMR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RMR_EL3[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL3_ref\<rbrakk>\<^sub>S = readS (RMR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RMR_EL3[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RMR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RMUID_EL0[liftState_simp]:
  "\<lbrakk>read_reg RMUID_EL0_ref\<rbrakk>\<^sub>S = readS (RMUID_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RMUID_EL0[liftState_simp]:
  "\<lbrakk>write_reg RMUID_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RMUID_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RNDR[liftState_simp]:
  "\<lbrakk>read_reg RNDR_ref\<rbrakk>\<^sub>S = readS (RNDR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RNDR[liftState_simp]:
  "\<lbrakk>write_reg RNDR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RNDR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RNDRRS[liftState_simp]:
  "\<lbrakk>read_reg RNDRRS_ref\<rbrakk>\<^sub>S = readS (RNDRRS \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RNDRRS[liftState_simp]:
  "\<lbrakk>write_reg RNDRRS_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RNDRRS_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RVBAR[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_ref\<rbrakk>\<^sub>S = readS (RVBAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RVBAR[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RVBAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL1_ref\<rbrakk>\<^sub>S = readS (RVBAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RVBAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL2_ref\<rbrakk>\<^sub>S = readS (RVBAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RVBAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL3_ref\<rbrakk>\<^sub>S = readS (RVBAR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RVBAR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCXTNUM_EL0[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL0_ref\<rbrakk>\<^sub>S = readS (SCXTNUM_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCXTNUM_EL0[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCXTNUM_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCXTNUM_EL1[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL1_ref\<rbrakk>\<^sub>S = readS (SCXTNUM_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCXTNUM_EL1[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCXTNUM_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCXTNUM_EL2[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL2_ref\<rbrakk>\<^sub>S = readS (SCXTNUM_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCXTNUM_EL2[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCXTNUM_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCXTNUM_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL3_ref\<rbrakk>\<^sub>S = readS (SCXTNUM_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCXTNUM_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCXTNUM_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SDER32_EL2[liftState_simp]:
  "\<lbrakk>read_reg SDER32_EL2_ref\<rbrakk>\<^sub>S = readS (SDER32_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SDER32_EL2[liftState_simp]:
  "\<lbrakk>write_reg SDER32_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SDER32_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL0_ref\<rbrakk>\<^sub>S = readS (SPSR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>read_reg SP_EL0_ref\<rbrakk>\<^sub>S = readS (SP_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>write_reg SP_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>read_reg SP_EL1_ref\<rbrakk>\<^sub>S = readS (SP_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>write_reg SP_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>read_reg SP_EL2_ref\<rbrakk>\<^sub>S = readS (SP_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>write_reg SP_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>read_reg SP_EL3_ref\<rbrakk>\<^sub>S = readS (SP_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>write_reg SP_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ShouldAdvanceIT[liftState_simp]:
  "\<lbrakk>read_reg ShouldAdvanceIT_ref\<rbrakk>\<^sub>S = readS (ShouldAdvanceIT \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ShouldAdvanceIT[liftState_simp]:
  "\<lbrakk>write_reg ShouldAdvanceIT_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ShouldAdvanceIT_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBTR[liftState_simp]:
  "\<lbrakk>read_reg TLBTR_ref\<rbrakk>\<^sub>S = readS (TLBTR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBTR[liftState_simp]:
  "\<lbrakk>write_reg TLBTR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBTR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TPIDRRO_EL0[liftState_simp]:
  "\<lbrakk>read_reg TPIDRRO_EL0_ref\<rbrakk>\<^sub>S = readS (TPIDRRO_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TPIDRRO_EL0[liftState_simp]:
  "\<lbrakk>write_reg TPIDRRO_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TPIDRRO_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TPIDR_EL0[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL0_ref\<rbrakk>\<^sub>S = readS (TPIDR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TPIDR_EL0[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TPIDR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TPIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL1_ref\<rbrakk>\<^sub>S = readS (TPIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TPIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TPIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL2_ref\<rbrakk>\<^sub>S = readS (TPIDR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TPIDR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TPIDR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL3_ref\<rbrakk>\<^sub>S = readS (TPIDR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TPIDR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TPIDR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TRFCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TRFCR_EL1_ref\<rbrakk>\<^sub>S = readS (TRFCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TRFCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TRFCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TRFCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TRFCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TRFCR_EL2_ref\<rbrakk>\<^sub>S = readS (TRFCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TRFCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TRFCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TRFCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_EL0[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL0_ref\<rbrakk>\<^sub>S = readS (VBAR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_EL0[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VDISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VDISR_EL2_ref\<rbrakk>\<^sub>S = readS (VDISR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VDISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VDISR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VDISR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VMPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VMPIDR_EL2_ref\<rbrakk>\<^sub>S = readS (VMPIDR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VMPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VMPIDR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VMPIDR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VNCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VNCR_EL2_ref\<rbrakk>\<^sub>S = readS (VNCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VNCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VNCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VNCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VPIDR_EL2_ref\<rbrakk>\<^sub>S = readS (VPIDR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VPIDR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VPIDR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_V[liftState_simp]:
  "\<lbrakk>read_reg V_ref\<rbrakk>\<^sub>S = readS (V \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_V[liftState_simp]:
  "\<lbrakk>write_reg V_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (V_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_currentCond[liftState_simp]:
  "\<lbrakk>read_reg currentCond_ref\<rbrakk>\<^sub>S = readS (currentCond \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_currentCond[liftState_simp]:
  "\<lbrakk>write_reg currentCond_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (currentCond_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_exclusive_block_address[liftState_simp]:
  "\<lbrakk>read_reg exclusive_block_address_ref\<rbrakk>\<^sub>S = readS (exclusive_block_address \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_exclusive_block_address[liftState_simp]:
  "\<lbrakk>write_reg exclusive_block_address_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (exclusive_block_address_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_saved_exception_level[liftState_simp]:
  "\<lbrakk>read_reg saved_exception_level_ref\<rbrakk>\<^sub>S = readS (saved_exception_level \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_saved_exception_level[liftState_simp]:
  "\<lbrakk>write_reg saved_exception_level_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (saved_exception_level_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_unconditional[liftState_simp]:
  "\<lbrakk>read_reg unconditional_ref\<rbrakk>\<^sub>S = readS (unconditional \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_unconditional[liftState_simp]:
  "\<lbrakk>write_reg unconditional_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (unconditional_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CONTEXTIDR_S[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_S_ref\<rbrakk>\<^sub>S = readS (CONTEXTIDR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CONTEXTIDR_S[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CONTEXTIDR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsAccess[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsAccess_ref\<rbrakk>\<^sub>S = readS (GTEExtObsAccess \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsAccess[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsAccess_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsAccess_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsAddress[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsAddress_ref\<rbrakk>\<^sub>S = readS (GTEExtObsAddress \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsAddress[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsAddress_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsAddress_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsData[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsData_ref\<rbrakk>\<^sub>S = readS (GTEExtObsData \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsData[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsData_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsData_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsResult[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsResult_ref\<rbrakk>\<^sub>S = readS (GTEExtObsResult \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsResult[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsResult_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsResult_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsActive[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsActive_ref\<rbrakk>\<^sub>S = readS (GTEExtObsActive \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsActive[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsActive_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsActive_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsCount[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsCount_ref\<rbrakk>\<^sub>S = readS (GTEExtObsCount \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsCount[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsCount_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsCount_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsIndex[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsIndex_ref\<rbrakk>\<^sub>S = readS (GTEExtObsIndex \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsIndex[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsIndex_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsIndex_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsResultIndex[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsResultIndex_ref\<rbrakk>\<^sub>S = readS (GTEExtObsResultIndex \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsResultIndex[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsResultIndex_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsResultIndex_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEExtObsResultIsAddress[liftState_simp]:
  "\<lbrakk>read_reg GTEExtObsResultIsAddress_ref\<rbrakk>\<^sub>S = readS (GTEExtObsResultIsAddress \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEExtObsResultIsAddress[liftState_simp]:
  "\<lbrakk>write_reg GTEExtObsResultIsAddress_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEExtObsResultIsAddress_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEListParam0[liftState_simp]:
  "\<lbrakk>read_reg GTEListParam0_ref\<rbrakk>\<^sub>S = readS (GTEListParam0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEListParam0[liftState_simp]:
  "\<lbrakk>write_reg GTEListParam0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEListParam0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEListParam1[liftState_simp]:
  "\<lbrakk>read_reg GTEListParam1_ref\<rbrakk>\<^sub>S = readS (GTEListParam1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEListParam1[liftState_simp]:
  "\<lbrakk>write_reg GTEListParam1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEListParam1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEParam[liftState_simp]:
  "\<lbrakk>read_reg GTEParam_ref\<rbrakk>\<^sub>S = readS (GTEParam \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEParam[liftState_simp]:
  "\<lbrakk>write_reg GTEParam_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEParam_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_AS_RecordedAccess[liftState_simp]:
  "\<lbrakk>read_reg GTE_AS_RecordedAccess_ref\<rbrakk>\<^sub>S = readS (GTE_AS_RecordedAccess \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_AS_RecordedAccess[liftState_simp]:
  "\<lbrakk>write_reg GTE_AS_RecordedAccess_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_AS_RecordedAccess_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_AS_RecordedAddress[liftState_simp]:
  "\<lbrakk>read_reg GTE_AS_RecordedAddress_ref\<rbrakk>\<^sub>S = readS (GTE_AS_RecordedAddress \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_AS_RecordedAddress[liftState_simp]:
  "\<lbrakk>write_reg GTE_AS_RecordedAddress_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_AS_RecordedAddress_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_AS_RecordedData[liftState_simp]:
  "\<lbrakk>read_reg GTE_AS_RecordedData_ref\<rbrakk>\<^sub>S = readS (GTE_AS_RecordedData \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_AS_RecordedData[liftState_simp]:
  "\<lbrakk>write_reg GTE_AS_RecordedData_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_AS_RecordedData_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_PPU_Access[liftState_simp]:
  "\<lbrakk>read_reg GTE_PPU_Access_ref\<rbrakk>\<^sub>S = readS (GTE_PPU_Access \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_PPU_Access[liftState_simp]:
  "\<lbrakk>write_reg GTE_PPU_Access_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_PPU_Access_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_PPU_Address[liftState_simp]:
  "\<lbrakk>read_reg GTE_PPU_Address_ref\<rbrakk>\<^sub>S = readS (GTE_PPU_Address \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_PPU_Address[liftState_simp]:
  "\<lbrakk>write_reg GTE_PPU_Address_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_PPU_Address_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_PPU_SizeEn[liftState_simp]:
  "\<lbrakk>read_reg GTE_PPU_SizeEn_ref\<rbrakk>\<^sub>S = readS (GTE_PPU_SizeEn \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_PPU_SizeEn[liftState_simp]:
  "\<lbrakk>write_reg GTE_PPU_SizeEn_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_PPU_SizeEn_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Hi1[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Hi1_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Hi1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Hi1[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Hi1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Hi1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Hi1_Hi[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Hi1_Hi_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Hi1_Hi \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Hi1_Hi[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Hi1_Hi_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Hi1_Hi_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Hi2[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Hi2_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Hi2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Hi2[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Hi2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Hi2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Hi2_Hi[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Hi2_Hi_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Hi2_Hi \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Hi2_Hi[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Hi2_Hi_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Hi2_Hi_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Lo1[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Lo1_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Lo1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Lo1[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Lo1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Lo1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Lo1_Hi[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Lo1_Hi_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Lo1_Hi \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Lo1_Hi[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Lo1_Hi_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Lo1_Hi_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Lo2[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Lo2_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Lo2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Lo2[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Lo2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Lo2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AbortRgn64Lo2_Hi[liftState_simp]:
  "\<lbrakk>read_reg AbortRgn64Lo2_Hi_ref\<rbrakk>\<^sub>S = readS (AbortRgn64Lo2_Hi \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AbortRgn64Lo2_Hi[liftState_simp]:
  "\<lbrakk>write_reg AbortRgn64Lo2_Hi_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AbortRgn64Lo2_Hi_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTCR[liftState_simp]:
  "\<lbrakk>read_reg CNTCR_ref\<rbrakk>\<^sub>S = readS (CNTCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTCR[liftState_simp]:
  "\<lbrakk>write_reg CNTCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTCV[liftState_simp]:
  "\<lbrakk>read_reg CNTCV_ref\<rbrakk>\<^sub>S = readS (CNTCV \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTCV[liftState_simp]:
  "\<lbrakk>write_reg CNTCV_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTCV_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTFID0[liftState_simp]:
  "\<lbrakk>read_reg CNTFID0_ref\<rbrakk>\<^sub>S = readS (CNTFID0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTFID0[liftState_simp]:
  "\<lbrakk>write_reg CNTFID0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTFID0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTSR[liftState_simp]:
  "\<lbrakk>read_reg CNTSR_ref\<rbrakk>\<^sub>S = readS (CNTSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTSR[liftState_simp]:
  "\<lbrakk>write_reg CNTSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL1_ref\<rbrakk>\<^sub>S = readS (CONTEXTIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CONTEXTIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL2_ref\<rbrakk>\<^sub>S = readS (CONTEXTIDR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CONTEXTIDR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DACR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg DACR32_EL2_ref\<rbrakk>\<^sub>S = readS (DACR32_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DACR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg DACR32_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DACR32_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DACR_S[liftState_simp]:
  "\<lbrakk>read_reg DACR_S_ref\<rbrakk>\<^sub>S = readS (DACR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DACR_S[liftState_simp]:
  "\<lbrakk>write_reg DACR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DACR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGBCR[liftState_simp]:
  "\<lbrakk>read_reg DBGBCR_ref\<rbrakk>\<^sub>S = readS (DBGBCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGBCR[liftState_simp]:
  "\<lbrakk>write_reg DBGBCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGBCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBCR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGBCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGBCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGBVR[liftState_simp]:
  "\<lbrakk>read_reg DBGBVR_ref\<rbrakk>\<^sub>S = readS (DBGBVR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGBVR[liftState_simp]:
  "\<lbrakk>write_reg DBGBVR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGBVR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBVR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGBVR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBVR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGBVR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGBXVR[liftState_simp]:
  "\<lbrakk>read_reg DBGBXVR_ref\<rbrakk>\<^sub>S = readS (DBGBXVR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGBXVR[liftState_simp]:
  "\<lbrakk>write_reg DBGBXVR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGBXVR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGDIDR[liftState_simp]:
  "\<lbrakk>read_reg DBGDIDR_ref\<rbrakk>\<^sub>S = readS (DBGDIDR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGDIDR[liftState_simp]:
  "\<lbrakk>write_reg DBGDIDR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGDIDR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGEN[liftState_simp]:
  "\<lbrakk>read_reg DBGEN_ref\<rbrakk>\<^sub>S = readS (DBGEN \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGEN[liftState_simp]:
  "\<lbrakk>write_reg DBGEN_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGEN_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGPRCR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGPRCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGPRCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGPRCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGVCR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg DBGVCR32_EL2_ref\<rbrakk>\<^sub>S = readS (DBGVCR32_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGVCR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg DBGVCR32_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGVCR32_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGWCR[liftState_simp]:
  "\<lbrakk>read_reg DBGWCR_ref\<rbrakk>\<^sub>S = readS (DBGWCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGWCR[liftState_simp]:
  "\<lbrakk>write_reg DBGWCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGWCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWCR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGWCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGWCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGWVR[liftState_simp]:
  "\<lbrakk>read_reg DBGWVR_ref\<rbrakk>\<^sub>S = readS (DBGWVR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGWVR[liftState_simp]:
  "\<lbrakk>write_reg DBGWVR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGWVR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWVR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGWVR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWVR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGWVR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DLR_EL0_ref\<rbrakk>\<^sub>S = readS (DLR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DLR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DLR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DSPSR_EL0_ref\<rbrakk>\<^sub>S = readS (DSPSR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DSPSR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DSPSR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDSCR[liftState_simp]:
  "\<lbrakk>read_reg EDSCR_ref\<rbrakk>\<^sub>S = readS (EDSCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDSCR[liftState_simp]:
  "\<lbrakk>write_reg EDSCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDSCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DFSR_S[liftState_simp]:
  "\<lbrakk>read_reg DFSR_S_ref\<rbrakk>\<^sub>S = readS (DFSR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DFSR_S[liftState_simp]:
  "\<lbrakk>write_reg DFSR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DFSR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL3_ref\<rbrakk>\<^sub>S = readS (ELR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL1_ref\<rbrakk>\<^sub>S = readS (ELR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL3_ref\<rbrakk>\<^sub>S = readS (ESR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL1_ref\<rbrakk>\<^sub>S = readS (ESR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL2_ref\<rbrakk>\<^sub>S = readS (ELR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL2_ref\<rbrakk>\<^sub>S = readS (TCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL2_ref\<rbrakk>\<^sub>S = readS (ESR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL1_ref\<rbrakk>\<^sub>S = readS (FAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL2_ref\<rbrakk>\<^sub>S = readS (FAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL3_ref\<rbrakk>\<^sub>S = readS (FAR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FAR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HCR_EL2_ref\<rbrakk>\<^sub>S = readS (HCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HPFAR_EL2_ref\<rbrakk>\<^sub>S = readS (HPFAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HPFAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HPFAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64DFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64DFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64DFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64DFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_IFSR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg IFSR32_EL2_ref\<rbrakk>\<^sub>S = readS (IFSR32_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_IFSR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg IFSR32_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (IFSR32_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_IFSR_S[liftState_simp]:
  "\<lbrakk>read_reg IFSR_S_ref\<rbrakk>\<^sub>S = readS (IFSR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_IFSR_S[liftState_simp]:
  "\<lbrakk>write_reg IFSR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (IFSR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_InGuardedPage[liftState_simp]:
  "\<lbrakk>read_reg InGuardedPage_ref\<rbrakk>\<^sub>S = readS (InGuardedPage \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_InGuardedPage[liftState_simp]:
  "\<lbrakk>write_reg InGuardedPage_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (InGuardedPage_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LR_mon[liftState_simp]:
  "\<lbrakk>read_reg LR_mon_ref\<rbrakk>\<^sub>S = readS (LR_mon \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LR_mon[liftState_simp]:
  "\<lbrakk>write_reg LR_mon_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LR_mon_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR0_S[liftState_simp]:
  "\<lbrakk>read_reg MAIR0_S_ref\<rbrakk>\<^sub>S = readS (MAIR0_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR0_S[liftState_simp]:
  "\<lbrakk>write_reg MAIR0_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR0_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR1_S[liftState_simp]:
  "\<lbrakk>read_reg MAIR1_S_ref\<rbrakk>\<^sub>S = readS (MAIR1_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR1_S[liftState_simp]:
  "\<lbrakk>write_reg MAIR1_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR1_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL1_ref\<rbrakk>\<^sub>S = readS (MAIR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL2_ref\<rbrakk>\<^sub>S = readS (MAIR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL3_ref\<rbrakk>\<^sub>S = readS (MAIR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL2_ref\<rbrakk>\<^sub>S = readS (MDCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL3_ref\<rbrakk>\<^sub>S = readS (MDCR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDCR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDSCR_EL1_ref\<rbrakk>\<^sub>S = readS (MDSCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDSCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDSCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAM0_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAM0_EL1_ref\<rbrakk>\<^sub>S = readS (MPAM0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAM0_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAM0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAM0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAM1_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAM1_EL1_ref\<rbrakk>\<^sub>S = readS (MPAM1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAM1_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAM1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAM1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAM2_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAM2_EL2_ref\<rbrakk>\<^sub>S = readS (MPAM2_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAM2_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAM2_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAM2_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAM3_EL3[liftState_simp]:
  "\<lbrakk>read_reg MPAM3_EL3_ref\<rbrakk>\<^sub>S = readS (MPAM3_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAM3_EL3[liftState_simp]:
  "\<lbrakk>write_reg MPAM3_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAM3_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMHCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMHCR_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMHCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMHCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMHCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMHCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAMIDR_EL1_ref\<rbrakk>\<^sub>S = readS (MPAMIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAMIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM0_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM0_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM0_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM0_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM0_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM0_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM1_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM1_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM1_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM1_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM1_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM1_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM2_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM2_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM2_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM2_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM2_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM2_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM3_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM3_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM3_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM3_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM3_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM3_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM4_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM4_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM4_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM4_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM4_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM4_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM5_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM5_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM5_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM5_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM5_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM5_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM6_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM6_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM6_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM6_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM6_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM6_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPM7_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM7_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPM7_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPM7_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM7_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPM7_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPAMVPMV_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPMV_EL2_ref\<rbrakk>\<^sub>S = readS (MPAMVPMV_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPAMVPMV_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPMV_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPAMVPMV_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MPIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPIDR_EL1_ref\<rbrakk>\<^sub>S = readS (MPIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MPIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MPIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MVBAR[liftState_simp]:
  "\<lbrakk>read_reg MVBAR_ref\<rbrakk>\<^sub>S = readS (MVBAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MVBAR[liftState_simp]:
  "\<lbrakk>write_reg MVBAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MVBAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_NMRR_S[liftState_simp]:
  "\<lbrakk>read_reg NMRR_S_ref\<rbrakk>\<^sub>S = readS (NMRR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_NMRR_S[liftState_simp]:
  "\<lbrakk>write_reg NMRR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (NMRR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDLR_EL1_ref\<rbrakk>\<^sub>S = readS (OSDLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSDLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSLSR_EL1_ref\<rbrakk>\<^sub>S = readS (OSLSR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSLSR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSLSR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PRRR_S[liftState_simp]:
  "\<lbrakk>read_reg PRRR_S_ref\<rbrakk>\<^sub>S = readS (PRRR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PRRR_S[liftState_simp]:
  "\<lbrakk>write_reg PRRR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PRRR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PSTATE[liftState_simp]:
  "\<lbrakk>read_reg PSTATE_ref\<rbrakk>\<^sub>S = readS (PSTATE \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PSTATE[liftState_simp]:
  "\<lbrakk>write_reg PSTATE_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PSTATE_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCR_EL3_ref\<rbrakk>\<^sub>S = readS (SCR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL1_ref\<rbrakk>\<^sub>S = readS (SCTLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL2_ref\<rbrakk>\<^sub>S = readS (SCTLR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL3_ref\<rbrakk>\<^sub>S = readS (SCTLR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR_S[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_S_ref\<rbrakk>\<^sub>S = readS (SCTLR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR_S[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SDER32_EL3[liftState_simp]:
  "\<lbrakk>read_reg SDER32_EL3_ref\<rbrakk>\<^sub>S = readS (SDER32_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SDER32_EL3[liftState_simp]:
  "\<lbrakk>write_reg SDER32_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SDER32_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>read_reg SPIDEN_ref\<rbrakk>\<^sub>S = readS (SPIDEN \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>write_reg SPIDEN_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPIDEN_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL1_ref\<rbrakk>\<^sub>S = readS (SPSR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL2_ref\<rbrakk>\<^sub>S = readS (SPSR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL3_ref\<rbrakk>\<^sub>S = readS (SPSR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>read_reg SPSR_abt_ref\<rbrakk>\<^sub>S = readS (SPSR_abt \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>write_reg SPSR_abt_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_abt_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_fiq_ref\<rbrakk>\<^sub>S = readS (SPSR_fiq \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_fiq_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_fiq_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_irq_ref\<rbrakk>\<^sub>S = readS (SPSR_irq \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_irq_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_irq_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>read_reg SPSR_und_ref\<rbrakk>\<^sub>S = readS (SPSR_und \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>write_reg SPSR_und_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_und_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_mon[liftState_simp]:
  "\<lbrakk>read_reg SP_mon_ref\<rbrakk>\<^sub>S = readS (SP_mon \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_mon[liftState_simp]:
  "\<lbrakk>write_reg SP_mon_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_mon_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ScheduledFIQ[liftState_simp]:
  "\<lbrakk>read_reg ScheduledFIQ_ref\<rbrakk>\<^sub>S = readS (ScheduledFIQ \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ScheduledFIQ[liftState_simp]:
  "\<lbrakk>write_reg ScheduledFIQ_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ScheduledFIQ_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ScheduledIRQ[liftState_simp]:
  "\<lbrakk>read_reg ScheduledIRQ_ref\<rbrakk>\<^sub>S = readS (ScheduledIRQ \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ScheduledIRQ[liftState_simp]:
  "\<lbrakk>write_reg ScheduledIRQ_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ScheduledIRQ_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL1_ref\<rbrakk>\<^sub>S = readS (TCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL3_ref\<rbrakk>\<^sub>S = readS (TCR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TCR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TFSRE0_EL1[liftState_simp]:
  "\<lbrakk>read_reg TFSRE0_EL1_ref\<rbrakk>\<^sub>S = readS (TFSRE0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TFSRE0_EL1[liftState_simp]:
  "\<lbrakk>write_reg TFSRE0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TFSRE0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TFSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TFSR_EL1_ref\<rbrakk>\<^sub>S = readS (TFSR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TFSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TFSR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TFSR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TFSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TFSR_EL2_ref\<rbrakk>\<^sub>S = readS (TFSR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TFSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TFSR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TFSR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TFSR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TFSR_EL3_ref\<rbrakk>\<^sub>S = readS (TFSR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TFSR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TFSR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TFSR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBHits[liftState_simp]:
  "\<lbrakk>read_reg TLBHits_ref\<rbrakk>\<^sub>S = readS (TLBHits \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBHits[liftState_simp]:
  "\<lbrakk>write_reg TLBHits_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBHits_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBMisses[liftState_simp]:
  "\<lbrakk>read_reg TLBMisses_ref\<rbrakk>\<^sub>S = readS (TLBMisses \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBMisses[liftState_simp]:
  "\<lbrakk>write_reg TLBMisses_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBMisses_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBCR2_S[liftState_simp]:
  "\<lbrakk>read_reg TTBCR2_S_ref\<rbrakk>\<^sub>S = readS (TTBCR2_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBCR2_S[liftState_simp]:
  "\<lbrakk>write_reg TTBCR2_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBCR2_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBCR_S[liftState_simp]:
  "\<lbrakk>read_reg TTBCR_S_ref\<rbrakk>\<^sub>S = readS (TTBCR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBCR_S[liftState_simp]:
  "\<lbrakk>write_reg TTBCR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBCR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL1_ref\<rbrakk>\<^sub>S = readS (TTBR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL2_ref\<rbrakk>\<^sub>S = readS (TTBR0_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR0_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL3_ref\<rbrakk>\<^sub>S = readS (TTBR0_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR0_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR0_S[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_S_ref\<rbrakk>\<^sub>S = readS (TTBR0_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR0_S[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR0_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL1_ref\<rbrakk>\<^sub>S = readS (TTBR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL2_ref\<rbrakk>\<^sub>S = readS (TTBR1_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR1_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR1_S[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_S_ref\<rbrakk>\<^sub>S = readS (TTBR1_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR1_S[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR1_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL1_ref\<rbrakk>\<^sub>S = readS (VBAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL2_ref\<rbrakk>\<^sub>S = readS (VBAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL3_ref\<rbrakk>\<^sub>S = readS (VBAR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_S[liftState_simp]:
  "\<lbrakk>read_reg VBAR_S_ref\<rbrakk>\<^sub>S = readS (VBAR_S \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_S[liftState_simp]:
  "\<lbrakk>write_reg VBAR_S_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_S_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSESR_EL2_ref\<rbrakk>\<^sub>S = readS (VSESR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSESR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VSESR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VSTCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSTCR_EL2_ref\<rbrakk>\<^sub>S = readS (VSTCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VSTCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSTCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VSTCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VSTTBR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSTTBR_EL2_ref\<rbrakk>\<^sub>S = readS (VSTTBR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VSTTBR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSTTBR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VSTTBR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTCR_EL2_ref\<rbrakk>\<^sub>S = readS (VTCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VTCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTTBR_EL2_ref\<rbrakk>\<^sub>S = readS (VTTBR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTTBR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VTTBR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_AXIAbortCtl[liftState_simp]:
  "\<lbrakk>read_reg AXIAbortCtl_ref\<rbrakk>\<^sub>S = readS (AXIAbortCtl \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_AXIAbortCtl[liftState_simp]:
  "\<lbrakk>write_reg AXIAbortCtl_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (AXIAbortCtl_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ClearFIQ[liftState_simp]:
  "\<lbrakk>read_reg ClearFIQ_ref\<rbrakk>\<^sub>S = readS (ClearFIQ \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ClearFIQ[liftState_simp]:
  "\<lbrakk>write_reg ClearFIQ_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ClearFIQ_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ClearIRQ[liftState_simp]:
  "\<lbrakk>read_reg ClearIRQ_ref\<rbrakk>\<^sub>S = readS (ClearIRQ \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ClearIRQ[liftState_simp]:
  "\<lbrakk>write_reg ClearIRQ_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ClearIRQ_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FIQPending[liftState_simp]:
  "\<lbrakk>read_reg FIQPending_ref\<rbrakk>\<^sub>S = readS (FIQPending \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FIQPending[liftState_simp]:
  "\<lbrakk>write_reg FIQPending_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FIQPending_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEActive[liftState_simp]:
  "\<lbrakk>read_reg GTEActive_ref\<rbrakk>\<^sub>S = readS (GTEActive \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEActive[liftState_simp]:
  "\<lbrakk>write_reg GTEActive_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEActive_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTECurrentAPI[liftState_simp]:
  "\<lbrakk>read_reg GTECurrentAPI_ref\<rbrakk>\<^sub>S = readS (GTECurrentAPI \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTECurrentAPI[liftState_simp]:
  "\<lbrakk>write_reg GTECurrentAPI_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTECurrentAPI_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEHaveParamLo[liftState_simp]:
  "\<lbrakk>read_reg GTEHaveParamLo_ref\<rbrakk>\<^sub>S = readS (GTEHaveParamLo \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEHaveParamLo[liftState_simp]:
  "\<lbrakk>write_reg GTEHaveParamLo_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEHaveParamLo_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEListParam[liftState_simp]:
  "\<lbrakk>read_reg GTEListParam_ref\<rbrakk>\<^sub>S = readS (GTEListParam \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEListParam[liftState_simp]:
  "\<lbrakk>write_reg GTEListParam_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEListParam_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEListParamIndex[liftState_simp]:
  "\<lbrakk>read_reg GTEListParamIndex_ref\<rbrakk>\<^sub>S = readS (GTEListParamIndex \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEListParamIndex[liftState_simp]:
  "\<lbrakk>write_reg GTEListParamIndex_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEListParamIndex_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEListParamTerminator[liftState_simp]:
  "\<lbrakk>read_reg GTEListParamTerminator_ref\<rbrakk>\<^sub>S = readS (GTEListParamTerminator \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEListParamTerminator[liftState_simp]:
  "\<lbrakk>write_reg GTEListParamTerminator_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEListParamTerminator_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEListParamTerminatorCount[liftState_simp]:
  "\<lbrakk>read_reg GTEListParamTerminatorCount_ref\<rbrakk>\<^sub>S = readS (GTEListParamTerminatorCount \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEListParamTerminatorCount[liftState_simp]:
  "\<lbrakk>write_reg GTEListParamTerminatorCount_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEListParamTerminatorCount_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEListParamTerminators[liftState_simp]:
  "\<lbrakk>read_reg GTEListParamTerminators_ref\<rbrakk>\<^sub>S = readS (GTEListParamTerminators \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEListParamTerminators[liftState_simp]:
  "\<lbrakk>write_reg GTEListParamTerminators_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEListParamTerminators_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEParamCount[liftState_simp]:
  "\<lbrakk>read_reg GTEParamCount_ref\<rbrakk>\<^sub>S = readS (GTEParamCount \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEParamCount[liftState_simp]:
  "\<lbrakk>write_reg GTEParamCount_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEParamCount_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEParamLo[liftState_simp]:
  "\<lbrakk>read_reg GTEParamLo_ref\<rbrakk>\<^sub>S = readS (GTEParamLo \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEParamLo[liftState_simp]:
  "\<lbrakk>write_reg GTEParamLo_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEParamLo_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEParamType[liftState_simp]:
  "\<lbrakk>read_reg GTEParamType_ref\<rbrakk>\<^sub>S = readS (GTEParamType \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEParamType[liftState_simp]:
  "\<lbrakk>write_reg GTEParamType_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEParamType_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEParamsComplete[liftState_simp]:
  "\<lbrakk>read_reg GTEParamsComplete_ref\<rbrakk>\<^sub>S = readS (GTEParamsComplete \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEParamsComplete[liftState_simp]:
  "\<lbrakk>write_reg GTEParamsComplete_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEParamsComplete_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTEStatus[liftState_simp]:
  "\<lbrakk>read_reg GTEStatus_ref\<rbrakk>\<^sub>S = readS (GTEStatus \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTEStatus[liftState_simp]:
  "\<lbrakk>write_reg GTEStatus_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTEStatus_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_AS_Access[liftState_simp]:
  "\<lbrakk>read_reg GTE_AS_Access_ref\<rbrakk>\<^sub>S = readS (GTE_AS_Access \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_AS_Access[liftState_simp]:
  "\<lbrakk>write_reg GTE_AS_Access_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_AS_Access_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_AS_AccessCount[liftState_simp]:
  "\<lbrakk>read_reg GTE_AS_AccessCount_ref\<rbrakk>\<^sub>S = readS (GTE_AS_AccessCount \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_AS_AccessCount[liftState_simp]:
  "\<lbrakk>write_reg GTE_AS_AccessCount_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_AS_AccessCount_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_AS_Address[liftState_simp]:
  "\<lbrakk>read_reg GTE_AS_Address_ref\<rbrakk>\<^sub>S = readS (GTE_AS_Address \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_AS_Address[liftState_simp]:
  "\<lbrakk>write_reg GTE_AS_Address_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_AS_Address_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GTE_AS_Size[liftState_simp]:
  "\<lbrakk>read_reg GTE_AS_Size_ref\<rbrakk>\<^sub>S = readS (GTE_AS_Size \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GTE_AS_Size[liftState_simp]:
  "\<lbrakk>write_reg GTE_AS_Size_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GTE_AS_Size_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_IRQPending[liftState_simp]:
  "\<lbrakk>read_reg IRQPending_ref\<rbrakk>\<^sub>S = readS (IRQPending \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_IRQPending[liftState_simp]:
  "\<lbrakk>write_reg IRQPending_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (IRQPending_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PC[liftState_simp]:
  "\<lbrakk>read_reg PC_ref\<rbrakk>\<^sub>S = readS (PC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PC[liftState_simp]:
  "\<lbrakk>write_reg PC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PPURACR[liftState_simp]:
  "\<lbrakk>read_reg PPURACR_ref\<rbrakk>\<^sub>S = readS (PPURACR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PPURACR[liftState_simp]:
  "\<lbrakk>write_reg PPURACR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PPURACR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PPURBAR[liftState_simp]:
  "\<lbrakk>read_reg PPURBAR_ref\<rbrakk>\<^sub>S = readS (PPURBAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PPURBAR[liftState_simp]:
  "\<lbrakk>write_reg PPURBAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PPURBAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PPURSER[liftState_simp]:
  "\<lbrakk>read_reg PPURSER_ref\<rbrakk>\<^sub>S = readS (PPURSER \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PPURSER[liftState_simp]:
  "\<lbrakk>write_reg PPURSER_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PPURSER_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PendingPhysicalSE[liftState_simp]:
  "\<lbrakk>read_reg PendingPhysicalSE_ref\<rbrakk>\<^sub>S = readS (PendingPhysicalSE \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PendingPhysicalSE[liftState_simp]:
  "\<lbrakk>write_reg PendingPhysicalSE_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PendingPhysicalSE_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_R[liftState_simp]:
  "\<lbrakk>read_reg R_ref\<rbrakk>\<^sub>S = readS (R \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_R[liftState_simp]:
  "\<lbrakk>write_reg R_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (R_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ScheduleFIQ[liftState_simp]:
  "\<lbrakk>read_reg ScheduleFIQ_ref\<rbrakk>\<^sub>S = readS (ScheduleFIQ \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ScheduleFIQ[liftState_simp]:
  "\<lbrakk>write_reg ScheduleFIQ_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ScheduleFIQ_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ScheduleIRQ[liftState_simp]:
  "\<lbrakk>read_reg ScheduleIRQ_ref\<rbrakk>\<^sub>S = readS (ScheduleIRQ \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ScheduleIRQ[liftState_simp]:
  "\<lbrakk>write_reg ScheduleIRQ_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ScheduleIRQ_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLB[liftState_simp]:
  "\<lbrakk>read_reg TLB_ref\<rbrakk>\<^sub>S = readS (TLB \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLB[liftState_simp]:
  "\<lbrakk>write_reg TLB_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLB_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TargetCPU[liftState_simp]:
  "\<lbrakk>read_reg TargetCPU_ref\<rbrakk>\<^sub>S = readS (TargetCPU \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TargetCPU[liftState_simp]:
  "\<lbrakk>write_reg TargetCPU_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TargetCPU_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CNTControlBase[liftState_simp]:
  "\<lbrakk>read_reg CNTControlBase_ref\<rbrakk>\<^sub>S = readS (CNTControlBase \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CNTControlBase[liftState_simp]:
  "\<lbrakk>write_reg CNTControlBase_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CNTControlBase_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LSISyndrome[liftState_simp]:
  "\<lbrakk>read_reg LSISyndrome_ref\<rbrakk>\<^sub>S = readS (LSISyndrome \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LSISyndrome[liftState_simp]:
  "\<lbrakk>write_reg LSISyndrome_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LSISyndrome_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PC_changed[liftState_simp]:
  "\<lbrakk>read_reg PC_changed_ref\<rbrakk>\<^sub>S = readS (PC_changed \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PC_changed[liftState_simp]:
  "\<lbrakk>write_reg PC_changed_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PC_changed_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_currentInstr[liftState_simp]:
  "\<lbrakk>read_reg currentInstr_ref\<rbrakk>\<^sub>S = readS (currentInstr \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_currentInstr[liftState_simp]:
  "\<lbrakk>write_reg currentInstr_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (currentInstr_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_currentInstrLength[liftState_simp]:
  "\<lbrakk>read_reg currentInstrLength_ref\<rbrakk>\<^sub>S = readS (currentInstrLength \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_currentInstrLength[liftState_simp]:
  "\<lbrakk>write_reg currentInstrLength_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (currentInstrLength_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_defaultRAM[liftState_simp]:
  "\<lbrakk>read_reg defaultRAM_ref\<rbrakk>\<^sub>S = readS (defaultRAM \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_defaultRAM[liftState_simp]:
  "\<lbrakk>write_reg defaultRAM_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (defaultRAM_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_highest_el_aarch32[liftState_simp]:
  "\<lbrakk>read_reg highest_el_aarch32_ref\<rbrakk>\<^sub>S = readS (highest_el_aarch32 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_highest_el_aarch32[liftState_simp]:
  "\<lbrakk>write_reg highest_el_aarch32_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (highest_el_aarch32_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

end
