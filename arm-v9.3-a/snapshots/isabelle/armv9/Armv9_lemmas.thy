theory Armv9_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Armv9_step
begin

lemma registers_distinct:
  "distinct (map fst registers)"
  unfolding registers_def list.simps fst_conv
  by (distinct_string; simp)

lemma registers_eqs_setup:
  "!x : set registers. map_of registers (fst x) = Some (snd x)"
  using registers_distinct
  by simp

lemmas map_of_registers_eqs[simp] =
    registers_eqs_setup[simplified arg_cong[where f=set, OF registers_def]
        list.simps ball_simps fst_conv snd_conv]

lemmas get_regval_unfold = get_regval_def[THEN fun_cong,
    unfolded register_accessors_def mk_accessors_def fst_conv snd_conv]
lemmas set_regval_unfold = set_regval_def[THEN fun_cong,
    unfolded register_accessors_def mk_accessors_def fst_conv snd_conv]

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_unfold set_regval_unfold STACK_LIMIT_ref_def STACK_BASE_ref_def
  HEAP_LIMIT_ref_def HEAP_BASE_ref_def DBG_ROM_ADDR_ref_def mops_forward_copy_ref_def
  trickbox_enabled_ref_def v93_implemented_ref_def v92_implemented_ref_def v91_implemented_ref_def
  v90_implemented_ref_def v88_implemented_ref_def v87_implemented_ref_def v86_implemented_ref_def
  v85_implemented_ref_def v84_implemented_ref_def v83_implemented_ref_def v82_implemented_ref_def
  v81_implemented_ref_def syncAbortOnDeviceWrite_ref_def syncAbortOnWriteNormNonCache_ref_def
  syncAbortOnWriteNormCache_ref_def syncAbortOnTTWNonCache_ref_def syncAbortOnTTWCache_ref_def
  syncAbortOnPrefetch_ref_def syncAbortOnSoWrite_ref_def syncAbortOnSoRead_ref_def
  syncAbortOnDeviceRead_ref_def syncAbortOnReadNormNonCache_ref_def syncAbortOnReadNormCache_ref_def
  PMUBase_ref_def GICITSControlBase_ref_def GICDistBase_ref_def GICCPUInterfaceBase_ref_def
  ExtDebugBase_ref_def CNTControlBase_ref_def CTIBase_ref_def CNTSCR_ref_def
  ExclusiveMonitorSet_ref_def ETEBase_ref_def VLPI_base_ref_def SGI_base_ref_def RD_base_ref_def
  CNTCTLBase_ref_def CNTEL0BaseN_ref_def CNTBaseN_ref_def CNTReadBase_ref_def
  InstructionStep_ref_def DTRTX_ref_def DTRRX_ref_def Dclone_ref_def BTypeCompatible_ref_def
  BTypeNext_ref_def RC_ref_def EventRegister_ref_def ShouldAdvanceSS_ref_def ShouldAdvanceIT_ref_def
  IsWFEsleep_ref_def IsWFIsleep_ref_def DBGOSLAR_ref_def TPIDRURW_S_ref_def TPIDRURO_S_ref_def
  TPIDRPRW_S_ref_def TCMTR_ref_def CNTP_CVAL_S_ref_def AMAIR1_S_ref_def AMAIR0_S_ref_def
  AIFSR_S_ref_def ADFSR_S_ref_def ACTLR_S_ref_def ACTLR2_S_ref_def CP15SDISABLE2_ref_def
  CP15SDISABLE_ref_def DACR_S_ref_def CONTEXTIDR_S_ref_def ignore_rvbar_in_aarch32_ref_def
  CFG_RMR_AA64_ref_def rme_l0gptsz_ref_def pan_implemented_ref_def mpam_has_altsp_ref_def
  gmid_log2_block_size_ref_def empam_frac_ref_def dot_product_implemented_ref_def
  dczid_log2_block_size_ref_def crc32_implemented_ref_def CNTbase_frequency_ref_def
  GICD_TYPER_ref_def CTIDEVARCH_ref_def CNTFID0_ref_def CFG_MPIDR_ref_def AMIIDR_ref_def
  AMDEVARCH_ref_def CNTV_TVAL_EL0_ref_def CNTP_TVAL_EL0_ref_def CNTPS_TVAL_EL1_ref_def
  CNTHV_TVAL_EL2_ref_def CNTHVS_TVAL_EL2_ref_def CNTHP_TVAL_EL2_ref_def CNTHPS_TVAL_EL2_ref_def
  fp16_implemented_ref_def exclusive_granule_size_ref_def ConfigReg_ref_def TLBTR_ref_def
  NMRR_S_ref_def FPSID_ref_def DBGDEVID_ref_def TTBR1_S_ref_def TTBR0_S_ref_def TTBCR2_S_ref_def
  SDCR_ref_def MAIR0_S_ref_def PMVIDSR_ref_def PMPIDR4_ref_def PMPIDR3_ref_def PMPIDR2_ref_def
  PMPIDR1_ref_def PMPIDR0_ref_def PMPCSR_ref_def PMMIR_ref_def PMLSR_ref_def PMLAR_ref_def
  PMITCTRL_ref_def PMDEVTYPE_ref_def PMDEVID_ref_def PMCIDR3_ref_def PMCIDR2_ref_def PMCIDR1_ref_def
  PMCIDR0_ref_def PMCFGR_ref_def PMAUTHSTATUS_ref_def PAR_S_ref_def JOSCR_ref_def JMCR_ref_def
  JIDR_ref_def ICC_MSRE_ref_def ICC_MGRPEN1_ref_def ICC_MCTLR_ref_def GITS_TYPER_ref_def
  GITS_STATUSR_ref_def GITS_SGIR_ref_def GITS_PARTIDR_ref_def GITS_MPIDR_ref_def
  GITS_MPAMIDR_ref_def GITS_IIDR_ref_def GITS_CWRITER_ref_def GITS_CTLR_ref_def GITS_CREADR_ref_def
  GITS_CBASER_ref_def GICV_STATUSR_ref_def GICV_RPR_ref_def GICV_PMR_ref_def GICV_IAR_ref_def
  GICV_HPPIR_ref_def GICV_EOIR_ref_def GICV_DIR_ref_def GICV_CTLR_ref_def GICV_BPR_ref_def
  GICV_AIAR_ref_def GICV_AHPPIR_ref_def GICV_AEOIR_ref_def GICV_ABPR_ref_def GICR_WAKER_ref_def
  GICR_VSGIR_ref_def GICR_VSGIPENDR_ref_def GICR_VPROPBASER_ref_def GICR_VPENDBASER_ref_def
  GICR_SYNCR_ref_def GICR_STATUSR_ref_def GICR_SETLPIR_ref_def GICR_PROPBASER_ref_def
  GICR_PENDBASER_ref_def GICR_PARTIDR_ref_def GICR_MPAMIDR_ref_def GICR_ISENABLER0_ref_def
  GICR_INVLPIR_ref_def GICR_INVALLR_ref_def GICR_INMIR0_ref_def GICR_IIDR_ref_def GICR_CTLR_ref_def
  GICR_CLRLPIR_ref_def GICM_TYPER_ref_def GICM_SETSPI_SR_ref_def GICM_SETSPI_NSR_ref_def
  GICM_IIDR_ref_def GICM_CLRSPI_SR_ref_def GICM_CLRSPI_NSR_ref_def GICH_VTR_ref_def
  GICH_VMCR_ref_def GICH_MISR_ref_def GICH_HCR_ref_def GICH_ELRSR_ref_def GICH_EISR_ref_def
  GICD_TYPER2_ref_def GICD_STATUSR_ref_def GICD_SGIR_ref_def GICD_SETSPI_SR_ref_def
  GICD_SETSPI_NSR_ref_def GICD_IIDR_ref_def GICD_CTLR_ref_def GICD_CLRSPI_SR_ref_def
  GICD_CLRSPI_NSR_ref_def GICC_STATUSR_ref_def GICC_RPR_ref_def GICC_PMR_ref_def GICC_IAR_ref_def
  GICC_HPPIR_ref_def GICC_EOIR_ref_def GICC_DIR_ref_def GICC_BPR_ref_def GICC_AIAR_ref_def
  GICC_AHPPIR_ref_def GICC_AEOIR_ref_def GICC_ABPR_ref_def FCSEIDR_ref_def EDVIDSR_ref_def
  EDRCR_ref_def EDPRCR_ref_def EDPIDR4_ref_def EDPIDR3_ref_def EDPIDR2_ref_def EDPIDR1_ref_def
  EDPIDR0_ref_def EDPFR_ref_def EDPCSR_ref_def EDLSR_ref_def EDLAR_ref_def EDITCTRL_ref_def
  EDHSR_ref_def EDESR_ref_def EDECR_ref_def EDDFR_ref_def EDDEVTYPE_ref_def EDDEVID2_ref_def
  EDDEVID1_ref_def EDDEVID_ref_def EDCIDR3_ref_def EDCIDR2_ref_def EDCIDR1_ref_def EDCIDR0_ref_def
  EDAA32PFR_ref_def DBGWFAR_ref_def DBGDSAR_ref_def DBGDIDR_ref_def DBGDEVID2_ref_def
  DBGDEVID1_ref_def CTIPIDR4_ref_def CTIPIDR3_ref_def CTIPIDR2_ref_def CTIPIDR1_ref_def
  CTIPIDR0_ref_def CTILSR_ref_def CTILAR_ref_def CTIITCTRL_ref_def CTIDEVTYPE_ref_def
  CTIDEVID2_ref_def CTIDEVID1_ref_def CTIDEVID_ref_def CTIDEVCTL_ref_def CTICONTROL_ref_def
  CTICIDR3_ref_def CTICIDR2_ref_def CTICIDR1_ref_def CTICIDR0_ref_def CTIAUTHSTATUS_ref_def
  CSSELR_S_ref_def CNTSR_ref_def CNTP_CTL_S_ref_def CNTNSAR_ref_def CNTID_ref_def CNTEL0ACR_ref_def
  CNTCR_ref_def AMPIDR4_ref_def AMPIDR3_ref_def AMPIDR2_ref_def AMPIDR1_ref_def AMPIDR0_ref_def
  AMDEVTYPE_ref_def AMCIDR3_ref_def AMCIDR2_ref_def AMCIDR1_ref_def AMCIDR0_ref_def
  clock_divider_ref_def EDPRSR_ref_def PMSWINC_EL0_ref_def OSLAR_EL1_ref_def ICV_EOIR1_EL1_ref_def
  ICC_EOIR1_EL1_ref_def ICV_EOIR0_EL1_ref_def ICC_EOIR0_EL1_ref_def ICC_SGI1R_EL1_ref_def
  ICC_SGI0R_EL1_ref_def ICV_DIR_EL1_ref_def ICC_DIR_EL1_ref_def ICC_ASGI1R_EL1_ref_def
  DBGDTRTX_EL0_ref_def VSESR_EL2_ref_def VMPIDR_EL2_ref_def MPIDR_EL1_ref_def VDISR_EL2_ref_def
  DISR_EL1_ref_def TRFCR_EL2_ref_def TRFCR_EL1_ref_def TPIDR_EL3_ref_def TPIDR_EL2_ref_def
  TPIDR_EL1_ref_def TPIDR_EL0_ref_def TPIDRRO_EL0_ref_def TPIDR2_EL0_ref_def SMPRI_EL1_ref_def
  SMPRIMAP_EL2_ref_def SMIDR_EL1_ref_def SCXTNUM_EL3_ref_def SCXTNUM_EL2_ref_def SCXTNUM_EL1_ref_def
  SCXTNUM_EL0_ref_def RVBAR_EL3_ref_def RVBAR_EL2_ref_def RVBAR_EL1_ref_def RNDR_ref_def
  RNDRRS_ref_def RMR_EL3_ref_def RMR_EL2_ref_def RMR_EL1_ref_def RGSR_EL1_ref_def REVIDR_EL1_ref_def
  PMXEVTYPER_EL0_ref_def PMXEVCNTR_EL0_ref_def PMSNEVFR_EL1_ref_def PMSLATFR_EL1_ref_def
  PMSIRR_EL1_ref_def PMSIDR_EL1_ref_def PMSICR_EL1_ref_def PMSFCR_EL1_ref_def PMSEVFR_EL1_ref_def
  PMSELR_EL0_ref_def PMSCR_EL2_ref_def PMSCR_EL1_ref_def PMOVSSET_EL0_ref_def PMOVSCLR_EL0_ref_def
  PMMIR_EL1_ref_def PMINTENSET_EL1_ref_def PMINTENCLR_EL1_ref_def PMEVCNTR_EL0_ref_def
  PMCNTENSET_EL0_ref_def PMCNTENCLR_EL0_ref_def PMCEID1_EL0_ref_def PMCEID0_EL0_ref_def
  PMCCNTR_EL0_ref_def PMUSERENR_EL0_ref_def PMCCFILTR_EL0_ref_def PMBSR_EL1_ref_def
  PMBPTR_EL1_ref_def PMBLIMITR_EL1_ref_def PMBIDR_EL1_ref_def PAR_EL1_ref_def OSDTRTX_EL1_ref_def
  OSDTRRX_EL1_ref_def MVFR2_EL1_ref_def MVFR1_EL1_ref_def MVFR0_EL1_ref_def VPIDR_EL2_ref_def
  MIDR_EL1_ref_def MDRAR_EL1_ref_def MDCCINT_EL1_ref_def LORSA_EL1_ref_def LORN_EL1_ref_def
  LORID_EL1_ref_def LOREA_EL1_ref_def LORC_EL1_ref_def ISR_EL1_ref_def ID_PFR2_EL1_ref_def
  ID_PFR1_EL1_ref_def ID_PFR0_EL1_ref_def ID_MMFR5_EL1_ref_def ID_MMFR4_EL1_ref_def
  ID_MMFR3_EL1_ref_def ID_MMFR2_EL1_ref_def ID_MMFR1_EL1_ref_def ID_MMFR0_EL1_ref_def
  ID_ISAR6_EL1_ref_def ID_ISAR5_EL1_ref_def ID_ISAR4_EL1_ref_def ID_ISAR3_EL1_ref_def
  ID_ISAR2_EL1_ref_def ID_ISAR1_EL1_ref_def ID_ISAR0_EL1_ref_def ID_DFR1_EL1_ref_def
  ID_DFR0_EL1_ref_def ID_AFR0_EL1_ref_def ID_AA64ZFR0_EL1_ref_def ID_AA64SMFR0_EL1_ref_def
  ID_AA64PFR1_EL1_ref_def ID_AA64PFR0_EL1_ref_def ID_AA64MMFR2_EL1_ref_def ID_AA64MMFR1_EL1_ref_def
  ID_AA64MMFR0_EL1_ref_def ID_AA64ISAR2_EL1_ref_def ID_AA64ISAR1_EL1_ref_def
  ID_AA64ISAR0_EL1_ref_def ID_AA64DFR1_EL1_ref_def ID_AA64DFR0_EL1_ref_def ID_AA64AFR1_EL1_ref_def
  ID_AA64AFR0_EL1_ref_def ICV_NMIAR1_EL1_ref_def ICC_NMIAR1_EL1_ref_def ICV_BPR1_EL1_ref_def
  ICC_BPR1_EL1_S_ref_def ICC_BPR1_EL1_NS_ref_def ICH_VTR_EL2_ref_def ICH_VMCR_EL2_ref_def
  ICH_MISR_EL2_ref_def ICH_LR_EL2_ref_def ICH_ELRSR_EL2_ref_def ICH_EISR_EL2_ref_def
  ICH_AP1R_EL2_ref_def ICH_AP0R_EL2_ref_def ICV_RPR_EL1_ref_def ICC_RPR_EL1_ref_def
  ICV_PMR_EL1_ref_def ICC_IGRPEN1_EL3_ref_def ICV_IGRPEN1_EL1_ref_def ICC_IGRPEN1_EL1_S_ref_def
  ICC_IGRPEN1_EL1_NS_ref_def ICV_IGRPEN0_EL1_ref_def ICC_IGRPEN0_EL1_ref_def ICV_IAR1_EL1_ref_def
  ICC_IAR1_EL1_ref_def ICV_IAR0_EL1_ref_def ICC_IAR0_EL1_ref_def ICV_HPPIR1_EL1_ref_def
  ICC_HPPIR1_EL1_ref_def ICV_HPPIR0_EL1_ref_def ICC_HPPIR0_EL1_ref_def ICC_CTLR_EL3_ref_def
  ICV_CTLR_EL1_ref_def ICC_CTLR_EL1_S_ref_def ICC_CTLR_EL1_NS_ref_def ICV_BPR0_EL1_ref_def
  ICC_BPR0_EL1_ref_def ICV_AP1R_EL1_ref_def ICC_AP1R_EL1_S_ref_def ICC_AP1R_EL1_NS_ref_def
  ICV_AP0R_EL1_ref_def ICH_HCR_EL2_ref_def ICC_SRE_EL3_ref_def ICC_SRE_EL2_ref_def
  ICC_SRE_EL1_S_ref_def ICC_SRE_EL1_NS_ref_def ICC_AP0R_EL1_ref_def HSTR_EL2_ref_def
  HFGWTR_EL2_ref_def HFGITR_EL2_ref_def HDFGWTR_EL2_ref_def HACR_EL2_ref_def GMID_EL1_ref_def
  GCR_EL1_ref_def FPEXC32_EL2_ref_def ERXSTATUS_EL1_ref_def ERXPFGF_EL1_ref_def
  ERXPFGCTL_EL1_ref_def ERXPFGCDN_EL1_ref_def ERXMISC3_EL1_ref_def ERXMISC2_EL1_ref_def
  ERXMISC1_EL1_ref_def ERXMISC0_EL1_ref_def ERXFR_EL1_ref_def ERXCTLR_EL1_ref_def
  ERXADDR_EL1_ref_def ERRSELR_EL1_ref_def ERRIDR_EL1_ref_def DCZID_EL0_ref_def DBGVCR32_EL2_ref_def
  DBGDTR_EL0_ref_def DBGDTRRX_EL0_ref_def DBGCLAIMSET_EL1_ref_def DBGCLAIMCLR_EL1_ref_def
  DBGAUTHSTATUS_EL1_ref_def DACR32_EL2_ref_def CSSELR_EL1_ref_def CNTPS_CVAL_EL1_ref_def
  CNTPS_CTL_EL1_ref_def CNTVOFF_EL2_ref_def CNTV_CVAL_EL0_ref_def CNTHV_CVAL_EL2_ref_def
  CNTHVS_CVAL_EL2_ref_def CNTV_CTL_EL0_ref_def CNTHV_CTL_EL2_ref_def CNTHVS_CTL_EL2_ref_def
  CNTP_CVAL_EL0_ref_def CNTP_CTL_EL0_ref_def CNTPOFF_EL2_ref_def CNTHP_CVAL_EL2_ref_def
  CNTHP_CTL_EL2_ref_def CNTHPS_CVAL_EL2_ref_def CNTHPS_CTL_EL2_ref_def CNTKCTL_EL1_ref_def
  CNTHCTL_EL2_ref_def CNTFRQ_EL0_ref_def CCSIDR_EL1_ref_def CCSIDR2_EL1_ref_def BRBTS_EL1_ref_def
  BRBTGT_EL1_ref_def BRBTGTINJ_EL1_ref_def BRBSRC_EL1_ref_def BRBSRCINJ_EL1_ref_def
  BRBINF_EL1_ref_def BRBINFINJ_EL1_ref_def HDFGRTR_EL2_ref_def APIBKeyLo_EL1_ref_def
  APIBKeyHi_EL1_ref_def APIAKeyLo_EL1_ref_def APIAKeyHi_EL1_ref_def APGAKeyLo_EL1_ref_def
  APGAKeyHi_EL1_ref_def APDBKeyLo_EL1_ref_def APDBKeyHi_EL1_ref_def APDAKeyLo_EL1_ref_def
  APDAKeyHi_EL1_ref_def AMEVTYPER1_EL0_ref_def AMEVTYPER0_EL0_ref_def AMEVCNTVOFF1_EL2_ref_def
  AMEVCNTVOFF0_EL2_ref_def AMEVCNTR1_EL0_ref_def AMEVCNTR0_ref_def AMCR_EL0_ref_def
  AMCNTENSET1_EL0_ref_def AMCNTENSET0_EL0_ref_def AMCNTENCLR1_EL0_ref_def HAFGRTR_EL2_ref_def
  AMCNTENCLR0_EL0_ref_def AMCGCR_EL0_ref_def AMCG1IDR_EL0_ref_def AMUSERENR_EL0_ref_def
  AMCFGR_EL0_ref_def AMAIR_EL3_ref_def AMAIR_EL2_ref_def AMAIR_EL1_ref_def AIDR_EL1_ref_def
  AFSR1_EL3_ref_def AFSR1_EL2_ref_def AFSR1_EL1_ref_def AFSR0_EL3_ref_def AFSR0_EL2_ref_def
  AFSR0_EL1_ref_def ACTLR_EL3_ref_def ACTLR_EL2_ref_def VNCR_EL2_ref_def tlb_enabled_ref_def
  VSTTBR_EL2_ref_def VSTCR_EL2_ref_def TTBR0_EL3_ref_def TTBR1_EL2_ref_def TTBR0_EL2_ref_def
  TTBR1_EL1_ref_def TTBR0_EL1_ref_def InGuardedPage_ref_def GIC_Active_ref_def GICC_CTLR_ref_def
  GPTBR_EL3_ref_def GPCCR_EL3_ref_def MPAMSM_EL1_ref_def MPAM0_EL1_ref_def MPAMVPM7_EL2_ref_def
  MPAMVPM6_EL2_ref_def MPAMVPM5_EL2_ref_def MPAMVPM4_EL2_ref_def MPAMVPM3_EL2_ref_def
  MPAMVPM2_EL2_ref_def MPAMVPM1_EL2_ref_def MPAMVPMV_EL2_ref_def MPAMVPM0_EL2_ref_def
  MPAMHCR_EL2_ref_def MPAM1_EL1_0_62_ref_def MPAMIDR_EL1_ref_def MPAM2_EL2_0_62_ref_def
  MPAM3_EL3_ref_def MAIR_EL3_ref_def MAIR_EL2_ref_def MAIR_EL1_ref_def SDER32_EL2_ref_def
  EDWAR_ref_def DBGWVR_EL1_ref_def DBGWCR_EL1_ref_def OSLSR_EL1_ref_def VTTBR_EL2_ref_def
  VTCR_EL2_ref_def DBGBVR_EL1_ref_def DBGBCR_EL1_ref_def CONTEXTIDR_EL2_ref_def
  CONTEXTIDR_EL1_ref_def TFSR_EL3_ref_def TFSR_EL2_ref_def TFSR_EL1_ref_def TFSRE0_EL1_ref_def
  DBGDSCRint_16_28_ref_def MDSCR_EL1_ref_def TTBCR_S_ref_def IFSR_S_ref_def IFSR32_EL2_ref_def
  DFSR_S_ref_def MVBAR_ref_def ACTLR_EL1_ref_def HFGRTR_EL2_ref_def ACCDATA_EL1_ref_def
  VBAR_S_ref_def VBAR_EL3_ref_def VBAR_EL2_ref_def VBAR_EL1_ref_def SPSR_und_ref_def
  SPSR_mon_ref_def SPSR_irq_ref_def SPSR_fiq_ref_def SPSR_abt_ref_def SPSR_EL3_ref_def
  SPSR_EL2_ref_def SPSR_EL1_ref_def SCTLR_S_ref_def SCTLR_EL3_ref_def SCTLR_EL2_ref_def
  SCTLR_EL1_ref_def ZA_ref_def Z_ref_def SP_EL3_ref_def SP_EL2_ref_def SP_EL1_ref_def SP_EL0_ref_def
  P_ref_def NSACR_ref_def CPTR_EL3_ref_def CPTR_EL2_ref_def CPACR_EL1_ref_def FFR_ref_def
  SMCR_EL3_ref_def SMCR_EL2_ref_def SMCR_EL1_ref_def max_implemented_smeveclen_ref_def
  ZCR_EL3_ref_def ZCR_EL2_ref_def ZCR_EL1_ref_def ELR_EL3_ref_def ELR_EL2_ref_def ELR_EL1_ref_def
  RTPIDEN_ref_def RLPIDEN_ref_def DBGPRCR_EL1_ref_def OSDLR_EL1_ref_def SPIDEN_ref_def DBGEN_ref_def
  EDSCR_31_31_ref_def EDSCR_0_28_ref_def MDCCSR_EL0_ref_def DSPSR_EL0_ref_def DLR_EL0_ref_def
  OSECCR_EL1_ref_def BranchTaken_ref_def PC_ref_def SP_mon_ref_def LR_mon_ref_def TCR_EL3_ref_def
  TCR_EL2_ref_def TCR_EL1_ref_def Records_TGT_ref_def Records_SRC_ref_def Records_INF_ref_def
  BRBIDR0_EL1_ref_def TSTATE_ref_def ICC_PMR_EL1_ref_def PMUEventAccumulator_ref_def
  PMEVTYPER_EL0_ref_def PMCR_EL0_ref_def MDCR_EL2_ref_def MDCR_EL3_ref_def last_branch_valid_ref_def
  last_cycle_count_ref_def BRBFCR_EL1_ref_def BRBCR_EL2_ref_def BRBCR_EL1_ref_def MFAR_EL3_ref_def
  HPFAR_EL2_ref_def FAR_EL3_ref_def FAR_EL2_ref_def FAR_EL1_ref_def ESR_EL3_ref_def ESR_EL2_ref_def
  ESR_EL1_ref_def ThisInstrEnc_ref_def R_ref_def ThisInstr_ref_def unpred_tsize_aborts_ref_def
  ICACHE_CCSIDR_RESET_ref_def DCACHE_CCSIDR_RESET_ref_def CLIDR_EL1_ref_def cycle_count_ref_def
  GIC_Pending_ref_def HCRX_EL2_ref_def SCR_ref_def SCR_EL3_ref_def HCR_EL2_ref_def
  trcclaim_tags_ref_def claim_tags_ref_def ERRnFR_ref_def RVBAR_ref_def FPSR_ref_def FPCR_ref_def
  mpam_vpmr_max_ref_def mpam_pmg_max_ref_def mpam_partid_max_ref_def mpam_has_hcr_ref_def
  impdef_res_TG1_ref_def impdef_res_TG0_ref_def PhysicalCount_ref_def CFG_RVBAR_ref_def
  supported_va_size_ref_def supported_pa_size_ref_def num_watchpoints_ref_def
  num_event_counters_ref_def num_ctx_breakpoints_ref_def num_breakpoints_ref_def
  num_brb_records_ref_def has_sve_extended_bf16_ref_def block_bbm_implemented_ref_def
  CTR_EL0_ref_def vmid16_implemented_ref_def sme_only_ref_def rme_implemented_ref_def
  pacqarma5_implemented_ref_def pacqarma3_implemented_ref_def pac_frac_implemented_ref_def
  mte_implemented_ref_def mpam_implemented_ref_def mops_option_a_supported_ref_def
  isb_is_branch_ref_def highest_el_aarch32_ref_def has_sme_priority_control_ref_def
  has_sme_i16i64_ref_def has_sme_f64f64_ref_def has_sme_ref_def feat_ls64_v_ref_def
  feat_ls64_accdata_ref_def feat_ls64_ref_def empam_tidr_implemented_ref_def
  empam_sdeflt_implemented_ref_def empam_implemented_ref_def empam_force_ns_implemented_ref_def
  empam_force_ns_RAO_ref_def crypto_sm4_implemented_ref_def crypto_sm3_implemented_ref_def
  crypto_sha512_implemented_ref_def crypto_sha3_implemented_ref_def
  crypto_sha256_implemented_ref_def crypto_sha1_implemented_ref_def crypto_aes_implemented_ref_def
  brbev1p1_implemented_ref_def brbe_implemented_ref_def apply_effective_shareability_ref_def
  aa32_hpd_implemented_ref_def PSTATE_ref_def SEE_ref_def

lemma bool_of_register_value_eq_Some_iff[simp]:
  "bool_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_bool v"
  by (cases rv; auto)

declare register_value_of_bool_def[simp]

lemma regval_bool[simp]:
  "bool_of_register_value (register_value_of_bool v) = Some v"
  by auto

lemma int_of_register_value_eq_Some_iff[simp]:
  "int_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_int v"
  by (cases rv; auto)

declare register_value_of_int_def[simp]

lemma regval_int[simp]:
  "int_of_register_value (register_value_of_int v) = Some v"
  by auto

lemma real_of_register_value_eq_Some_iff[simp]:
  "real_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_real v"
  by (cases rv; auto)

declare register_value_of_real_def[simp]

lemma regval_real[simp]:
  "real_of_register_value (register_value_of_real v) = Some v"
  by auto

lemma string_of_register_value_eq_Some_iff[simp]:
  "string_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_string v"
  by (cases rv; auto)

declare register_value_of_string_def[simp]

lemma regval_string[simp]:
  "string_of_register_value (register_value_of_string v) = Some v"
  by auto

lemma InterruptID_of_regval_eq_Some_iff[simp]:
  "InterruptID_of_regval rv = Some v \<longleftrightarrow> rv = Regval_InterruptID v"
  by (cases rv; auto)

declare regval_of_InterruptID_def[simp]

lemma regval_InterruptID[simp]:
  "InterruptID_of_regval (regval_of_InterruptID v) = Some v"
  by auto

lemma ProcState_of_regval_eq_Some_iff[simp]:
  "ProcState_of_regval rv = Some v \<longleftrightarrow> rv = Regval_ProcState v"
  by (cases rv; auto)

declare regval_of_ProcState_def[simp]

lemma regval_ProcState[simp]:
  "ProcState_of_regval (regval_of_ProcState v) = Some v"
  by auto

lemma TMState_of_regval_eq_Some_iff[simp]:
  "TMState_of_regval rv = Some v \<longleftrightarrow> rv = Regval_TMState v"
  by (cases rv; auto)

declare regval_of_TMState_def[simp]

lemma regval_TMState[simp]:
  "TMState_of_regval (regval_of_TMState v) = Some v"
  by auto

lemma InstrEnc_of_regval_eq_Some_iff[simp]:
  "InstrEnc_of_regval rv = Some v \<longleftrightarrow> rv = Regval___InstrEnc v"
  by (cases rv; auto)

declare regval_of___InstrEnc_def[simp]

lemma regval___InstrEnc[simp]:
  "InstrEnc_of_regval (regval_of___InstrEnc v) = Some v"
  by auto

lemma bit_of_regval_eq_Some_iff[simp]:
  "bit_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bit v"
  by (cases rv; auto)

declare regval_of_bit_def[simp]

lemma regval_bit[simp]:
  "bit_of_regval (regval_of_bit v) = Some v"
  by auto

lemma bitvector_13_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_13_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_13_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_13_dec_def[simp]

lemma regval_bitvector_13_dec[simp]:
  "bitvector_13_dec_of_regval (regval_of_bitvector_13_dec v) = Some v"
  by auto

lemma bitvector_16_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_16_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_16_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_16_dec_def[simp]

lemma regval_bitvector_16_dec[simp]:
  "bitvector_16_dec_of_regval (regval_of_bitvector_16_dec v) = Some v"
  by auto

lemma bitvector_1_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_1_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_1_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_1_dec_def[simp]

lemma regval_bitvector_1_dec[simp]:
  "bitvector_1_dec_of_regval (regval_of_bitvector_1_dec v) = Some v"
  by auto

lemma bitvector_2048_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_2048_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_2048_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_2048_dec_def[simp]

lemma regval_bitvector_2048_dec[simp]:
  "bitvector_2048_dec_of_regval (regval_of_bitvector_2048_dec v) = Some v"
  by auto

lemma bitvector_256_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_256_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_256_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_256_dec_def[simp]

lemma regval_bitvector_256_dec[simp]:
  "bitvector_256_dec_of_regval (regval_of_bitvector_256_dec v) = Some v"
  by auto

lemma bitvector_29_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_29_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_29_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_29_dec_def[simp]

lemma regval_bitvector_29_dec[simp]:
  "bitvector_29_dec_of_regval (regval_of_bitvector_29_dec v) = Some v"
  by auto

lemma bitvector_2_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_2_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_2_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_2_dec_def[simp]

lemma regval_bitvector_2_dec[simp]:
  "bitvector_2_dec_of_regval (regval_of_bitvector_2_dec v) = Some v"
  by auto

lemma bitvector_32_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_32_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_32_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_32_dec_def[simp]

lemma regval_bitvector_32_dec[simp]:
  "bitvector_32_dec_of_regval (regval_of_bitvector_32_dec v) = Some v"
  by auto

lemma bitvector_3_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_3_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_3_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_3_dec_def[simp]

lemma regval_bitvector_3_dec[simp]:
  "bitvector_3_dec_of_regval (regval_of_bitvector_3_dec v) = Some v"
  by auto

lemma bitvector_4_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_4_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_4_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_4_dec_def[simp]

lemma regval_bitvector_4_dec[simp]:
  "bitvector_4_dec_of_regval (regval_of_bitvector_4_dec v) = Some v"
  by auto

lemma bitvector_52_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_52_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_52_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_52_dec_def[simp]

lemma regval_bitvector_52_dec[simp]:
  "bitvector_52_dec_of_regval (regval_of_bitvector_52_dec v) = Some v"
  by auto

lemma bitvector_63_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_63_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_63_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_63_dec_def[simp]

lemma regval_bitvector_63_dec[simp]:
  "bitvector_63_dec_of_regval (regval_of_bitvector_63_dec v) = Some v"
  by auto

lemma bitvector_64_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_64_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_64_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_64_dec_def[simp]

lemma regval_bitvector_64_dec[simp]:
  "bitvector_64_dec_of_regval (regval_of_bitvector_64_dec v) = Some v"
  by auto

lemma bitvector_88_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_88_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_88_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_88_dec_def[simp]

lemma regval_bitvector_88_dec[simp]:
  "bitvector_88_dec_of_regval (regval_of_bitvector_88_dec v) = Some v"
  by auto

lemma bitvector_8_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_8_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_8_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_8_dec_def[simp]

lemma regval_bitvector_8_dec[simp]:
  "bitvector_8_dec_of_regval (regval_of_bitvector_8_dec v) = Some v"
  by auto

lemma signal_of_regval_eq_Some_iff[simp]:
  "signal_of_regval rv = Some v \<longleftrightarrow> rv = Regval_signal v"
  by (cases rv; auto)

declare regval_of_signal_def[simp]

lemma regval_signal[simp]:
  "signal_of_regval (regval_of_signal v) = Some v"
  by auto

lemma vector_of_rv_rv_of_vector[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "vector_of_regval of_rv (regval_of_vector rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  then show ?thesis by (auto simp: regval_of_vector_def)
qed

lemma option_of_rv_rv_of_option[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "option_of_regval of_rv (regval_of_option rv_of v) = Some v"
  using assms by (cases v) (auto simp: regval_of_option_def)

lemma list_of_rv_rv_of_list[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "list_of_regval of_rv (regval_of_list rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  with assms show ?thesis by (induction v) (auto simp: regval_of_list_def)
qed

lemma liftS_read_reg_STACK_LIMIT[liftState_simp]:
  "\<lbrakk>read_reg STACK_LIMIT_ref\<rbrakk>\<^sub>S = read_regS STACK_LIMIT_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_STACK_LIMIT[liftState_simp]:
  "\<lbrakk>write_reg STACK_LIMIT_ref v\<rbrakk>\<^sub>S = write_regS STACK_LIMIT_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_STACK_BASE[liftState_simp]:
  "\<lbrakk>read_reg STACK_BASE_ref\<rbrakk>\<^sub>S = read_regS STACK_BASE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_STACK_BASE[liftState_simp]:
  "\<lbrakk>write_reg STACK_BASE_ref v\<rbrakk>\<^sub>S = write_regS STACK_BASE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HEAP_LIMIT[liftState_simp]:
  "\<lbrakk>read_reg HEAP_LIMIT_ref\<rbrakk>\<^sub>S = read_regS HEAP_LIMIT_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HEAP_LIMIT[liftState_simp]:
  "\<lbrakk>write_reg HEAP_LIMIT_ref v\<rbrakk>\<^sub>S = write_regS HEAP_LIMIT_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HEAP_BASE[liftState_simp]:
  "\<lbrakk>read_reg HEAP_BASE_ref\<rbrakk>\<^sub>S = read_regS HEAP_BASE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HEAP_BASE[liftState_simp]:
  "\<lbrakk>write_reg HEAP_BASE_ref v\<rbrakk>\<^sub>S = write_regS HEAP_BASE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBG_ROM_ADDR[liftState_simp]:
  "\<lbrakk>read_reg DBG_ROM_ADDR_ref\<rbrakk>\<^sub>S = read_regS DBG_ROM_ADDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBG_ROM_ADDR[liftState_simp]:
  "\<lbrakk>write_reg DBG_ROM_ADDR_ref v\<rbrakk>\<^sub>S = write_regS DBG_ROM_ADDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mops_forward_copy[liftState_simp]:
  "\<lbrakk>read_reg mops_forward_copy_ref\<rbrakk>\<^sub>S = read_regS mops_forward_copy_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mops_forward_copy[liftState_simp]:
  "\<lbrakk>write_reg mops_forward_copy_ref v\<rbrakk>\<^sub>S = write_regS mops_forward_copy_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_trickbox_enabled[liftState_simp]:
  "\<lbrakk>read_reg trickbox_enabled_ref\<rbrakk>\<^sub>S = read_regS trickbox_enabled_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_trickbox_enabled[liftState_simp]:
  "\<lbrakk>write_reg trickbox_enabled_ref v\<rbrakk>\<^sub>S = write_regS trickbox_enabled_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v93_implemented[liftState_simp]:
  "\<lbrakk>read_reg v93_implemented_ref\<rbrakk>\<^sub>S = read_regS v93_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v93_implemented[liftState_simp]:
  "\<lbrakk>write_reg v93_implemented_ref v\<rbrakk>\<^sub>S = write_regS v93_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v92_implemented[liftState_simp]:
  "\<lbrakk>read_reg v92_implemented_ref\<rbrakk>\<^sub>S = read_regS v92_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v92_implemented[liftState_simp]:
  "\<lbrakk>write_reg v92_implemented_ref v\<rbrakk>\<^sub>S = write_regS v92_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v91_implemented[liftState_simp]:
  "\<lbrakk>read_reg v91_implemented_ref\<rbrakk>\<^sub>S = read_regS v91_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v91_implemented[liftState_simp]:
  "\<lbrakk>write_reg v91_implemented_ref v\<rbrakk>\<^sub>S = write_regS v91_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v90_implemented[liftState_simp]:
  "\<lbrakk>read_reg v90_implemented_ref\<rbrakk>\<^sub>S = read_regS v90_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v90_implemented[liftState_simp]:
  "\<lbrakk>write_reg v90_implemented_ref v\<rbrakk>\<^sub>S = write_regS v90_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v88_implemented[liftState_simp]:
  "\<lbrakk>read_reg v88_implemented_ref\<rbrakk>\<^sub>S = read_regS v88_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v88_implemented[liftState_simp]:
  "\<lbrakk>write_reg v88_implemented_ref v\<rbrakk>\<^sub>S = write_regS v88_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v87_implemented[liftState_simp]:
  "\<lbrakk>read_reg v87_implemented_ref\<rbrakk>\<^sub>S = read_regS v87_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v87_implemented[liftState_simp]:
  "\<lbrakk>write_reg v87_implemented_ref v\<rbrakk>\<^sub>S = write_regS v87_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v86_implemented[liftState_simp]:
  "\<lbrakk>read_reg v86_implemented_ref\<rbrakk>\<^sub>S = read_regS v86_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v86_implemented[liftState_simp]:
  "\<lbrakk>write_reg v86_implemented_ref v\<rbrakk>\<^sub>S = write_regS v86_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v85_implemented[liftState_simp]:
  "\<lbrakk>read_reg v85_implemented_ref\<rbrakk>\<^sub>S = read_regS v85_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v85_implemented[liftState_simp]:
  "\<lbrakk>write_reg v85_implemented_ref v\<rbrakk>\<^sub>S = write_regS v85_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v84_implemented[liftState_simp]:
  "\<lbrakk>read_reg v84_implemented_ref\<rbrakk>\<^sub>S = read_regS v84_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v84_implemented[liftState_simp]:
  "\<lbrakk>write_reg v84_implemented_ref v\<rbrakk>\<^sub>S = write_regS v84_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v83_implemented[liftState_simp]:
  "\<lbrakk>read_reg v83_implemented_ref\<rbrakk>\<^sub>S = read_regS v83_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v83_implemented[liftState_simp]:
  "\<lbrakk>write_reg v83_implemented_ref v\<rbrakk>\<^sub>S = write_regS v83_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v82_implemented[liftState_simp]:
  "\<lbrakk>read_reg v82_implemented_ref\<rbrakk>\<^sub>S = read_regS v82_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v82_implemented[liftState_simp]:
  "\<lbrakk>write_reg v82_implemented_ref v\<rbrakk>\<^sub>S = write_regS v82_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_v81_implemented[liftState_simp]:
  "\<lbrakk>read_reg v81_implemented_ref\<rbrakk>\<^sub>S = read_regS v81_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_v81_implemented[liftState_simp]:
  "\<lbrakk>write_reg v81_implemented_ref v\<rbrakk>\<^sub>S = write_regS v81_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnDeviceWrite[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnDeviceWrite_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnDeviceWrite_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnDeviceWrite[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnDeviceWrite_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnDeviceWrite_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnWriteNormNonCache[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnWriteNormNonCache_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnWriteNormNonCache_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnWriteNormNonCache[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnWriteNormNonCache_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnWriteNormNonCache_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnWriteNormCache[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnWriteNormCache_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnWriteNormCache_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnWriteNormCache[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnWriteNormCache_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnWriteNormCache_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnTTWNonCache[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnTTWNonCache_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnTTWNonCache_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnTTWNonCache[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnTTWNonCache_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnTTWNonCache_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnTTWCache[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnTTWCache_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnTTWCache_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnTTWCache[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnTTWCache_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnTTWCache_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnPrefetch[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnPrefetch_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnPrefetch_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnPrefetch[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnPrefetch_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnPrefetch_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnSoWrite[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnSoWrite_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnSoWrite_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnSoWrite[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnSoWrite_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnSoWrite_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnSoRead[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnSoRead_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnSoRead_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnSoRead[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnSoRead_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnSoRead_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnDeviceRead[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnDeviceRead_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnDeviceRead_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnDeviceRead[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnDeviceRead_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnDeviceRead_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnReadNormNonCache[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnReadNormNonCache_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnReadNormNonCache_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnReadNormNonCache[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnReadNormNonCache_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnReadNormNonCache_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_syncAbortOnReadNormCache[liftState_simp]:
  "\<lbrakk>read_reg syncAbortOnReadNormCache_ref\<rbrakk>\<^sub>S = read_regS syncAbortOnReadNormCache_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_syncAbortOnReadNormCache[liftState_simp]:
  "\<lbrakk>write_reg syncAbortOnReadNormCache_ref v\<rbrakk>\<^sub>S = write_regS syncAbortOnReadNormCache_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMUBase[liftState_simp]:
  "\<lbrakk>read_reg PMUBase_ref\<rbrakk>\<^sub>S = read_regS PMUBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMUBase[liftState_simp]:
  "\<lbrakk>write_reg PMUBase_ref v\<rbrakk>\<^sub>S = write_regS PMUBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICITSControlBase[liftState_simp]:
  "\<lbrakk>read_reg GICITSControlBase_ref\<rbrakk>\<^sub>S = read_regS GICITSControlBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICITSControlBase[liftState_simp]:
  "\<lbrakk>write_reg GICITSControlBase_ref v\<rbrakk>\<^sub>S = write_regS GICITSControlBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICDistBase[liftState_simp]:
  "\<lbrakk>read_reg GICDistBase_ref\<rbrakk>\<^sub>S = read_regS GICDistBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICDistBase[liftState_simp]:
  "\<lbrakk>write_reg GICDistBase_ref v\<rbrakk>\<^sub>S = write_regS GICDistBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICCPUInterfaceBase[liftState_simp]:
  "\<lbrakk>read_reg GICCPUInterfaceBase_ref\<rbrakk>\<^sub>S = read_regS GICCPUInterfaceBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICCPUInterfaceBase[liftState_simp]:
  "\<lbrakk>write_reg GICCPUInterfaceBase_ref v\<rbrakk>\<^sub>S = write_regS GICCPUInterfaceBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ExtDebugBase[liftState_simp]:
  "\<lbrakk>read_reg ExtDebugBase_ref\<rbrakk>\<^sub>S = read_regS ExtDebugBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ExtDebugBase[liftState_simp]:
  "\<lbrakk>write_reg ExtDebugBase_ref v\<rbrakk>\<^sub>S = write_regS ExtDebugBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTControlBase[liftState_simp]:
  "\<lbrakk>read_reg CNTControlBase_ref\<rbrakk>\<^sub>S = read_regS CNTControlBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTControlBase[liftState_simp]:
  "\<lbrakk>write_reg CNTControlBase_ref v\<rbrakk>\<^sub>S = write_regS CNTControlBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIBase[liftState_simp]:
  "\<lbrakk>read_reg CTIBase_ref\<rbrakk>\<^sub>S = read_regS CTIBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIBase[liftState_simp]:
  "\<lbrakk>write_reg CTIBase_ref v\<rbrakk>\<^sub>S = write_regS CTIBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTSCR[liftState_simp]:
  "\<lbrakk>read_reg CNTSCR_ref\<rbrakk>\<^sub>S = read_regS CNTSCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTSCR[liftState_simp]:
  "\<lbrakk>write_reg CNTSCR_ref v\<rbrakk>\<^sub>S = write_regS CNTSCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ExclusiveMonitorSet[liftState_simp]:
  "\<lbrakk>read_reg ExclusiveMonitorSet_ref\<rbrakk>\<^sub>S = read_regS ExclusiveMonitorSet_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ExclusiveMonitorSet[liftState_simp]:
  "\<lbrakk>write_reg ExclusiveMonitorSet_ref v\<rbrakk>\<^sub>S = write_regS ExclusiveMonitorSet_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ETEBase[liftState_simp]:
  "\<lbrakk>read_reg ETEBase_ref\<rbrakk>\<^sub>S = read_regS ETEBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ETEBase[liftState_simp]:
  "\<lbrakk>write_reg ETEBase_ref v\<rbrakk>\<^sub>S = write_regS ETEBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VLPI_base[liftState_simp]:
  "\<lbrakk>read_reg VLPI_base_ref\<rbrakk>\<^sub>S = read_regS VLPI_base_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VLPI_base[liftState_simp]:
  "\<lbrakk>write_reg VLPI_base_ref v\<rbrakk>\<^sub>S = write_regS VLPI_base_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SGI_base[liftState_simp]:
  "\<lbrakk>read_reg SGI_base_ref\<rbrakk>\<^sub>S = read_regS SGI_base_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SGI_base[liftState_simp]:
  "\<lbrakk>write_reg SGI_base_ref v\<rbrakk>\<^sub>S = write_regS SGI_base_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RD_base[liftState_simp]:
  "\<lbrakk>read_reg RD_base_ref\<rbrakk>\<^sub>S = read_regS RD_base_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RD_base[liftState_simp]:
  "\<lbrakk>write_reg RD_base_ref v\<rbrakk>\<^sub>S = write_regS RD_base_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTCTLBase[liftState_simp]:
  "\<lbrakk>read_reg CNTCTLBase_ref\<rbrakk>\<^sub>S = read_regS CNTCTLBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTCTLBase[liftState_simp]:
  "\<lbrakk>write_reg CNTCTLBase_ref v\<rbrakk>\<^sub>S = write_regS CNTCTLBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTEL0BaseN[liftState_simp]:
  "\<lbrakk>read_reg CNTEL0BaseN_ref\<rbrakk>\<^sub>S = read_regS CNTEL0BaseN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTEL0BaseN[liftState_simp]:
  "\<lbrakk>write_reg CNTEL0BaseN_ref v\<rbrakk>\<^sub>S = write_regS CNTEL0BaseN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTBaseN[liftState_simp]:
  "\<lbrakk>read_reg CNTBaseN_ref\<rbrakk>\<^sub>S = read_regS CNTBaseN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTBaseN[liftState_simp]:
  "\<lbrakk>write_reg CNTBaseN_ref v\<rbrakk>\<^sub>S = write_regS CNTBaseN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTReadBase[liftState_simp]:
  "\<lbrakk>read_reg CNTReadBase_ref\<rbrakk>\<^sub>S = read_regS CNTReadBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTReadBase[liftState_simp]:
  "\<lbrakk>write_reg CNTReadBase_ref v\<rbrakk>\<^sub>S = write_regS CNTReadBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_InstructionStep[liftState_simp]:
  "\<lbrakk>read_reg InstructionStep_ref\<rbrakk>\<^sub>S = read_regS InstructionStep_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_InstructionStep[liftState_simp]:
  "\<lbrakk>write_reg InstructionStep_ref v\<rbrakk>\<^sub>S = write_regS InstructionStep_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DTRTX[liftState_simp]:
  "\<lbrakk>read_reg DTRTX_ref\<rbrakk>\<^sub>S = read_regS DTRTX_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DTRTX[liftState_simp]:
  "\<lbrakk>write_reg DTRTX_ref v\<rbrakk>\<^sub>S = write_regS DTRTX_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DTRRX[liftState_simp]:
  "\<lbrakk>read_reg DTRRX_ref\<rbrakk>\<^sub>S = read_regS DTRRX_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DTRRX[liftState_simp]:
  "\<lbrakk>write_reg DTRRX_ref v\<rbrakk>\<^sub>S = write_regS DTRRX_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_Dclone[liftState_simp]:
  "\<lbrakk>read_reg Dclone_ref\<rbrakk>\<^sub>S = read_regS Dclone_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_Dclone[liftState_simp]:
  "\<lbrakk>write_reg Dclone_ref v\<rbrakk>\<^sub>S = write_regS Dclone_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BTypeCompatible[liftState_simp]:
  "\<lbrakk>read_reg BTypeCompatible_ref\<rbrakk>\<^sub>S = read_regS BTypeCompatible_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BTypeCompatible[liftState_simp]:
  "\<lbrakk>write_reg BTypeCompatible_ref v\<rbrakk>\<^sub>S = write_regS BTypeCompatible_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BTypeNext[liftState_simp]:
  "\<lbrakk>read_reg BTypeNext_ref\<rbrakk>\<^sub>S = read_regS BTypeNext_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BTypeNext[liftState_simp]:
  "\<lbrakk>write_reg BTypeNext_ref v\<rbrakk>\<^sub>S = write_regS BTypeNext_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RC[liftState_simp]:
  "\<lbrakk>read_reg RC_ref\<rbrakk>\<^sub>S = read_regS RC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RC[liftState_simp]:
  "\<lbrakk>write_reg RC_ref v\<rbrakk>\<^sub>S = write_regS RC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EventRegister[liftState_simp]:
  "\<lbrakk>read_reg EventRegister_ref\<rbrakk>\<^sub>S = read_regS EventRegister_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EventRegister[liftState_simp]:
  "\<lbrakk>write_reg EventRegister_ref v\<rbrakk>\<^sub>S = write_regS EventRegister_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ShouldAdvanceSS[liftState_simp]:
  "\<lbrakk>read_reg ShouldAdvanceSS_ref\<rbrakk>\<^sub>S = read_regS ShouldAdvanceSS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ShouldAdvanceSS[liftState_simp]:
  "\<lbrakk>write_reg ShouldAdvanceSS_ref v\<rbrakk>\<^sub>S = write_regS ShouldAdvanceSS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ShouldAdvanceIT[liftState_simp]:
  "\<lbrakk>read_reg ShouldAdvanceIT_ref\<rbrakk>\<^sub>S = read_regS ShouldAdvanceIT_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ShouldAdvanceIT[liftState_simp]:
  "\<lbrakk>write_reg ShouldAdvanceIT_ref v\<rbrakk>\<^sub>S = write_regS ShouldAdvanceIT_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_IsWFEsleep[liftState_simp]:
  "\<lbrakk>read_reg IsWFEsleep_ref\<rbrakk>\<^sub>S = read_regS IsWFEsleep_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_IsWFEsleep[liftState_simp]:
  "\<lbrakk>write_reg IsWFEsleep_ref v\<rbrakk>\<^sub>S = write_regS IsWFEsleep_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_IsWFIsleep[liftState_simp]:
  "\<lbrakk>read_reg IsWFIsleep_ref\<rbrakk>\<^sub>S = read_regS IsWFIsleep_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_IsWFIsleep[liftState_simp]:
  "\<lbrakk>write_reg IsWFIsleep_ref v\<rbrakk>\<^sub>S = write_regS IsWFIsleep_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGOSLAR[liftState_simp]:
  "\<lbrakk>read_reg DBGOSLAR_ref\<rbrakk>\<^sub>S = read_regS DBGOSLAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGOSLAR[liftState_simp]:
  "\<lbrakk>write_reg DBGOSLAR_ref v\<rbrakk>\<^sub>S = write_regS DBGOSLAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDRURW_S[liftState_simp]:
  "\<lbrakk>read_reg TPIDRURW_S_ref\<rbrakk>\<^sub>S = read_regS TPIDRURW_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDRURW_S[liftState_simp]:
  "\<lbrakk>write_reg TPIDRURW_S_ref v\<rbrakk>\<^sub>S = write_regS TPIDRURW_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDRURO_S[liftState_simp]:
  "\<lbrakk>read_reg TPIDRURO_S_ref\<rbrakk>\<^sub>S = read_regS TPIDRURO_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDRURO_S[liftState_simp]:
  "\<lbrakk>write_reg TPIDRURO_S_ref v\<rbrakk>\<^sub>S = write_regS TPIDRURO_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDRPRW_S[liftState_simp]:
  "\<lbrakk>read_reg TPIDRPRW_S_ref\<rbrakk>\<^sub>S = read_regS TPIDRPRW_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDRPRW_S[liftState_simp]:
  "\<lbrakk>write_reg TPIDRPRW_S_ref v\<rbrakk>\<^sub>S = write_regS TPIDRPRW_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TCMTR[liftState_simp]:
  "\<lbrakk>read_reg TCMTR_ref\<rbrakk>\<^sub>S = read_regS TCMTR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TCMTR[liftState_simp]:
  "\<lbrakk>write_reg TCMTR_ref v\<rbrakk>\<^sub>S = write_regS TCMTR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_CVAL_S[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CVAL_S_ref\<rbrakk>\<^sub>S = read_regS CNTP_CVAL_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_CVAL_S[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CVAL_S_ref v\<rbrakk>\<^sub>S = write_regS CNTP_CVAL_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR1_S[liftState_simp]:
  "\<lbrakk>read_reg AMAIR1_S_ref\<rbrakk>\<^sub>S = read_regS AMAIR1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR1_S[liftState_simp]:
  "\<lbrakk>write_reg AMAIR1_S_ref v\<rbrakk>\<^sub>S = write_regS AMAIR1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR0_S[liftState_simp]:
  "\<lbrakk>read_reg AMAIR0_S_ref\<rbrakk>\<^sub>S = read_regS AMAIR0_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR0_S[liftState_simp]:
  "\<lbrakk>write_reg AMAIR0_S_ref v\<rbrakk>\<^sub>S = write_regS AMAIR0_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AIFSR_S[liftState_simp]:
  "\<lbrakk>read_reg AIFSR_S_ref\<rbrakk>\<^sub>S = read_regS AIFSR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AIFSR_S[liftState_simp]:
  "\<lbrakk>write_reg AIFSR_S_ref v\<rbrakk>\<^sub>S = write_regS AIFSR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ADFSR_S[liftState_simp]:
  "\<lbrakk>read_reg ADFSR_S_ref\<rbrakk>\<^sub>S = read_regS ADFSR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ADFSR_S[liftState_simp]:
  "\<lbrakk>write_reg ADFSR_S_ref v\<rbrakk>\<^sub>S = write_regS ADFSR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR_S[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_S_ref\<rbrakk>\<^sub>S = read_regS ACTLR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR_S[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_S_ref v\<rbrakk>\<^sub>S = write_regS ACTLR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR2_S[liftState_simp]:
  "\<lbrakk>read_reg ACTLR2_S_ref\<rbrakk>\<^sub>S = read_regS ACTLR2_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR2_S[liftState_simp]:
  "\<lbrakk>write_reg ACTLR2_S_ref v\<rbrakk>\<^sub>S = write_regS ACTLR2_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP15SDISABLE2[liftState_simp]:
  "\<lbrakk>read_reg CP15SDISABLE2_ref\<rbrakk>\<^sub>S = read_regS CP15SDISABLE2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP15SDISABLE2[liftState_simp]:
  "\<lbrakk>write_reg CP15SDISABLE2_ref v\<rbrakk>\<^sub>S = write_regS CP15SDISABLE2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP15SDISABLE[liftState_simp]:
  "\<lbrakk>read_reg CP15SDISABLE_ref\<rbrakk>\<^sub>S = read_regS CP15SDISABLE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP15SDISABLE[liftState_simp]:
  "\<lbrakk>write_reg CP15SDISABLE_ref v\<rbrakk>\<^sub>S = write_regS CP15SDISABLE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DACR_S[liftState_simp]:
  "\<lbrakk>read_reg DACR_S_ref\<rbrakk>\<^sub>S = read_regS DACR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DACR_S[liftState_simp]:
  "\<lbrakk>write_reg DACR_S_ref v\<rbrakk>\<^sub>S = write_regS DACR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CONTEXTIDR_S[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_S_ref\<rbrakk>\<^sub>S = read_regS CONTEXTIDR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CONTEXTIDR_S[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_S_ref v\<rbrakk>\<^sub>S = write_regS CONTEXTIDR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ignore_rvbar_in_aarch32[liftState_simp]:
  "\<lbrakk>read_reg ignore_rvbar_in_aarch32_ref\<rbrakk>\<^sub>S = read_regS ignore_rvbar_in_aarch32_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ignore_rvbar_in_aarch32[liftState_simp]:
  "\<lbrakk>write_reg ignore_rvbar_in_aarch32_ref v\<rbrakk>\<^sub>S = write_regS ignore_rvbar_in_aarch32_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CFG_RMR_AA64[liftState_simp]:
  "\<lbrakk>read_reg CFG_RMR_AA64_ref\<rbrakk>\<^sub>S = read_regS CFG_RMR_AA64_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CFG_RMR_AA64[liftState_simp]:
  "\<lbrakk>write_reg CFG_RMR_AA64_ref v\<rbrakk>\<^sub>S = write_regS CFG_RMR_AA64_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_rme_l0gptsz[liftState_simp]:
  "\<lbrakk>read_reg rme_l0gptsz_ref\<rbrakk>\<^sub>S = read_regS rme_l0gptsz_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_rme_l0gptsz[liftState_simp]:
  "\<lbrakk>write_reg rme_l0gptsz_ref v\<rbrakk>\<^sub>S = write_regS rme_l0gptsz_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_pan_implemented[liftState_simp]:
  "\<lbrakk>read_reg pan_implemented_ref\<rbrakk>\<^sub>S = read_regS pan_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_pan_implemented[liftState_simp]:
  "\<lbrakk>write_reg pan_implemented_ref v\<rbrakk>\<^sub>S = write_regS pan_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mpam_has_altsp[liftState_simp]:
  "\<lbrakk>read_reg mpam_has_altsp_ref\<rbrakk>\<^sub>S = read_regS mpam_has_altsp_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mpam_has_altsp[liftState_simp]:
  "\<lbrakk>write_reg mpam_has_altsp_ref v\<rbrakk>\<^sub>S = write_regS mpam_has_altsp_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_gmid_log2_block_size[liftState_simp]:
  "\<lbrakk>read_reg gmid_log2_block_size_ref\<rbrakk>\<^sub>S = read_regS gmid_log2_block_size_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_gmid_log2_block_size[liftState_simp]:
  "\<lbrakk>write_reg gmid_log2_block_size_ref v\<rbrakk>\<^sub>S = write_regS gmid_log2_block_size_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_empam_frac[liftState_simp]:
  "\<lbrakk>read_reg empam_frac_ref\<rbrakk>\<^sub>S = read_regS empam_frac_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_empam_frac[liftState_simp]:
  "\<lbrakk>write_reg empam_frac_ref v\<rbrakk>\<^sub>S = write_regS empam_frac_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_dot_product_implemented[liftState_simp]:
  "\<lbrakk>read_reg dot_product_implemented_ref\<rbrakk>\<^sub>S = read_regS dot_product_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_dot_product_implemented[liftState_simp]:
  "\<lbrakk>write_reg dot_product_implemented_ref v\<rbrakk>\<^sub>S = write_regS dot_product_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_dczid_log2_block_size[liftState_simp]:
  "\<lbrakk>read_reg dczid_log2_block_size_ref\<rbrakk>\<^sub>S = read_regS dczid_log2_block_size_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_dczid_log2_block_size[liftState_simp]:
  "\<lbrakk>write_reg dczid_log2_block_size_ref v\<rbrakk>\<^sub>S = write_regS dczid_log2_block_size_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crc32_implemented[liftState_simp]:
  "\<lbrakk>read_reg crc32_implemented_ref\<rbrakk>\<^sub>S = read_regS crc32_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crc32_implemented[liftState_simp]:
  "\<lbrakk>write_reg crc32_implemented_ref v\<rbrakk>\<^sub>S = write_regS crc32_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTbase_frequency[liftState_simp]:
  "\<lbrakk>read_reg CNTbase_frequency_ref\<rbrakk>\<^sub>S = read_regS CNTbase_frequency_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTbase_frequency[liftState_simp]:
  "\<lbrakk>write_reg CNTbase_frequency_ref v\<rbrakk>\<^sub>S = write_regS CNTbase_frequency_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_TYPER[liftState_simp]:
  "\<lbrakk>read_reg GICD_TYPER_ref\<rbrakk>\<^sub>S = read_regS GICD_TYPER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_TYPER[liftState_simp]:
  "\<lbrakk>write_reg GICD_TYPER_ref v\<rbrakk>\<^sub>S = write_regS GICD_TYPER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIDEVARCH[liftState_simp]:
  "\<lbrakk>read_reg CTIDEVARCH_ref\<rbrakk>\<^sub>S = read_regS CTIDEVARCH_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIDEVARCH[liftState_simp]:
  "\<lbrakk>write_reg CTIDEVARCH_ref v\<rbrakk>\<^sub>S = write_regS CTIDEVARCH_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTFID0[liftState_simp]:
  "\<lbrakk>read_reg CNTFID0_ref\<rbrakk>\<^sub>S = read_regS CNTFID0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTFID0[liftState_simp]:
  "\<lbrakk>write_reg CNTFID0_ref v\<rbrakk>\<^sub>S = write_regS CNTFID0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CFG_MPIDR[liftState_simp]:
  "\<lbrakk>read_reg CFG_MPIDR_ref\<rbrakk>\<^sub>S = read_regS CFG_MPIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CFG_MPIDR[liftState_simp]:
  "\<lbrakk>write_reg CFG_MPIDR_ref v\<rbrakk>\<^sub>S = write_regS CFG_MPIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMIIDR[liftState_simp]:
  "\<lbrakk>read_reg AMIIDR_ref\<rbrakk>\<^sub>S = read_regS AMIIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMIIDR[liftState_simp]:
  "\<lbrakk>write_reg AMIIDR_ref v\<rbrakk>\<^sub>S = write_regS AMIIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMDEVARCH[liftState_simp]:
  "\<lbrakk>read_reg AMDEVARCH_ref\<rbrakk>\<^sub>S = read_regS AMDEVARCH_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMDEVARCH[liftState_simp]:
  "\<lbrakk>write_reg AMDEVARCH_ref v\<rbrakk>\<^sub>S = write_regS AMDEVARCH_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTV_TVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_TVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTV_TVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTV_TVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_TVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTV_TVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_TVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_TVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTP_TVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_TVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_TVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTP_TVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPS_TVAL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_TVAL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTPS_TVAL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPS_TVAL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_TVAL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTPS_TVAL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHV_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHV_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHV_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHV_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHVS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHVS_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHVS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHVS_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHP_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHP_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHP_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHP_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHPS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHPS_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHPS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHPS_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_fp16_implemented[liftState_simp]:
  "\<lbrakk>read_reg fp16_implemented_ref\<rbrakk>\<^sub>S = read_regS fp16_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_fp16_implemented[liftState_simp]:
  "\<lbrakk>write_reg fp16_implemented_ref v\<rbrakk>\<^sub>S = write_regS fp16_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_exclusive_granule_size[liftState_simp]:
  "\<lbrakk>read_reg exclusive_granule_size_ref\<rbrakk>\<^sub>S = read_regS exclusive_granule_size_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_exclusive_granule_size[liftState_simp]:
  "\<lbrakk>write_reg exclusive_granule_size_ref v\<rbrakk>\<^sub>S = write_regS exclusive_granule_size_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ConfigReg[liftState_simp]:
  "\<lbrakk>read_reg ConfigReg_ref\<rbrakk>\<^sub>S = read_regS ConfigReg_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ConfigReg[liftState_simp]:
  "\<lbrakk>write_reg ConfigReg_ref v\<rbrakk>\<^sub>S = write_regS ConfigReg_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBTR[liftState_simp]:
  "\<lbrakk>read_reg TLBTR_ref\<rbrakk>\<^sub>S = read_regS TLBTR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBTR[liftState_simp]:
  "\<lbrakk>write_reg TLBTR_ref v\<rbrakk>\<^sub>S = write_regS TLBTR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_NMRR_S[liftState_simp]:
  "\<lbrakk>read_reg NMRR_S_ref\<rbrakk>\<^sub>S = read_regS NMRR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_NMRR_S[liftState_simp]:
  "\<lbrakk>write_reg NMRR_S_ref v\<rbrakk>\<^sub>S = write_regS NMRR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FPSID[liftState_simp]:
  "\<lbrakk>read_reg FPSID_ref\<rbrakk>\<^sub>S = read_regS FPSID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FPSID[liftState_simp]:
  "\<lbrakk>write_reg FPSID_ref v\<rbrakk>\<^sub>S = write_regS FPSID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDEVID[liftState_simp]:
  "\<lbrakk>read_reg DBGDEVID_ref\<rbrakk>\<^sub>S = read_regS DBGDEVID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDEVID[liftState_simp]:
  "\<lbrakk>write_reg DBGDEVID_ref v\<rbrakk>\<^sub>S = write_regS DBGDEVID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR1_S[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_S_ref\<rbrakk>\<^sub>S = read_regS TTBR1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR1_S[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_S_ref v\<rbrakk>\<^sub>S = write_regS TTBR1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR0_S[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_S_ref\<rbrakk>\<^sub>S = read_regS TTBR0_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR0_S[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_S_ref v\<rbrakk>\<^sub>S = write_regS TTBR0_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBCR2_S[liftState_simp]:
  "\<lbrakk>read_reg TTBCR2_S_ref\<rbrakk>\<^sub>S = read_regS TTBCR2_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBCR2_S[liftState_simp]:
  "\<lbrakk>write_reg TTBCR2_S_ref v\<rbrakk>\<^sub>S = write_regS TTBCR2_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SDCR[liftState_simp]:
  "\<lbrakk>read_reg SDCR_ref\<rbrakk>\<^sub>S = read_regS SDCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SDCR[liftState_simp]:
  "\<lbrakk>write_reg SDCR_ref v\<rbrakk>\<^sub>S = write_regS SDCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MAIR0_S[liftState_simp]:
  "\<lbrakk>read_reg MAIR0_S_ref\<rbrakk>\<^sub>S = read_regS MAIR0_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MAIR0_S[liftState_simp]:
  "\<lbrakk>write_reg MAIR0_S_ref v\<rbrakk>\<^sub>S = write_regS MAIR0_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMVIDSR[liftState_simp]:
  "\<lbrakk>read_reg PMVIDSR_ref\<rbrakk>\<^sub>S = read_regS PMVIDSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMVIDSR[liftState_simp]:
  "\<lbrakk>write_reg PMVIDSR_ref v\<rbrakk>\<^sub>S = write_regS PMVIDSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMPIDR4[liftState_simp]:
  "\<lbrakk>read_reg PMPIDR4_ref\<rbrakk>\<^sub>S = read_regS PMPIDR4_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMPIDR4[liftState_simp]:
  "\<lbrakk>write_reg PMPIDR4_ref v\<rbrakk>\<^sub>S = write_regS PMPIDR4_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMPIDR3[liftState_simp]:
  "\<lbrakk>read_reg PMPIDR3_ref\<rbrakk>\<^sub>S = read_regS PMPIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMPIDR3[liftState_simp]:
  "\<lbrakk>write_reg PMPIDR3_ref v\<rbrakk>\<^sub>S = write_regS PMPIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMPIDR2[liftState_simp]:
  "\<lbrakk>read_reg PMPIDR2_ref\<rbrakk>\<^sub>S = read_regS PMPIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMPIDR2[liftState_simp]:
  "\<lbrakk>write_reg PMPIDR2_ref v\<rbrakk>\<^sub>S = write_regS PMPIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMPIDR1[liftState_simp]:
  "\<lbrakk>read_reg PMPIDR1_ref\<rbrakk>\<^sub>S = read_regS PMPIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMPIDR1[liftState_simp]:
  "\<lbrakk>write_reg PMPIDR1_ref v\<rbrakk>\<^sub>S = write_regS PMPIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMPIDR0[liftState_simp]:
  "\<lbrakk>read_reg PMPIDR0_ref\<rbrakk>\<^sub>S = read_regS PMPIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMPIDR0[liftState_simp]:
  "\<lbrakk>write_reg PMPIDR0_ref v\<rbrakk>\<^sub>S = write_regS PMPIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMPCSR[liftState_simp]:
  "\<lbrakk>read_reg PMPCSR_ref\<rbrakk>\<^sub>S = read_regS PMPCSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMPCSR[liftState_simp]:
  "\<lbrakk>write_reg PMPCSR_ref v\<rbrakk>\<^sub>S = write_regS PMPCSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMMIR[liftState_simp]:
  "\<lbrakk>read_reg PMMIR_ref\<rbrakk>\<^sub>S = read_regS PMMIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMMIR[liftState_simp]:
  "\<lbrakk>write_reg PMMIR_ref v\<rbrakk>\<^sub>S = write_regS PMMIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMLSR[liftState_simp]:
  "\<lbrakk>read_reg PMLSR_ref\<rbrakk>\<^sub>S = read_regS PMLSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMLSR[liftState_simp]:
  "\<lbrakk>write_reg PMLSR_ref v\<rbrakk>\<^sub>S = write_regS PMLSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMLAR[liftState_simp]:
  "\<lbrakk>read_reg PMLAR_ref\<rbrakk>\<^sub>S = read_regS PMLAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMLAR[liftState_simp]:
  "\<lbrakk>write_reg PMLAR_ref v\<rbrakk>\<^sub>S = write_regS PMLAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMITCTRL[liftState_simp]:
  "\<lbrakk>read_reg PMITCTRL_ref\<rbrakk>\<^sub>S = read_regS PMITCTRL_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMITCTRL[liftState_simp]:
  "\<lbrakk>write_reg PMITCTRL_ref v\<rbrakk>\<^sub>S = write_regS PMITCTRL_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMDEVTYPE[liftState_simp]:
  "\<lbrakk>read_reg PMDEVTYPE_ref\<rbrakk>\<^sub>S = read_regS PMDEVTYPE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMDEVTYPE[liftState_simp]:
  "\<lbrakk>write_reg PMDEVTYPE_ref v\<rbrakk>\<^sub>S = write_regS PMDEVTYPE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMDEVID[liftState_simp]:
  "\<lbrakk>read_reg PMDEVID_ref\<rbrakk>\<^sub>S = read_regS PMDEVID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMDEVID[liftState_simp]:
  "\<lbrakk>write_reg PMDEVID_ref v\<rbrakk>\<^sub>S = write_regS PMDEVID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCIDR3[liftState_simp]:
  "\<lbrakk>read_reg PMCIDR3_ref\<rbrakk>\<^sub>S = read_regS PMCIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCIDR3[liftState_simp]:
  "\<lbrakk>write_reg PMCIDR3_ref v\<rbrakk>\<^sub>S = write_regS PMCIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCIDR2[liftState_simp]:
  "\<lbrakk>read_reg PMCIDR2_ref\<rbrakk>\<^sub>S = read_regS PMCIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCIDR2[liftState_simp]:
  "\<lbrakk>write_reg PMCIDR2_ref v\<rbrakk>\<^sub>S = write_regS PMCIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCIDR1[liftState_simp]:
  "\<lbrakk>read_reg PMCIDR1_ref\<rbrakk>\<^sub>S = read_regS PMCIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCIDR1[liftState_simp]:
  "\<lbrakk>write_reg PMCIDR1_ref v\<rbrakk>\<^sub>S = write_regS PMCIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCIDR0[liftState_simp]:
  "\<lbrakk>read_reg PMCIDR0_ref\<rbrakk>\<^sub>S = read_regS PMCIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCIDR0[liftState_simp]:
  "\<lbrakk>write_reg PMCIDR0_ref v\<rbrakk>\<^sub>S = write_regS PMCIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCFGR[liftState_simp]:
  "\<lbrakk>read_reg PMCFGR_ref\<rbrakk>\<^sub>S = read_regS PMCFGR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCFGR[liftState_simp]:
  "\<lbrakk>write_reg PMCFGR_ref v\<rbrakk>\<^sub>S = write_regS PMCFGR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMAUTHSTATUS[liftState_simp]:
  "\<lbrakk>read_reg PMAUTHSTATUS_ref\<rbrakk>\<^sub>S = read_regS PMAUTHSTATUS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMAUTHSTATUS[liftState_simp]:
  "\<lbrakk>write_reg PMAUTHSTATUS_ref v\<rbrakk>\<^sub>S = write_regS PMAUTHSTATUS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PAR_S[liftState_simp]:
  "\<lbrakk>read_reg PAR_S_ref\<rbrakk>\<^sub>S = read_regS PAR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PAR_S[liftState_simp]:
  "\<lbrakk>write_reg PAR_S_ref v\<rbrakk>\<^sub>S = write_regS PAR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_JOSCR[liftState_simp]:
  "\<lbrakk>read_reg JOSCR_ref\<rbrakk>\<^sub>S = read_regS JOSCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_JOSCR[liftState_simp]:
  "\<lbrakk>write_reg JOSCR_ref v\<rbrakk>\<^sub>S = write_regS JOSCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_JMCR[liftState_simp]:
  "\<lbrakk>read_reg JMCR_ref\<rbrakk>\<^sub>S = read_regS JMCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_JMCR[liftState_simp]:
  "\<lbrakk>write_reg JMCR_ref v\<rbrakk>\<^sub>S = write_regS JMCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_JIDR[liftState_simp]:
  "\<lbrakk>read_reg JIDR_ref\<rbrakk>\<^sub>S = read_regS JIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_JIDR[liftState_simp]:
  "\<lbrakk>write_reg JIDR_ref v\<rbrakk>\<^sub>S = write_regS JIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_MSRE[liftState_simp]:
  "\<lbrakk>read_reg ICC_MSRE_ref\<rbrakk>\<^sub>S = read_regS ICC_MSRE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_MSRE[liftState_simp]:
  "\<lbrakk>write_reg ICC_MSRE_ref v\<rbrakk>\<^sub>S = write_regS ICC_MSRE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_MGRPEN1[liftState_simp]:
  "\<lbrakk>read_reg ICC_MGRPEN1_ref\<rbrakk>\<^sub>S = read_regS ICC_MGRPEN1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_MGRPEN1[liftState_simp]:
  "\<lbrakk>write_reg ICC_MGRPEN1_ref v\<rbrakk>\<^sub>S = write_regS ICC_MGRPEN1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_MCTLR[liftState_simp]:
  "\<lbrakk>read_reg ICC_MCTLR_ref\<rbrakk>\<^sub>S = read_regS ICC_MCTLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_MCTLR[liftState_simp]:
  "\<lbrakk>write_reg ICC_MCTLR_ref v\<rbrakk>\<^sub>S = write_regS ICC_MCTLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_TYPER[liftState_simp]:
  "\<lbrakk>read_reg GITS_TYPER_ref\<rbrakk>\<^sub>S = read_regS GITS_TYPER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_TYPER[liftState_simp]:
  "\<lbrakk>write_reg GITS_TYPER_ref v\<rbrakk>\<^sub>S = write_regS GITS_TYPER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_STATUSR[liftState_simp]:
  "\<lbrakk>read_reg GITS_STATUSR_ref\<rbrakk>\<^sub>S = read_regS GITS_STATUSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_STATUSR[liftState_simp]:
  "\<lbrakk>write_reg GITS_STATUSR_ref v\<rbrakk>\<^sub>S = write_regS GITS_STATUSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_SGIR[liftState_simp]:
  "\<lbrakk>read_reg GITS_SGIR_ref\<rbrakk>\<^sub>S = read_regS GITS_SGIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_SGIR[liftState_simp]:
  "\<lbrakk>write_reg GITS_SGIR_ref v\<rbrakk>\<^sub>S = write_regS GITS_SGIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_PARTIDR[liftState_simp]:
  "\<lbrakk>read_reg GITS_PARTIDR_ref\<rbrakk>\<^sub>S = read_regS GITS_PARTIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_PARTIDR[liftState_simp]:
  "\<lbrakk>write_reg GITS_PARTIDR_ref v\<rbrakk>\<^sub>S = write_regS GITS_PARTIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_MPIDR[liftState_simp]:
  "\<lbrakk>read_reg GITS_MPIDR_ref\<rbrakk>\<^sub>S = read_regS GITS_MPIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_MPIDR[liftState_simp]:
  "\<lbrakk>write_reg GITS_MPIDR_ref v\<rbrakk>\<^sub>S = write_regS GITS_MPIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_MPAMIDR[liftState_simp]:
  "\<lbrakk>read_reg GITS_MPAMIDR_ref\<rbrakk>\<^sub>S = read_regS GITS_MPAMIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_MPAMIDR[liftState_simp]:
  "\<lbrakk>write_reg GITS_MPAMIDR_ref v\<rbrakk>\<^sub>S = write_regS GITS_MPAMIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_IIDR[liftState_simp]:
  "\<lbrakk>read_reg GITS_IIDR_ref\<rbrakk>\<^sub>S = read_regS GITS_IIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_IIDR[liftState_simp]:
  "\<lbrakk>write_reg GITS_IIDR_ref v\<rbrakk>\<^sub>S = write_regS GITS_IIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_CWRITER[liftState_simp]:
  "\<lbrakk>read_reg GITS_CWRITER_ref\<rbrakk>\<^sub>S = read_regS GITS_CWRITER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_CWRITER[liftState_simp]:
  "\<lbrakk>write_reg GITS_CWRITER_ref v\<rbrakk>\<^sub>S = write_regS GITS_CWRITER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_CTLR[liftState_simp]:
  "\<lbrakk>read_reg GITS_CTLR_ref\<rbrakk>\<^sub>S = read_regS GITS_CTLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_CTLR[liftState_simp]:
  "\<lbrakk>write_reg GITS_CTLR_ref v\<rbrakk>\<^sub>S = write_regS GITS_CTLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_CREADR[liftState_simp]:
  "\<lbrakk>read_reg GITS_CREADR_ref\<rbrakk>\<^sub>S = read_regS GITS_CREADR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_CREADR[liftState_simp]:
  "\<lbrakk>write_reg GITS_CREADR_ref v\<rbrakk>\<^sub>S = write_regS GITS_CREADR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GITS_CBASER[liftState_simp]:
  "\<lbrakk>read_reg GITS_CBASER_ref\<rbrakk>\<^sub>S = read_regS GITS_CBASER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GITS_CBASER[liftState_simp]:
  "\<lbrakk>write_reg GITS_CBASER_ref v\<rbrakk>\<^sub>S = write_regS GITS_CBASER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_STATUSR[liftState_simp]:
  "\<lbrakk>read_reg GICV_STATUSR_ref\<rbrakk>\<^sub>S = read_regS GICV_STATUSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_STATUSR[liftState_simp]:
  "\<lbrakk>write_reg GICV_STATUSR_ref v\<rbrakk>\<^sub>S = write_regS GICV_STATUSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_RPR[liftState_simp]:
  "\<lbrakk>read_reg GICV_RPR_ref\<rbrakk>\<^sub>S = read_regS GICV_RPR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_RPR[liftState_simp]:
  "\<lbrakk>write_reg GICV_RPR_ref v\<rbrakk>\<^sub>S = write_regS GICV_RPR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_PMR[liftState_simp]:
  "\<lbrakk>read_reg GICV_PMR_ref\<rbrakk>\<^sub>S = read_regS GICV_PMR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_PMR[liftState_simp]:
  "\<lbrakk>write_reg GICV_PMR_ref v\<rbrakk>\<^sub>S = write_regS GICV_PMR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_IAR[liftState_simp]:
  "\<lbrakk>read_reg GICV_IAR_ref\<rbrakk>\<^sub>S = read_regS GICV_IAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_IAR[liftState_simp]:
  "\<lbrakk>write_reg GICV_IAR_ref v\<rbrakk>\<^sub>S = write_regS GICV_IAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_HPPIR[liftState_simp]:
  "\<lbrakk>read_reg GICV_HPPIR_ref\<rbrakk>\<^sub>S = read_regS GICV_HPPIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_HPPIR[liftState_simp]:
  "\<lbrakk>write_reg GICV_HPPIR_ref v\<rbrakk>\<^sub>S = write_regS GICV_HPPIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_EOIR[liftState_simp]:
  "\<lbrakk>read_reg GICV_EOIR_ref\<rbrakk>\<^sub>S = read_regS GICV_EOIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_EOIR[liftState_simp]:
  "\<lbrakk>write_reg GICV_EOIR_ref v\<rbrakk>\<^sub>S = write_regS GICV_EOIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_DIR[liftState_simp]:
  "\<lbrakk>read_reg GICV_DIR_ref\<rbrakk>\<^sub>S = read_regS GICV_DIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_DIR[liftState_simp]:
  "\<lbrakk>write_reg GICV_DIR_ref v\<rbrakk>\<^sub>S = write_regS GICV_DIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_CTLR[liftState_simp]:
  "\<lbrakk>read_reg GICV_CTLR_ref\<rbrakk>\<^sub>S = read_regS GICV_CTLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_CTLR[liftState_simp]:
  "\<lbrakk>write_reg GICV_CTLR_ref v\<rbrakk>\<^sub>S = write_regS GICV_CTLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_BPR[liftState_simp]:
  "\<lbrakk>read_reg GICV_BPR_ref\<rbrakk>\<^sub>S = read_regS GICV_BPR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_BPR[liftState_simp]:
  "\<lbrakk>write_reg GICV_BPR_ref v\<rbrakk>\<^sub>S = write_regS GICV_BPR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_AIAR[liftState_simp]:
  "\<lbrakk>read_reg GICV_AIAR_ref\<rbrakk>\<^sub>S = read_regS GICV_AIAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_AIAR[liftState_simp]:
  "\<lbrakk>write_reg GICV_AIAR_ref v\<rbrakk>\<^sub>S = write_regS GICV_AIAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_AHPPIR[liftState_simp]:
  "\<lbrakk>read_reg GICV_AHPPIR_ref\<rbrakk>\<^sub>S = read_regS GICV_AHPPIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_AHPPIR[liftState_simp]:
  "\<lbrakk>write_reg GICV_AHPPIR_ref v\<rbrakk>\<^sub>S = write_regS GICV_AHPPIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_AEOIR[liftState_simp]:
  "\<lbrakk>read_reg GICV_AEOIR_ref\<rbrakk>\<^sub>S = read_regS GICV_AEOIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_AEOIR[liftState_simp]:
  "\<lbrakk>write_reg GICV_AEOIR_ref v\<rbrakk>\<^sub>S = write_regS GICV_AEOIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICV_ABPR[liftState_simp]:
  "\<lbrakk>read_reg GICV_ABPR_ref\<rbrakk>\<^sub>S = read_regS GICV_ABPR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICV_ABPR[liftState_simp]:
  "\<lbrakk>write_reg GICV_ABPR_ref v\<rbrakk>\<^sub>S = write_regS GICV_ABPR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_WAKER[liftState_simp]:
  "\<lbrakk>read_reg GICR_WAKER_ref\<rbrakk>\<^sub>S = read_regS GICR_WAKER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_WAKER[liftState_simp]:
  "\<lbrakk>write_reg GICR_WAKER_ref v\<rbrakk>\<^sub>S = write_regS GICR_WAKER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_VSGIR[liftState_simp]:
  "\<lbrakk>read_reg GICR_VSGIR_ref\<rbrakk>\<^sub>S = read_regS GICR_VSGIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_VSGIR[liftState_simp]:
  "\<lbrakk>write_reg GICR_VSGIR_ref v\<rbrakk>\<^sub>S = write_regS GICR_VSGIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_VSGIPENDR[liftState_simp]:
  "\<lbrakk>read_reg GICR_VSGIPENDR_ref\<rbrakk>\<^sub>S = read_regS GICR_VSGIPENDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_VSGIPENDR[liftState_simp]:
  "\<lbrakk>write_reg GICR_VSGIPENDR_ref v\<rbrakk>\<^sub>S = write_regS GICR_VSGIPENDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_VPROPBASER[liftState_simp]:
  "\<lbrakk>read_reg GICR_VPROPBASER_ref\<rbrakk>\<^sub>S = read_regS GICR_VPROPBASER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_VPROPBASER[liftState_simp]:
  "\<lbrakk>write_reg GICR_VPROPBASER_ref v\<rbrakk>\<^sub>S = write_regS GICR_VPROPBASER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_VPENDBASER[liftState_simp]:
  "\<lbrakk>read_reg GICR_VPENDBASER_ref\<rbrakk>\<^sub>S = read_regS GICR_VPENDBASER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_VPENDBASER[liftState_simp]:
  "\<lbrakk>write_reg GICR_VPENDBASER_ref v\<rbrakk>\<^sub>S = write_regS GICR_VPENDBASER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_SYNCR[liftState_simp]:
  "\<lbrakk>read_reg GICR_SYNCR_ref\<rbrakk>\<^sub>S = read_regS GICR_SYNCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_SYNCR[liftState_simp]:
  "\<lbrakk>write_reg GICR_SYNCR_ref v\<rbrakk>\<^sub>S = write_regS GICR_SYNCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_STATUSR[liftState_simp]:
  "\<lbrakk>read_reg GICR_STATUSR_ref\<rbrakk>\<^sub>S = read_regS GICR_STATUSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_STATUSR[liftState_simp]:
  "\<lbrakk>write_reg GICR_STATUSR_ref v\<rbrakk>\<^sub>S = write_regS GICR_STATUSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_SETLPIR[liftState_simp]:
  "\<lbrakk>read_reg GICR_SETLPIR_ref\<rbrakk>\<^sub>S = read_regS GICR_SETLPIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_SETLPIR[liftState_simp]:
  "\<lbrakk>write_reg GICR_SETLPIR_ref v\<rbrakk>\<^sub>S = write_regS GICR_SETLPIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_PROPBASER[liftState_simp]:
  "\<lbrakk>read_reg GICR_PROPBASER_ref\<rbrakk>\<^sub>S = read_regS GICR_PROPBASER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_PROPBASER[liftState_simp]:
  "\<lbrakk>write_reg GICR_PROPBASER_ref v\<rbrakk>\<^sub>S = write_regS GICR_PROPBASER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_PENDBASER[liftState_simp]:
  "\<lbrakk>read_reg GICR_PENDBASER_ref\<rbrakk>\<^sub>S = read_regS GICR_PENDBASER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_PENDBASER[liftState_simp]:
  "\<lbrakk>write_reg GICR_PENDBASER_ref v\<rbrakk>\<^sub>S = write_regS GICR_PENDBASER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_PARTIDR[liftState_simp]:
  "\<lbrakk>read_reg GICR_PARTIDR_ref\<rbrakk>\<^sub>S = read_regS GICR_PARTIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_PARTIDR[liftState_simp]:
  "\<lbrakk>write_reg GICR_PARTIDR_ref v\<rbrakk>\<^sub>S = write_regS GICR_PARTIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_MPAMIDR[liftState_simp]:
  "\<lbrakk>read_reg GICR_MPAMIDR_ref\<rbrakk>\<^sub>S = read_regS GICR_MPAMIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_MPAMIDR[liftState_simp]:
  "\<lbrakk>write_reg GICR_MPAMIDR_ref v\<rbrakk>\<^sub>S = write_regS GICR_MPAMIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_ISENABLER0[liftState_simp]:
  "\<lbrakk>read_reg GICR_ISENABLER0_ref\<rbrakk>\<^sub>S = read_regS GICR_ISENABLER0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_ISENABLER0[liftState_simp]:
  "\<lbrakk>write_reg GICR_ISENABLER0_ref v\<rbrakk>\<^sub>S = write_regS GICR_ISENABLER0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_INVLPIR[liftState_simp]:
  "\<lbrakk>read_reg GICR_INVLPIR_ref\<rbrakk>\<^sub>S = read_regS GICR_INVLPIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_INVLPIR[liftState_simp]:
  "\<lbrakk>write_reg GICR_INVLPIR_ref v\<rbrakk>\<^sub>S = write_regS GICR_INVLPIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_INVALLR[liftState_simp]:
  "\<lbrakk>read_reg GICR_INVALLR_ref\<rbrakk>\<^sub>S = read_regS GICR_INVALLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_INVALLR[liftState_simp]:
  "\<lbrakk>write_reg GICR_INVALLR_ref v\<rbrakk>\<^sub>S = write_regS GICR_INVALLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_INMIR0[liftState_simp]:
  "\<lbrakk>read_reg GICR_INMIR0_ref\<rbrakk>\<^sub>S = read_regS GICR_INMIR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_INMIR0[liftState_simp]:
  "\<lbrakk>write_reg GICR_INMIR0_ref v\<rbrakk>\<^sub>S = write_regS GICR_INMIR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_IIDR[liftState_simp]:
  "\<lbrakk>read_reg GICR_IIDR_ref\<rbrakk>\<^sub>S = read_regS GICR_IIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_IIDR[liftState_simp]:
  "\<lbrakk>write_reg GICR_IIDR_ref v\<rbrakk>\<^sub>S = write_regS GICR_IIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_CTLR[liftState_simp]:
  "\<lbrakk>read_reg GICR_CTLR_ref\<rbrakk>\<^sub>S = read_regS GICR_CTLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_CTLR[liftState_simp]:
  "\<lbrakk>write_reg GICR_CTLR_ref v\<rbrakk>\<^sub>S = write_regS GICR_CTLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICR_CLRLPIR[liftState_simp]:
  "\<lbrakk>read_reg GICR_CLRLPIR_ref\<rbrakk>\<^sub>S = read_regS GICR_CLRLPIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICR_CLRLPIR[liftState_simp]:
  "\<lbrakk>write_reg GICR_CLRLPIR_ref v\<rbrakk>\<^sub>S = write_regS GICR_CLRLPIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICM_TYPER[liftState_simp]:
  "\<lbrakk>read_reg GICM_TYPER_ref\<rbrakk>\<^sub>S = read_regS GICM_TYPER_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICM_TYPER[liftState_simp]:
  "\<lbrakk>write_reg GICM_TYPER_ref v\<rbrakk>\<^sub>S = write_regS GICM_TYPER_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICM_SETSPI_SR[liftState_simp]:
  "\<lbrakk>read_reg GICM_SETSPI_SR_ref\<rbrakk>\<^sub>S = read_regS GICM_SETSPI_SR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICM_SETSPI_SR[liftState_simp]:
  "\<lbrakk>write_reg GICM_SETSPI_SR_ref v\<rbrakk>\<^sub>S = write_regS GICM_SETSPI_SR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICM_SETSPI_NSR[liftState_simp]:
  "\<lbrakk>read_reg GICM_SETSPI_NSR_ref\<rbrakk>\<^sub>S = read_regS GICM_SETSPI_NSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICM_SETSPI_NSR[liftState_simp]:
  "\<lbrakk>write_reg GICM_SETSPI_NSR_ref v\<rbrakk>\<^sub>S = write_regS GICM_SETSPI_NSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICM_IIDR[liftState_simp]:
  "\<lbrakk>read_reg GICM_IIDR_ref\<rbrakk>\<^sub>S = read_regS GICM_IIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICM_IIDR[liftState_simp]:
  "\<lbrakk>write_reg GICM_IIDR_ref v\<rbrakk>\<^sub>S = write_regS GICM_IIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICM_CLRSPI_SR[liftState_simp]:
  "\<lbrakk>read_reg GICM_CLRSPI_SR_ref\<rbrakk>\<^sub>S = read_regS GICM_CLRSPI_SR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICM_CLRSPI_SR[liftState_simp]:
  "\<lbrakk>write_reg GICM_CLRSPI_SR_ref v\<rbrakk>\<^sub>S = write_regS GICM_CLRSPI_SR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICM_CLRSPI_NSR[liftState_simp]:
  "\<lbrakk>read_reg GICM_CLRSPI_NSR_ref\<rbrakk>\<^sub>S = read_regS GICM_CLRSPI_NSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICM_CLRSPI_NSR[liftState_simp]:
  "\<lbrakk>write_reg GICM_CLRSPI_NSR_ref v\<rbrakk>\<^sub>S = write_regS GICM_CLRSPI_NSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICH_VTR[liftState_simp]:
  "\<lbrakk>read_reg GICH_VTR_ref\<rbrakk>\<^sub>S = read_regS GICH_VTR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICH_VTR[liftState_simp]:
  "\<lbrakk>write_reg GICH_VTR_ref v\<rbrakk>\<^sub>S = write_regS GICH_VTR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICH_VMCR[liftState_simp]:
  "\<lbrakk>read_reg GICH_VMCR_ref\<rbrakk>\<^sub>S = read_regS GICH_VMCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICH_VMCR[liftState_simp]:
  "\<lbrakk>write_reg GICH_VMCR_ref v\<rbrakk>\<^sub>S = write_regS GICH_VMCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICH_MISR[liftState_simp]:
  "\<lbrakk>read_reg GICH_MISR_ref\<rbrakk>\<^sub>S = read_regS GICH_MISR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICH_MISR[liftState_simp]:
  "\<lbrakk>write_reg GICH_MISR_ref v\<rbrakk>\<^sub>S = write_regS GICH_MISR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICH_HCR[liftState_simp]:
  "\<lbrakk>read_reg GICH_HCR_ref\<rbrakk>\<^sub>S = read_regS GICH_HCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICH_HCR[liftState_simp]:
  "\<lbrakk>write_reg GICH_HCR_ref v\<rbrakk>\<^sub>S = write_regS GICH_HCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICH_ELRSR[liftState_simp]:
  "\<lbrakk>read_reg GICH_ELRSR_ref\<rbrakk>\<^sub>S = read_regS GICH_ELRSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICH_ELRSR[liftState_simp]:
  "\<lbrakk>write_reg GICH_ELRSR_ref v\<rbrakk>\<^sub>S = write_regS GICH_ELRSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICH_EISR[liftState_simp]:
  "\<lbrakk>read_reg GICH_EISR_ref\<rbrakk>\<^sub>S = read_regS GICH_EISR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICH_EISR[liftState_simp]:
  "\<lbrakk>write_reg GICH_EISR_ref v\<rbrakk>\<^sub>S = write_regS GICH_EISR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_TYPER2[liftState_simp]:
  "\<lbrakk>read_reg GICD_TYPER2_ref\<rbrakk>\<^sub>S = read_regS GICD_TYPER2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_TYPER2[liftState_simp]:
  "\<lbrakk>write_reg GICD_TYPER2_ref v\<rbrakk>\<^sub>S = write_regS GICD_TYPER2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_STATUSR[liftState_simp]:
  "\<lbrakk>read_reg GICD_STATUSR_ref\<rbrakk>\<^sub>S = read_regS GICD_STATUSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_STATUSR[liftState_simp]:
  "\<lbrakk>write_reg GICD_STATUSR_ref v\<rbrakk>\<^sub>S = write_regS GICD_STATUSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_SGIR[liftState_simp]:
  "\<lbrakk>read_reg GICD_SGIR_ref\<rbrakk>\<^sub>S = read_regS GICD_SGIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_SGIR[liftState_simp]:
  "\<lbrakk>write_reg GICD_SGIR_ref v\<rbrakk>\<^sub>S = write_regS GICD_SGIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_SETSPI_SR[liftState_simp]:
  "\<lbrakk>read_reg GICD_SETSPI_SR_ref\<rbrakk>\<^sub>S = read_regS GICD_SETSPI_SR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_SETSPI_SR[liftState_simp]:
  "\<lbrakk>write_reg GICD_SETSPI_SR_ref v\<rbrakk>\<^sub>S = write_regS GICD_SETSPI_SR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_SETSPI_NSR[liftState_simp]:
  "\<lbrakk>read_reg GICD_SETSPI_NSR_ref\<rbrakk>\<^sub>S = read_regS GICD_SETSPI_NSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_SETSPI_NSR[liftState_simp]:
  "\<lbrakk>write_reg GICD_SETSPI_NSR_ref v\<rbrakk>\<^sub>S = write_regS GICD_SETSPI_NSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_IIDR[liftState_simp]:
  "\<lbrakk>read_reg GICD_IIDR_ref\<rbrakk>\<^sub>S = read_regS GICD_IIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_IIDR[liftState_simp]:
  "\<lbrakk>write_reg GICD_IIDR_ref v\<rbrakk>\<^sub>S = write_regS GICD_IIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_CTLR[liftState_simp]:
  "\<lbrakk>read_reg GICD_CTLR_ref\<rbrakk>\<^sub>S = read_regS GICD_CTLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_CTLR[liftState_simp]:
  "\<lbrakk>write_reg GICD_CTLR_ref v\<rbrakk>\<^sub>S = write_regS GICD_CTLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_CLRSPI_SR[liftState_simp]:
  "\<lbrakk>read_reg GICD_CLRSPI_SR_ref\<rbrakk>\<^sub>S = read_regS GICD_CLRSPI_SR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_CLRSPI_SR[liftState_simp]:
  "\<lbrakk>write_reg GICD_CLRSPI_SR_ref v\<rbrakk>\<^sub>S = write_regS GICD_CLRSPI_SR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICD_CLRSPI_NSR[liftState_simp]:
  "\<lbrakk>read_reg GICD_CLRSPI_NSR_ref\<rbrakk>\<^sub>S = read_regS GICD_CLRSPI_NSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICD_CLRSPI_NSR[liftState_simp]:
  "\<lbrakk>write_reg GICD_CLRSPI_NSR_ref v\<rbrakk>\<^sub>S = write_regS GICD_CLRSPI_NSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_STATUSR[liftState_simp]:
  "\<lbrakk>read_reg GICC_STATUSR_ref\<rbrakk>\<^sub>S = read_regS GICC_STATUSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_STATUSR[liftState_simp]:
  "\<lbrakk>write_reg GICC_STATUSR_ref v\<rbrakk>\<^sub>S = write_regS GICC_STATUSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_RPR[liftState_simp]:
  "\<lbrakk>read_reg GICC_RPR_ref\<rbrakk>\<^sub>S = read_regS GICC_RPR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_RPR[liftState_simp]:
  "\<lbrakk>write_reg GICC_RPR_ref v\<rbrakk>\<^sub>S = write_regS GICC_RPR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_PMR[liftState_simp]:
  "\<lbrakk>read_reg GICC_PMR_ref\<rbrakk>\<^sub>S = read_regS GICC_PMR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_PMR[liftState_simp]:
  "\<lbrakk>write_reg GICC_PMR_ref v\<rbrakk>\<^sub>S = write_regS GICC_PMR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_IAR[liftState_simp]:
  "\<lbrakk>read_reg GICC_IAR_ref\<rbrakk>\<^sub>S = read_regS GICC_IAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_IAR[liftState_simp]:
  "\<lbrakk>write_reg GICC_IAR_ref v\<rbrakk>\<^sub>S = write_regS GICC_IAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_HPPIR[liftState_simp]:
  "\<lbrakk>read_reg GICC_HPPIR_ref\<rbrakk>\<^sub>S = read_regS GICC_HPPIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_HPPIR[liftState_simp]:
  "\<lbrakk>write_reg GICC_HPPIR_ref v\<rbrakk>\<^sub>S = write_regS GICC_HPPIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_EOIR[liftState_simp]:
  "\<lbrakk>read_reg GICC_EOIR_ref\<rbrakk>\<^sub>S = read_regS GICC_EOIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_EOIR[liftState_simp]:
  "\<lbrakk>write_reg GICC_EOIR_ref v\<rbrakk>\<^sub>S = write_regS GICC_EOIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_DIR[liftState_simp]:
  "\<lbrakk>read_reg GICC_DIR_ref\<rbrakk>\<^sub>S = read_regS GICC_DIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_DIR[liftState_simp]:
  "\<lbrakk>write_reg GICC_DIR_ref v\<rbrakk>\<^sub>S = write_regS GICC_DIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_BPR[liftState_simp]:
  "\<lbrakk>read_reg GICC_BPR_ref\<rbrakk>\<^sub>S = read_regS GICC_BPR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_BPR[liftState_simp]:
  "\<lbrakk>write_reg GICC_BPR_ref v\<rbrakk>\<^sub>S = write_regS GICC_BPR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_AIAR[liftState_simp]:
  "\<lbrakk>read_reg GICC_AIAR_ref\<rbrakk>\<^sub>S = read_regS GICC_AIAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_AIAR[liftState_simp]:
  "\<lbrakk>write_reg GICC_AIAR_ref v\<rbrakk>\<^sub>S = write_regS GICC_AIAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_AHPPIR[liftState_simp]:
  "\<lbrakk>read_reg GICC_AHPPIR_ref\<rbrakk>\<^sub>S = read_regS GICC_AHPPIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_AHPPIR[liftState_simp]:
  "\<lbrakk>write_reg GICC_AHPPIR_ref v\<rbrakk>\<^sub>S = write_regS GICC_AHPPIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_AEOIR[liftState_simp]:
  "\<lbrakk>read_reg GICC_AEOIR_ref\<rbrakk>\<^sub>S = read_regS GICC_AEOIR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_AEOIR[liftState_simp]:
  "\<lbrakk>write_reg GICC_AEOIR_ref v\<rbrakk>\<^sub>S = write_regS GICC_AEOIR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_ABPR[liftState_simp]:
  "\<lbrakk>read_reg GICC_ABPR_ref\<rbrakk>\<^sub>S = read_regS GICC_ABPR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_ABPR[liftState_simp]:
  "\<lbrakk>write_reg GICC_ABPR_ref v\<rbrakk>\<^sub>S = write_regS GICC_ABPR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FCSEIDR[liftState_simp]:
  "\<lbrakk>read_reg FCSEIDR_ref\<rbrakk>\<^sub>S = read_regS FCSEIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FCSEIDR[liftState_simp]:
  "\<lbrakk>write_reg FCSEIDR_ref v\<rbrakk>\<^sub>S = write_regS FCSEIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDVIDSR[liftState_simp]:
  "\<lbrakk>read_reg EDVIDSR_ref\<rbrakk>\<^sub>S = read_regS EDVIDSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDVIDSR[liftState_simp]:
  "\<lbrakk>write_reg EDVIDSR_ref v\<rbrakk>\<^sub>S = write_regS EDVIDSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDRCR[liftState_simp]:
  "\<lbrakk>read_reg EDRCR_ref\<rbrakk>\<^sub>S = read_regS EDRCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDRCR[liftState_simp]:
  "\<lbrakk>write_reg EDRCR_ref v\<rbrakk>\<^sub>S = write_regS EDRCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPRCR[liftState_simp]:
  "\<lbrakk>read_reg EDPRCR_ref\<rbrakk>\<^sub>S = read_regS EDPRCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPRCR[liftState_simp]:
  "\<lbrakk>write_reg EDPRCR_ref v\<rbrakk>\<^sub>S = write_regS EDPRCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPIDR4[liftState_simp]:
  "\<lbrakk>read_reg EDPIDR4_ref\<rbrakk>\<^sub>S = read_regS EDPIDR4_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPIDR4[liftState_simp]:
  "\<lbrakk>write_reg EDPIDR4_ref v\<rbrakk>\<^sub>S = write_regS EDPIDR4_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPIDR3[liftState_simp]:
  "\<lbrakk>read_reg EDPIDR3_ref\<rbrakk>\<^sub>S = read_regS EDPIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPIDR3[liftState_simp]:
  "\<lbrakk>write_reg EDPIDR3_ref v\<rbrakk>\<^sub>S = write_regS EDPIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPIDR2[liftState_simp]:
  "\<lbrakk>read_reg EDPIDR2_ref\<rbrakk>\<^sub>S = read_regS EDPIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPIDR2[liftState_simp]:
  "\<lbrakk>write_reg EDPIDR2_ref v\<rbrakk>\<^sub>S = write_regS EDPIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPIDR1[liftState_simp]:
  "\<lbrakk>read_reg EDPIDR1_ref\<rbrakk>\<^sub>S = read_regS EDPIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPIDR1[liftState_simp]:
  "\<lbrakk>write_reg EDPIDR1_ref v\<rbrakk>\<^sub>S = write_regS EDPIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPIDR0[liftState_simp]:
  "\<lbrakk>read_reg EDPIDR0_ref\<rbrakk>\<^sub>S = read_regS EDPIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPIDR0[liftState_simp]:
  "\<lbrakk>write_reg EDPIDR0_ref v\<rbrakk>\<^sub>S = write_regS EDPIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPFR[liftState_simp]:
  "\<lbrakk>read_reg EDPFR_ref\<rbrakk>\<^sub>S = read_regS EDPFR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPFR[liftState_simp]:
  "\<lbrakk>write_reg EDPFR_ref v\<rbrakk>\<^sub>S = write_regS EDPFR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPCSR[liftState_simp]:
  "\<lbrakk>read_reg EDPCSR_ref\<rbrakk>\<^sub>S = read_regS EDPCSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPCSR[liftState_simp]:
  "\<lbrakk>write_reg EDPCSR_ref v\<rbrakk>\<^sub>S = write_regS EDPCSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDLSR[liftState_simp]:
  "\<lbrakk>read_reg EDLSR_ref\<rbrakk>\<^sub>S = read_regS EDLSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDLSR[liftState_simp]:
  "\<lbrakk>write_reg EDLSR_ref v\<rbrakk>\<^sub>S = write_regS EDLSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDLAR[liftState_simp]:
  "\<lbrakk>read_reg EDLAR_ref\<rbrakk>\<^sub>S = read_regS EDLAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDLAR[liftState_simp]:
  "\<lbrakk>write_reg EDLAR_ref v\<rbrakk>\<^sub>S = write_regS EDLAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDITCTRL[liftState_simp]:
  "\<lbrakk>read_reg EDITCTRL_ref\<rbrakk>\<^sub>S = read_regS EDITCTRL_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDITCTRL[liftState_simp]:
  "\<lbrakk>write_reg EDITCTRL_ref v\<rbrakk>\<^sub>S = write_regS EDITCTRL_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDHSR[liftState_simp]:
  "\<lbrakk>read_reg EDHSR_ref\<rbrakk>\<^sub>S = read_regS EDHSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDHSR[liftState_simp]:
  "\<lbrakk>write_reg EDHSR_ref v\<rbrakk>\<^sub>S = write_regS EDHSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDESR[liftState_simp]:
  "\<lbrakk>read_reg EDESR_ref\<rbrakk>\<^sub>S = read_regS EDESR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDESR[liftState_simp]:
  "\<lbrakk>write_reg EDESR_ref v\<rbrakk>\<^sub>S = write_regS EDESR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDECR[liftState_simp]:
  "\<lbrakk>read_reg EDECR_ref\<rbrakk>\<^sub>S = read_regS EDECR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDECR[liftState_simp]:
  "\<lbrakk>write_reg EDECR_ref v\<rbrakk>\<^sub>S = write_regS EDECR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDDFR[liftState_simp]:
  "\<lbrakk>read_reg EDDFR_ref\<rbrakk>\<^sub>S = read_regS EDDFR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDDFR[liftState_simp]:
  "\<lbrakk>write_reg EDDFR_ref v\<rbrakk>\<^sub>S = write_regS EDDFR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDDEVTYPE[liftState_simp]:
  "\<lbrakk>read_reg EDDEVTYPE_ref\<rbrakk>\<^sub>S = read_regS EDDEVTYPE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDDEVTYPE[liftState_simp]:
  "\<lbrakk>write_reg EDDEVTYPE_ref v\<rbrakk>\<^sub>S = write_regS EDDEVTYPE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDDEVID2[liftState_simp]:
  "\<lbrakk>read_reg EDDEVID2_ref\<rbrakk>\<^sub>S = read_regS EDDEVID2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDDEVID2[liftState_simp]:
  "\<lbrakk>write_reg EDDEVID2_ref v\<rbrakk>\<^sub>S = write_regS EDDEVID2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDDEVID1[liftState_simp]:
  "\<lbrakk>read_reg EDDEVID1_ref\<rbrakk>\<^sub>S = read_regS EDDEVID1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDDEVID1[liftState_simp]:
  "\<lbrakk>write_reg EDDEVID1_ref v\<rbrakk>\<^sub>S = write_regS EDDEVID1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDDEVID[liftState_simp]:
  "\<lbrakk>read_reg EDDEVID_ref\<rbrakk>\<^sub>S = read_regS EDDEVID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDDEVID[liftState_simp]:
  "\<lbrakk>write_reg EDDEVID_ref v\<rbrakk>\<^sub>S = write_regS EDDEVID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDCIDR3[liftState_simp]:
  "\<lbrakk>read_reg EDCIDR3_ref\<rbrakk>\<^sub>S = read_regS EDCIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDCIDR3[liftState_simp]:
  "\<lbrakk>write_reg EDCIDR3_ref v\<rbrakk>\<^sub>S = write_regS EDCIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDCIDR2[liftState_simp]:
  "\<lbrakk>read_reg EDCIDR2_ref\<rbrakk>\<^sub>S = read_regS EDCIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDCIDR2[liftState_simp]:
  "\<lbrakk>write_reg EDCIDR2_ref v\<rbrakk>\<^sub>S = write_regS EDCIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDCIDR1[liftState_simp]:
  "\<lbrakk>read_reg EDCIDR1_ref\<rbrakk>\<^sub>S = read_regS EDCIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDCIDR1[liftState_simp]:
  "\<lbrakk>write_reg EDCIDR1_ref v\<rbrakk>\<^sub>S = write_regS EDCIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDCIDR0[liftState_simp]:
  "\<lbrakk>read_reg EDCIDR0_ref\<rbrakk>\<^sub>S = read_regS EDCIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDCIDR0[liftState_simp]:
  "\<lbrakk>write_reg EDCIDR0_ref v\<rbrakk>\<^sub>S = write_regS EDCIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDAA32PFR[liftState_simp]:
  "\<lbrakk>read_reg EDAA32PFR_ref\<rbrakk>\<^sub>S = read_regS EDAA32PFR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDAA32PFR[liftState_simp]:
  "\<lbrakk>write_reg EDAA32PFR_ref v\<rbrakk>\<^sub>S = write_regS EDAA32PFR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGWFAR[liftState_simp]:
  "\<lbrakk>read_reg DBGWFAR_ref\<rbrakk>\<^sub>S = read_regS DBGWFAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGWFAR[liftState_simp]:
  "\<lbrakk>write_reg DBGWFAR_ref v\<rbrakk>\<^sub>S = write_regS DBGWFAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDSAR[liftState_simp]:
  "\<lbrakk>read_reg DBGDSAR_ref\<rbrakk>\<^sub>S = read_regS DBGDSAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDSAR[liftState_simp]:
  "\<lbrakk>write_reg DBGDSAR_ref v\<rbrakk>\<^sub>S = write_regS DBGDSAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDIDR[liftState_simp]:
  "\<lbrakk>read_reg DBGDIDR_ref\<rbrakk>\<^sub>S = read_regS DBGDIDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDIDR[liftState_simp]:
  "\<lbrakk>write_reg DBGDIDR_ref v\<rbrakk>\<^sub>S = write_regS DBGDIDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDEVID2[liftState_simp]:
  "\<lbrakk>read_reg DBGDEVID2_ref\<rbrakk>\<^sub>S = read_regS DBGDEVID2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDEVID2[liftState_simp]:
  "\<lbrakk>write_reg DBGDEVID2_ref v\<rbrakk>\<^sub>S = write_regS DBGDEVID2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDEVID1[liftState_simp]:
  "\<lbrakk>read_reg DBGDEVID1_ref\<rbrakk>\<^sub>S = read_regS DBGDEVID1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDEVID1[liftState_simp]:
  "\<lbrakk>write_reg DBGDEVID1_ref v\<rbrakk>\<^sub>S = write_regS DBGDEVID1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIPIDR4[liftState_simp]:
  "\<lbrakk>read_reg CTIPIDR4_ref\<rbrakk>\<^sub>S = read_regS CTIPIDR4_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIPIDR4[liftState_simp]:
  "\<lbrakk>write_reg CTIPIDR4_ref v\<rbrakk>\<^sub>S = write_regS CTIPIDR4_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIPIDR3[liftState_simp]:
  "\<lbrakk>read_reg CTIPIDR3_ref\<rbrakk>\<^sub>S = read_regS CTIPIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIPIDR3[liftState_simp]:
  "\<lbrakk>write_reg CTIPIDR3_ref v\<rbrakk>\<^sub>S = write_regS CTIPIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIPIDR2[liftState_simp]:
  "\<lbrakk>read_reg CTIPIDR2_ref\<rbrakk>\<^sub>S = read_regS CTIPIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIPIDR2[liftState_simp]:
  "\<lbrakk>write_reg CTIPIDR2_ref v\<rbrakk>\<^sub>S = write_regS CTIPIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIPIDR1[liftState_simp]:
  "\<lbrakk>read_reg CTIPIDR1_ref\<rbrakk>\<^sub>S = read_regS CTIPIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIPIDR1[liftState_simp]:
  "\<lbrakk>write_reg CTIPIDR1_ref v\<rbrakk>\<^sub>S = write_regS CTIPIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIPIDR0[liftState_simp]:
  "\<lbrakk>read_reg CTIPIDR0_ref\<rbrakk>\<^sub>S = read_regS CTIPIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIPIDR0[liftState_simp]:
  "\<lbrakk>write_reg CTIPIDR0_ref v\<rbrakk>\<^sub>S = write_regS CTIPIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTILSR[liftState_simp]:
  "\<lbrakk>read_reg CTILSR_ref\<rbrakk>\<^sub>S = read_regS CTILSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTILSR[liftState_simp]:
  "\<lbrakk>write_reg CTILSR_ref v\<rbrakk>\<^sub>S = write_regS CTILSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTILAR[liftState_simp]:
  "\<lbrakk>read_reg CTILAR_ref\<rbrakk>\<^sub>S = read_regS CTILAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTILAR[liftState_simp]:
  "\<lbrakk>write_reg CTILAR_ref v\<rbrakk>\<^sub>S = write_regS CTILAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIITCTRL[liftState_simp]:
  "\<lbrakk>read_reg CTIITCTRL_ref\<rbrakk>\<^sub>S = read_regS CTIITCTRL_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIITCTRL[liftState_simp]:
  "\<lbrakk>write_reg CTIITCTRL_ref v\<rbrakk>\<^sub>S = write_regS CTIITCTRL_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIDEVTYPE[liftState_simp]:
  "\<lbrakk>read_reg CTIDEVTYPE_ref\<rbrakk>\<^sub>S = read_regS CTIDEVTYPE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIDEVTYPE[liftState_simp]:
  "\<lbrakk>write_reg CTIDEVTYPE_ref v\<rbrakk>\<^sub>S = write_regS CTIDEVTYPE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIDEVID2[liftState_simp]:
  "\<lbrakk>read_reg CTIDEVID2_ref\<rbrakk>\<^sub>S = read_regS CTIDEVID2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIDEVID2[liftState_simp]:
  "\<lbrakk>write_reg CTIDEVID2_ref v\<rbrakk>\<^sub>S = write_regS CTIDEVID2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIDEVID1[liftState_simp]:
  "\<lbrakk>read_reg CTIDEVID1_ref\<rbrakk>\<^sub>S = read_regS CTIDEVID1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIDEVID1[liftState_simp]:
  "\<lbrakk>write_reg CTIDEVID1_ref v\<rbrakk>\<^sub>S = write_regS CTIDEVID1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIDEVID[liftState_simp]:
  "\<lbrakk>read_reg CTIDEVID_ref\<rbrakk>\<^sub>S = read_regS CTIDEVID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIDEVID[liftState_simp]:
  "\<lbrakk>write_reg CTIDEVID_ref v\<rbrakk>\<^sub>S = write_regS CTIDEVID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIDEVCTL[liftState_simp]:
  "\<lbrakk>read_reg CTIDEVCTL_ref\<rbrakk>\<^sub>S = read_regS CTIDEVCTL_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIDEVCTL[liftState_simp]:
  "\<lbrakk>write_reg CTIDEVCTL_ref v\<rbrakk>\<^sub>S = write_regS CTIDEVCTL_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTICONTROL[liftState_simp]:
  "\<lbrakk>read_reg CTICONTROL_ref\<rbrakk>\<^sub>S = read_regS CTICONTROL_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTICONTROL[liftState_simp]:
  "\<lbrakk>write_reg CTICONTROL_ref v\<rbrakk>\<^sub>S = write_regS CTICONTROL_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTICIDR3[liftState_simp]:
  "\<lbrakk>read_reg CTICIDR3_ref\<rbrakk>\<^sub>S = read_regS CTICIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTICIDR3[liftState_simp]:
  "\<lbrakk>write_reg CTICIDR3_ref v\<rbrakk>\<^sub>S = write_regS CTICIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTICIDR2[liftState_simp]:
  "\<lbrakk>read_reg CTICIDR2_ref\<rbrakk>\<^sub>S = read_regS CTICIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTICIDR2[liftState_simp]:
  "\<lbrakk>write_reg CTICIDR2_ref v\<rbrakk>\<^sub>S = write_regS CTICIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTICIDR1[liftState_simp]:
  "\<lbrakk>read_reg CTICIDR1_ref\<rbrakk>\<^sub>S = read_regS CTICIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTICIDR1[liftState_simp]:
  "\<lbrakk>write_reg CTICIDR1_ref v\<rbrakk>\<^sub>S = write_regS CTICIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTICIDR0[liftState_simp]:
  "\<lbrakk>read_reg CTICIDR0_ref\<rbrakk>\<^sub>S = read_regS CTICIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTICIDR0[liftState_simp]:
  "\<lbrakk>write_reg CTICIDR0_ref v\<rbrakk>\<^sub>S = write_regS CTICIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTIAUTHSTATUS[liftState_simp]:
  "\<lbrakk>read_reg CTIAUTHSTATUS_ref\<rbrakk>\<^sub>S = read_regS CTIAUTHSTATUS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTIAUTHSTATUS[liftState_simp]:
  "\<lbrakk>write_reg CTIAUTHSTATUS_ref v\<rbrakk>\<^sub>S = write_regS CTIAUTHSTATUS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CSSELR_S[liftState_simp]:
  "\<lbrakk>read_reg CSSELR_S_ref\<rbrakk>\<^sub>S = read_regS CSSELR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CSSELR_S[liftState_simp]:
  "\<lbrakk>write_reg CSSELR_S_ref v\<rbrakk>\<^sub>S = write_regS CSSELR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTSR[liftState_simp]:
  "\<lbrakk>read_reg CNTSR_ref\<rbrakk>\<^sub>S = read_regS CNTSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTSR[liftState_simp]:
  "\<lbrakk>write_reg CNTSR_ref v\<rbrakk>\<^sub>S = write_regS CNTSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_CTL_S[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CTL_S_ref\<rbrakk>\<^sub>S = read_regS CNTP_CTL_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_CTL_S[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CTL_S_ref v\<rbrakk>\<^sub>S = write_regS CNTP_CTL_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTNSAR[liftState_simp]:
  "\<lbrakk>read_reg CNTNSAR_ref\<rbrakk>\<^sub>S = read_regS CNTNSAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTNSAR[liftState_simp]:
  "\<lbrakk>write_reg CNTNSAR_ref v\<rbrakk>\<^sub>S = write_regS CNTNSAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTID[liftState_simp]:
  "\<lbrakk>read_reg CNTID_ref\<rbrakk>\<^sub>S = read_regS CNTID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTID[liftState_simp]:
  "\<lbrakk>write_reg CNTID_ref v\<rbrakk>\<^sub>S = write_regS CNTID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTEL0ACR[liftState_simp]:
  "\<lbrakk>read_reg CNTEL0ACR_ref\<rbrakk>\<^sub>S = read_regS CNTEL0ACR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTEL0ACR[liftState_simp]:
  "\<lbrakk>write_reg CNTEL0ACR_ref v\<rbrakk>\<^sub>S = write_regS CNTEL0ACR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTCR[liftState_simp]:
  "\<lbrakk>read_reg CNTCR_ref\<rbrakk>\<^sub>S = read_regS CNTCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTCR[liftState_simp]:
  "\<lbrakk>write_reg CNTCR_ref v\<rbrakk>\<^sub>S = write_regS CNTCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMPIDR4[liftState_simp]:
  "\<lbrakk>read_reg AMPIDR4_ref\<rbrakk>\<^sub>S = read_regS AMPIDR4_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMPIDR4[liftState_simp]:
  "\<lbrakk>write_reg AMPIDR4_ref v\<rbrakk>\<^sub>S = write_regS AMPIDR4_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMPIDR3[liftState_simp]:
  "\<lbrakk>read_reg AMPIDR3_ref\<rbrakk>\<^sub>S = read_regS AMPIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMPIDR3[liftState_simp]:
  "\<lbrakk>write_reg AMPIDR3_ref v\<rbrakk>\<^sub>S = write_regS AMPIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMPIDR2[liftState_simp]:
  "\<lbrakk>read_reg AMPIDR2_ref\<rbrakk>\<^sub>S = read_regS AMPIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMPIDR2[liftState_simp]:
  "\<lbrakk>write_reg AMPIDR2_ref v\<rbrakk>\<^sub>S = write_regS AMPIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMPIDR1[liftState_simp]:
  "\<lbrakk>read_reg AMPIDR1_ref\<rbrakk>\<^sub>S = read_regS AMPIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMPIDR1[liftState_simp]:
  "\<lbrakk>write_reg AMPIDR1_ref v\<rbrakk>\<^sub>S = write_regS AMPIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMPIDR0[liftState_simp]:
  "\<lbrakk>read_reg AMPIDR0_ref\<rbrakk>\<^sub>S = read_regS AMPIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMPIDR0[liftState_simp]:
  "\<lbrakk>write_reg AMPIDR0_ref v\<rbrakk>\<^sub>S = write_regS AMPIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMDEVTYPE[liftState_simp]:
  "\<lbrakk>read_reg AMDEVTYPE_ref\<rbrakk>\<^sub>S = read_regS AMDEVTYPE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMDEVTYPE[liftState_simp]:
  "\<lbrakk>write_reg AMDEVTYPE_ref v\<rbrakk>\<^sub>S = write_regS AMDEVTYPE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCIDR3[liftState_simp]:
  "\<lbrakk>read_reg AMCIDR3_ref\<rbrakk>\<^sub>S = read_regS AMCIDR3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCIDR3[liftState_simp]:
  "\<lbrakk>write_reg AMCIDR3_ref v\<rbrakk>\<^sub>S = write_regS AMCIDR3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCIDR2[liftState_simp]:
  "\<lbrakk>read_reg AMCIDR2_ref\<rbrakk>\<^sub>S = read_regS AMCIDR2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCIDR2[liftState_simp]:
  "\<lbrakk>write_reg AMCIDR2_ref v\<rbrakk>\<^sub>S = write_regS AMCIDR2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCIDR1[liftState_simp]:
  "\<lbrakk>read_reg AMCIDR1_ref\<rbrakk>\<^sub>S = read_regS AMCIDR1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCIDR1[liftState_simp]:
  "\<lbrakk>write_reg AMCIDR1_ref v\<rbrakk>\<^sub>S = write_regS AMCIDR1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCIDR0[liftState_simp]:
  "\<lbrakk>read_reg AMCIDR0_ref\<rbrakk>\<^sub>S = read_regS AMCIDR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCIDR0[liftState_simp]:
  "\<lbrakk>write_reg AMCIDR0_ref v\<rbrakk>\<^sub>S = write_regS AMCIDR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_clock_divider[liftState_simp]:
  "\<lbrakk>read_reg clock_divider_ref\<rbrakk>\<^sub>S = read_regS clock_divider_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_clock_divider[liftState_simp]:
  "\<lbrakk>write_reg clock_divider_ref v\<rbrakk>\<^sub>S = write_regS clock_divider_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDPRSR[liftState_simp]:
  "\<lbrakk>read_reg EDPRSR_ref\<rbrakk>\<^sub>S = read_regS EDPRSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDPRSR[liftState_simp]:
  "\<lbrakk>write_reg EDPRSR_ref v\<rbrakk>\<^sub>S = write_regS EDPRSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSWINC_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMSWINC_EL0_ref\<rbrakk>\<^sub>S = read_regS PMSWINC_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSWINC_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMSWINC_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMSWINC_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSLAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSLAR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSLAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSLAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSLAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSLAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_EOIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_EOIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_EOIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_EOIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_EOIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_EOIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_EOIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_EOIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_EOIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_EOIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_EOIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_EOIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_EOIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_EOIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_EOIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_EOIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SGI1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_SGI1R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_SGI1R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SGI1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_SGI1R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_SGI1R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SGI0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_SGI0R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_SGI0R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SGI0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_SGI0R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_SGI0R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_DIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_DIR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_DIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_DIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_DIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_DIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_DIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_DIR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_DIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_DIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_DIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_DIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_ASGI1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_ASGI1R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_ASGI1R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_ASGI1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_ASGI1R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_ASGI1R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDTRTX_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTRTX_EL0_ref\<rbrakk>\<^sub>S = read_regS DBGDTRTX_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDTRTX_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTRTX_EL0_ref v\<rbrakk>\<^sub>S = write_regS DBGDTRTX_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSESR_EL2_ref\<rbrakk>\<^sub>S = read_regS VSESR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSESR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VSESR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VMPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VMPIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS VMPIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VMPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VMPIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VMPIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS MPIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MPIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VDISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VDISR_EL2_ref\<rbrakk>\<^sub>S = read_regS VDISR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VDISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VDISR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VDISR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DISR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DISR_EL1_ref\<rbrakk>\<^sub>S = read_regS DISR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DISR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DISR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DISR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TRFCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TRFCR_EL2_ref\<rbrakk>\<^sub>S = read_regS TRFCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TRFCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TRFCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS TRFCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TRFCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TRFCR_EL1_ref\<rbrakk>\<^sub>S = read_regS TRFCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TRFCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TRFCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS TRFCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL3_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL3_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL0[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL0_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL0[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL0_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDRRO_EL0[liftState_simp]:
  "\<lbrakk>read_reg TPIDRRO_EL0_ref\<rbrakk>\<^sub>S = read_regS TPIDRRO_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDRRO_EL0[liftState_simp]:
  "\<lbrakk>write_reg TPIDRRO_EL0_ref v\<rbrakk>\<^sub>S = write_regS TPIDRRO_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR2_EL0[liftState_simp]:
  "\<lbrakk>read_reg TPIDR2_EL0_ref\<rbrakk>\<^sub>S = read_regS TPIDR2_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR2_EL0[liftState_simp]:
  "\<lbrakk>write_reg TPIDR2_EL0_ref v\<rbrakk>\<^sub>S = write_regS TPIDR2_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SMPRI_EL1[liftState_simp]:
  "\<lbrakk>read_reg SMPRI_EL1_ref\<rbrakk>\<^sub>S = read_regS SMPRI_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SMPRI_EL1[liftState_simp]:
  "\<lbrakk>write_reg SMPRI_EL1_ref v\<rbrakk>\<^sub>S = write_regS SMPRI_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SMPRIMAP_EL2[liftState_simp]:
  "\<lbrakk>read_reg SMPRIMAP_EL2_ref\<rbrakk>\<^sub>S = read_regS SMPRIMAP_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SMPRIMAP_EL2[liftState_simp]:
  "\<lbrakk>write_reg SMPRIMAP_EL2_ref v\<rbrakk>\<^sub>S = write_regS SMPRIMAP_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SMIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SMIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS SMIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SMIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SMIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS SMIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCXTNUM_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL3_ref\<rbrakk>\<^sub>S = read_regS SCXTNUM_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCXTNUM_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL3_ref v\<rbrakk>\<^sub>S = write_regS SCXTNUM_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCXTNUM_EL2[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL2_ref\<rbrakk>\<^sub>S = read_regS SCXTNUM_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCXTNUM_EL2[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL2_ref v\<rbrakk>\<^sub>S = write_regS SCXTNUM_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCXTNUM_EL1[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL1_ref\<rbrakk>\<^sub>S = read_regS SCXTNUM_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCXTNUM_EL1[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL1_ref v\<rbrakk>\<^sub>S = write_regS SCXTNUM_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCXTNUM_EL0[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL0_ref\<rbrakk>\<^sub>S = read_regS SCXTNUM_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCXTNUM_EL0[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL0_ref v\<rbrakk>\<^sub>S = write_regS SCXTNUM_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL3_ref\<rbrakk>\<^sub>S = read_regS RVBAR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL3_ref v\<rbrakk>\<^sub>S = write_regS RVBAR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL2_ref\<rbrakk>\<^sub>S = read_regS RVBAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS RVBAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL1_ref\<rbrakk>\<^sub>S = read_regS RVBAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS RVBAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RNDR[liftState_simp]:
  "\<lbrakk>read_reg RNDR_ref\<rbrakk>\<^sub>S = read_regS RNDR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RNDR[liftState_simp]:
  "\<lbrakk>write_reg RNDR_ref v\<rbrakk>\<^sub>S = write_regS RNDR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RNDRRS[liftState_simp]:
  "\<lbrakk>read_reg RNDRRS_ref\<rbrakk>\<^sub>S = read_regS RNDRRS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RNDRRS[liftState_simp]:
  "\<lbrakk>write_reg RNDRRS_ref v\<rbrakk>\<^sub>S = write_regS RNDRRS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RMR_EL3[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL3_ref\<rbrakk>\<^sub>S = read_regS RMR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RMR_EL3[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL3_ref v\<rbrakk>\<^sub>S = write_regS RMR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RMR_EL2[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL2_ref\<rbrakk>\<^sub>S = read_regS RMR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RMR_EL2[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL2_ref v\<rbrakk>\<^sub>S = write_regS RMR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL1_ref\<rbrakk>\<^sub>S = read_regS RMR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL1_ref v\<rbrakk>\<^sub>S = write_regS RMR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RGSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RGSR_EL1_ref\<rbrakk>\<^sub>S = read_regS RGSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RGSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RGSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS RGSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_REVIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg REVIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS REVIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_REVIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg REVIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS REVIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMXEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMXEVTYPER_EL0_ref\<rbrakk>\<^sub>S = read_regS PMXEVTYPER_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMXEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMXEVTYPER_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMXEVTYPER_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMXEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMXEVCNTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMXEVCNTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMXEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMXEVCNTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMXEVCNTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSNEVFR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSNEVFR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSNEVFR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSNEVFR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSNEVFR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSNEVFR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSLATFR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSLATFR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSLATFR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSLATFR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSLATFR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSLATFR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSIRR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSIRR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSIRR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSIRR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSIRR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSIRR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSICR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSICR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSICR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSICR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSICR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSICR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSFCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSFCR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSFCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSFCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSFCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSFCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSEVFR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSEVFR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSEVFR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSEVFR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSEVFR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSEVFR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSELR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMSELR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMSELR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSELR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMSELR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMSELR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg PMSCR_EL2_ref\<rbrakk>\<^sub>S = read_regS PMSCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg PMSCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS PMSCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSCR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMOVSSET_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMOVSSET_EL0_ref\<rbrakk>\<^sub>S = read_regS PMOVSSET_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMOVSSET_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMOVSSET_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMOVSSET_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMOVSCLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMOVSCLR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMOVSCLR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMOVSCLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMOVSCLR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMOVSCLR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMMIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMMIR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMMIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMMIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMMIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMMIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMINTENSET_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMINTENSET_EL1_ref\<rbrakk>\<^sub>S = read_regS PMINTENSET_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMINTENSET_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMINTENSET_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMINTENSET_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMINTENCLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMINTENCLR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMINTENCLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMINTENCLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMINTENCLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMINTENCLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMEVCNTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMEVCNTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMEVCNTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMEVCNTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCNTENSET_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCNTENSET_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCNTENSET_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCNTENSET_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCNTENSET_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCNTENSET_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCNTENCLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCNTENCLR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCNTENCLR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCNTENCLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCNTENCLR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCNTENCLR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCEID1_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCEID1_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCEID1_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCEID1_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCEID1_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCEID1_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCEID0_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCEID0_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCEID0_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCEID0_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCEID0_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCEID0_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCCNTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCCNTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCCNTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCCNTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMUSERENR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMUSERENR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMUSERENR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMUSERENR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCCFILTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCCFILTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCCFILTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCCFILTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCCFILTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCCFILTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBSR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBPTR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBPTR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBPTR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBPTR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBPTR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBPTR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBLIMITR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBLIMITR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBLIMITR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBLIMITR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBLIMITR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBLIMITR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PAR_EL1_ref\<rbrakk>\<^sub>S = read_regS PAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSDTRTX_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDTRTX_EL1_ref\<rbrakk>\<^sub>S = read_regS OSDTRTX_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSDTRTX_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDTRTX_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSDTRTX_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSDTRRX_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDTRRX_EL1_ref\<rbrakk>\<^sub>S = read_regS OSDTRRX_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSDTRRX_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDTRRX_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSDTRRX_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MVFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS MVFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MVFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS MVFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MVFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS MVFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MVFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS MVFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MVFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS MVFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MVFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS MVFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VPIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS VPIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VPIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VPIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS MIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDRAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDRAR_EL1_ref\<rbrakk>\<^sub>S = read_regS MDRAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDRAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDRAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MDRAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCCINT_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDCCINT_EL1_ref\<rbrakk>\<^sub>S = read_regS MDCCINT_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCCINT_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDCCINT_EL1_ref v\<rbrakk>\<^sub>S = write_regS MDCCINT_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORSA_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORSA_EL1_ref\<rbrakk>\<^sub>S = read_regS LORSA_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORSA_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORSA_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORSA_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORN_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORN_EL1_ref\<rbrakk>\<^sub>S = read_regS LORN_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORN_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORN_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORN_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORID_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORID_EL1_ref\<rbrakk>\<^sub>S = read_regS LORID_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORID_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORID_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORID_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LOREA_EL1[liftState_simp]:
  "\<lbrakk>read_reg LOREA_EL1_ref\<rbrakk>\<^sub>S = read_regS LOREA_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LOREA_EL1[liftState_simp]:
  "\<lbrakk>write_reg LOREA_EL1_ref v\<rbrakk>\<^sub>S = write_regS LOREA_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORC_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORC_EL1_ref\<rbrakk>\<^sub>S = read_regS LORC_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORC_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORC_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORC_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ISR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ISR_EL1_ref\<rbrakk>\<^sub>S = read_regS ISR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ISR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ISR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ISR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_PFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_PFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_PFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_PFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_PFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_PFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_PFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_PFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_PFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_PFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_PFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_PFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR5_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR5_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR5_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR5_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR5_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR5_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR4_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR4_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR4_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR4_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR4_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR4_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR3_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR3_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR3_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR3_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR3_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR3_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR6_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR6_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR6_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR6_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR6_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR6_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR5_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR5_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR5_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR5_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR5_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR5_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR4_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR4_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR4_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR4_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR4_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR4_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR3_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR3_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR3_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR3_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR3_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR3_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_DFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_DFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_DFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_DFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_DFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_DFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_DFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_DFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_DFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_DFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_DFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_DFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64ZFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ZFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64ZFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64ZFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ZFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64ZFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64SMFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64SMFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64SMFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64SMFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64SMFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64SMFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64PFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64PFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64PFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64PFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64PFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64PFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64PFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64PFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64PFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64PFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64PFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64PFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64MMFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64MMFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64MMFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64MMFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64MMFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64MMFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64MMFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64MMFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64MMFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64MMFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64MMFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64MMFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64ISAR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ISAR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64ISAR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64ISAR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ISAR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64ISAR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64ISAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ISAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64ISAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64ISAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ISAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64ISAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64ISAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ISAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64ISAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64ISAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ISAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64ISAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64DFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64DFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64DFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64DFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64DFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64DFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64DFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64DFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64DFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64DFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64AFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64AFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64AFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64AFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64AFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64AFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64AFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64AFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64AFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64AFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64AFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64AFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_NMIAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_NMIAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_NMIAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_NMIAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_NMIAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_NMIAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_NMIAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_NMIAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_NMIAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_NMIAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_NMIAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_NMIAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_BPR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_BPR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_BPR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_BPR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_BPR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_BPR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_BPR1_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR1_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_BPR1_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_BPR1_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR1_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_BPR1_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_BPR1_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR1_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_BPR1_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_BPR1_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR1_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_BPR1_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_VTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_VTR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_VTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_VTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_VTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_VTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_VMCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_VMCR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_VMCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_VMCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_VMCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_VMCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_MISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_MISR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_MISR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_MISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_MISR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_MISR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_LR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_LR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_LR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_LR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_LR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_LR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_ELRSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_ELRSR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_ELRSR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_ELRSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_ELRSR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_ELRSR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_EISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_EISR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_EISR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_EISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_EISR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_EISR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_AP1R_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_AP1R_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_AP1R_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_AP1R_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_AP1R_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_AP1R_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_AP0R_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_AP0R_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_AP0R_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_AP0R_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_AP0R_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_AP0R_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_RPR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_RPR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_RPR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_RPR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_RPR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_RPR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_RPR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_RPR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_RPR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_RPR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_RPR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_RPR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_PMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_PMR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_PMR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_PMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_PMR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_PMR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL3_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN1_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL3_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN1_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IGRPEN1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IGRPEN1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IGRPEN1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IGRPEN1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IGRPEN1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IGRPEN1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN1_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN1_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN1_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN1_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IGRPEN0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IGRPEN0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IGRPEN0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IGRPEN0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_IAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_IAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_IAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_IAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_HPPIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_HPPIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_HPPIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_HPPIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_HPPIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_HPPIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_HPPIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_HPPIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_HPPIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_HPPIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_HPPIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_HPPIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_HPPIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_HPPIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_HPPIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_HPPIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_CTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL3_ref\<rbrakk>\<^sub>S = read_regS ICC_CTLR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_CTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ICC_CTLR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_CTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_CTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_CTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_CTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_CTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_CTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_CTLR_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_CTLR_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_CTLR_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_CTLR_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_CTLR_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_CTLR_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_CTLR_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_CTLR_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_BPR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_BPR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_BPR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_BPR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_BPR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_BPR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_BPR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_BPR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_BPR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_BPR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_AP1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_AP1R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_AP1R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_AP1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_AP1R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_AP1R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_AP1R_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP1R_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_AP1R_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_AP1R_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP1R_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_AP1R_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_AP1R_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP1R_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_AP1R_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_AP1R_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP1R_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_AP1R_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_AP0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_AP0R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_AP0R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_AP0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_AP0R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_AP0R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_HCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_HCR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_HCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_HCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_HCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_HCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL3_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL3_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL2_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_AP0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP0R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_AP0R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_AP0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP0R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_AP0R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HSTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HSTR_EL2_ref\<rbrakk>\<^sub>S = read_regS HSTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HSTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HSTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HSTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HFGWTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HFGWTR_EL2_ref\<rbrakk>\<^sub>S = read_regS HFGWTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HFGWTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HFGWTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HFGWTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HFGITR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HFGITR_EL2_ref\<rbrakk>\<^sub>S = read_regS HFGITR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HFGITR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HFGITR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HFGITR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HDFGWTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HDFGWTR_EL2_ref\<rbrakk>\<^sub>S = read_regS HDFGWTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HDFGWTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HDFGWTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HDFGWTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HACR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HACR_EL2_ref\<rbrakk>\<^sub>S = read_regS HACR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HACR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HACR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HACR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GMID_EL1[liftState_simp]:
  "\<lbrakk>read_reg GMID_EL1_ref\<rbrakk>\<^sub>S = read_regS GMID_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GMID_EL1[liftState_simp]:
  "\<lbrakk>write_reg GMID_EL1_ref v\<rbrakk>\<^sub>S = write_regS GMID_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg GCR_EL1_ref\<rbrakk>\<^sub>S = read_regS GCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg GCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS GCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FPEXC32_EL2[liftState_simp]:
  "\<lbrakk>read_reg FPEXC32_EL2_ref\<rbrakk>\<^sub>S = read_regS FPEXC32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FPEXC32_EL2[liftState_simp]:
  "\<lbrakk>write_reg FPEXC32_EL2_ref v\<rbrakk>\<^sub>S = write_regS FPEXC32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXSTATUS_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXSTATUS_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXSTATUS_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXSTATUS_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXSTATUS_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXSTATUS_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXPFGF_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXPFGF_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXPFGF_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXPFGF_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXPFGF_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXPFGF_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXPFGCTL_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXPFGCTL_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXPFGCTL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXPFGCTL_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXPFGCTL_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXPFGCTL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXPFGCDN_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXPFGCDN_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXPFGCDN_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXPFGCDN_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXPFGCDN_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXPFGCDN_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXMISC3_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXMISC3_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXMISC3_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXMISC3_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXMISC3_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXMISC3_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXMISC2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXMISC2_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXMISC2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXMISC2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXMISC2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXMISC2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXMISC1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXMISC1_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXMISC1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXMISC1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXMISC1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXMISC1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXMISC0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXMISC0_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXMISC0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXMISC0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXMISC0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXMISC0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXFR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXFR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXFR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXFR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXFR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXFR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXCTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXCTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXCTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXCTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXCTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXCTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXADDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXADDR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXADDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXADDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXADDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXADDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERRSELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERRSELR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERRSELR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERRSELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERRSELR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERRSELR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERRIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERRIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERRIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERRIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERRIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERRIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DCZID_EL0[liftState_simp]:
  "\<lbrakk>read_reg DCZID_EL0_ref\<rbrakk>\<^sub>S = read_regS DCZID_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DCZID_EL0[liftState_simp]:
  "\<lbrakk>write_reg DCZID_EL0_ref v\<rbrakk>\<^sub>S = write_regS DCZID_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGVCR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg DBGVCR32_EL2_ref\<rbrakk>\<^sub>S = read_regS DBGVCR32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGVCR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg DBGVCR32_EL2_ref v\<rbrakk>\<^sub>S = write_regS DBGVCR32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTR_EL0_ref\<rbrakk>\<^sub>S = read_regS DBGDTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS DBGDTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDTRRX_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTRRX_EL0_ref\<rbrakk>\<^sub>S = read_regS DBGDTRRX_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDTRRX_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTRRX_EL0_ref v\<rbrakk>\<^sub>S = write_regS DBGDTRRX_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGCLAIMSET_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGCLAIMSET_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGCLAIMSET_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGCLAIMSET_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGCLAIMSET_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGCLAIMSET_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGCLAIMCLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGCLAIMCLR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGCLAIMCLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGCLAIMCLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGCLAIMCLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGCLAIMCLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGAUTHSTATUS_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGAUTHSTATUS_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGAUTHSTATUS_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGAUTHSTATUS_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGAUTHSTATUS_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGAUTHSTATUS_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DACR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg DACR32_EL2_ref\<rbrakk>\<^sub>S = read_regS DACR32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DACR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg DACR32_EL2_ref v\<rbrakk>\<^sub>S = write_regS DACR32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CSSELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CSSELR_EL1_ref\<rbrakk>\<^sub>S = read_regS CSSELR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CSSELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CSSELR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CSSELR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPS_CVAL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_CVAL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTPS_CVAL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPS_CVAL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_CVAL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTPS_CVAL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPS_CTL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_CTL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTPS_CTL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPS_CTL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_CTL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTPS_CTL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTVOFF_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTVOFF_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTVOFF_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTVOFF_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTVOFF_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTVOFF_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTV_CVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_CVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTV_CVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTV_CVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_CVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTV_CVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHV_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHV_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHV_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHV_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHVS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHVS_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHVS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHVS_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTV_CTL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_CTL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTV_CTL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTV_CTL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_CTL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTV_CTL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHV_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHV_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHV_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHV_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHVS_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHVS_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHVS_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHVS_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_CVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTP_CVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_CVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTP_CVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_CTL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CTL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTP_CTL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_CTL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CTL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTP_CTL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPOFF_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTPOFF_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTPOFF_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPOFF_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTPOFF_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTPOFF_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHP_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHP_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHP_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHP_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHP_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHP_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHP_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHP_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHPS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHPS_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHPS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHPS_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHPS_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHPS_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHPS_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHPS_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTKCTL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTKCTL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTKCTL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTKCTL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTKCTL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTKCTL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHCTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHCTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHCTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHCTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHCTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHCTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTFRQ_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTFRQ_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTFRQ_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTFRQ_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTFRQ_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTFRQ_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CCSIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CCSIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS CCSIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CCSIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CCSIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CCSIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CCSIDR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg CCSIDR2_EL1_ref\<rbrakk>\<^sub>S = read_regS CCSIDR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CCSIDR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg CCSIDR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS CCSIDR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBTS_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBTS_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBTS_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBTS_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBTS_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBTS_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBTGT_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBTGT_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBTGT_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBTGT_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBTGT_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBTGT_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBTGTINJ_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBTGTINJ_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBTGTINJ_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBTGTINJ_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBTGTINJ_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBTGTINJ_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBSRC_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBSRC_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBSRC_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBSRC_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBSRC_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBSRC_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBSRCINJ_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBSRCINJ_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBSRCINJ_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBSRCINJ_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBSRCINJ_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBSRCINJ_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBINF_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBINF_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBINF_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBINF_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBINF_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBINF_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBINFINJ_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBINFINJ_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBINFINJ_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBINFINJ_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBINFINJ_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBINFINJ_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HDFGRTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HDFGRTR_EL2_ref\<rbrakk>\<^sub>S = read_regS HDFGRTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HDFGRTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HDFGRTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HDFGRTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APIBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIBKeyLo_EL1_ref\<rbrakk>\<^sub>S = read_regS APIBKeyLo_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APIBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIBKeyLo_EL1_ref v\<rbrakk>\<^sub>S = write_regS APIBKeyLo_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APIBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIBKeyHi_EL1_ref\<rbrakk>\<^sub>S = read_regS APIBKeyHi_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APIBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIBKeyHi_EL1_ref v\<rbrakk>\<^sub>S = write_regS APIBKeyHi_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APIAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIAKeyLo_EL1_ref\<rbrakk>\<^sub>S = read_regS APIAKeyLo_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APIAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = write_regS APIAKeyLo_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APIAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIAKeyHi_EL1_ref\<rbrakk>\<^sub>S = read_regS APIAKeyHi_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APIAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = write_regS APIAKeyHi_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APGAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APGAKeyLo_EL1_ref\<rbrakk>\<^sub>S = read_regS APGAKeyLo_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APGAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APGAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = write_regS APGAKeyLo_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APGAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APGAKeyHi_EL1_ref\<rbrakk>\<^sub>S = read_regS APGAKeyHi_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APGAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APGAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = write_regS APGAKeyHi_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APDBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDBKeyLo_EL1_ref\<rbrakk>\<^sub>S = read_regS APDBKeyLo_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APDBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDBKeyLo_EL1_ref v\<rbrakk>\<^sub>S = write_regS APDBKeyLo_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APDBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDBKeyHi_EL1_ref\<rbrakk>\<^sub>S = read_regS APDBKeyHi_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APDBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDBKeyHi_EL1_ref v\<rbrakk>\<^sub>S = write_regS APDBKeyHi_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APDAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDAKeyLo_EL1_ref\<rbrakk>\<^sub>S = read_regS APDAKeyLo_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APDAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = write_regS APDAKeyLo_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_APDAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDAKeyHi_EL1_ref\<rbrakk>\<^sub>S = read_regS APDAKeyHi_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_APDAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = write_regS APDAKeyHi_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMEVTYPER1_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMEVTYPER1_EL0_ref\<rbrakk>\<^sub>S = read_regS AMEVTYPER1_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMEVTYPER1_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMEVTYPER1_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMEVTYPER1_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMEVTYPER0_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMEVTYPER0_EL0_ref\<rbrakk>\<^sub>S = read_regS AMEVTYPER0_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMEVTYPER0_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMEVTYPER0_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMEVTYPER0_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMEVCNTVOFF1_EL2[liftState_simp]:
  "\<lbrakk>read_reg AMEVCNTVOFF1_EL2_ref\<rbrakk>\<^sub>S = read_regS AMEVCNTVOFF1_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMEVCNTVOFF1_EL2[liftState_simp]:
  "\<lbrakk>write_reg AMEVCNTVOFF1_EL2_ref v\<rbrakk>\<^sub>S = write_regS AMEVCNTVOFF1_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMEVCNTVOFF0_EL2[liftState_simp]:
  "\<lbrakk>read_reg AMEVCNTVOFF0_EL2_ref\<rbrakk>\<^sub>S = read_regS AMEVCNTVOFF0_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMEVCNTVOFF0_EL2[liftState_simp]:
  "\<lbrakk>write_reg AMEVCNTVOFF0_EL2_ref v\<rbrakk>\<^sub>S = write_regS AMEVCNTVOFF0_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMEVCNTR1_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMEVCNTR1_EL0_ref\<rbrakk>\<^sub>S = read_regS AMEVCNTR1_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMEVCNTR1_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMEVCNTR1_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMEVCNTR1_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMEVCNTR0[liftState_simp]:
  "\<lbrakk>read_reg AMEVCNTR0_ref\<rbrakk>\<^sub>S = read_regS AMEVCNTR0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMEVCNTR0[liftState_simp]:
  "\<lbrakk>write_reg AMEVCNTR0_ref v\<rbrakk>\<^sub>S = write_regS AMEVCNTR0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCR_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCR_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCR_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCR_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCNTENSET1_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCNTENSET1_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCNTENSET1_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCNTENSET1_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCNTENSET1_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCNTENSET1_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCNTENSET0_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCNTENSET0_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCNTENSET0_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCNTENSET0_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCNTENSET0_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCNTENSET0_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCNTENCLR1_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCNTENCLR1_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCNTENCLR1_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCNTENCLR1_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCNTENCLR1_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCNTENCLR1_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HAFGRTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HAFGRTR_EL2_ref\<rbrakk>\<^sub>S = read_regS HAFGRTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HAFGRTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HAFGRTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HAFGRTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCNTENCLR0_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCNTENCLR0_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCNTENCLR0_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCNTENCLR0_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCNTENCLR0_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCNTENCLR0_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCGCR_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCGCR_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCGCR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCGCR_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCGCR_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCGCR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCG1IDR_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCG1IDR_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCG1IDR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCG1IDR_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCG1IDR_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCG1IDR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMUSERENR_EL0_ref\<rbrakk>\<^sub>S = read_regS AMUSERENR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMUSERENR_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMUSERENR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMCFGR_EL0[liftState_simp]:
  "\<lbrakk>read_reg AMCFGR_EL0_ref\<rbrakk>\<^sub>S = read_regS AMCFGR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMCFGR_EL0[liftState_simp]:
  "\<lbrakk>write_reg AMCFGR_EL0_ref v\<rbrakk>\<^sub>S = write_regS AMCFGR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR_EL3[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL3_ref\<rbrakk>\<^sub>S = read_regS AMAIR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR_EL3[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL3_ref v\<rbrakk>\<^sub>S = write_regS AMAIR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR_EL2[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL2_ref\<rbrakk>\<^sub>S = read_regS AMAIR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR_EL2[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL2_ref v\<rbrakk>\<^sub>S = write_regS AMAIR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL1_ref\<rbrakk>\<^sub>S = read_regS AMAIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS AMAIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg AIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS AIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg AIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS AIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR1_EL3[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL3_ref\<rbrakk>\<^sub>S = read_regS AFSR1_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR1_EL3[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL3_ref v\<rbrakk>\<^sub>S = write_regS AFSR1_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR1_EL2[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL2_ref\<rbrakk>\<^sub>S = read_regS AFSR1_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR1_EL2[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL2_ref v\<rbrakk>\<^sub>S = write_regS AFSR1_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL1_ref\<rbrakk>\<^sub>S = read_regS AFSR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS AFSR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR0_EL3[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL3_ref\<rbrakk>\<^sub>S = read_regS AFSR0_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR0_EL3[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL3_ref v\<rbrakk>\<^sub>S = write_regS AFSR0_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR0_EL2[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL2_ref\<rbrakk>\<^sub>S = read_regS AFSR0_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR0_EL2[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL2_ref v\<rbrakk>\<^sub>S = write_regS AFSR0_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL1_ref\<rbrakk>\<^sub>S = read_regS AFSR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS AFSR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL3_ref\<rbrakk>\<^sub>S = read_regS ACTLR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ACTLR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL2_ref\<rbrakk>\<^sub>S = read_regS ACTLR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ACTLR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VNCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VNCR_EL2_ref\<rbrakk>\<^sub>S = read_regS VNCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VNCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VNCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VNCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_tlb_enabled[liftState_simp]:
  "\<lbrakk>read_reg tlb_enabled_ref\<rbrakk>\<^sub>S = read_regS tlb_enabled_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_tlb_enabled[liftState_simp]:
  "\<lbrakk>write_reg tlb_enabled_ref v\<rbrakk>\<^sub>S = write_regS tlb_enabled_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VSTTBR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSTTBR_EL2_ref\<rbrakk>\<^sub>S = read_regS VSTTBR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VSTTBR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSTTBR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VSTTBR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VSTCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSTCR_EL2_ref\<rbrakk>\<^sub>S = read_regS VSTCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VSTCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSTCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VSTCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL3_ref\<rbrakk>\<^sub>S = read_regS TTBR0_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL3_ref v\<rbrakk>\<^sub>S = write_regS TTBR0_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL2_ref\<rbrakk>\<^sub>S = read_regS TTBR1_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL2_ref v\<rbrakk>\<^sub>S = write_regS TTBR1_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL2_ref\<rbrakk>\<^sub>S = read_regS TTBR0_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL2_ref v\<rbrakk>\<^sub>S = write_regS TTBR0_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL1_ref\<rbrakk>\<^sub>S = read_regS TTBR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS TTBR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL1_ref\<rbrakk>\<^sub>S = read_regS TTBR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS TTBR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_InGuardedPage[liftState_simp]:
  "\<lbrakk>read_reg InGuardedPage_ref\<rbrakk>\<^sub>S = read_regS InGuardedPage_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_InGuardedPage[liftState_simp]:
  "\<lbrakk>write_reg InGuardedPage_ref v\<rbrakk>\<^sub>S = write_regS InGuardedPage_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GIC_Active[liftState_simp]:
  "\<lbrakk>read_reg GIC_Active_ref\<rbrakk>\<^sub>S = read_regS GIC_Active_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GIC_Active[liftState_simp]:
  "\<lbrakk>write_reg GIC_Active_ref v\<rbrakk>\<^sub>S = write_regS GIC_Active_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GICC_CTLR[liftState_simp]:
  "\<lbrakk>read_reg GICC_CTLR_ref\<rbrakk>\<^sub>S = read_regS GICC_CTLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GICC_CTLR[liftState_simp]:
  "\<lbrakk>write_reg GICC_CTLR_ref v\<rbrakk>\<^sub>S = write_regS GICC_CTLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GPTBR_EL3[liftState_simp]:
  "\<lbrakk>read_reg GPTBR_EL3_ref\<rbrakk>\<^sub>S = read_regS GPTBR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GPTBR_EL3[liftState_simp]:
  "\<lbrakk>write_reg GPTBR_EL3_ref v\<rbrakk>\<^sub>S = write_regS GPTBR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GPCCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg GPCCR_EL3_ref\<rbrakk>\<^sub>S = read_regS GPCCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GPCCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg GPCCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS GPCCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMSM_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAMSM_EL1_ref\<rbrakk>\<^sub>S = read_regS MPAMSM_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMSM_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAMSM_EL1_ref v\<rbrakk>\<^sub>S = write_regS MPAMSM_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM0_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAM0_EL1_ref\<rbrakk>\<^sub>S = read_regS MPAM0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM0_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAM0_EL1_ref v\<rbrakk>\<^sub>S = write_regS MPAM0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM7_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM7_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM7_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM7_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM7_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM7_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM6_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM6_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM6_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM6_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM6_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM6_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM5_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM5_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM5_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM5_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM5_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM5_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM4_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM4_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM4_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM4_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM4_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM4_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM3_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM3_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM3_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM3_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM3_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM3_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM2_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM2_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM2_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM2_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM2_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM2_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM1_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM1_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM1_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM1_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM1_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM1_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPMV_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPMV_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPMV_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPMV_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPMV_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPMV_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM0_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM0_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM0_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM0_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM0_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM0_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMHCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMHCR_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMHCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMHCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMHCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMHCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM1_EL1_0_62[liftState_simp]:
  "\<lbrakk>read_reg MPAM1_EL1_0_62_ref\<rbrakk>\<^sub>S = read_regS MPAM1_EL1_0_62_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM1_EL1_0_62[liftState_simp]:
  "\<lbrakk>write_reg MPAM1_EL1_0_62_ref v\<rbrakk>\<^sub>S = write_regS MPAM1_EL1_0_62_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAMIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS MPAMIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAMIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MPAMIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM2_EL2_0_62[liftState_simp]:
  "\<lbrakk>read_reg MPAM2_EL2_0_62_ref\<rbrakk>\<^sub>S = read_regS MPAM2_EL2_0_62_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM2_EL2_0_62[liftState_simp]:
  "\<lbrakk>write_reg MPAM2_EL2_0_62_ref v\<rbrakk>\<^sub>S = write_regS MPAM2_EL2_0_62_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM3_EL3[liftState_simp]:
  "\<lbrakk>read_reg MPAM3_EL3_ref\<rbrakk>\<^sub>S = read_regS MPAM3_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM3_EL3[liftState_simp]:
  "\<lbrakk>write_reg MPAM3_EL3_ref v\<rbrakk>\<^sub>S = write_regS MPAM3_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL3_ref\<rbrakk>\<^sub>S = read_regS MAIR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL3_ref v\<rbrakk>\<^sub>S = write_regS MAIR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL2_ref\<rbrakk>\<^sub>S = read_regS MAIR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL2_ref v\<rbrakk>\<^sub>S = write_regS MAIR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL1_ref\<rbrakk>\<^sub>S = read_regS MAIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MAIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SDER32_EL2[liftState_simp]:
  "\<lbrakk>read_reg SDER32_EL2_ref\<rbrakk>\<^sub>S = read_regS SDER32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SDER32_EL2[liftState_simp]:
  "\<lbrakk>write_reg SDER32_EL2_ref v\<rbrakk>\<^sub>S = write_regS SDER32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDWAR[liftState_simp]:
  "\<lbrakk>read_reg EDWAR_ref\<rbrakk>\<^sub>S = read_regS EDWAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDWAR[liftState_simp]:
  "\<lbrakk>write_reg EDWAR_ref v\<rbrakk>\<^sub>S = write_regS EDWAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWVR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGWVR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWVR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGWVR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWCR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGWCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGWCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSLSR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSLSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSLSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSLSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTTBR_EL2_ref\<rbrakk>\<^sub>S = read_regS VTTBR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTTBR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VTTBR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTCR_EL2_ref\<rbrakk>\<^sub>S = read_regS VTCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VTCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBVR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGBVR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBVR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGBVR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBCR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGBCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGBCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS CONTEXTIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS CONTEXTIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS CONTEXTIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CONTEXTIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TFSR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TFSR_EL3_ref\<rbrakk>\<^sub>S = read_regS TFSR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TFSR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TFSR_EL3_ref v\<rbrakk>\<^sub>S = write_regS TFSR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TFSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TFSR_EL2_ref\<rbrakk>\<^sub>S = read_regS TFSR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TFSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TFSR_EL2_ref v\<rbrakk>\<^sub>S = write_regS TFSR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TFSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TFSR_EL1_ref\<rbrakk>\<^sub>S = read_regS TFSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TFSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TFSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS TFSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TFSRE0_EL1[liftState_simp]:
  "\<lbrakk>read_reg TFSRE0_EL1_ref\<rbrakk>\<^sub>S = read_regS TFSRE0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TFSRE0_EL1[liftState_simp]:
  "\<lbrakk>write_reg TFSRE0_EL1_ref v\<rbrakk>\<^sub>S = write_regS TFSRE0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDSCRint_16_28[liftState_simp]:
  "\<lbrakk>read_reg DBGDSCRint_16_28_ref\<rbrakk>\<^sub>S = read_regS DBGDSCRint_16_28_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDSCRint_16_28[liftState_simp]:
  "\<lbrakk>write_reg DBGDSCRint_16_28_ref v\<rbrakk>\<^sub>S = write_regS DBGDSCRint_16_28_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDSCR_EL1_ref\<rbrakk>\<^sub>S = read_regS MDSCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDSCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MDSCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBCR_S[liftState_simp]:
  "\<lbrakk>read_reg TTBCR_S_ref\<rbrakk>\<^sub>S = read_regS TTBCR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBCR_S[liftState_simp]:
  "\<lbrakk>write_reg TTBCR_S_ref v\<rbrakk>\<^sub>S = write_regS TTBCR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_IFSR_S[liftState_simp]:
  "\<lbrakk>read_reg IFSR_S_ref\<rbrakk>\<^sub>S = read_regS IFSR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_IFSR_S[liftState_simp]:
  "\<lbrakk>write_reg IFSR_S_ref v\<rbrakk>\<^sub>S = write_regS IFSR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_IFSR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg IFSR32_EL2_ref\<rbrakk>\<^sub>S = read_regS IFSR32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_IFSR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg IFSR32_EL2_ref v\<rbrakk>\<^sub>S = write_regS IFSR32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DFSR_S[liftState_simp]:
  "\<lbrakk>read_reg DFSR_S_ref\<rbrakk>\<^sub>S = read_regS DFSR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DFSR_S[liftState_simp]:
  "\<lbrakk>write_reg DFSR_S_ref v\<rbrakk>\<^sub>S = write_regS DFSR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MVBAR[liftState_simp]:
  "\<lbrakk>read_reg MVBAR_ref\<rbrakk>\<^sub>S = read_regS MVBAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MVBAR[liftState_simp]:
  "\<lbrakk>write_reg MVBAR_ref v\<rbrakk>\<^sub>S = write_regS MVBAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS ACTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ACTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HFGRTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HFGRTR_EL2_ref\<rbrakk>\<^sub>S = read_regS HFGRTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HFGRTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HFGRTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HFGRTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACCDATA_EL1[liftState_simp]:
  "\<lbrakk>read_reg ACCDATA_EL1_ref\<rbrakk>\<^sub>S = read_regS ACCDATA_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACCDATA_EL1[liftState_simp]:
  "\<lbrakk>write_reg ACCDATA_EL1_ref v\<rbrakk>\<^sub>S = write_regS ACCDATA_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VBAR_S[liftState_simp]:
  "\<lbrakk>read_reg VBAR_S_ref\<rbrakk>\<^sub>S = read_regS VBAR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VBAR_S[liftState_simp]:
  "\<lbrakk>write_reg VBAR_S_ref v\<rbrakk>\<^sub>S = write_regS VBAR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL3_ref\<rbrakk>\<^sub>S = read_regS VBAR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL3_ref v\<rbrakk>\<^sub>S = write_regS VBAR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL2_ref\<rbrakk>\<^sub>S = read_regS VBAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VBAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL1_ref\<rbrakk>\<^sub>S = read_regS VBAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS VBAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>read_reg SPSR_und_ref\<rbrakk>\<^sub>S = read_regS SPSR_und_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>write_reg SPSR_und_ref v\<rbrakk>\<^sub>S = write_regS SPSR_und_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_mon[liftState_simp]:
  "\<lbrakk>read_reg SPSR_mon_ref\<rbrakk>\<^sub>S = read_regS SPSR_mon_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_mon[liftState_simp]:
  "\<lbrakk>write_reg SPSR_mon_ref v\<rbrakk>\<^sub>S = write_regS SPSR_mon_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_irq_ref\<rbrakk>\<^sub>S = read_regS SPSR_irq_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_irq_ref v\<rbrakk>\<^sub>S = write_regS SPSR_irq_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_fiq_ref\<rbrakk>\<^sub>S = read_regS SPSR_fiq_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_fiq_ref v\<rbrakk>\<^sub>S = write_regS SPSR_fiq_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>read_reg SPSR_abt_ref\<rbrakk>\<^sub>S = read_regS SPSR_abt_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>write_reg SPSR_abt_ref v\<rbrakk>\<^sub>S = write_regS SPSR_abt_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL3_ref\<rbrakk>\<^sub>S = read_regS SPSR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL3_ref v\<rbrakk>\<^sub>S = write_regS SPSR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL2_ref\<rbrakk>\<^sub>S = read_regS SPSR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL2_ref v\<rbrakk>\<^sub>S = write_regS SPSR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL1_ref\<rbrakk>\<^sub>S = read_regS SPSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS SPSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCTLR_S[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_S_ref\<rbrakk>\<^sub>S = read_regS SCTLR_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCTLR_S[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_S_ref v\<rbrakk>\<^sub>S = write_regS SCTLR_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL3_ref\<rbrakk>\<^sub>S = read_regS SCTLR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL3_ref v\<rbrakk>\<^sub>S = write_regS SCTLR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL2_ref\<rbrakk>\<^sub>S = read_regS SCTLR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL2_ref v\<rbrakk>\<^sub>S = write_regS SCTLR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS SCTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS SCTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ZA[liftState_simp]:
  "\<lbrakk>read_reg ZA_ref\<rbrakk>\<^sub>S = read_regS ZA_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ZA[liftState_simp]:
  "\<lbrakk>write_reg ZA_ref v\<rbrakk>\<^sub>S = write_regS ZA_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_Z[liftState_simp]:
  "\<lbrakk>read_reg Z_ref\<rbrakk>\<^sub>S = read_regS Z_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_Z[liftState_simp]:
  "\<lbrakk>write_reg Z_ref v\<rbrakk>\<^sub>S = write_regS Z_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>read_reg SP_EL3_ref\<rbrakk>\<^sub>S = read_regS SP_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>write_reg SP_EL3_ref v\<rbrakk>\<^sub>S = write_regS SP_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>read_reg SP_EL2_ref\<rbrakk>\<^sub>S = read_regS SP_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>write_reg SP_EL2_ref v\<rbrakk>\<^sub>S = write_regS SP_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>read_reg SP_EL1_ref\<rbrakk>\<^sub>S = read_regS SP_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>write_reg SP_EL1_ref v\<rbrakk>\<^sub>S = write_regS SP_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>read_reg SP_EL0_ref\<rbrakk>\<^sub>S = read_regS SP_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>write_reg SP_EL0_ref v\<rbrakk>\<^sub>S = write_regS SP_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_P[liftState_simp]:
  "\<lbrakk>read_reg P_ref\<rbrakk>\<^sub>S = read_regS P_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_P[liftState_simp]:
  "\<lbrakk>write_reg P_ref v\<rbrakk>\<^sub>S = write_regS P_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_NSACR[liftState_simp]:
  "\<lbrakk>read_reg NSACR_ref\<rbrakk>\<^sub>S = read_regS NSACR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_NSACR[liftState_simp]:
  "\<lbrakk>write_reg NSACR_ref v\<rbrakk>\<^sub>S = write_regS NSACR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL3_ref\<rbrakk>\<^sub>S = read_regS CPTR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL3_ref v\<rbrakk>\<^sub>S = write_regS CPTR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL2_ref\<rbrakk>\<^sub>S = read_regS CPTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS CPTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CPACR_EL1_ref\<rbrakk>\<^sub>S = read_regS CPACR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CPACR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CPACR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FFR[liftState_simp]:
  "\<lbrakk>read_reg FFR_ref\<rbrakk>\<^sub>S = read_regS FFR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FFR[liftState_simp]:
  "\<lbrakk>write_reg FFR_ref v\<rbrakk>\<^sub>S = write_regS FFR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SMCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SMCR_EL3_ref\<rbrakk>\<^sub>S = read_regS SMCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SMCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SMCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS SMCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SMCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SMCR_EL2_ref\<rbrakk>\<^sub>S = read_regS SMCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SMCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SMCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS SMCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SMCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SMCR_EL1_ref\<rbrakk>\<^sub>S = read_regS SMCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SMCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SMCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS SMCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_max_implemented_smeveclen[liftState_simp]:
  "\<lbrakk>read_reg max_implemented_smeveclen_ref\<rbrakk>\<^sub>S = read_regS max_implemented_smeveclen_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_max_implemented_smeveclen[liftState_simp]:
  "\<lbrakk>write_reg max_implemented_smeveclen_ref v\<rbrakk>\<^sub>S = write_regS max_implemented_smeveclen_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ZCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ZCR_EL3_ref\<rbrakk>\<^sub>S = read_regS ZCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ZCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ZCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ZCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ZCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ZCR_EL2_ref\<rbrakk>\<^sub>S = read_regS ZCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ZCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ZCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ZCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ZCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ZCR_EL1_ref\<rbrakk>\<^sub>S = read_regS ZCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ZCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ZCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ZCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL3_ref\<rbrakk>\<^sub>S = read_regS ELR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ELR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL2_ref\<rbrakk>\<^sub>S = read_regS ELR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ELR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL1_ref\<rbrakk>\<^sub>S = read_regS ELR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ELR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RTPIDEN[liftState_simp]:
  "\<lbrakk>read_reg RTPIDEN_ref\<rbrakk>\<^sub>S = read_regS RTPIDEN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RTPIDEN[liftState_simp]:
  "\<lbrakk>write_reg RTPIDEN_ref v\<rbrakk>\<^sub>S = write_regS RTPIDEN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RLPIDEN[liftState_simp]:
  "\<lbrakk>read_reg RLPIDEN_ref\<rbrakk>\<^sub>S = read_regS RLPIDEN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RLPIDEN[liftState_simp]:
  "\<lbrakk>write_reg RLPIDEN_ref v\<rbrakk>\<^sub>S = write_regS RLPIDEN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGPRCR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGPRCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGPRCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGPRCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDLR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSDLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSDLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>read_reg SPIDEN_ref\<rbrakk>\<^sub>S = read_regS SPIDEN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>write_reg SPIDEN_ref v\<rbrakk>\<^sub>S = write_regS SPIDEN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGEN[liftState_simp]:
  "\<lbrakk>read_reg DBGEN_ref\<rbrakk>\<^sub>S = read_regS DBGEN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGEN[liftState_simp]:
  "\<lbrakk>write_reg DBGEN_ref v\<rbrakk>\<^sub>S = write_regS DBGEN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDSCR_31_31[liftState_simp]:
  "\<lbrakk>read_reg EDSCR_31_31_ref\<rbrakk>\<^sub>S = read_regS EDSCR_31_31_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDSCR_31_31[liftState_simp]:
  "\<lbrakk>write_reg EDSCR_31_31_ref v\<rbrakk>\<^sub>S = write_regS EDSCR_31_31_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDSCR_0_28[liftState_simp]:
  "\<lbrakk>read_reg EDSCR_0_28_ref\<rbrakk>\<^sub>S = read_regS EDSCR_0_28_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDSCR_0_28[liftState_simp]:
  "\<lbrakk>write_reg EDSCR_0_28_ref v\<rbrakk>\<^sub>S = write_regS EDSCR_0_28_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCCSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg MDCCSR_EL0_ref\<rbrakk>\<^sub>S = read_regS MDCCSR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCCSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg MDCCSR_EL0_ref v\<rbrakk>\<^sub>S = write_regS MDCCSR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DSPSR_EL0_ref\<rbrakk>\<^sub>S = read_regS DSPSR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DSPSR_EL0_ref v\<rbrakk>\<^sub>S = write_regS DSPSR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DLR_EL0_ref\<rbrakk>\<^sub>S = read_regS DLR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DLR_EL0_ref v\<rbrakk>\<^sub>S = write_regS DLR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSECCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSECCR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSECCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSECCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSECCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSECCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BranchTaken[liftState_simp]:
  "\<lbrakk>read_reg BranchTaken_ref\<rbrakk>\<^sub>S = read_regS BranchTaken_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BranchTaken[liftState_simp]:
  "\<lbrakk>write_reg BranchTaken_ref v\<rbrakk>\<^sub>S = write_regS BranchTaken_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PC[liftState_simp]:
  "\<lbrakk>read_reg PC_ref\<rbrakk>\<^sub>S = read_regS PC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PC[liftState_simp]:
  "\<lbrakk>write_reg PC_ref v\<rbrakk>\<^sub>S = write_regS PC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_mon[liftState_simp]:
  "\<lbrakk>read_reg SP_mon_ref\<rbrakk>\<^sub>S = read_regS SP_mon_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_mon[liftState_simp]:
  "\<lbrakk>write_reg SP_mon_ref v\<rbrakk>\<^sub>S = write_regS SP_mon_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LR_mon[liftState_simp]:
  "\<lbrakk>read_reg LR_mon_ref\<rbrakk>\<^sub>S = read_regS LR_mon_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LR_mon[liftState_simp]:
  "\<lbrakk>write_reg LR_mon_ref v\<rbrakk>\<^sub>S = write_regS LR_mon_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL3_ref\<rbrakk>\<^sub>S = read_regS TCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS TCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL2_ref\<rbrakk>\<^sub>S = read_regS TCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS TCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL1_ref\<rbrakk>\<^sub>S = read_regS TCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS TCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_Records_TGT[liftState_simp]:
  "\<lbrakk>read_reg Records_TGT_ref\<rbrakk>\<^sub>S = read_regS Records_TGT_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_Records_TGT[liftState_simp]:
  "\<lbrakk>write_reg Records_TGT_ref v\<rbrakk>\<^sub>S = write_regS Records_TGT_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_Records_SRC[liftState_simp]:
  "\<lbrakk>read_reg Records_SRC_ref\<rbrakk>\<^sub>S = read_regS Records_SRC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_Records_SRC[liftState_simp]:
  "\<lbrakk>write_reg Records_SRC_ref v\<rbrakk>\<^sub>S = write_regS Records_SRC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_Records_INF[liftState_simp]:
  "\<lbrakk>read_reg Records_INF_ref\<rbrakk>\<^sub>S = read_regS Records_INF_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_Records_INF[liftState_simp]:
  "\<lbrakk>write_reg Records_INF_ref v\<rbrakk>\<^sub>S = write_regS Records_INF_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBIDR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBIDR0_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBIDR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBIDR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBIDR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBIDR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TSTATE[liftState_simp]:
  "\<lbrakk>read_reg TSTATE_ref\<rbrakk>\<^sub>S = read_regS TSTATE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TSTATE[liftState_simp]:
  "\<lbrakk>write_reg TSTATE_ref v\<rbrakk>\<^sub>S = write_regS TSTATE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_PMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_PMR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_PMR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_PMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_PMR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_PMR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMUEventAccumulator[liftState_simp]:
  "\<lbrakk>read_reg PMUEventAccumulator_ref\<rbrakk>\<^sub>S = read_regS PMUEventAccumulator_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMUEventAccumulator[liftState_simp]:
  "\<lbrakk>write_reg PMUEventAccumulator_ref v\<rbrakk>\<^sub>S = write_regS PMUEventAccumulator_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMEVTYPER_EL0_ref\<rbrakk>\<^sub>S = read_regS PMEVTYPER_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMEVTYPER_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMEVTYPER_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL2_ref\<rbrakk>\<^sub>S = read_regS MDCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS MDCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL3_ref\<rbrakk>\<^sub>S = read_regS MDCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS MDCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_last_branch_valid[liftState_simp]:
  "\<lbrakk>read_reg last_branch_valid_ref\<rbrakk>\<^sub>S = read_regS last_branch_valid_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_last_branch_valid[liftState_simp]:
  "\<lbrakk>write_reg last_branch_valid_ref v\<rbrakk>\<^sub>S = write_regS last_branch_valid_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_last_cycle_count[liftState_simp]:
  "\<lbrakk>read_reg last_cycle_count_ref\<rbrakk>\<^sub>S = read_regS last_cycle_count_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_last_cycle_count[liftState_simp]:
  "\<lbrakk>write_reg last_cycle_count_ref v\<rbrakk>\<^sub>S = write_regS last_cycle_count_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBFCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBFCR_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBFCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBFCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBFCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBFCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg BRBCR_EL2_ref\<rbrakk>\<^sub>S = read_regS BRBCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg BRBCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS BRBCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BRBCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg BRBCR_EL1_ref\<rbrakk>\<^sub>S = read_regS BRBCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BRBCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg BRBCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS BRBCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MFAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MFAR_EL3_ref\<rbrakk>\<^sub>S = read_regS MFAR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MFAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MFAR_EL3_ref v\<rbrakk>\<^sub>S = write_regS MFAR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HPFAR_EL2_ref\<rbrakk>\<^sub>S = read_regS HPFAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HPFAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HPFAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL3_ref\<rbrakk>\<^sub>S = read_regS FAR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL3_ref v\<rbrakk>\<^sub>S = write_regS FAR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL2_ref\<rbrakk>\<^sub>S = read_regS FAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS FAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL1_ref\<rbrakk>\<^sub>S = read_regS FAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS FAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL3_ref\<rbrakk>\<^sub>S = read_regS ESR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ESR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL2_ref\<rbrakk>\<^sub>S = read_regS ESR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ESR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL1_ref\<rbrakk>\<^sub>S = read_regS ESR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ESR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ThisInstrEnc[liftState_simp]:
  "\<lbrakk>read_reg ThisInstrEnc_ref\<rbrakk>\<^sub>S = read_regS ThisInstrEnc_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ThisInstrEnc[liftState_simp]:
  "\<lbrakk>write_reg ThisInstrEnc_ref v\<rbrakk>\<^sub>S = write_regS ThisInstrEnc_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R[liftState_simp]:
  "\<lbrakk>read_reg R_ref\<rbrakk>\<^sub>S = read_regS R_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R[liftState_simp]:
  "\<lbrakk>write_reg R_ref v\<rbrakk>\<^sub>S = write_regS R_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ThisInstr[liftState_simp]:
  "\<lbrakk>read_reg ThisInstr_ref\<rbrakk>\<^sub>S = read_regS ThisInstr_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ThisInstr[liftState_simp]:
  "\<lbrakk>write_reg ThisInstr_ref v\<rbrakk>\<^sub>S = write_regS ThisInstr_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_unpred_tsize_aborts[liftState_simp]:
  "\<lbrakk>read_reg unpred_tsize_aborts_ref\<rbrakk>\<^sub>S = read_regS unpred_tsize_aborts_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_unpred_tsize_aborts[liftState_simp]:
  "\<lbrakk>write_reg unpred_tsize_aborts_ref v\<rbrakk>\<^sub>S = write_regS unpred_tsize_aborts_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICACHE_CCSIDR_RESET[liftState_simp]:
  "\<lbrakk>read_reg ICACHE_CCSIDR_RESET_ref\<rbrakk>\<^sub>S = read_regS ICACHE_CCSIDR_RESET_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICACHE_CCSIDR_RESET[liftState_simp]:
  "\<lbrakk>write_reg ICACHE_CCSIDR_RESET_ref v\<rbrakk>\<^sub>S = write_regS ICACHE_CCSIDR_RESET_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DCACHE_CCSIDR_RESET[liftState_simp]:
  "\<lbrakk>read_reg DCACHE_CCSIDR_RESET_ref\<rbrakk>\<^sub>S = read_regS DCACHE_CCSIDR_RESET_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DCACHE_CCSIDR_RESET[liftState_simp]:
  "\<lbrakk>write_reg DCACHE_CCSIDR_RESET_ref v\<rbrakk>\<^sub>S = write_regS DCACHE_CCSIDR_RESET_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CLIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CLIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS CLIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CLIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CLIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CLIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_cycle_count[liftState_simp]:
  "\<lbrakk>read_reg cycle_count_ref\<rbrakk>\<^sub>S = read_regS cycle_count_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_cycle_count[liftState_simp]:
  "\<lbrakk>write_reg cycle_count_ref v\<rbrakk>\<^sub>S = write_regS cycle_count_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GIC_Pending[liftState_simp]:
  "\<lbrakk>read_reg GIC_Pending_ref\<rbrakk>\<^sub>S = read_regS GIC_Pending_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GIC_Pending[liftState_simp]:
  "\<lbrakk>write_reg GIC_Pending_ref v\<rbrakk>\<^sub>S = write_regS GIC_Pending_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HCRX_EL2[liftState_simp]:
  "\<lbrakk>read_reg HCRX_EL2_ref\<rbrakk>\<^sub>S = read_regS HCRX_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HCRX_EL2[liftState_simp]:
  "\<lbrakk>write_reg HCRX_EL2_ref v\<rbrakk>\<^sub>S = write_regS HCRX_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCR[liftState_simp]:
  "\<lbrakk>read_reg SCR_ref\<rbrakk>\<^sub>S = read_regS SCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCR[liftState_simp]:
  "\<lbrakk>write_reg SCR_ref v\<rbrakk>\<^sub>S = write_regS SCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCR_EL3_ref\<rbrakk>\<^sub>S = read_regS SCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS SCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HCR_EL2_ref\<rbrakk>\<^sub>S = read_regS HCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_trcclaim_tags[liftState_simp]:
  "\<lbrakk>read_reg trcclaim_tags_ref\<rbrakk>\<^sub>S = read_regS trcclaim_tags_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_trcclaim_tags[liftState_simp]:
  "\<lbrakk>write_reg trcclaim_tags_ref v\<rbrakk>\<^sub>S = write_regS trcclaim_tags_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_claim_tags[liftState_simp]:
  "\<lbrakk>read_reg claim_tags_ref\<rbrakk>\<^sub>S = read_regS claim_tags_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_claim_tags[liftState_simp]:
  "\<lbrakk>write_reg claim_tags_ref v\<rbrakk>\<^sub>S = write_regS claim_tags_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERRnFR[liftState_simp]:
  "\<lbrakk>read_reg ERRnFR_ref\<rbrakk>\<^sub>S = read_regS ERRnFR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERRnFR[liftState_simp]:
  "\<lbrakk>write_reg ERRnFR_ref v\<rbrakk>\<^sub>S = write_regS ERRnFR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RVBAR[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_ref\<rbrakk>\<^sub>S = read_regS RVBAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RVBAR[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_ref v\<rbrakk>\<^sub>S = write_regS RVBAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FPSR[liftState_simp]:
  "\<lbrakk>read_reg FPSR_ref\<rbrakk>\<^sub>S = read_regS FPSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FPSR[liftState_simp]:
  "\<lbrakk>write_reg FPSR_ref v\<rbrakk>\<^sub>S = write_regS FPSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FPCR[liftState_simp]:
  "\<lbrakk>read_reg FPCR_ref\<rbrakk>\<^sub>S = read_regS FPCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FPCR[liftState_simp]:
  "\<lbrakk>write_reg FPCR_ref v\<rbrakk>\<^sub>S = write_regS FPCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mpam_vpmr_max[liftState_simp]:
  "\<lbrakk>read_reg mpam_vpmr_max_ref\<rbrakk>\<^sub>S = read_regS mpam_vpmr_max_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mpam_vpmr_max[liftState_simp]:
  "\<lbrakk>write_reg mpam_vpmr_max_ref v\<rbrakk>\<^sub>S = write_regS mpam_vpmr_max_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mpam_pmg_max[liftState_simp]:
  "\<lbrakk>read_reg mpam_pmg_max_ref\<rbrakk>\<^sub>S = read_regS mpam_pmg_max_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mpam_pmg_max[liftState_simp]:
  "\<lbrakk>write_reg mpam_pmg_max_ref v\<rbrakk>\<^sub>S = write_regS mpam_pmg_max_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mpam_partid_max[liftState_simp]:
  "\<lbrakk>read_reg mpam_partid_max_ref\<rbrakk>\<^sub>S = read_regS mpam_partid_max_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mpam_partid_max[liftState_simp]:
  "\<lbrakk>write_reg mpam_partid_max_ref v\<rbrakk>\<^sub>S = write_regS mpam_partid_max_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mpam_has_hcr[liftState_simp]:
  "\<lbrakk>read_reg mpam_has_hcr_ref\<rbrakk>\<^sub>S = read_regS mpam_has_hcr_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mpam_has_hcr[liftState_simp]:
  "\<lbrakk>write_reg mpam_has_hcr_ref v\<rbrakk>\<^sub>S = write_regS mpam_has_hcr_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_impdef_res_TG1[liftState_simp]:
  "\<lbrakk>read_reg impdef_res_TG1_ref\<rbrakk>\<^sub>S = read_regS impdef_res_TG1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_impdef_res_TG1[liftState_simp]:
  "\<lbrakk>write_reg impdef_res_TG1_ref v\<rbrakk>\<^sub>S = write_regS impdef_res_TG1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_impdef_res_TG0[liftState_simp]:
  "\<lbrakk>read_reg impdef_res_TG0_ref\<rbrakk>\<^sub>S = read_regS impdef_res_TG0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_impdef_res_TG0[liftState_simp]:
  "\<lbrakk>write_reg impdef_res_TG0_ref v\<rbrakk>\<^sub>S = write_regS impdef_res_TG0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PhysicalCount[liftState_simp]:
  "\<lbrakk>read_reg PhysicalCount_ref\<rbrakk>\<^sub>S = read_regS PhysicalCount_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PhysicalCount[liftState_simp]:
  "\<lbrakk>write_reg PhysicalCount_ref v\<rbrakk>\<^sub>S = write_regS PhysicalCount_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CFG_RVBAR[liftState_simp]:
  "\<lbrakk>read_reg CFG_RVBAR_ref\<rbrakk>\<^sub>S = read_regS CFG_RVBAR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CFG_RVBAR[liftState_simp]:
  "\<lbrakk>write_reg CFG_RVBAR_ref v\<rbrakk>\<^sub>S = write_regS CFG_RVBAR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_supported_va_size[liftState_simp]:
  "\<lbrakk>read_reg supported_va_size_ref\<rbrakk>\<^sub>S = read_regS supported_va_size_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_supported_va_size[liftState_simp]:
  "\<lbrakk>write_reg supported_va_size_ref v\<rbrakk>\<^sub>S = write_regS supported_va_size_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_supported_pa_size[liftState_simp]:
  "\<lbrakk>read_reg supported_pa_size_ref\<rbrakk>\<^sub>S = read_regS supported_pa_size_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_supported_pa_size[liftState_simp]:
  "\<lbrakk>write_reg supported_pa_size_ref v\<rbrakk>\<^sub>S = write_regS supported_pa_size_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_num_watchpoints[liftState_simp]:
  "\<lbrakk>read_reg num_watchpoints_ref\<rbrakk>\<^sub>S = read_regS num_watchpoints_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_num_watchpoints[liftState_simp]:
  "\<lbrakk>write_reg num_watchpoints_ref v\<rbrakk>\<^sub>S = write_regS num_watchpoints_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_num_event_counters[liftState_simp]:
  "\<lbrakk>read_reg num_event_counters_ref\<rbrakk>\<^sub>S = read_regS num_event_counters_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_num_event_counters[liftState_simp]:
  "\<lbrakk>write_reg num_event_counters_ref v\<rbrakk>\<^sub>S = write_regS num_event_counters_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_num_ctx_breakpoints[liftState_simp]:
  "\<lbrakk>read_reg num_ctx_breakpoints_ref\<rbrakk>\<^sub>S = read_regS num_ctx_breakpoints_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_num_ctx_breakpoints[liftState_simp]:
  "\<lbrakk>write_reg num_ctx_breakpoints_ref v\<rbrakk>\<^sub>S = write_regS num_ctx_breakpoints_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_num_breakpoints[liftState_simp]:
  "\<lbrakk>read_reg num_breakpoints_ref\<rbrakk>\<^sub>S = read_regS num_breakpoints_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_num_breakpoints[liftState_simp]:
  "\<lbrakk>write_reg num_breakpoints_ref v\<rbrakk>\<^sub>S = write_regS num_breakpoints_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_num_brb_records[liftState_simp]:
  "\<lbrakk>read_reg num_brb_records_ref\<rbrakk>\<^sub>S = read_regS num_brb_records_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_num_brb_records[liftState_simp]:
  "\<lbrakk>write_reg num_brb_records_ref v\<rbrakk>\<^sub>S = write_regS num_brb_records_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_has_sve_extended_bf16[liftState_simp]:
  "\<lbrakk>read_reg has_sve_extended_bf16_ref\<rbrakk>\<^sub>S = read_regS has_sve_extended_bf16_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_has_sve_extended_bf16[liftState_simp]:
  "\<lbrakk>write_reg has_sve_extended_bf16_ref v\<rbrakk>\<^sub>S = write_regS has_sve_extended_bf16_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_block_bbm_implemented[liftState_simp]:
  "\<lbrakk>read_reg block_bbm_implemented_ref\<rbrakk>\<^sub>S = read_regS block_bbm_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_block_bbm_implemented[liftState_simp]:
  "\<lbrakk>write_reg block_bbm_implemented_ref v\<rbrakk>\<^sub>S = write_regS block_bbm_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg CTR_EL0_ref\<rbrakk>\<^sub>S = read_regS CTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg CTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS CTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_vmid16_implemented[liftState_simp]:
  "\<lbrakk>read_reg vmid16_implemented_ref\<rbrakk>\<^sub>S = read_regS vmid16_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_vmid16_implemented[liftState_simp]:
  "\<lbrakk>write_reg vmid16_implemented_ref v\<rbrakk>\<^sub>S = write_regS vmid16_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_sme_only[liftState_simp]:
  "\<lbrakk>read_reg sme_only_ref\<rbrakk>\<^sub>S = read_regS sme_only_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_sme_only[liftState_simp]:
  "\<lbrakk>write_reg sme_only_ref v\<rbrakk>\<^sub>S = write_regS sme_only_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_rme_implemented[liftState_simp]:
  "\<lbrakk>read_reg rme_implemented_ref\<rbrakk>\<^sub>S = read_regS rme_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_rme_implemented[liftState_simp]:
  "\<lbrakk>write_reg rme_implemented_ref v\<rbrakk>\<^sub>S = write_regS rme_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_pacqarma5_implemented[liftState_simp]:
  "\<lbrakk>read_reg pacqarma5_implemented_ref\<rbrakk>\<^sub>S = read_regS pacqarma5_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_pacqarma5_implemented[liftState_simp]:
  "\<lbrakk>write_reg pacqarma5_implemented_ref v\<rbrakk>\<^sub>S = write_regS pacqarma5_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_pacqarma3_implemented[liftState_simp]:
  "\<lbrakk>read_reg pacqarma3_implemented_ref\<rbrakk>\<^sub>S = read_regS pacqarma3_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_pacqarma3_implemented[liftState_simp]:
  "\<lbrakk>write_reg pacqarma3_implemented_ref v\<rbrakk>\<^sub>S = write_regS pacqarma3_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_pac_frac_implemented[liftState_simp]:
  "\<lbrakk>read_reg pac_frac_implemented_ref\<rbrakk>\<^sub>S = read_regS pac_frac_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_pac_frac_implemented[liftState_simp]:
  "\<lbrakk>write_reg pac_frac_implemented_ref v\<rbrakk>\<^sub>S = write_regS pac_frac_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mte_implemented[liftState_simp]:
  "\<lbrakk>read_reg mte_implemented_ref\<rbrakk>\<^sub>S = read_regS mte_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mte_implemented[liftState_simp]:
  "\<lbrakk>write_reg mte_implemented_ref v\<rbrakk>\<^sub>S = write_regS mte_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mpam_implemented[liftState_simp]:
  "\<lbrakk>read_reg mpam_implemented_ref\<rbrakk>\<^sub>S = read_regS mpam_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mpam_implemented[liftState_simp]:
  "\<lbrakk>write_reg mpam_implemented_ref v\<rbrakk>\<^sub>S = write_regS mpam_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_mops_option_a_supported[liftState_simp]:
  "\<lbrakk>read_reg mops_option_a_supported_ref\<rbrakk>\<^sub>S = read_regS mops_option_a_supported_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_mops_option_a_supported[liftState_simp]:
  "\<lbrakk>write_reg mops_option_a_supported_ref v\<rbrakk>\<^sub>S = write_regS mops_option_a_supported_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_isb_is_branch[liftState_simp]:
  "\<lbrakk>read_reg isb_is_branch_ref\<rbrakk>\<^sub>S = read_regS isb_is_branch_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_isb_is_branch[liftState_simp]:
  "\<lbrakk>write_reg isb_is_branch_ref v\<rbrakk>\<^sub>S = write_regS isb_is_branch_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_highest_el_aarch32[liftState_simp]:
  "\<lbrakk>read_reg highest_el_aarch32_ref\<rbrakk>\<^sub>S = read_regS highest_el_aarch32_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_highest_el_aarch32[liftState_simp]:
  "\<lbrakk>write_reg highest_el_aarch32_ref v\<rbrakk>\<^sub>S = write_regS highest_el_aarch32_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_has_sme_priority_control[liftState_simp]:
  "\<lbrakk>read_reg has_sme_priority_control_ref\<rbrakk>\<^sub>S = read_regS has_sme_priority_control_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_has_sme_priority_control[liftState_simp]:
  "\<lbrakk>write_reg has_sme_priority_control_ref v\<rbrakk>\<^sub>S = write_regS has_sme_priority_control_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_has_sme_i16i64[liftState_simp]:
  "\<lbrakk>read_reg has_sme_i16i64_ref\<rbrakk>\<^sub>S = read_regS has_sme_i16i64_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_has_sme_i16i64[liftState_simp]:
  "\<lbrakk>write_reg has_sme_i16i64_ref v\<rbrakk>\<^sub>S = write_regS has_sme_i16i64_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_has_sme_f64f64[liftState_simp]:
  "\<lbrakk>read_reg has_sme_f64f64_ref\<rbrakk>\<^sub>S = read_regS has_sme_f64f64_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_has_sme_f64f64[liftState_simp]:
  "\<lbrakk>write_reg has_sme_f64f64_ref v\<rbrakk>\<^sub>S = write_regS has_sme_f64f64_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_has_sme[liftState_simp]:
  "\<lbrakk>read_reg has_sme_ref\<rbrakk>\<^sub>S = read_regS has_sme_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_has_sme[liftState_simp]:
  "\<lbrakk>write_reg has_sme_ref v\<rbrakk>\<^sub>S = write_regS has_sme_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_feat_ls64_v[liftState_simp]:
  "\<lbrakk>read_reg feat_ls64_v_ref\<rbrakk>\<^sub>S = read_regS feat_ls64_v_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_feat_ls64_v[liftState_simp]:
  "\<lbrakk>write_reg feat_ls64_v_ref v\<rbrakk>\<^sub>S = write_regS feat_ls64_v_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_feat_ls64_accdata[liftState_simp]:
  "\<lbrakk>read_reg feat_ls64_accdata_ref\<rbrakk>\<^sub>S = read_regS feat_ls64_accdata_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_feat_ls64_accdata[liftState_simp]:
  "\<lbrakk>write_reg feat_ls64_accdata_ref v\<rbrakk>\<^sub>S = write_regS feat_ls64_accdata_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_feat_ls64[liftState_simp]:
  "\<lbrakk>read_reg feat_ls64_ref\<rbrakk>\<^sub>S = read_regS feat_ls64_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_feat_ls64[liftState_simp]:
  "\<lbrakk>write_reg feat_ls64_ref v\<rbrakk>\<^sub>S = write_regS feat_ls64_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_empam_tidr_implemented[liftState_simp]:
  "\<lbrakk>read_reg empam_tidr_implemented_ref\<rbrakk>\<^sub>S = read_regS empam_tidr_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_empam_tidr_implemented[liftState_simp]:
  "\<lbrakk>write_reg empam_tidr_implemented_ref v\<rbrakk>\<^sub>S = write_regS empam_tidr_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_empam_sdeflt_implemented[liftState_simp]:
  "\<lbrakk>read_reg empam_sdeflt_implemented_ref\<rbrakk>\<^sub>S = read_regS empam_sdeflt_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_empam_sdeflt_implemented[liftState_simp]:
  "\<lbrakk>write_reg empam_sdeflt_implemented_ref v\<rbrakk>\<^sub>S = write_regS empam_sdeflt_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_empam_implemented[liftState_simp]:
  "\<lbrakk>read_reg empam_implemented_ref\<rbrakk>\<^sub>S = read_regS empam_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_empam_implemented[liftState_simp]:
  "\<lbrakk>write_reg empam_implemented_ref v\<rbrakk>\<^sub>S = write_regS empam_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_empam_force_ns_implemented[liftState_simp]:
  "\<lbrakk>read_reg empam_force_ns_implemented_ref\<rbrakk>\<^sub>S = read_regS empam_force_ns_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_empam_force_ns_implemented[liftState_simp]:
  "\<lbrakk>write_reg empam_force_ns_implemented_ref v\<rbrakk>\<^sub>S = write_regS empam_force_ns_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_empam_force_ns_RAO[liftState_simp]:
  "\<lbrakk>read_reg empam_force_ns_RAO_ref\<rbrakk>\<^sub>S = read_regS empam_force_ns_RAO_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_empam_force_ns_RAO[liftState_simp]:
  "\<lbrakk>write_reg empam_force_ns_RAO_ref v\<rbrakk>\<^sub>S = write_regS empam_force_ns_RAO_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crypto_sm4_implemented[liftState_simp]:
  "\<lbrakk>read_reg crypto_sm4_implemented_ref\<rbrakk>\<^sub>S = read_regS crypto_sm4_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crypto_sm4_implemented[liftState_simp]:
  "\<lbrakk>write_reg crypto_sm4_implemented_ref v\<rbrakk>\<^sub>S = write_regS crypto_sm4_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crypto_sm3_implemented[liftState_simp]:
  "\<lbrakk>read_reg crypto_sm3_implemented_ref\<rbrakk>\<^sub>S = read_regS crypto_sm3_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crypto_sm3_implemented[liftState_simp]:
  "\<lbrakk>write_reg crypto_sm3_implemented_ref v\<rbrakk>\<^sub>S = write_regS crypto_sm3_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crypto_sha512_implemented[liftState_simp]:
  "\<lbrakk>read_reg crypto_sha512_implemented_ref\<rbrakk>\<^sub>S = read_regS crypto_sha512_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crypto_sha512_implemented[liftState_simp]:
  "\<lbrakk>write_reg crypto_sha512_implemented_ref v\<rbrakk>\<^sub>S = write_regS crypto_sha512_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crypto_sha3_implemented[liftState_simp]:
  "\<lbrakk>read_reg crypto_sha3_implemented_ref\<rbrakk>\<^sub>S = read_regS crypto_sha3_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crypto_sha3_implemented[liftState_simp]:
  "\<lbrakk>write_reg crypto_sha3_implemented_ref v\<rbrakk>\<^sub>S = write_regS crypto_sha3_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crypto_sha256_implemented[liftState_simp]:
  "\<lbrakk>read_reg crypto_sha256_implemented_ref\<rbrakk>\<^sub>S = read_regS crypto_sha256_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crypto_sha256_implemented[liftState_simp]:
  "\<lbrakk>write_reg crypto_sha256_implemented_ref v\<rbrakk>\<^sub>S = write_regS crypto_sha256_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crypto_sha1_implemented[liftState_simp]:
  "\<lbrakk>read_reg crypto_sha1_implemented_ref\<rbrakk>\<^sub>S = read_regS crypto_sha1_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crypto_sha1_implemented[liftState_simp]:
  "\<lbrakk>write_reg crypto_sha1_implemented_ref v\<rbrakk>\<^sub>S = write_regS crypto_sha1_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_crypto_aes_implemented[liftState_simp]:
  "\<lbrakk>read_reg crypto_aes_implemented_ref\<rbrakk>\<^sub>S = read_regS crypto_aes_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_crypto_aes_implemented[liftState_simp]:
  "\<lbrakk>write_reg crypto_aes_implemented_ref v\<rbrakk>\<^sub>S = write_regS crypto_aes_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_brbev1p1_implemented[liftState_simp]:
  "\<lbrakk>read_reg brbev1p1_implemented_ref\<rbrakk>\<^sub>S = read_regS brbev1p1_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_brbev1p1_implemented[liftState_simp]:
  "\<lbrakk>write_reg brbev1p1_implemented_ref v\<rbrakk>\<^sub>S = write_regS brbev1p1_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_brbe_implemented[liftState_simp]:
  "\<lbrakk>read_reg brbe_implemented_ref\<rbrakk>\<^sub>S = read_regS brbe_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_brbe_implemented[liftState_simp]:
  "\<lbrakk>write_reg brbe_implemented_ref v\<rbrakk>\<^sub>S = write_regS brbe_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_apply_effective_shareability[liftState_simp]:
  "\<lbrakk>read_reg apply_effective_shareability_ref\<rbrakk>\<^sub>S = read_regS apply_effective_shareability_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_apply_effective_shareability[liftState_simp]:
  "\<lbrakk>write_reg apply_effective_shareability_ref v\<rbrakk>\<^sub>S = write_regS apply_effective_shareability_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_aa32_hpd_implemented[liftState_simp]:
  "\<lbrakk>read_reg aa32_hpd_implemented_ref\<rbrakk>\<^sub>S = read_regS aa32_hpd_implemented_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_aa32_hpd_implemented[liftState_simp]:
  "\<lbrakk>write_reg aa32_hpd_implemented_ref v\<rbrakk>\<^sub>S = write_regS aa32_hpd_implemented_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PSTATE[liftState_simp]:
  "\<lbrakk>read_reg PSTATE_ref\<rbrakk>\<^sub>S = read_regS PSTATE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PSTATE[liftState_simp]:
  "\<lbrakk>write_reg PSTATE_ref v\<rbrakk>\<^sub>S = write_regS PSTATE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SEE[liftState_simp]:
  "\<lbrakk>read_reg SEE_ref\<rbrakk>\<^sub>S = read_regS SEE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SEE[liftState_simp]:
  "\<lbrakk>write_reg SEE_ref v\<rbrakk>\<^sub>S = write_regS SEE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma set_regval_Some_type_cases:
  assumes "set_regval r rv s = Some s'"
  obtains (InstrEnc) v where "InstrEnc_of_regval rv = Some v" and "s' = s\<lparr>InstrEnc_reg := (InstrEnc_reg s)(r := v)\<rparr>"
  | (ProcState) v where "ProcState_of_regval rv = Some v" and "s' = s\<lparr>ProcState_reg := (ProcState_reg s)(r := v)\<rparr>"
  | (TMState) v where "TMState_of_regval rv = Some v" and "s' = s\<lparr>TMState_reg := (TMState_reg s)(r := v)\<rparr>"
  | (bitvector_13_dec) v where "bitvector_13_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_13_dec_reg := (bitvector_13_dec_reg s)(r := v)\<rparr>"
  | (bitvector_16_dec) v where "bitvector_16_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_16_dec_reg := (bitvector_16_dec_reg s)(r := v)\<rparr>"
  | (bitvector_1_dec) v where "bitvector_1_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_1_dec_reg := (bitvector_1_dec_reg s)(r := v)\<rparr>"
  | (bitvector_256_dec) v where "bitvector_256_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_256_dec_reg := (bitvector_256_dec_reg s)(r := v)\<rparr>"
  | (bitvector_29_dec) v where "bitvector_29_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_29_dec_reg := (bitvector_29_dec_reg s)(r := v)\<rparr>"
  | (bitvector_2_dec) v where "bitvector_2_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_2_dec_reg := (bitvector_2_dec_reg s)(r := v)\<rparr>"
  | (bitvector_32_dec) v where "bitvector_32_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_32_dec_reg := (bitvector_32_dec_reg s)(r := v)\<rparr>"
  | (bitvector_3_dec) v where "bitvector_3_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_3_dec_reg := (bitvector_3_dec_reg s)(r := v)\<rparr>"
  | (bitvector_4_dec) v where "bitvector_4_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_4_dec_reg := (bitvector_4_dec_reg s)(r := v)\<rparr>"
  | (bitvector_52_dec) v where "bitvector_52_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_52_dec_reg := (bitvector_52_dec_reg s)(r := v)\<rparr>"
  | (bitvector_63_dec) v where "bitvector_63_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_63_dec_reg := (bitvector_63_dec_reg s)(r := v)\<rparr>"
  | (bitvector_64_dec) v where "bitvector_64_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_64_dec_reg := (bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (bitvector_88_dec) v where "bitvector_88_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_88_dec_reg := (bitvector_88_dec_reg s)(r := v)\<rparr>"
  | (bitvector_8_dec) v where "bitvector_8_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_8_dec_reg := (bitvector_8_dec_reg s)(r := v)\<rparr>"
  | (bool) v where "bool_of_register_value rv = Some v" and "s' = s\<lparr>bool_reg := (bool_reg s)(r := v)\<rparr>"
  | (int) v where "int_of_register_value rv = Some v" and "s' = s\<lparr>int_reg := (int_reg s)(r := v)\<rparr>"
  | (option_InterruptID) v where "option_of_regval (\<lambda>v. InterruptID_of_regval v) rv = Some v" and "s' = s\<lparr>option_InterruptID_reg := (option_InterruptID_reg s)(r := v)\<rparr>"
  | (signal) v where "signal_of_regval rv = Some v" and "s' = s\<lparr>signal_reg := (signal_reg s)(r := v)\<rparr>"
  | (vector_16_inc_bitvector_256_dec) v where "vector_of_regval (\<lambda>v. bitvector_256_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_16_inc_bitvector_256_dec_reg := (vector_16_inc_bitvector_256_dec_reg s)(r := v)\<rparr>"
  | (vector_16_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_16_inc_bitvector_64_dec_reg := (vector_16_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (vector_256_inc_bitvector_2048_dec) v where "vector_of_regval (\<lambda>v. bitvector_2048_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_256_inc_bitvector_2048_dec_reg := (vector_256_inc_bitvector_2048_dec_reg s)(r := v)\<rparr>"
  | (vector_31_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_31_inc_bitvector_64_dec_reg := (vector_31_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (vector_31_inc_int) v where "vector_of_regval (\<lambda>v. int_of_register_value v) rv = Some v" and "s' = s\<lparr>vector_31_inc_int_reg := (vector_31_inc_int_reg s)(r := v)\<rparr>"
  | (vector_32_inc_bitvector_2048_dec) v where "vector_of_regval (\<lambda>v. bitvector_2048_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_32_inc_bitvector_2048_dec_reg := (vector_32_inc_bitvector_2048_dec_reg s)(r := v)\<rparr>"
  | (vector_32_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_32_inc_bitvector_64_dec_reg := (vector_32_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (vector_4_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_4_inc_bitvector_64_dec_reg := (vector_4_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (vector_5_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_5_inc_bitvector_64_dec_reg := (vector_5_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (vector_64_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_64_inc_bitvector_64_dec_reg := (vector_64_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (vector_7_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_7_inc_bitvector_64_dec_reg := (vector_7_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
proof -
  from assms show ?thesis
    unfolding set_regval_unfold registers_def
    apply (elim option_bind_SomeE map_of_Cons_SomeE)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_52_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_2_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_5_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_1_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_1_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_4_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_4_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_4_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_31_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using option_InterruptID by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_63_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_63_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_13_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_256_inc_bitvector_2048_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_32_inc_bitvector_2048_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_256_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_256_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_1_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_29_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_64_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_64_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_64_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using TMState by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_31_inc_int by (auto simp: register_defs fun_upd_def)
    subgoal using vector_31_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using InstrEnc by (auto simp: register_defs fun_upd_def)
    subgoal using vector_31_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using vector_7_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_7_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using option_InterruptID by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_8_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_3_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_8_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_16_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_2_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_2_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_88_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_4_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using ProcState by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    by auto
qed

lemma get_regval_type_cases:
  fixes r :: string
  obtains (InstrEnc) "get_regval r = (\<lambda>s. Some (regval_of___InstrEnc (InstrEnc_reg s r)))"
  | (ProcState) "get_regval r = (\<lambda>s. Some (regval_of_ProcState (ProcState_reg s r)))"
  | (TMState) "get_regval r = (\<lambda>s. Some (regval_of_TMState (TMState_reg s r)))"
  | (bitvector_13_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_13_dec (bitvector_13_dec_reg s r)))"
  | (bitvector_16_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_16_dec (bitvector_16_dec_reg s r)))"
  | (bitvector_1_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_1_dec (bitvector_1_dec_reg s r)))"
  | (bitvector_256_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_256_dec (bitvector_256_dec_reg s r)))"
  | (bitvector_29_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_29_dec (bitvector_29_dec_reg s r)))"
  | (bitvector_2_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_2_dec (bitvector_2_dec_reg s r)))"
  | (bitvector_32_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_32_dec (bitvector_32_dec_reg s r)))"
  | (bitvector_3_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_3_dec (bitvector_3_dec_reg s r)))"
  | (bitvector_4_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_4_dec (bitvector_4_dec_reg s r)))"
  | (bitvector_52_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_52_dec (bitvector_52_dec_reg s r)))"
  | (bitvector_63_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_63_dec (bitvector_63_dec_reg s r)))"
  | (bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_64_dec (bitvector_64_dec_reg s r)))"
  | (bitvector_88_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_88_dec (bitvector_88_dec_reg s r)))"
  | (bitvector_8_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_8_dec (bitvector_8_dec_reg s r)))"
  | (bool) "get_regval r = (\<lambda>s. Some (register_value_of_bool (bool_reg s r)))"
  | (int) "get_regval r = (\<lambda>s. Some (register_value_of_int (int_reg s r)))"
  | (option_InterruptID) "get_regval r = (\<lambda>s. Some (regval_of_option (\<lambda>v. regval_of_InterruptID v) (option_InterruptID_reg s r)))"
  | (signal) "get_regval r = (\<lambda>s. Some (regval_of_signal (signal_reg s r)))"
  | (vector_16_inc_bitvector_256_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_256_dec v) (vector_16_inc_bitvector_256_dec_reg s r)))"
  | (vector_16_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_16_inc_bitvector_64_dec_reg s r)))"
  | (vector_256_inc_bitvector_2048_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_2048_dec v) (vector_256_inc_bitvector_2048_dec_reg s r)))"
  | (vector_31_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_31_inc_bitvector_64_dec_reg s r)))"
  | (vector_31_inc_int) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. register_value_of_int v) (vector_31_inc_int_reg s r)))"
  | (vector_32_inc_bitvector_2048_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_2048_dec v) (vector_32_inc_bitvector_2048_dec_reg s r)))"
  | (vector_32_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_32_inc_bitvector_64_dec_reg s r)))"
  | (vector_4_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_4_inc_bitvector_64_dec_reg s r)))"
  | (vector_5_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_5_inc_bitvector_64_dec_reg s r)))"
  | (vector_64_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_64_inc_bitvector_64_dec_reg s r)))"
  | (vector_7_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_7_inc_bitvector_64_dec_reg s r)))"
  | (None) "get_regval r = (\<lambda>s. None)"
proof (cases "map_of registers r")
  case (Some ops)
  then show ?thesis
    unfolding registers_def
    apply (elim map_of_Cons_SomeE)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bitvector_52_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_2_dec by (auto simp: register_defs)
    subgoal using vector_5_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_1_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_1_dec by (auto simp: register_defs)
    subgoal using bitvector_4_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using bitvector_4_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_4_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_31_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_32_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using option_InterruptID by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_63_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_63_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_13_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_256_inc_bitvector_2048_dec by (auto simp: register_defs)
    subgoal using vector_32_inc_bitvector_2048_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_256_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_256_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using bitvector_1_dec by (auto simp: register_defs)
    subgoal using bitvector_29_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_64_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_64_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_64_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using TMState by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_31_inc_int by (auto simp: register_defs)
    subgoal using vector_31_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using InstrEnc by (auto simp: register_defs)
    subgoal using vector_31_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using vector_7_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_7_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using option_InterruptID by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_8_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_3_dec by (auto simp: register_defs)
    subgoal using bitvector_8_dec by (auto simp: register_defs)
    subgoal using bitvector_16_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_2_dec by (auto simp: register_defs)
    subgoal using bitvector_2_dec by (auto simp: register_defs)
    subgoal using bitvector_88_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_4_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using ProcState by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    by auto
qed (auto simp: get_regval_unfold)

end
