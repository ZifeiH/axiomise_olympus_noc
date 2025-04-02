

if {[info exists ::env(AXIOMISE)]} {

    clear -all

	puts "AXIOMISE defined"

    set WORKROOT                      $env(WORKROOT)

#  +define+FB_BEH_SIM +define+FB_BEH_MEM +define+BRCM_CONTINUE_ON_HIGHCURRENT_STATE +define+brcm_apd_n3p +define+DS03P_SBUS_RX_CNTL32_01_DONT_USE_BRCM_APD_WMK +define+DS03P_LIB_PM_TS3FFP_S0_V1_DONT_USE_BRCM_APD_WMK +define+cln03_apb2sbuscore +define+APB2SBUSCORE_NBR_DONT_USE_BRCM_APD_WMK +define+FB_BEH_SYNC2 +define+FB_BEH_SYNC3   +define+PROJ_DEF_CSR_AWIDTH=32 +define+USE_RANDOM_DELAY_SYNC

    set ANALYZE_OPTS                  {-sv09 +define+FB_BEH_MODE+FB_BEH_MEM+FB_BEH_CGC+FORMAL+FB_BEHV_CLKGATE+FB_BEH_CKG+FB_BEH_SIM+ENABLE_SVA_DVR_BIND+JG_ABVIP_STRONG_SEMANTICS+DONT_USE_PEC}
    set ELAB_OPTS                     {-sv09_strong_embedding}

    # Engine by default if you want to change engine please modify in the tcl for compiling the tb
    set_engine_mode {H B AD M N AM Tri}

} else {

    puts "AXIOMISE not defined"

    set WORKROOT                            $env(INFRA_ASIC_FPGA_ROOT)

    set_parallel_synthesis_mode             on
    set_parallel_synthesis_num_process      20
    set_parallel_synthesis_partition_method dynamic

}