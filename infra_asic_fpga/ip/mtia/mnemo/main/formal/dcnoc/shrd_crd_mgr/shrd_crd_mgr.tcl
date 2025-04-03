#==============================================================================
# File Name        : dcnoc.tcl
# File Description : TCL file for for running formal setup
#==============================================================================

global  MODELDIR

set      RTL_TOP                   "shrd_crd_mgr"
set      INFRA_ASIC_FPGA_ROOT      $env(INFRA_ASIC_FPGA_ROOT)

if {[info exists ::env(AXIOMISE)]} {

    clear   -all

    set     MODELDIR                [pwd]
    set     INFRA_ASIC_FPGA_TB      $env(INFRA_ASIC_FPGA_TB)

} else {

    set     INFRA_ASIC_FPGA_TB      $env(INFRA_ASIC_FPGA_ROOT)

}

include    "$INFRA_ASIC_FPGA_TB/ip/mtia/mnemo/main/formal/common.tcl"

#==============================================================================
# Analyze phase
#==============================================================================
eval       "analyze -f $MODELDIR/shrd_crd_mgr.f $ANALYZE_OPTS"

#==============================================================================
# Elaborate phase
#==============================================================================

set shrd_crd_mgr_params " \
-parameter shrd_crd_mgr.NUM_VC mnm_pkg::MNM_DNOC_TOTAL_NUM_VC \
-parameter shrd_crd_mgr.CRD_W mnm_rtr_pkg::MNM_RTR_DNOC_RX_DEPTH_W \
-parameter shrd_crd_mgr.NUM_RSVD_GROUPS mnm_pkg::MNM_RTR_NUM_RSVD_CREDIT_GROUPS \
-parameter shrd_crd_mgr.NUM_SHRD_GROUPS mnm_pkg::MNM_RTR_NUM_SHRD_CREDIT_GROUPS"

eval "elaborate -disable_auto_bbox -top shrd_crd_mgr $ELAB_OPTS $shrd_crd_mgr_params"

# set_prove_time_limit 12h
# set_proofgrid_per_engine_max_jobs 10

#==============================================================================
# clock and reset
#==============================================================================

clock clk
reset ~reset_n

#==============================================================================
# tcl starts
#==============================================================================

set_message -warning VERI-1348