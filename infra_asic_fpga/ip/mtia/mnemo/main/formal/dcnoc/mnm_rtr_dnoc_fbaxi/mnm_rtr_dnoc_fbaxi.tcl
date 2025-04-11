#==============================================================================
# File Name        : dcnoc.tcl
# File Description : TCL file for for running formal setup
#==============================================================================

global  MODELDIR

set      RTL_TOP                   "mnm_rtr_ca_dnoc_top"
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
# eval       "analyze -f $MODELDIR/mnm_rtr_dnoc_fbaxi.f $ANALYZE_OPTS"

set ANALYZE_F $MODELDIR/trl_rxpt.f if {[info exists IS_VENDOR_ENV] && $IS_VENDOR_ENV == 1} {     
  # This IS_VENDOR_ENV variable is only set in the git workflow (aka vendor env).     
  # Similarly MODELDIR has a different value in the git workflow.     
  set ANALYZE_F $MODELDIR/min_filelist.f 
} 
eval "analyze -f $ANALYZE_F $ANALYZE_OPTS"

#==============================================================================
# Elaborate phase
#==============================================================================
# eval       "elaborate -disable_auto_bbox -top $RTL_TOP $ELAB_OPTS -bbox_m DW_ecc"
eval         "elaborate -disable_auto_bbox -top mnm_rtr_ca_dnoc_top -parameter VCID_W 4 -parameter RX_DEPTH_W 8 -parameter SEQN_W 5 -parameter REMOVE_LANE 11'b000000000 -bbox_m DW_ecc"

set_prove_time_limit 12h

#==============================================================================
# clock and reset
#==============================================================================
clock clk 
reset ~soc_reset_n
#==============================================================================
# tcl starts
#==============================================================================

set_message -warning VERI-1348

assume -from_assert *_am_*