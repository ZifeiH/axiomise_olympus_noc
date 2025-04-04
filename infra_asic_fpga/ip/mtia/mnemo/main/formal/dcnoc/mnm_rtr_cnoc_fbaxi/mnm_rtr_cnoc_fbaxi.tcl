#==============================================================================
# File Name        : dcnoc.tcl
# File Description : TCL file for for running formal setup
#==============================================================================

global  MODELDIR

# set      RTL_TOP                   "mnm_rtr_dc_slice_a"
set      RTL_TOP                   "mnm_rtr_ca_cnoc_top"

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
eval       "analyze -f $MODELDIR/mnm_rtr_cnoc_fbaxi.f $ANALYZE_OPTS"

#==============================================================================
# Elaborate phase
#==============================================================================
# eval       "elaborate -disable_auto_bbox -top $RTL_TOP $ELAB_OPTS -bbox_m DW_ecc"
eval         "elaborate -disable_auto_bbox -top mnm_rtr_ca_cnoc_top -parameter VCID_W 4 -parameter SEQN_W 5 -parameter REMOVE_LANE 11'b011000000 -bbox_m DW_ecc"

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