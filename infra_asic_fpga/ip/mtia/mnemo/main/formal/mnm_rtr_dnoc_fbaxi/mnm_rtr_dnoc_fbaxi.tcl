#==============================================================================
# File Name        : dcnoc.tcl
# File Description : TCL file for for running formal setup
#==============================================================================

global  MODELDIR

set      RTL_TOP                   "mnm_rtr_dc_slice_a"
set      INFRA_ASIC_FPGA_ROOT      $env(INFRA_ASIC_FPGA_ROOT)

if {[info exists ::env(AXIOMISE)]} {

    clear   -all

    set     MODELDIR               [pwd]
    set     INFRA_ASIC_FPGA_TB      $env(INFRA_ASIC_FPGA_TB)

} else {

    set     INFRA_ASIC_FPGA_TB      $env(INFRA_ASIC_FPGA_ROOT)

}

include         "$INFRA_ASIC_FPGA_TB/ip/mtia/mnemo/main/formal/common.tcl"

#==============================================================================
# Analyze phase
#==============================================================================
eval "analyze -f $MODELDIR/mnm_rtr_dnoc_fbaxi.f $ANALYZE_OPTS"

#==============================================================================
# Elaborate phase
#==============================================================================
eval "elaborate -disable_auto_bbox -top $RTL_TOP $ELAB_OPTS -bbox_m DW_ecc"

set_prove_time_limit 12h

#==============================================================================
# clock and reset
#==============================================================================
clock clk 
reset ~soc_unoc_reset_n
#==============================================================================
# tcl starts
#==============================================================================

set_message -warning VERI-1348
