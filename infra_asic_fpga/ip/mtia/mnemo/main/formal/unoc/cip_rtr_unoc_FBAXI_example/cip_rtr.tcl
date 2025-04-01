#============================================================================== 
# File Name        : cip_rtr.tcl
# File Description : TCL file for for running formal setup 
#============================================================================== 


# =============================================================================
#  RTR LOCATION SETTINGS

# Please go through the ANALYSE PHASE DEFINES section below to check the details

set CIP_RTR_XCOOD 3
set CIP_RTR_YCOOD 4
set CIP_ID        0

# Supported locations for FBAXI checks that doesn't include invariants

#             - Supported locations
#               - x3y4c0, x3y1c0 

# #############################################################################

# =============================================================================
#  ANALYSE PHASE DEFINES

# GEN_INVARIANTS

#  DEFINES FOR GENERATING VARIOUS CHECKS

#      [GEN_INVARIANTS]
#          Purpose:
#          - To generate the invariants
#             
#             - Supported locations
#               - x3y4c0

if {[info exists ::env(AXIOMISE)]} {

    global  MODELDIR
    set     MODELDIR [pwd]

    set     INFRA_ASIC_FPGA_ROOT $env(INFRA_ASIC_FPGA_ROOT)
} else {
}

    include "$INFRA_ASIC_FPGA_ROOT/ip/mtia/medha/main/formal/cip_grid/cip_rtr/common.tcl"
    include "$INFRA_ASIC_FPGA_ROOT/ip/mtia/medha/main/formal/cip_grid/cip_rtr/scripts/cip_rtr_unoc_fbaxi_procs.tcl"

set RTL_TOP "cip_rtr"

set fname "$RTL_TOP.f"

#============================================================================== 
# Analyze phase
#==============================================================================

# META:
# clean_warning
set RTR_LOCATION_DEF [get_cip_rtr_location $CIP_RTR_YCOOD $CIP_RTR_YCOOD]

# META:
if {[info exists ::env(AXIOMISE)]} {
    eval "analyze -f $MODELDIR/$fname $ANALYZE_OPTS +define+ASSERT_OFF+$RTR_LOCATION_DEF"
    set_axm_proofgrid
} else {
    eval "analyze -f $MODELDIR/$fname $ANALYZE_OPTS +define+ASSERT_OFF+DONT_USE_PEC+$RTR_LOCATION_DEF"
    clean_warning
    set_meta_proofgrid
}

#============================================================================== 
# Elaborate phase
#==============================================================================

set_tcl_related_covers on

set CIP_RTR_UNOC_FLOW_CONTROL_PARAMS " \
-parameter u_cip_rtr_unoc_FBAXI_sva.flow_control_east.unoc_flow_control_east.MAX_ALLOWED_REQS 2 \
-parameter u_cip_rtr_unoc_FBAXI_sva.flow_control_west.unoc_flow_control_west.MAX_ALLOWED_REQS 2 \
-parameter u_cip_rtr_unoc_FBAXI_sva.flow_control_north.unoc_flow_control_north.MAX_ALLOWED_REQS 2 \
-parameter u_cip_rtr_unoc_FBAXI_sva.flow_control_south.unoc_flow_control_south.MAX_ALLOWED_REQS 2 \
-parameter u_cip_rtr_unoc_FBAXI_sva.flow_control_leaf0.unoc_flow_control_leaf0.MAX_ALLOWED_REQS 2 \
-parameter u_cip_rtr_unoc_FBAXI_sva.flow_control_leaf1.unoc_flow_control_leaf1.MAX_ALLOWED_REQS 2 \
-parameter u_cip_rtr_unoc_FBAXI_sva.FLOW_CONTROL_EAST 1 \
-parameter u_cip_rtr_unoc_FBAXI_sva.FLOW_CONTROL_WEST 1 \
-parameter u_cip_rtr_unoc_FBAXI_sva.FLOW_CONTROL_SOUTH 1 \
-parameter u_cip_rtr_unoc_FBAXI_sva.FLOW_CONTROL_NORTH 1 \
-parameter u_cip_rtr_unoc_FBAXI_sva.FLOW_CONTROL_LEAF0 1 \
-parameter u_cip_rtr_unoc_FBAXI_sva.FLOW_CONTROL_LEAF1 1"

set CIP_RTR_LOCATION_SET " \
-parameter u_cip_rtr_unoc_FBAXI_sva.CIP_ID  $CIP_ID \
-parameter u_cip_rtr_unoc_FBAXI_sva.CIP_RTR_XCOOD  $CIP_RTR_XCOOD \
-parameter u_cip_rtr_unoc_FBAXI_sva.CIP_RTR_YCOOD  $CIP_RTR_YCOOD"

proc disable_flow_control {} {
  assume -disable *flow_control*
}  

proc enable_flow_control {} {
  assume -enable *flow_control*
}


eval "elaborate -disable_auto_bbox -top $RTL_TOP -bbox_m cip_top_clkrst -bbox_m cip_clkrst $ELAB_OPTS \
-bbox_m cip_unoc_pipe \
-create_related_covers {precondition witness} \
-enable_sva_isunknown \
$CIP_RTR_LOCATION_SET \
$CIP_RTR_UNOC_FLOW_CONTROL_PARAMS \
$CIP_RTR_REDUCTION"

#============================================================================== 
# clock and reset
#==============================================================================
clock clk  $clk_list
reset -expression $rst_list

#============================================================================== 
# tcl starts
#==============================================================================

# set_proofmaster on
# set_proofmaster_dir ./proofmaster

proc remove_pipeline_stages {} { 

    # --- this depends on a previous '-bbox_m cip_unoc_pipe' argument in elaborate command ---
    #  directly connects up blackboxed module outputs to their corresponding inputs
    
    set CIP_RTR_CENTER_CRTR_UNOC_PIPE      "CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr.FT_unoc_no_stub.u_cip_unoc_pipe_FT_dir"
    set CIP_RTR_NORTH_IRTR_UNOC_PIPE       "CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_north_top.CIP_RTR_NORTH_TOP_DRIVE_0_FALSE.main_north_irtr.u_cip_rtr_north_irtr.u_cip_unoc_pipe"
    set CIP_RTR_SOUTH_IRTR_UNOC_PIPE       "CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_south_top.CIP_RTR_SOUTH_TOP_DRIVE_0_FALSE.main_south_irtr.u_cip_rtr_south_irtr.u_cip_unoc_pipe"

    assume -name AST_FVPH_RTR_FV_am_crtr_cntr_u_noc_in_pipe_out_same_as_in              "${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_in_pipe_out                == ${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_in_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_crtr_cntr_u_noc_in_valid_pipe_out_same_as_in        "${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_in_valid_pipe_out          == ${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_in_valid_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_crtr_cntr_u_noc_in_credit_release_in_same_as_out    "${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_in_credit_release_pipe_in  == ${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_in_credit_release_pipe_out"

    assume -name AST_FVPH_RTR_FV_am_crtr_cntr_u_noc_out_pipe_out_same_as_in             "${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_out_pipe_out               == ${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_out_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_crtr_cntr_u_noc_out_valid_pipe_out_same_as_in       "${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_out_valid_pipe_out         == ${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_out_valid_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_crtr_cntr_u_noc_out_credit_release_in_same_as_out   "${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_out_credit_release_pipe_in == ${CIP_RTR_CENTER_CRTR_UNOC_PIPE}.u_noc_out_credit_release_pipe_out"

    assume -name AST_FVPH_RTR_FV_am_irtr_north_u_noc_in_pipe_out_same_as_in              "${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_in_pipe_out                == ${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_in_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_north_u_noc_in_valid_pipe_out_same_as_in        "${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_in_valid_pipe_out          == ${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_in_valid_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_north_u_noc_in_credit_release_in_same_as_out    "${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_in_credit_release_pipe_in  == ${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_in_credit_release_pipe_out"

    assume -name AST_FVPH_RTR_FV_am_irtr_north_u_noc_out_pipe_out_same_as_in             "${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_out_pipe_out               == ${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_out_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_north_u_noc_out_valid_pipe_out_same_as_in       "${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_out_valid_pipe_out         == ${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_out_valid_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_north_u_noc_out_credit_release_in_same_as_out   "${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_out_credit_release_pipe_in == ${CIP_RTR_NORTH_IRTR_UNOC_PIPE}.u_noc_out_credit_release_pipe_out"

    assume -name AST_FVPH_RTR_FV_am_irtr_south_u_noc_in_pipe_out_same_as_in              "${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_in_pipe_out                == ${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_in_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_south_u_noc_in_valid_pipe_out_same_as_in        "${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_in_valid_pipe_out          == ${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_in_valid_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_south_u_noc_in_credit_release_in_same_as_out    "${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_in_credit_release_pipe_in  == ${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_in_credit_release_pipe_out"

    assume -name AST_FVPH_RTR_FV_am_irtr_south_u_noc_out_pipe_out_same_as_in             "${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_out_pipe_out               == ${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_out_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_south_u_noc_out_valid_pipe_out_same_as_in       "${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_out_valid_pipe_out         == ${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_out_valid_pipe_in"
    assume -name AST_FVPH_RTR_FV_am_irtr_south_u_noc_out_credit_release_in_same_as_out   "${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_out_credit_release_pipe_in == ${CIP_RTR_SOUTH_IRTR_UNOC_PIPE}.u_noc_out_credit_release_pipe_out"
}

remove_pipeline_stages

stopat CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_irtr.u_cip_rtr_center_irtr.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip0
stopat CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_irtr.u_cip_rtr_center_irtr.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip1
 
stopat CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip0
stopat CIP_RTR_DRIVE_0_FALSE.u_cip_rtr_center_top.CIP_RTR_CENTER_TOP_DRIVE_0_FALSE.main_center_crtr.u_cip_rtr_center_crtr.u_cip_rtr_unoc.u_cip_rtr_u_center.u_cip_rtr_u_cfg.disabled_pe_cip1

primary_io_interface_setup
get_design_info
set_engine_mode {H B Tri L}

if {![info exists ::env(AXIOMISE)]} {

    disable_flow_control

    set fvcfg(allow_unprocessed) 1
    set fvcfg(any_bound_ok) 1

    set_log_timestamp_mode on
    set_log_timestamp_format "%Y-%m-%d %H:%M:%S: "

    set_prove_time_limit 48h

    prove -property *e2e*

} else {
    puts "Axiomise defined, please put here your running proc"

    disable_flow_control

    set_prove_time_limit 24h

}