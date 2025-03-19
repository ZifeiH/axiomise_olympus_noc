#==============================================================================
# File Name        : dcnoc.tcl
# File Description : TCL file for for running formal setup
#==============================================================================

#Disable an enum variable may only be assigned the same enum typed variable or
#one of its values error
set_message -warning VERI-1348


# set_parallel_synthesis_mode on
# set_parallel_synthesis_num_process 20
# set_parallel_synthesis_partition_method dynamic

set ANALYZE_OPTS                  {-sv09 +define+FB_BEH_MODE+FB_BEH_CGC+FORMAL+FB_BEHV_CLKGATE+FB_BEH_CKG+FB_BEH_SIM+ENABLE_SVA_DVR_BIND+JG_ABVIP_STRONG_SEMANTICS+DONT_USE_PEC}
set ELAB_OPTS                     {-sv09_strong_embedding}
#==============================================================================
# Analyze phase
#==============================================================================
eval "analyze -f /home/zifeihuang/MEGA/axiomise_olympus_developement/infra_asic_fpga/ip/mtia/mnemo/main/formal/mnemo_dnoc_fbaxi/mnemo_dnoc_fbaxi.f $ANALYZE_OPTS"

#==============================================================================
# Elaborate phase
#==============================================================================
eval "elaborate -disable_auto_bbox -top mnm_rtr_dc_slice $ELAB_OPTS -bbox_m DW_ecc"

set_prove_time_limit 12h
set_proofgrid_per_engine_max_jobs 10

#==============================================================================
# clock and reset
#==============================================================================

#==============================================================================
# tcl starts
#==============================================================================