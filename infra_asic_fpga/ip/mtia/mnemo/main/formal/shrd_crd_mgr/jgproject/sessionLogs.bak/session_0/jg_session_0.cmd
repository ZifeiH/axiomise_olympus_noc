# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2023.12
# platform  : Linux 6.8.0-52-generic
# version   : 2023.12 FCS 64 bits
# build date: 2023.12.19 17:39:24 UTC
# ----------------------------------------
# started   : 2025-03-20 14:46:53 GMT
# hostname  : MAHESH.(none)
# pid       : 1153326
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:41819' '-style' 'windows' '-data' 'AAAA1nicY2RgYLCp////PwMYMFcBCQEGHwZfhiAGVyDpzxAGpOGA8QGUYcPIgApAfCZUkcAGFJqBgRWmGaYEpEGLQZchkSEHCPMZyhniGUoZ8hiKgWQBEOYzFDGUMKQypADF/RmCgaoVgHIZQFGQSDKUzmVIB7L0gCqTgaaAAABoehjU' '-proj' '/home/amir/Meta/axiomise_olympus_noc/infra_asic_fpga/ip/mtia/mnemo/main/formal/shrd_crd_mgr/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/amir/Meta/axiomise_olympus_noc/infra_asic_fpga/ip/mtia/mnemo/main/formal/shrd_crd_mgr/jgproject/.tmp/.initCmds.tcl' 'shrd_crd_mgr.tcl'
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
eval "analyze -f /home/amir/Meta/mtia-axiomise-collab/fbcode/infra_asic_fpga/ip/mtia/mnemo/main/formal/dcnoc/min_filelist.f $ANALYZE_OPTS"
include shrd_crd_mgr.tcl
include shrd_crd_mgr.tcl
