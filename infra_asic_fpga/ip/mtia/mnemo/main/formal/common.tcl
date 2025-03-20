

if {[info exists ::env(AXIOMISE)]} {

    clear -all

	puts "AXIOMISE defined"

    set WORKROOT                      $env(WORKROOT)

    set ANALYZE_OPTS                  {-sv09 +define+FB_BEH_MODE+FB_BEH_CGC+FORMAL+FB_BEHV_CLKGATE+FB_BEH_CKG+FB_BEH_SIM+ENABLE_SVA_DVR_BIND+JG_ABVIP_STRONG_SEMANTICS+DONT_USE_PEC}
    set ELAB_OPTS                     {-sv09_strong_embedding}

} else {

    puts "AXIOMISE not defined"

    set WORKROOT                            $env(INFRA_ASIC_FPGA_ROOT)

    set_parallel_synthesis_mode             on
    set_parallel_synthesis_num_process      20
    set_parallel_synthesis_partition_method dynamic

}