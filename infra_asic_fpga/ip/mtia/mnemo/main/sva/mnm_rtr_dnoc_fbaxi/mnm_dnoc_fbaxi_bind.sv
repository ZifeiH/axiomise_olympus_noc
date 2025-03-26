bind mnm_rtr_ca_dnoc_top mnm_dnoc_fbaxi_sva  #(.NUM_LANES(NUM_LANES),
                                               .NUM_VC(NUM_VC),
                                               .VCID_W(VCID_W),
                                               .RX_DEPTH_W(RX_DEPTH_W),
                                               .NUM_SHRD_CRD_GROUPS(NUM_SHRD_CRD_GROUPS),
                                               .NUM_RSVD_CRD_GROUPS(NUM_RSVD_CRD_GROUPS),
                                               .RSVD_CRD_GROUP_ID_W(RSVD_CRD_GROUP_ID_W),
                                               .SEQN_W(SEQN_W),
                                               .STUB(STUB),
                                               .REMOVE_LANE(REMOVE_LANE)) 
                                               u_mnm_rtr_dnoc_fbaxi_sva (.*);