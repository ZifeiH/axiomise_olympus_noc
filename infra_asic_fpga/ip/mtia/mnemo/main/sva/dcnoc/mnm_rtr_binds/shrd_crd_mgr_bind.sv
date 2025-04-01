bind shrd_crd_mgr shrd_crd_mgr_sva #( .NUM_VC(NUM_VC),
                                      .VCID_W(VCID_W),
                                      .CRD_W(CRD_W),
                                      .NUM_RSVD_GROUPS(NUM_RSVD_GROUPS),
                                      .NUM_SHRD_GROUPS(NUM_SHRD_GROUPS),
                                      .RSVD_GROUP_W(RSVD_GROUP_W),
                                      .MAX_LEN(MAX_LEN),
                                      .DISABLE_RTT_CHECK(DISABLE_RTT_CHECK))
                                      dc_shrd_crd_mgr_sva (.*);
                                      