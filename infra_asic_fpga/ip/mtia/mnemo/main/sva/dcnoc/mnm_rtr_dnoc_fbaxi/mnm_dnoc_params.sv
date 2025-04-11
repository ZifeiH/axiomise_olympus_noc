parameter NUM_HCB_DNOC = mnm_pkg::MNM_RTR_SLICE_NUM_HCB_DNOC;
parameter NUM_LLC_DNOC = mnm_pkg::MNM_RTR_SLICE_NUM_LLC_DNOC;
parameter NUM_NS_DNOC  = mnm_pkg::MNM_RTR_SLICE_NUM_NS_DNOC;
parameter NUM_EW_DNOC  = mnm_pkg::MNM_RTR_SLICE_NUM_EW_DNOC;
parameter NUM_VC       = mnm_pkg::MNM_DNOC_TOTAL_NUM_VC;
parameter VC_W         = $clog2(NUM_VC);
parameter CRED_W       = 8;
parameter NUM_RSVD_GRP = mnm_pkg::MNM_RTR_NUM_RSVD_CREDIT_GROUPS;
parameter RSVD_GRP_W   = $clog2(NUM_RSVD_GRP);
parameter NUM_SHRD_GRP = mnm_pkg::MNM_RTR_NUM_SHRD_CREDIT_GROUPS;
parameter SHRD_GRP_W   = $clog2(NUM_SHRD_GRP);
parameter LEN_W        = mnm_pkg::MNM_DAXI_AW_LEN_WIDTH;


typedef struct packed
{
    logic  [NUM_VC-1:0][CRED_W-1:0]                    vc_rsvd_max    ;
    logic  [NUM_VC-1:0][CRED_W-1:0]                    vc_shrd_max    ;
    logic  [NUM_VC-1:0]                                vc_grp_rsvd_en ;
    logic  [NUM_VC-1:0][RSVD_GRP_W-1:0]                vc_grp_rsvd_id ;
    logic  [NUM_VC-1:0][NUM_SHRD_GRP-1:0]              vc_grp_rsvd_max;
    logic  [NUM_RSVD_GRP-1:0][CRED_W-1:0]              vc_grp_shrd_max;
    logic  [NUM_VC-1:0][NUM_SHRD_GRP-1:0]              vc_grp_shrd    ;
    logic  [CRED_W-1:0]                                total_shrd_max ;
    logic  [CRED_W-1:0]                                total_credits  ;

} credit_cfg_t;