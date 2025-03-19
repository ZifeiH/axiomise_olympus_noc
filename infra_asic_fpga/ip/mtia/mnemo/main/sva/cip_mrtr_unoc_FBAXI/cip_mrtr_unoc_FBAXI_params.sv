///////////////////////////////////////////////////
/// File: cip_mrtr_unoc_FBAXI_params.sv
/// This file contains localparams used in different files
///////////////////////////////////////////////////

    localparam max_reqs_east                       = 1;
    localparam max_reqs_west                       = 1;
    localparam max_reqs_north                      = 1;
    localparam max_reqs_south                      = 1;
    localparam max_reqs_leaf0                      = 1;
    localparam max_reqs_leaf1                      = 1;
    
    localparam max_tracking_reqs                   = 20;
    
    localparam UNOC_DATA_WIDTH                     = $bits(cip_pkg::utility_noc_t);                             
    localparam EAST                                = cip_rtr_pkg::UNOC_DIR_EAST  ;                                // 3
    localparam WEST                                = cip_rtr_pkg::UNOC_DIR_WEST  ;                                // 1
    localparam NORTH                               = cip_rtr_pkg::UNOC_DIR_NORTH ;                                // 0
    localparam SOUTH                               = cip_rtr_pkg::UNOC_DIR_SOUTH ;                                // 2
    localparam LEAF0                               = cip_rtr_pkg::UNOC_DIR_LEAF0 ;                                // 4
    localparam LEAF1                               = cip_rtr_pkg::UNOC_DIR_LEAF1 ;                                // 5 
    localparam IID_WIDTH                           = 9;
    localparam XCOORD_WIDTH                        = 4;
    localparam YCOORD_WIDTH                        = 4;
    localparam ZCOORD_WIDTH                        = 4;
    localparam VC_WIDTH                            = $clog2(cip_pkg::CIP_UNOC_AWW_NUM_VC);

    localparam UNOC_ZCOORD_E_UNICAST_MAX2    = 4'h3;
    localparam UNOC_ZCOORD_E_UNICAST_MAX2_MB = 4'h4;