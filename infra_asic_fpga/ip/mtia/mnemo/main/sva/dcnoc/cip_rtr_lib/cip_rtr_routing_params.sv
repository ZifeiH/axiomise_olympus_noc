/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_rtr_routing_params.sv
// This file contains cip router parameters
/////////////////////////////////////////////////////////////////////////////////////////
//------------------------------------------------------------------------------
//-- Parameters --
//------------------------------------------------------------------------------

    parameter CNOC_DATA_WIDTH                    = $bits(cip_pkg::control_noc_t);
    parameter [1:0][2:0] DIR_VALUE               = 0;                               
    parameter EAST                               = cip_rtr_pkg::NOC_DIR_EAST  ;                                // 3
    parameter WEST                               = cip_rtr_pkg::NOC_DIR_WEST  ;                                // 1
    parameter NORTH                              = cip_rtr_pkg::NOC_DIR_NORTH ;                                // 0
    parameter SOUTH                              = cip_rtr_pkg::NOC_DIR_SOUTH ;                                // 2
    parameter LEAF0                              = cip_rtr_pkg::NOC_DIR_LEAF0 ;                                // 4
    parameter LEAF1                              = cip_rtr_pkg::NOC_DIR_LEAF1 ;   
    parameter NO_TRAFFIC                         = 7;   
    parameter IID_WIDTH                          = 9;
    parameter XCOORD_WIDTH                       = 4;
    parameter YCOORD_WIDTH                       = 4;
    parameter ZCOORD_WIDTH                       = 4;
    parameter CIP_CNOC_TOTAL_NUM_VC_WIDTH        = $clog2(cip_pkg::CIP_CRTR_CNOC_TOTAL_NUM_VC);    
    parameter CIP_DNOC_TOTAL_NUM_VC_WIDTH        = $clog2(cip_pkg::CIP_CRTR_DNOC_TOTAL_NUM_VC);