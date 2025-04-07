/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_signal_defines.sv
//  This file contains irtr dnoc routing testbench wires
/////////////////////////////////////////////////////////////////////////////////////////
//------------------------------------------------------------------------------
//-- C2C --
//------------------------------------------------------------------------------

    logic                                               dnoc_in_tgt_within_cip;
    logic                                               dnoc_in_src_within_cip;
    logic                                               dnoc_in_to_north_cip;
    logic                                               dnoc_in_to_south_cip;
    logic                                               dnoc_north_in_from_cip_0_to_cip_1;
    logic                                               dnoc_south_in_from_cip_1_to_cip_0;

    logic                                               dnoc_in_tgt_to_LLC;
    logic                                               dnoc_in_src_from_LLC;

    logic                                               dnoc_in_tgt_to_SOC;
    logic                                               dnoc_in_src_from_SOC;

    logic                                               dnoc_in_tgt_to_LLC;
    logic                                               dnoc_in_src_from_LLC;

    logic                                               dnoc_in_tgt_to_OWL;
    logic                                               dnoc_in_src_from_OWL;

    logic                                               dnoc_in_src_is_PE;

    logic                                               resp_from_SOC_to_LLC;
    logic                                               req_from_LLC_to_SOC;
    logic                                               req_from_OWL_to_SOC;
    logic                                               resp_from_SOC_to_OWL;
    logic                                               x_first_exception;
    logic                                               is_x_first;
    logic                                               is_y_first;

    logic  is_row_wise_read_multicast, is_read_unicast, is_col_wise_read_multicast;
    assign is_row_wise_read_multicast   = dnoc_in_is_R_channel && d_noc_in_rcc_opcode == cip_pkg::CC_OPCODE_E_RDM && d_noc_in_rcc_dir == cip_pkg::ROW_COLUMN_SELECT_E_ROW;
    assign is_col_wise_read_multicast   = dnoc_in_is_R_channel && d_noc_in_rcc_opcode == cip_pkg::CC_OPCODE_E_RDM && d_noc_in_rcc_dir == cip_pkg::ROW_COLUMN_SELECT_E_COLUMN;
    assign is_read_unicast              = dnoc_in_is_R_channel && d_noc_in_rcc_opcode != cip_pkg::CC_OPCODE_E_RDM;

    assign    dnoc_in_tgt_within_cip                     = RTR_LOCATION_CIP_ID == dnoc_in_tgtid_cip_id;
    assign    dnoc_in_src_within_cip                     = RTR_LOCATION_CIP_ID == dnoc_in_srcid_cip_id;
    
    assign    dnoc_in_to_north_cip                       = RTR_LOCATION_CIP_ID == 1 && dnoc_in_tgtid_cip_id == 0;    
    assign    dnoc_in_to_south_cip                       = RTR_LOCATION_CIP_ID == 0 && dnoc_in_tgtid_cip_id == 1;

    assign    dnoc_north_in_from_cip_0_to_cip_1          = RTR_LOCATION_CIP_ID == 1 && dnoc_in_srcid_cip_id == 0;
    assign    dnoc_south_in_from_cip_1_to_cip_0          = RTR_LOCATION_CIP_ID == 0 && dnoc_in_srcid_cip_id == 1;


    assign    dnoc_in_src_is_PE                          = (dnoc_in_srcid_xcoord >= CIP_RTR_GRID_COORD_X_START && dnoc_in_srcid_xcoord <= CIP_RTR_GRID_COORD_X_END && dnoc_in_srcid_ycoord >= CIP_RTR_GRID_COORD_Y_START && dnoc_in_srcid_ycoord <= CIP_RTR_GRID_COORD_Y_END-1); 

   // TODO: is y coord to be considred?
    assign    dnoc_in_src_from_LLC                       = (dnoc_in_srcid_xcoord < CIP_RTR_GRID_COORD_X_START || dnoc_in_srcid_xcoord > CIP_RTR_GRID_COORD_X_END ) ; 
    assign    dnoc_in_tgt_to_LLC                         = (dnoc_in_tgtid_xcoord < CIP_RTR_GRID_COORD_X_START || dnoc_in_tgtid_xcoord > CIP_RTR_GRID_COORD_X_END ) ; 
   // TODO: is x coord to be considred? 
    assign    dnoc_in_tgt_to_SOC                         =  dnoc_in_tgtid_ycoord <  CIP_RTR_GRID_COORD_Y_START && dnoc_in_tgtid_cip_id == 0; 
    assign    dnoc_in_src_from_SOC                       =  dnoc_in_srcid_ycoord <  CIP_RTR_GRID_COORD_Y_START && dnoc_in_srcid_cip_id == 0; 
    // TODO: is cip correct? 
    assign    dnoc_in_tgt_to_OWL                         =  dnoc_in_tgtid_ycoord >  CIP_RTR_GRID_COORD_Y_END && dnoc_in_tgtid_cip_id == 1; 
    assign    dnoc_in_src_from_OWL                       =  dnoc_in_srcid_ycoord >  CIP_RTR_GRID_COORD_Y_END && dnoc_in_srcid_cip_id == 1; 

    assign    req_from_LLC_to_SOC                        =  dnoc_in_is_AW_W_channel && dnoc_in_src_from_LLC   &&  dnoc_in_tgt_to_SOC ;
    assign    resp_from_SOC_to_LLC                       =  dnoc_in_is_R_channel  && dnoc_in_src_from_SOC   &&  dnoc_in_tgt_to_LLC ;
   
    assign    req_from_OWL_to_SOC                        =  dnoc_in_is_AW_W_channel && dnoc_in_src_from_OWL   &&  dnoc_in_tgt_to_SOC;
    assign    resp_from_SOC_to_OWL                       =  dnoc_in_is_R_channel  && dnoc_in_src_from_SOC   &&  dnoc_in_tgt_to_OWL;

//------------------------------------------------------------------------------
//-- Routing rules as spec suggessted --
//------------------------------------------------------------------------------

    // REQ is Y-first till the First PE row of CIP0 and turn left/right based on the SOC NIC, turns north to max2_mb
    assign    x_first_exception                          =   (is_north_edge_RTR && RTR_LOCATION_CIP_ID==0) && dnoc_in_tgt_to_SOC && dnoc_in_is_AW_W_channel;

    assign    is_y_first                                 =    !x_first_exception && 
                                                              ((dnoc_in_is_AW_W_channel && !req_from_LLC_to_SOC  && !req_from_OWL_to_SOC) || 
                                                              resp_from_SOC_to_LLC || resp_from_SOC_to_OWL);

    assign    is_x_first                                 =   (dnoc_in_is_R_channel  && !resp_from_SOC_to_LLC && !resp_from_SOC_to_OWL) || 
                                                              x_first_exception                                                    ||
                                                              req_from_LLC_to_SOC   ||  req_from_OWL_to_SOC ;