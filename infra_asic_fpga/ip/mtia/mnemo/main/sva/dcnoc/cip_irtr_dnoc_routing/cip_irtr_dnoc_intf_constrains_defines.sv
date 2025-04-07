/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_intf_constrains_defines.sv
//  This file contains irtr dnoc interface constrains
/////////////////////////////////////////////////////////////////////////////////////////

//------------------------------------------------------------------------------
//-- logic
//------------------------------------------------------------------------------

    logic                                               d_noc_east_in_tgt_set;
    logic                                               d_noc_west_in_tgt_set;
    logic                                               d_noc_north_in_tgt_set;
    logic                                               d_noc_south_in_tgt_set;
    logic                                               d_noc_leaf0_in_tgt_set;
    logic                                               d_noc_leaf1_in_tgt_set;

    logic                                               d_noc_east_in_src_set;
    logic                                               d_noc_west_in_src_set;
    logic                                               d_noc_north_in_src_set;
    logic                                               d_noc_south_in_src_set;
    logic                                               d_noc_leaf0_in_src_set;
    logic                                               d_noc_leaf1_in_src_set;
    logic                                               void_src_coords;
    logic                                               void_tgt_coords;


    assign    d_noc_east_in_tgt_set                      = is_y_first  ? dnoc_in_tgtid_xcoord <= RTR_LOCATION_X_COORD+1 && dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip:
                                                           is_x_first  ? dnoc_in_tgtid_xcoord <= RTR_LOCATION_X_COORD+1 :1;

    assign    d_noc_west_in_tgt_set                      = is_y_first  ? dnoc_in_tgtid_xcoord >= RTR_LOCATION_X_COORD && dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip:
                                                           is_x_first  ? dnoc_in_tgtid_xcoord >= RTR_LOCATION_X_COORD :1;    
    
    assign    d_noc_north_in_tgt_set                     = is_y_first  ? (dnoc_in_tgtid_ycoord >= RTR_LOCATION_Y_COORD) || dnoc_in_to_south_cip:
                                                           is_x_first  ?  dnoc_in_tgtid_xcoord inside {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1} :1;     

    assign    d_noc_south_in_tgt_set                     = is_y_first  || x_first_exception ? (dnoc_in_tgtid_ycoord <= RTR_LOCATION_Y_COORD) || dnoc_in_to_north_cip:
                                                           is_x_first                       ?  dnoc_in_tgtid_xcoord inside {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1} :1;    

    assign    d_noc_east_in_src_set                      = is_y_first  ? dnoc_in_srcid_xcoord > RTR_LOCATION_X_COORD+1 :
                                                           is_x_first  ? dnoc_in_srcid_xcoord > RTR_LOCATION_X_COORD+1 && dnoc_in_srcid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip :1;

    assign    d_noc_west_in_src_set                      = is_y_first  ? dnoc_in_srcid_xcoord < RTR_LOCATION_X_COORD :
                                                           is_x_first  ? dnoc_in_srcid_xcoord < RTR_LOCATION_X_COORD && dnoc_in_srcid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip :1;    
    
    assign    d_noc_north_in_src_set                     = is_y_first  ? ((dnoc_in_srcid_ycoord < RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip) || dnoc_north_in_from_cip_0_to_cip_1) && dnoc_in_srcid_xcoord == RTR_LOCATION_X_COORD :
                                                           is_x_first  ? ((dnoc_in_srcid_ycoord < RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip) || dnoc_north_in_from_cip_0_to_cip_1) :1;    

    assign    d_noc_south_in_src_set                     = is_y_first  || x_first_exception? ((dnoc_in_srcid_ycoord > RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip) || dnoc_south_in_from_cip_1_to_cip_0) && dnoc_in_srcid_xcoord == RTR_LOCATION_X_COORD :
                                                           is_x_first                          ? ((dnoc_in_srcid_ycoord > RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip) || dnoc_south_in_from_cip_1_to_cip_0) :1;    

    assign    d_noc_leaf0_in_src_set                     = dnoc_in_srcid_xcoord == RTR_LOCATION_X_COORD   && dnoc_in_srcid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip ;    
    assign    d_noc_leaf1_in_src_set                     = dnoc_in_srcid_xcoord == RTR_LOCATION_X_COORD+1 && dnoc_in_srcid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_src_within_cip ;     


    assign    void_tgt_coords                            =  (dnoc_in_tgtid_xcoord == 'd0 && dnoc_in_tgtid_ycoord == 'd0) ||
                                                            (dnoc_in_tgtid_xcoord == 'd0 && dnoc_in_tgtid_ycoord == 'd1) || 
                                                            (dnoc_in_tgtid_xcoord == 'd7 && dnoc_in_tgtid_ycoord == 'd0) || 
                                                            (dnoc_in_tgtid_xcoord == 'd7 && dnoc_in_tgtid_ycoord == 'd1) || 
                                                            (dnoc_in_tgtid_xcoord == 'd0 && dnoc_in_tgtid_ycoord == 'd10) || 
                                                            (dnoc_in_tgtid_xcoord == 'd0 && dnoc_in_tgtid_ycoord == 'd11) || 
                                                            (dnoc_in_tgtid_xcoord == 'd7 && dnoc_in_tgtid_ycoord == 'd10) || 
                                                            (dnoc_in_tgtid_xcoord == 'd7 && dnoc_in_tgtid_ycoord == 'd11) ; 

    assign    void_src_coords                            =  (dnoc_in_srcid_xcoord == 'd0 && dnoc_in_srcid_ycoord == 'd0) ||
                                                            (dnoc_in_srcid_xcoord == 'd0 && dnoc_in_srcid_ycoord == 'd1) || 
                                                            (dnoc_in_srcid_xcoord == 'd7 && dnoc_in_srcid_ycoord == 'd0) || 
                                                            (dnoc_in_srcid_xcoord == 'd7 && dnoc_in_srcid_ycoord == 'd1) || 
                                                            (dnoc_in_srcid_xcoord == 'd0 && dnoc_in_srcid_ycoord == 'd10) || 
                                                            (dnoc_in_srcid_xcoord == 'd0 && dnoc_in_srcid_ycoord == 'd11) || 
                                                            (dnoc_in_srcid_xcoord == 'd7 && dnoc_in_srcid_ycoord == 'd10) || 
                                                            (dnoc_in_srcid_xcoord == 'd7 && dnoc_in_srcid_ycoord == 'd11) ; 
