/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_routing_equations.sv
//  This file contains irtr dnoc routing rules
/////////////////////////////////////////////////////////////////////////////////////////

    logic                                               dnoc_tgt_dir_valid;

    logic                                               req_y_first_routing;
    logic                                               resp_x_first_routing;

    logic                                               dnoc_in_e2n_tgt_set;
    logic                                               dnoc_in_e2s_tgt_set;
    logic                                               dnoc_in_e2l0_tgt_set;
    logic                                               dnoc_in_e2l1_tgt_set;

	logic                                               dnoc_in_w2e_tgt_set;

    logic                                               dnoc_in_n2w_tgt_set;
    logic                                               dnoc_in_n2e_tgt_set;
    logic                                               dnoc_in_n2s_tgt_set;
    logic                                               dnoc_in_n2l0_tgt_set;
    logic                                               dnoc_in_n2l1_tgt_set;

	logic                                               dnoc_in_s2n_tgt_set;
	logic                                               dnoc_in_s2e_tgt_set;

    logic                                               dnoc_in_l02e_tgt_set; 
    logic                                               dnoc_in_l02w_tgt_set; 
    logic                                               dnoc_in_l02n_tgt_set; 
    logic                                               dnoc_in_l02s_tgt_set; 
    logic                                               dnoc_in_l02l1_tgt_set;

    logic                                               dnoc_in_l12l0_tgt_set;

    logic                                               send_to_left_pe_instead;
    logic                                               send_to_right_pe_instead;

    logic                                               my_pe_disabled;

    logic                                               dnoc_in_src_from_LLC;
    logic                                               dnoc_in_tgt_to_LLC;


//------------------------------------------------------------------------------
//-- Valid target each source --
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//-- SOURCE: EAST --
//------------------------------------------------------------------------------

assign dnoc_in_e2w_tgt_set            = is_y_first   ? (dnoc_in_tgtid_xcoord  <  RTR_LOCATION_X_COORD       &&  dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD  &&  dnoc_in_tgt_within_cip) :
                                        is_x_first   ? (dnoc_in_tgtid_xcoord  <  RTR_LOCATION_X_COORD)      :  
                                        0;
                                                        
assign dnoc_in_e2n_tgt_set            = is_x_first   && (dnoc_in_tgtid_xcoord  inside  {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1} ) && ((dnoc_in_tgtid_ycoord < RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) || dnoc_in_to_north_cip);

assign dnoc_in_e2s_tgt_set            = is_x_first   && (dnoc_in_tgtid_xcoord  inside  {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1} ) && ((dnoc_in_tgtid_ycoord > RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip)|| dnoc_in_to_south_cip) ;

assign dnoc_in_e2l0_tgt_set           = is_y_first    ? (dnoc_in_tgtid_xcoord  == RTR_LOCATION_X_COORD      &&  dnoc_in_tgtid_ycoord ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) : 
                                        is_x_first    ? (dnoc_in_tgtid_xcoord  == RTR_LOCATION_X_COORD      &&  dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD  &&  dnoc_in_tgt_within_cip) : 
                                        0; 

assign dnoc_in_e2l1_tgt_set           = is_y_first    ? (dnoc_in_tgtid_xcoord  == (RTR_LOCATION_X_COORD+1)) &&  (dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) :
                                        is_x_first    ? (dnoc_in_tgtid_xcoord  == (RTR_LOCATION_X_COORD+1)) &&  (dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) : 
                                        0; 

//------------------------------------------------------------------------------
//-- SOURCE: WEST --
//------------------------------------------------------------------------------

assign dnoc_in_w2e_tgt_set           = is_y_first     ? (dnoc_in_tgtid_xcoord  >  RTR_LOCATION_X_COORD+1  &&  dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) :
                                       is_x_first     ? (dnoc_in_tgtid_xcoord  >  RTR_LOCATION_X_COORD+1) :
                                       0;
                                                         
//------------------------------------------------------------------------------
//-- SOURCE: NORTH --
//------------------------------------------------------------------------------

assign dnoc_in_n2w_tgt_set           = is_y_first     ? (dnoc_in_tgtid_xcoord   <  RTR_LOCATION_X_COORD      &&  dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) :
                                       is_x_first     ? (dnoc_in_tgtid_xcoord   <  RTR_LOCATION_X_COORD) :
                                       0;

assign dnoc_in_n2e_tgt_set           = is_y_first     ? (dnoc_in_tgtid_xcoord  >  RTR_LOCATION_X_COORD+1    &&  dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) :
                                       is_x_first     ? (dnoc_in_tgtid_xcoord  >  RTR_LOCATION_X_COORD+1) :
                                       0;

assign dnoc_in_n2s_tgt_set           = is_y_first     ? ( (dnoc_in_tgtid_ycoord  >  RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) || dnoc_in_to_south_cip) :
                                       is_x_first     ? (((dnoc_in_tgtid_ycoord  >  RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) || dnoc_in_to_south_cip) && (dnoc_in_tgtid_xcoord inside  {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1} )) :
                                       0;

assign dnoc_in_n2l0_tgt_set          = is_y_first     ? (dnoc_in_tgtid_xcoord  ==  RTR_LOCATION_X_COORD      &&  dnoc_in_tgtid_ycoord ==  RTR_LOCATION_Y_COORD   &&  dnoc_in_tgt_within_cip) :
                                       is_x_first     ? (dnoc_in_tgtid_xcoord  == RTR_LOCATION_X_COORD       &&  dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD    &&  dnoc_in_tgt_within_cip) :
                                       0;

assign dnoc_in_n2l1_tgt_set          = is_y_first     ? (dnoc_in_tgtid_xcoord  == (RTR_LOCATION_X_COORD+1))  &&  (dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) :
                                       is_x_first     ? (dnoc_in_tgtid_xcoord  == (RTR_LOCATION_X_COORD+1))  &&  (dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD &&  dnoc_in_tgt_within_cip) :
                                       0;

//------------------------------------------------------------------------------
//-- SOURCE: SOUTH --
//------------------------------------------------------------------------------
// TO DO: Review row wise multicast equations

assign dnoc_in_s2n_tgt_set          = is_y_first      ? ( dnoc_in_tgtid_ycoord  <  RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) || dnoc_in_to_north_cip :
                                      is_x_first      ? ((dnoc_in_tgtid_ycoord  <  RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) || dnoc_in_to_north_cip ) && (dnoc_in_tgtid_xcoord  inside  {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1} ) :
                                      0;

//------------------------------------------------------------------------------
//-- SOURCE: LEAF0 --
//------------------------------------------------------------------------------

assign dnoc_in_l02e_tgt_set         = is_y_first  && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  >  RTR_LOCATION_X_COORD+1   &&  dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) :
                                      is_x_first  && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  >  RTR_LOCATION_X_COORD+1   ) : 
                                                                                   0;

assign dnoc_in_l02w_tgt_set         = is_y_first  && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  <  RTR_LOCATION_X_COORD     &&  dnoc_in_tgtid_ycoord  ==  RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip):
                                      is_x_first  && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  <  RTR_LOCATION_X_COORD    ) : 
                                      0;

assign dnoc_in_l02n_tgt_set         = is_y_first  && !my_pe_disabled  ? ((dnoc_in_tgtid_ycoord  <  RTR_LOCATION_Y_COORD    &&  dnoc_in_tgt_within_cip) || dnoc_in_to_north_cip)   &&  
                                                                        ((d_noc_in_awnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_AW_W_channel) || (d_noc_in_rnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_R_channel)) :
                                      is_x_first  && !my_pe_disabled  ? ( dnoc_in_tgtid_xcoord  inside  {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1}) && ((dnoc_in_tgtid_ycoord  <  RTR_LOCATION_Y_COORD && !dnoc_in_to_south_cip) || dnoc_in_to_north_cip) &&
                                                                        ((d_noc_in_awnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_AW_W_channel) || (d_noc_in_rnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_R_channel)) : 
                                      0;

assign dnoc_in_l02s_tgt_set         = is_y_first  && !my_pe_disabled  ? ((dnoc_in_tgtid_ycoord  >  RTR_LOCATION_Y_COORD  &&  dnoc_in_tgt_within_cip) || dnoc_in_to_south_cip)    &&  
                                                                        ((d_noc_in_awnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_AW_W_channel) || (d_noc_in_rnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_R_channel)) :
                                      is_x_first  && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  inside  {RTR_LOCATION_X_COORD, RTR_LOCATION_X_COORD+1}) && ((dnoc_in_tgtid_ycoord  >  RTR_LOCATION_Y_COORD && !dnoc_in_to_north_cip)  || dnoc_in_to_south_cip)  &&  
                                                                        ((d_noc_in_awnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_AW_W_channel) || (d_noc_in_rnoc_id[1:0] == DEST_NOC_ID && dnoc_in_is_R_channel)) : 
                                      0;

assign dnoc_in_l02l1_tgt_set        = is_y_first  && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  ==  RTR_LOCATION_X_COORD+1 && dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD  && dnoc_in_tgt_within_cip) :
                                      is_x_first  && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  ==  RTR_LOCATION_X_COORD+1 && dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD  && dnoc_in_tgt_within_cip) : 
                                      0;

//------------------------------------------------------------------------------
//-- SOURCE: LEAF1 --
//------------------------------------------------------------------------------
// TO DO: Review row wise multicast equations

assign dnoc_in_l12l0_tgt_set        = dnoc_in_is_AW_W_channel && !my_pe_disabled  ? (dnoc_in_tgtid_xcoord  ==  RTR_LOCATION_X_COORD   &&  dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) :
                                      dnoc_in_is_R_channel && !my_pe_disabled   ? (dnoc_in_tgtid_xcoord  ==  RTR_LOCATION_X_COORD   &&  dnoc_in_tgtid_ycoord == RTR_LOCATION_Y_COORD && dnoc_in_tgt_within_cip) : 
                                      0;



    assign dnoc_tgt_dir_valid           =     ( DIR_VALUE == {EAST,WEST})                                    ? dnoc_in_e2w_tgt_set   :
                                              ((DIR_VALUE == {EAST,NORTH}) || (DIR_VALUE == {WEST,NORTH}))   ? dnoc_in_e2n_tgt_set   : 
                                              ((DIR_VALUE == {EAST,SOUTH}) || (DIR_VALUE == {WEST,SOUTH}))   ? dnoc_in_e2s_tgt_set   :
                                              ((DIR_VALUE == {EAST,LEAF0}) || (DIR_VALUE == {WEST,LEAF0}))   ?(dnoc_in_e2l0_tgt_set  && !left_pe_disabled)   :
                                              ((DIR_VALUE == {EAST,LEAF1}) || (DIR_VALUE == {WEST,LEAF1}))   ?(dnoc_in_e2l1_tgt_set  && !right_pe_disabled)  :
											  ( DIR_VALUE == {WEST,EAST})                                    ? dnoc_in_w2e_tgt_set   :
                                          	  ((DIR_VALUE == {NORTH,EAST}) || (DIR_VALUE == {SOUTH,EAST}))   ? dnoc_in_n2e_tgt_set   :
                                           	  ((DIR_VALUE == {NORTH,WEST}) || (DIR_VALUE == {SOUTH,WEST}))   ? dnoc_in_n2w_tgt_set   :
                                           	  ( DIR_VALUE == {NORTH,SOUTH})                                  ? dnoc_in_n2s_tgt_set  : 
                                           	  ((DIR_VALUE == {NORTH,LEAF0})|| (DIR_VALUE == {SOUTH,LEAF0}))  ? dnoc_in_n2l0_tgt_set  && !left_pe_disabled : 
                                           	  ((DIR_VALUE == {NORTH,LEAF1})|| (DIR_VALUE == {SOUTH,LEAF1}))  ? dnoc_in_n2l1_tgt_set  && !right_pe_disabled : 
                                           	  ( DIR_VALUE == {SOUTH,NORTH}) 	                             ? dnoc_in_s2n_tgt_set   : 
                                              ((DIR_VALUE == {LEAF0,EAST} ) || (DIR_VALUE == {LEAF1,EAST })) ? dnoc_in_l02e_tgt_set  :
                                              ((DIR_VALUE == {LEAF0,WEST} ) || (DIR_VALUE == {LEAF1,WEST })) ? dnoc_in_l02w_tgt_set  :
                                              ((DIR_VALUE == {LEAF0,NORTH}) || (DIR_VALUE == {LEAF1,NORTH})) ? dnoc_in_l02n_tgt_set  :
                                              ((DIR_VALUE == {LEAF0,SOUTH}) || (DIR_VALUE == {LEAF1,SOUTH})) ? dnoc_in_l02s_tgt_set  :
                                              ( DIR_VALUE == {LEAF0,LEAF1})                                  ? dnoc_in_l02l1_tgt_set :
                                              ( DIR_VALUE == {LEAF1,LEAF0})                                  ? dnoc_in_l12l0_tgt_set :
                                              0;

    assign my_pe_disabled               =     (DIR_VALUE[5:3] == LEAF0) ? left_pe_disabled : 
                                              (DIR_VALUE[5:3] == LEAF1) ? right_pe_disabled:0;

