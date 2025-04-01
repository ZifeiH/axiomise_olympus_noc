///////////////////////////////////////////////////
/// File: cip_rtr_unoc_credit_release_sva.sv
/// This file contains the defines for assumptions
///////////////////////////////////////////////////

  logic                                               u_noc_east_in_tgtid_set;
  logic                                               u_noc_west_in_tgtid_set;
  logic                                               u_noc_north_in_tgtid_set;
  logic                                               u_noc_south_in_tgtid_set;
  logic                                               u_noc_leaf0_in_tgtid_set;
  logic                                               u_noc_leaf1_in_tgtid_set;

  logic                                               u_noc_east_in_srcid_set;
  logic                                               u_noc_west_in_srcid_set;
  logic                                               u_noc_north_in_srcid_set;
  logic                                               u_noc_south_in_srcid_set;
  logic                                               u_noc_leaf0_in_srcid_set;
  logic                                               u_noc_leaf1_in_srcid_set;

	logic                                              	  is_north_edge_RTR;
  logic                                              		is_south_edge_RTR;
  logic                                              		is_west_edge_RTR ;
  logic                                              		is_east_edge_RTR ;
  logic                                                 is_cntr_col_RTR;
  logic                                              		is_ne_corner_RTR;
  logic                                              		is_nw_corner_RTR;
  logic                                              		is_se_corner_RTR;
  logic                                              		is_sw_corner_RTR;
  logic                                              		is_cntr_RTR;
  logic                                              		is_top_n_RTR;

	logic																									cip0;
	logic																									cip1;

  logic                                              		all_req_types;
  logic                                              		all_scw;
  logic                                              		scw2pe_and_rtr;
  logic                                              		scw2pe;
  logic                                              		scw2rtr;
  logic                                              		scw2side;
  logic                                              		unicast2pe;
  logic                                              		unicast2irtr;
  logic                                              		unicast2crtr;
	logic																									unicast2rtr;
  logic                                              		non_scw;

	logic                                              		all_resp_types;
  logic                                              		all_scw_resp;
  logic                                              		scw_pe_and_rtr_resp;
  logic                                              		scw_pe_resp;
  logic                                              		scw_rtr_resp;
  logic                                              		scw_side_resp;
  logic                                              		unicast_pe_resp;
  logic                                              		unicast_irtr_resp;
  logic                                              		unicast_crtr_resp;
	logic																									unicast_rtr_resp;
  logic                                              		non_scw_resp;
  logic                                                 req_any_unicast2max;
  logic                                                 resp_any_unicast2max;

  logic                                                 scw_aw_originator_n;
  logic                                                 scw_aw_originator_w;
  logic                                                 scw_aw_originator_e;
  logic                                                 scw_org_set_n;
  logic                                                 scw_org_set_w;
  logic                                                 scw_org_set_e;

	assign is_north_edge_RTR                          	= rtr_location.ycoord == cip_pkg::CIP_RTR_GRID_COORD_Y_START ;
  assign is_south_edge_RTR                            = rtr_location.ycoord == cip_pkg::CIP_RTR_GRID_COORD_Y_END   ;
  assign is_west_edge_RTR                             = rtr_location.xcoord == cip_pkg::CIP_RTR_GRID_COORD_X_START ;
  assign is_east_edge_RTR                             = rtr_location.xcoord == cip_pkg::CIP_RTR_GRID_COORD_X_END-1 ;
  assign is_cntr_col_RTR                              = rtr_location.xcoord == cip_pkg::CIP_RTR_GRID_COORD_X_CENTER;

  assign is_ne_corner_RTR                             = is_north_edge_RTR	&& is_east_edge_RTR ;
  assign is_nw_corner_RTR                             = is_north_edge_RTR	&& is_west_edge_RTR ;
  assign is_se_corner_RTR                             = is_south_edge_RTR	&& is_east_edge_RTR ;
  assign is_sw_corner_RTR                             = is_south_edge_RTR	&& is_west_edge_RTR ;
	assign is_cntr_RTR																	=	!is_north_edge_RTR && !is_south_edge_RTR 	&&
																												!is_east_edge_RTR  &&	!is_west_edge_RTR		;
	assign is_top_n_RTR																	=	is_north_edge_RTR	&& !is_nw_corner_RTR && !is_ne_corner_RTR;

	assign cip0																	        = !rtr_location.cip_id[0];
	assign cip1																	        =  rtr_location.cip_id[0];

  assign scw_aw_originator_n                          = is_west_edge_RTR? {unoc_in_srcid_cip_id,unoc_in_srcid_xcoord,unoc_in_srcid_ycoord,unoc_in_srcid_zcoord} inside {{2'b00,EXTM_NW_UNOC_COORD}} :
                                                        is_cntr_col_RTR?  {unoc_in_srcid_cip_id,unoc_in_srcid_xcoord,unoc_in_srcid_ycoord,unoc_in_srcid_zcoord} inside {{2'b00,EXTM_N_UNOC_COORD}}  :
                                                        is_east_edge_RTR? {unoc_in_srcid_cip_id,unoc_in_srcid_xcoord,unoc_in_srcid_ycoord,unoc_in_srcid_zcoord} inside {{2'b00,EXTM_NE_UNOC_COORD}} : 'h1;

  assign scw_aw_originator_w                          = is_cntr_col_RTR && !is_south_edge_RTR ?  {unoc_in_srcid_cip_id,unoc_in_srcid_xcoord,unoc_in_srcid_ycoord,unoc_in_srcid_zcoord} inside {{2'b00,EXTM_NW_UNOC_COORD}}  :
                                                        is_east_edge_RTR && !is_south_edge_RTR?  {unoc_in_srcid_cip_id,unoc_in_srcid_xcoord,unoc_in_srcid_ycoord,unoc_in_srcid_zcoord} inside {{2'b00,EXTM_NW_UNOC_COORD}, {2'b00,EXTM_N_UNOC_COORD}} : 'h1;

  assign scw_aw_originator_e                          = is_cntr_col_RTR && !is_south_edge_RTR ?  {unoc_in_srcid_cip_id,unoc_in_srcid_xcoord,unoc_in_srcid_ycoord,unoc_in_srcid_zcoord} inside {{2'b00,EXTM_NE_UNOC_COORD}}  :
                                                        is_west_edge_RTR && !is_south_edge_RTR?  {unoc_in_srcid_cip_id,unoc_in_srcid_xcoord,unoc_in_srcid_ycoord,unoc_in_srcid_zcoord} inside {{2'b00,EXTM_NE_UNOC_COORD}, {2'b00,EXTM_N_UNOC_COORD}} : 'h1;

	assign u_noc_north_in_tgtid_set									= (is_y_first? (((unoc_in_tgtid_ycoord >= rtr_location.ycoord)								||
																																	 (unoc_in_tgtid_cip_id > rtr_location.cip_id)                 ||
                                                                   (is_north_edge_RTR && cip0                                   && 
                                                                  !(unoc_in_tgtid_ycoord < rtr_location.ycoord                  &&
                                                                    unoc_in_tgtid_xcoord inside {rtr_location.xcoord,
                                                                                                 rtr_location.xcoord+1})))      &&
																											             (unoc_in_tgtid_ycoord <= (RTR_GRID_COORD_Y_END + 1))   			&&
                                                                   (unoc_in_tgtid_xcoord <= (RTR_GRID_COORD_X_END + 1)))  		
																																	 																															:
																																	
																																	((((unoc_in_tgtid_ycoord >= rtr_location.ycoord               ||
                                                                      unoc_in_tgtid_cip_id > rtr_location.cip_id) 							&&
                                                                   (unoc_in_tgtid_xcoord inside {rtr_location.xcoord,
                                                                                                 rtr_location.xcoord+1}))			  ||
																																	 (is_north_edge_RTR	&& cip0														        &&
																																	!(unoc_in_tgtid_ycoord < rtr_location.ycoord                  &&
                                                                    unoc_in_tgtid_xcoord inside {rtr_location.xcoord,
                                                                                                 rtr_location.xcoord+1})))      &&
                                                                   (unoc_in_tgtid_ycoord <= (RTR_GRID_COORD_Y_END + 1))         &&
                                                                   (unoc_in_tgtid_xcoord <= (RTR_GRID_COORD_X_END + 1))))				&&
																																	 (unoc_in_tgtid_cip_id >= rtr_location.cip_id)         				;

  assign u_noc_south_in_tgtid_set									= (is_y_first? (unoc_in_tgtid_ycoord <= rtr_location.ycoord)									&&
                                                                 (unoc_in_tgtid_xcoord <= (RTR_GRID_COORD_X_END + 1)) 		
																																	 																															:
                                                                  
																																	(unoc_in_tgtid_ycoord <= rtr_location.ycoord)          				&&
                                                                  (unoc_in_tgtid_xcoord inside {rtr_location.xcoord,
                                                                                                 rtr_location.xcoord+1})) 		  &&
																																	(unoc_in_tgtid_cip_id <= rtr_location.cip_id)         				;

  assign u_noc_east_in_tgtid_set									  = is_y_first? (((unoc_in_tgtid_ycoord == rtr_location.ycoord)								||
																																		(is_north_edge_RTR																					&&
																																		unoc_in_tgtid_ycoord <= rtr_location.ycoord))								&&
                                                                   (unoc_in_tgtid_xcoord <= (rtr_location.xcoord + 1))					&&
																																	 (unoc_in_tgtid_cip_id == rtr_location.cip_id))   		
																																	 																															:
                                                                  
																																	((unoc_in_tgtid_xcoord <= (rtr_location.xcoord + 1))    			&&
                                                                   (unoc_in_tgtid_ycoord <= (RTR_GRID_COORD_Y_END + 1)))  			;

  assign u_noc_west_in_tgtid_set									  = is_y_first? (((unoc_in_tgtid_ycoord == rtr_location.ycoord)          			||
																																		(is_north_edge_RTR																					&&
																																		unoc_in_tgtid_ycoord <= rtr_location.ycoord))								&&
                                                                   (unoc_in_tgtid_xcoord >= rtr_location.xcoord)								&&
																																	 (unoc_in_tgtid_cip_id == rtr_location.cip_id))         		
																																	 																															:
                                                                  
																																	((unoc_in_tgtid_xcoord >= rtr_location.xcoord)          			&&
                                                                   (unoc_in_tgtid_ycoord <= (RTR_GRID_COORD_Y_END + 1)))  			;

  assign u_noc_leaf0_in_tgtid_set									=             ((unoc_in_tgtid_xcoord <= (RTR_GRID_COORD_X_END + 1))       		&&
                                                                   (unoc_in_tgtid_ycoord <= (RTR_GRID_COORD_Y_END + 1)))      	&&
                                                                 !((unoc_in_tgtid_xcoord == rtr_location.xcoord)              	&&
                                                                   (unoc_in_tgtid_ycoord == rtr_location.ycoord)              	&&
                                                                   (unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_DEFAULT))  						;

  assign u_noc_leaf1_in_tgtid_set									=             ((unoc_in_tgtid_xcoord <= (RTR_GRID_COORD_X_END + 1))       		&&
                                                                   (unoc_in_tgtid_ycoord <= (RTR_GRID_COORD_Y_END + 1)))      	&&
                                                                 !((unoc_in_tgtid_xcoord == (rtr_location.xcoord + 1))        	&&
                                                                   (unoc_in_tgtid_ycoord == rtr_location.ycoord)              	&&
                                                                   (unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_DEFAULT))  						;

  
  assign u_noc_north_in_srcid_set									= (is_y_first? ((unoc_in_srcid_ycoord < rtr_location.ycoord)           				&&
																											             (unoc_in_srcid_xcoord inside {rtr_location.xcoord      			, 
                                                                                                 rtr_location.xcoord+1})) 			
																																																 																:
                                                                  
																																	(unoc_in_srcid_ycoord < rtr_location.ycoord)           				&&
                                                                   ((unoc_in_srcid_xcoord <= (RTR_GRID_COORD_X_END + 1))				||
																																	 (is_north_edge_RTR && cip0														&&																		
																																	 unoc_in_srcid_xcoord inside {rtr_location.xcoord      				, 
                                                                                                 rtr_location.xcoord+1})))			&&
																																	 (unoc_in_srcid_cip_id <= rtr_location.cip_id)								;

  assign u_noc_south_in_srcid_set									= (is_y_first? ((unoc_in_srcid_ycoord > rtr_location.ycoord)           				&&
                                                                   (unoc_in_srcid_ycoord <= (RTR_GRID_COORD_Y_END + 1))   			&&
																											             (unoc_in_srcid_xcoord inside {rtr_location.xcoord      			, 
                                                                                                 rtr_location.xcoord+1})) 
																																																 																:
                                                                  
																																	(unoc_in_srcid_ycoord > rtr_location.ycoord)           				&&
                                                                   (unoc_in_srcid_ycoord <= (RTR_GRID_COORD_Y_END + 1))   			&&
                                                                   (unoc_in_srcid_xcoord <= (RTR_GRID_COORD_X_END + 1)))  			&&
																																	 (unoc_in_srcid_cip_id >= rtr_location.cip_id)								;

  assign u_noc_east_in_srcid_set									  = is_y_first? ((unoc_in_srcid_ycoord <= (RTR_GRID_COORD_Y_END + 1))   			&&
                                                                   (unoc_in_srcid_xcoord > (rtr_location.xcoord + 1))     			&&
                                                                   (unoc_in_srcid_xcoord <= (RTR_GRID_COORD_X_END + 1)))	
																																	 																															:
                                                                  
																																	((unoc_in_srcid_xcoord > (rtr_location.xcoord + 1))     			&&
                                                                   (unoc_in_srcid_xcoord <= (RTR_GRID_COORD_X_END + 1))					&&
                                                                   ((unoc_in_srcid_ycoord == rtr_location.ycoord)								|| 				
																																	  (is_north_edge_RTR && cip0													&&
																																		 unoc_in_srcid_ycoord <= rtr_location.ycoord)))  						;

  assign u_noc_west_in_srcid_set									  = is_y_first? ((unoc_in_srcid_ycoord <= (RTR_GRID_COORD_Y_END + 1))   			&&
                                                                   (unoc_in_srcid_xcoord <   rtr_location.xcoord))     					:
                                                                  ((unoc_in_srcid_xcoord <   rtr_location.xcoord)     					&&
                                                                   ((unoc_in_srcid_ycoord == rtr_location.ycoord)								|| 				
																																	  (is_north_edge_RTR && cip0													&&
																																		 unoc_in_srcid_ycoord <= rtr_location.ycoord)))  						;

  assign u_noc_leaf0_in_srcid_set										= ((unoc_in_srcid_xcoord <= (RTR_GRID_COORD_X_END + 1))       							&&
                                                  	     (unoc_in_srcid_ycoord <= (RTR_GRID_COORD_Y_END + 1)))      						&&
                                                  	   !((unoc_in_srcid_xcoord == rtr_location.xcoord)              						&&
                                                  	     (unoc_in_srcid_ycoord == rtr_location.ycoord)              						&&
                                                  	     (unoc_in_srcid_zcoord == UNOC_ZCOORD_E_DEFAULT))  											;

  assign u_noc_leaf1_in_srcid_set										= ((unoc_in_srcid_xcoord <= (RTR_GRID_COORD_X_END + 1))       							&&
                                                  	     (unoc_in_srcid_ycoord <= (RTR_GRID_COORD_Y_END + 1)))      						&&
                                                  	   !((unoc_in_srcid_xcoord == (rtr_location.xcoord + 1))        						&&
                                                  	     (unoc_in_srcid_ycoord == rtr_location.ycoord)              						&&
                                                  	     (unoc_in_srcid_zcoord == UNOC_ZCOORD_E_DEFAULT))  											;

  assign scw_org_set_n                              = (unoc_in_is_AW_W_channel && all_scw) ? scw_aw_originator_n            :
                                                      'h1;
  assign scw_org_set_w                              = (unoc_in_is_AW_W_channel && all_scw) ? scw_aw_originator_w            :
                                                      'h1;
  assign scw_org_set_e                              = (unoc_in_is_AW_W_channel && all_scw) ? scw_aw_originator_e            :
                                                      'h1;

  assign all_req_types                                =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR,
                                                                                        cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};

  assign req_any_unicast2max    =                   unoc_in_tgtid_zcoord inside {
                                                            UNOC_ZCOORD_E_UNICAST_MAX2,
                                                            UNOC_ZCOORD_E_UNICAST_MAX2_MB
                                                        };

  assign all_scw                                      =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};


  assign scw2pe_and_rtr                               =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW,
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW};

  assign scw2pe                                       =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW};
                                                                                        
  assign scw2rtr                                      =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW};

  assign scw2side                                     =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};

  assign unicast2pe                                   =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT};

  assign unicast2crtr                                 =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR};
    
  assign unicast2irtr                                 =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

  assign unicast2rtr                                  =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

  assign non_scw                                      =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

	assign all_resp_types                                =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR,
                                                                                        cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};

  assign all_scw_resp                                      =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};


  assign scw_pe_and_rtr_resp                               =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW,
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW};

  assign scw_pe_resp                                       =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW};
                                                                                        
  assign scw_rtr_resp                                      =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW};

  assign scw_side_resp                                     =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};

  assign unicast_pe_resp                                   =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT};

  assign unicast_crtr_resp                                 =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR};
    
  assign unicast_irtr_resp                                 =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

  assign unicast_rtr_resp                                  =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

  assign non_scw_resp                                      =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};	

  assign resp_any_unicast2max     =                    unoc_in_srcid_zcoord inside {
                                                            UNOC_ZCOORD_E_UNICAST_MAX2,
                                                            UNOC_ZCOORD_E_UNICAST_MAX2_MB
                                                        };                                                                                      																																										

