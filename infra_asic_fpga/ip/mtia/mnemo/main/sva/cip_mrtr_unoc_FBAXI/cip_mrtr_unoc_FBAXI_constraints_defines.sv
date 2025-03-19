///////////////////////////////////////////////////
/// File: cip_mrtr_unoc_FBAXI_constraints_defines.sv
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

	logic																								cip0;
	logic																								cip1;

  logic                                              	all_req_types;
  logic                                              	all_scw;
  logic                                              	scw2pe_and_rtr;
  logic                                              	scw2pe;
  logic                                              	scw2rtr;
  logic                                              	scw2side;
  logic                                              	unicast2me;
  logic                                              	unicast2irtr;
  logic                                              	unicast2mrtr;
  logic                                              	unicast2crtr;
	logic																								unicast2rtr;
  logic                                              	non_scw;

	logic                                              	all_resp_types;
	logic                                              	scw_resp_cip1;
  logic                                              	all_scw_resp;
  logic                                              	scw_pe_and_rtr_resp;
  logic                                              	scw_pe_resp;
  logic                                              	scw_rtr_resp;
  logic                                              	scw_side_resp;
  logic                                              	unicast_pe_resp;
  logic                                              	unicast_irtr_resp;
  logic                                              	unicast_crtr_resp;
	logic																								unicast_rtr_resp;
  logic                                              	non_scw_resp;

	assign cip0																	        = !rtr_location.cip_id[0];
	assign cip1																	        =  rtr_location.cip_id[0];

	assign u_noc_north_in_tgtid_set									= (is_y_first? ((unoc_in_tgtid_ycoord >= rtr_location.ycoord                  ||
                                                                   unoc_in_tgtid_cip_id && cip0)                                &&
                                                                  (unoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))          &&
                                                                  (unoc_in_tgtid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1))          &&
                                                                  (unoc_in_tgtid_cip_id >= rtr_location.cip_id))
																																	 																															:
																																	
																																	((unoc_in_tgtid_ycoord >= rtr_location.ycoord                 ||
                                                                   unoc_in_tgtid_cip_id && cip0)                                &&
                                                                  (unoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))          &&
                                                                  (unoc_in_tgtid_xcoord inside {rtr_location.xcoord,
                                                                                                rtr_location.xcoord+1})         &&
                                                                  (unoc_in_tgtid_cip_id >= rtr_location.cip_id)))        				;

  assign u_noc_south_in_tgtid_set									= (is_y_first? ((unoc_in_tgtid_ycoord <= rtr_location.ycoord)                 ||
                                                                  (`is_south_edge_RTR && cip1                                    &&
                                                                 !(unoc_in_tgtid_ycoord > rtr_location.ycoord                   &&
                                                                   unoc_in_tgtid_xcoord inside {rtr_location.xcoord,
                                                                                                rtr_location.xcoord+1})))			  &&
                                                                 (unoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))           &&
                                                                 (unoc_in_tgtid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1)) 		
																																	 																															:
                                                                  
																																	(unoc_in_tgtid_ycoord <= rtr_location.ycoord)          				&&
                                                                  (unoc_in_tgtid_xcoord inside {rtr_location.xcoord,
                                                                                                rtr_location.xcoord+1})) 		    &&
																																	(unoc_in_tgtid_cip_id <= rtr_location.cip_id)         				;

  assign u_noc_east_in_tgtid_set									  = is_y_first? ((unoc_in_tgtid_ycoord >= rtr_location.ycoord)								&&
                                                                   (unoc_in_tgtid_xcoord <= (rtr_location.xcoord + 1))					&&
																																	 (unoc_in_tgtid_cip_id == rtr_location.cip_id))   		
																																	 																															:
                                                                  
																																	((unoc_in_tgtid_xcoord <= (rtr_location.xcoord + 1))    			&&
                                                                   (unoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1)))  			;

  assign u_noc_west_in_tgtid_set									  = is_y_first? ((unoc_in_tgtid_ycoord >= rtr_location.ycoord)								&&
                                                                   (unoc_in_tgtid_xcoord >= rtr_location.xcoord)					      &&
																																	 (unoc_in_tgtid_cip_id == rtr_location.cip_id))   		
																																	 																															:
                                                                  
																																	 (unoc_in_tgtid_xcoord >= rtr_location.xcoord)    			      &&
                                                                   (unoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))  			  ;

  assign u_noc_leaf0_in_tgtid_set									=             ((unoc_in_tgtid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1))       		&&
                                                                   (unoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1)))      	&&
                                                                 !((unoc_in_tgtid_xcoord == rtr_location.xcoord)              	&&
                                                                   (unoc_in_tgtid_ycoord == rtr_location.ycoord)              	&&
                                                                   (unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_DEFAULT))  						;

  assign u_noc_leaf1_in_tgtid_set									=             ((unoc_in_tgtid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1))       		&&
                                                                   (unoc_in_tgtid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1)))      	&&
                                                                 !((unoc_in_tgtid_xcoord == (rtr_location.xcoord + 1))        	&&
                                                                   (unoc_in_tgtid_ycoord == rtr_location.ycoord)              	&&
                                                                   (unoc_in_tgtid_zcoord == UNOC_ZCOORD_E_DEFAULT))  						;

    
  assign u_noc_north_in_srcid_set									= (is_y_first? ((unoc_in_srcid_ycoord < rtr_location.ycoord)           				&&
																											            (unoc_in_srcid_xcoord inside {rtr_location.xcoord      			  , 
                                                                                                 rtr_location.xcoord+1})) 			
																																																 																:
                                                                  
																																	(unoc_in_srcid_ycoord < rtr_location.ycoord)           				&&
                                                                  (unoc_in_srcid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1)))	    		&&
																																	(unoc_in_srcid_cip_id <= rtr_location.cip_id) 								;

  assign u_noc_south_in_srcid_set									= (is_y_first? ((unoc_in_srcid_ycoord > rtr_location.ycoord)           				&&
                                                                   (unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))   			&&
																											             (unoc_in_srcid_xcoord inside {rtr_location.xcoord      			, 
                                                                                                 rtr_location.xcoord+1})) 
																																																 																:
                                                                  
																																	(unoc_in_srcid_ycoord > rtr_location.ycoord)           				&&
                                                                   (unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))   			&&
                                                                  (unoc_in_srcid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1)))        &&
																																	 (unoc_in_srcid_cip_id >= rtr_location.cip_id)								;

  assign u_noc_east_in_srcid_set									  = is_y_first? ((unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))   			&&
                                                                   (unoc_in_srcid_xcoord > (rtr_location.xcoord + 1))     			&&
                                                                   (unoc_in_srcid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1)))	
																																	 																															:
                                                                  
																																	((unoc_in_srcid_xcoord > (rtr_location.xcoord + 1))     			&&
                                                                   (unoc_in_srcid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1))					&&
                                                                   ((unoc_in_srcid_ycoord == rtr_location.ycoord)								|| 				
																																	  (`is_south_edge_RTR && cip1													        &&
																																		 unoc_in_srcid_ycoord >= rtr_location.ycoord)))  						&&
                                                                    (unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))        ;

  assign u_noc_west_in_srcid_set									  = is_y_first? (unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))   			&&
                                                                   (unoc_in_srcid_xcoord < rtr_location.xcoord)           				
																																	 																															:
                                                                  
																																	((unoc_in_srcid_xcoord < rtr_location.xcoord)            			&&
                                                                   ((unoc_in_srcid_ycoord == rtr_location.ycoord)								|| 				
																																	  (`is_south_edge_RTR && cip1													        &&
																																		 unoc_in_srcid_ycoord >= rtr_location.ycoord)))  						&&
                                                                    (unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1))        ;

  assign u_noc_leaf0_in_srcid_set										= ((unoc_in_srcid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1))       							&&
                                                  	     (unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1)))      						&&
                                                  	   !((unoc_in_srcid_xcoord == rtr_location.xcoord)              						&&
                                                  	     (unoc_in_srcid_ycoord == rtr_location.ycoord)              						&&
                                                  	     (unoc_in_srcid_zcoord == UNOC_ZCOORD_E_DEFAULT))  											;

  assign u_noc_leaf1_in_srcid_set										= ((unoc_in_srcid_xcoord <= (CIP_RTR_GRID_COORD_X_END + 1))       							&&
                                                  	     (unoc_in_srcid_ycoord <= (CIP_RTR_GRID_COORD_Y_END + 1)))      						&&
                                                  	   !((unoc_in_srcid_xcoord == (rtr_location.xcoord + 1))        						&&
                                                  	     (unoc_in_srcid_ycoord == rtr_location.ycoord)              						&&
                                                  	     (unoc_in_srcid_zcoord == UNOC_ZCOORD_E_DEFAULT))  											;


  assign all_req_types                                =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR,
                                                                                        				 UNOC_ZCOORD_E_UNICAST_MAX2,
																																																 UNOC_ZCOORD_E_UNICAST_MAX2_MB,
                                                                                        cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};

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

  assign unicast2me                                   =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT};

  assign unicast2crtr                                 =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR};
    
  assign unicast2irtr                                 =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

  assign unicast2mrtr                                 =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

  assign unicast2rtr                                  =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR,
                                                                                      cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR};

  assign non_scw                                      =  unoc_in_tgtid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR,
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR,
																																																 UNOC_ZCOORD_E_UNICAST_MAX2,
																																																 UNOC_ZCOORD_E_UNICAST_MAX2_MB};

	assign all_resp_types                                =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_DEFAULT, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_CRTR, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR,
																																																 UNOC_ZCOORD_E_UNICAST_MAX2,
																																																 UNOC_ZCOORD_E_UNICAST_MAX2_MB,
                                                                                        cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};

  assign all_scw_resp                                      =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_PE_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW, 
                                                                                        cip_pkg::UNOC_ZCOORD_E_SIDE_SHARED_CW};

  assign scw_resp_cip1                                     =  unoc_in_srcid_zcoord inside {cip_pkg::UNOC_ZCOORD_E_CRTR_REGISTERS_SHARED_CW, 
                                                                                           cip_pkg::UNOC_ZCOORD_E_IRTR_REGISTERS_SHARED_CW};

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
                                                                                        cip_pkg::UNOC_ZCOORD_E_UNICAST_IRTR,
																																																 UNOC_ZCOORD_E_UNICAST_MAX2,
																																																 UNOC_ZCOORD_E_UNICAST_MAX2_MB};																																											

