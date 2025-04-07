/////////////////////////////////////////////////////////////////////////////////////////
// File: cip_rtr_location_defines.sv
// This file contains cip router locations
/////////////////////////////////////////////////////////////////////////////////////////

// logic                                              	  is_north_edge_RTR;
// logic                                              		is_south_edge_RTR;
// logic                                              		is_west_edge_RTR ;
// logic                                              		is_east_edge_RTR ;

// logic                                              		is_ne_corner_RTR;
// logic                                              		is_n_top_RTR;
// logic                                              		is_nw_corner_RTR;
// logic                                              		is_se_corner_RTR;
// logic                                              		is_sw_corner_RTR;

// logic                                              		is_cntr_RTR;

// assign is_north_edge_RTR                          	= (rtr_location.ycoord == cip_pkg::CIP_RTR_GRID_COORD_Y_START) ;
// assign is_south_edge_RTR                            = (rtr_location.ycoord == cip_pkg::CIP_RTR_GRID_COORD_Y_END)   ;
// assign is_west_edge_RTR                             = (rtr_location.xcoord == cip_pkg::CIP_RTR_GRID_COORD_X_START) ;
// assign is_east_edge_RTR                             = (rtr_location.xcoord == cip_pkg::CIP_RTR_GRID_COORD_X_END-1) ;

// assign is_ne_corner_RTR                             = is_north_edge_RTR	&& is_east_edge_RTR ;
// assign is_n_top_RTR                                 = is_north_edge_RTR	&& !is_east_edge_RTR && !is_west_edge_RTR;
// assign is_nw_corner_RTR                             = is_north_edge_RTR	&& is_west_edge_RTR ;
// assign is_se_corner_RTR                             = is_south_edge_RTR	&& is_east_edge_RTR ;
// assign is_sw_corner_RTR                             = is_south_edge_RTR	&& is_west_edge_RTR ;

// assign is_cntr_RTR																	=	!is_north_edge_RTR && !is_south_edge_RTR 	&&
// 																											!is_east_edge_RTR  &&	!is_west_edge_RTR		;


`define                                             is_north_edge_RTR (RTR_LOCATION_Y_COORD == CIP_RTR_GRID_COORD_Y_START)
`define                                             is_south_edge_RTR (RTR_LOCATION_Y_COORD == CIP_RTR_GRID_COORD_Y_END)   
`define                                             is_west_edge_RTR  (RTR_LOCATION_X_COORD == CIP_RTR_GRID_COORD_X_START) 
`define                                             is_east_edge_RTR  (RTR_LOCATION_X_COORD == (CIP_RTR_GRID_COORD_X_END-1)) 

`define                                             is_south_edge_scw_RTR (RTR_LOCATION_Y_COORD == CIP_RTR_GRID_COORD_Y_END-1)   

`define                                             is_ne_corner_RTR  ((`is_north_edge_RTR) && (`is_east_edge_RTR))
`define                                             is_nw_corner_RTR  ((`is_north_edge_RTR) && (`is_west_edge_RTR))
`define                                             is_se_corner_RTR  ((`is_south_edge_RTR) && (`is_east_edge_RTR))
`define                                             is_sw_corner_RTR  ((`is_south_edge_RTR) && (`is_west_edge_RTR))
`define                                             is_n_top_RTR      ((`is_north_edge_RTR) && (!`is_nw_corner_RTR) && (!`is_ne_corner_RTR))
`define                                             is_cntr_col_RTR   (RTR_LOCATION_X_COORD == CIP_RTR_GRID_COORD_X_CENTER)

`define                                             is_cntr_RTR      !((`is_north_edge_RTR) || (`is_south_edge_RTR) || (`is_west_edge_RTR) || (`is_east_edge_RTR))
