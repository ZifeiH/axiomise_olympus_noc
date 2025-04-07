/////////////////////////////////////////////////////////////////////////////////////////
/// File: cip_irtr_dnoc_params.sv
//  This file contains irtr dnoc routing parmeters
/////////////////////////////////////////////////////////////////////////////////////////

    parameter  EW_INTF_CREDITS_DNOC                         = cip_pkg::CIP_IRTR_EW_INTF_CREDITS_DNOC;
    parameter  NS_INTF_CREDITS_DNOC                         = cip_pkg::CIP_IRTR_NS_INTF_CREDITS_DNOC;
    parameter  FI_INTF_CREDITS_DNOC                         = cip_pkg::CIP_IRTR_FI_INTF_CREDITS_DNOC;
    parameter  NUM_EW_DNOC                                  = cip_pkg::CIP_IRTR_NUM_EW_DNOC;
    parameter  NUM_NS_DNOC                                  = cip_pkg::CIP_IRTR_NUM_NS_DNOC;
    parameter  NUM_DNOC_FROM_FI                             = cip_pkg::CIP_IRTR_NUM_DNOC_FROM_FI;
    parameter  NUM_DNOC_TO_FI                               = cip_pkg::CIP_IRTR_NUM_DNOC_TO_FI;
    parameter  TOTAL_NUM_VC                                 = cip_pkg::CIP_IRTR_DNOC_TOTAL_NUM_VC;
    parameter  REQ_TOTAL_NUM_VC                             = cip_pkg::CIP_IRTR_DNOC_AWW_NUM_VC;
    parameter  RESP_TOTAL_NUM_VC                            = cip_pkg::CIP_IRTR_DNOC_R_NUM_VC;
    parameter  NUM_DIRECTIONS                               = cip_pkg::CIP_RTR_NUM_DIRECTIONS;
    parameter  REQ_FIFO_CHECK_BIT                           = 57;
    parameter  RESP_FIFO_CHECK_BIT                          = 11;
    parameter  LANES_CAN_TURN                               = 1;
    parameter  NOC_TYPE                                     = "IODNOC";

    `ifdef IS_CENTER_RTR
      parameter  FLOW_CONTROL_EAST    = 1;
      parameter  FLOW_CONTROL_WEST    = 1;
      parameter  FLOW_CONTROL_NORTH   = 1;
      parameter  FLOW_CONTROL_SOUTH   = 1;
      parameter  FLOW_CONTROL_LEAF0   = 1;
      parameter  FLOW_CONTROL_LEAF1   = 1;
    `else 
      parameter  FLOW_CONTROL_EAST    = 0;
      parameter  FLOW_CONTROL_WEST    = 0;
      parameter  FLOW_CONTROL_NORTH   = 0;
      parameter  FLOW_CONTROL_SOUTH   = 0;
      parameter  FLOW_CONTROL_LEAF0   = 0;
      parameter  FLOW_CONTROL_LEAF1   = 0;
    `endif 

    parameter [NUM_EW_DNOC-1:0][3-1:0] max_reqs_east        = {3'd3, 3'd3, 3'd3, 3'd3};
    parameter [NUM_EW_DNOC-1:0][3-1:0] max_reqs_west        = {3'd3, 3'd3, 3'd3, 3'd3};
    parameter [NUM_NS_DNOC-1:0][3-1:0] max_reqs_north       = {3'd3, 3'd3, 3'd3, 3'd3,
                                                                3'd3, 3'd3, 3'd3, 3'd3};
    parameter [NUM_NS_DNOC-1:0][3-1:0] max_reqs_south       = {3'd3, 3'd3, 3'd3, 3'd3,
                                                                3'd3, 3'd3, 3'd3, 3'd3};

    parameter max_reqs_leaf0       = 3'd3;
    parameter max_reqs_leaf1       = 3'd3;
    
    parameter [NUM_DIRECTIONS-1:0][NUM_DIRECTIONS-1:0][TOTAL_NUM_VC-1:0]  ILLEGAL_TGT_ID_TABLE   = 
                                                                //                   leaf1                                            leaf0                                            east                                           south                                                 west                                                        north                                                    
                                                              {{{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}}, {RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}}}, //leaf1
                                                               {{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}}, {RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}}}, //leaf0
                                                               {{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}}, {RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}}, //east
                                                               {{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}}, {RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}}, // south
                                                               {{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}}, {RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}}, // west
                                                               {{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}}, {RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}}}};// north
    
    parameter [NUM_DIRECTIONS-1:0][NUM_DIRECTIONS-1:0][TOTAL_NUM_VC-1:0]  ILLEGAL_TGT_ID_TABLE_NOTURN   =   
                                                                //                   leaf1                                            leaf0                                            east                                           south                                                      west                                            north                                                    
                                                              {{{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}}}, //leaf1
                                                               {{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b1}}}}, //leaf0
                                                               {{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}}}, //east
                                                               {{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}}, // south
                                                               {{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}}}, // west
                                                               {{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}},{{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b1}}}}};// north
    
    parameter [7-1:0][TOTAL_NUM_VC-1:0]  LEAF_TX_ILLEGAL_TRUNS_TABLE    = { {{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}, //6
                                                                            {{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}, //5
                                                                            {{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}}, //4
                                                                            {{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}, //3
                                                                            {{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}, //2
                                                                            {{REQ_TOTAL_NUM_VC{1'b1}},{RESP_TOTAL_NUM_VC{1'b0}}}, //1
                                                                            {{REQ_TOTAL_NUM_VC{1'b0}},{RESP_TOTAL_NUM_VC{1'b0}}}}; //0
