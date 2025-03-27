/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_cnoc_input_signal_defines.sv
// This file contains mnm cnoc input signal defines
/////////////////////////////////////////////////////////////////////////////////////////
  logic                                                             c_noc_in_is_ar_channel;
  logic                                                             c_noc_in_is_b_channel;

  logic                                                             c_noc_in_arvalid;
  logic [mnm_pkg::MNM_DAXI_AR_ID_WIDTH-1:0]                         c_noc_in_arid;
  logic [mnm_pkg::MNM_DAXI_AR_LEN_WIDTH-1:0]                        c_noc_in_arlen;
  logic [mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:0]                       c_noc_in_araddr;
  logic [mnm_pkg::MNM_DAXI_AR_USER_WIDTH-1:0]                       c_noc_in_aruser;
  logic [mnm_pkg::MNM_DAXI_ARUSER_NOC_ID_WIDTH-1:0]                 c_noc_in_arnocid;
  mnm_pkg::coord_id_t                                               c_noc_in_arsrcid;
  mnm_pkg::coord_id_t                                               c_noc_in_artgtid;
  // logic [mnm_pkg::MNM_DAXI_ARUSER_HOST_SUBF_WIDTH-1:0]              c_noc_in_arhost;
  logic [mnm_pkg::MNM_DAXI_ARUSER_SIZE_WIDTH-1:0]                   c_noc_in_arsize;
  logic [mnm_pkg::MNM_DAXI_ARUSER_VC_WIDTH-1:0]                     c_noc_in_aruservc;
  // mnm_pkg::CC_OPCODE_e                                              c_noc_in_arcc_opcode;

  logic                                                             c_noc_in_bvalid;
  logic [mnm_pkg::MNM_UAXI_B_ID_WIDTH-1:0]                          c_noc_in_bid;
  logic [mnm_pkg::MNM_DAXI_B_USER_WIDTH-1:0]                        c_noc_in_buser;
  logic [mnm_pkg::MNM_DAXI_BUSER_NOC_ID_WIDTH-1:0]                  c_noc_in_bnocid;
  mnm_pkg::coord_id_t                                               c_noc_in_bsrcid;
  mnm_pkg::coord_id_t                                               c_noc_in_btgtid;
  logic [mnm_pkg::MNM_DAXI_BUSER_VC_WIDTH-1:0]                      c_noc_in_buservc;


  assign c_noc_in_is_ar_channel = (c_noc_in.channel == mnm_pkg::CNOC_CHANNEL_E_AR);
  assign c_noc_in_is_b_channel  = (c_noc_in.channel == mnm_pkg::CNOC_CHANNEL_E_B);
  
  assign c_noc_in_arvalid       = c_noc_in_valid && c_noc_in_is_ar_channel;
  assign c_noc_in_arid          = c_noc_in.payload.daxi_ar.id.iid;
  assign c_noc_in_arlen         = c_noc_in.payload.daxi_ar.len;
  assign c_noc_in_araddr        = c_noc_in.payload.daxi_ar.addr;
  assign c_noc_in_aruser        = c_noc_in.payload.daxi_ar.user;
  assign c_noc_in_arnocid       = c_noc_in.payload.daxi_ar.user.noc_id;
  assign c_noc_in_arsrcid       = c_noc_in.payload.daxi_ar.user.src_id;
  assign c_noc_in_artgtid       = c_noc_in.payload.daxi_ar.user.tgt_id;
  // assign c_noc_in_arhost        = c_noc_in.payload.daxi_ar.user.host;
  assign c_noc_in_arsize        = c_noc_in.payload.daxi_ar.user.size;
  assign c_noc_in_aruservc      = c_noc_in.payload.daxi_ar.user.vc;
  // assign c_noc_in_arcc_opcode   = c_noc_in.payload.daxi_ar.user.cc_opcode;

  assign c_noc_in_bvalid        = c_noc_in_valid && c_noc_in_is_b_channel;
  assign c_noc_in_bid           = c_noc_in.payload.daxi_b.id.iid;
  assign c_noc_in_buser         = c_noc_in.payload.daxi_b.user;
  assign c_noc_in_bnocid        = c_noc_in.payload.daxi_b.user.noc_id;
  assign c_noc_in_bsrcid        = c_noc_in.payload.daxi_b.user.src_id;
  assign c_noc_in_btgtid        = c_noc_in.payload.daxi_b.user.tgt_id;
  assign c_noc_in_buservc       = c_noc_in.payload.daxi_b.user.vc;