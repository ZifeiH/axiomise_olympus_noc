/////////////////////////////////////////////////////////////////////////////////////////
// File: mnm_cnoc_input_signal_defines.sv
// This file contains mnm cnoc input signal defines
/////////////////////////////////////////////////////////////////////////////////////////
  logic                                                             c_noc_out_is_ar_channel;
  logic                                                             c_noc_out_is_b_channel;

  logic                                                             c_noc_out_arvalid;
  logic [mnm_pkg::MNM_DAXI_AR_ID_WIDTH-1:0]                         c_noc_out_arid;
  logic [mnm_pkg::MNM_DAXI_AR_LEN_WIDTH-1:0]                        c_noc_out_arlen;
  logic [mnm_pkg::MNM_DAXI_AR_ADDR_WIDTH-1:0]                       c_noc_out_araddr;
  logic [mnm_pkg::MNM_DAXI_AR_USER_WIDTH-1:0]                       c_noc_out_aruser;
  logic [mnm_pkg::MNM_DAXI_ARUSER_NOC_ID_WIDTH-1:0]                 c_noc_out_arnocid;
  mnm_pkg::coord_id_t                                               c_noc_out_arsrcid;
  mnm_pkg::coord_id_t                                               c_noc_out_artgtid;
  // logic [mnm_pkg::MNM_DAXI_ARUSER_HOST_SUBF_WIDTH-1:0]              c_noc_out_arhost;
  logic [mnm_pkg::MNM_DAXI_ARUSER_SIZE_WIDTH-1:0]                   c_noc_out_arsize;
  logic [mnm_pkg::MNM_DAXI_ARUSER_VC_WIDTH-1:0]                     c_noc_out_aruservc;
  // mnm_pkg::CC_OPCODE_e                                              c_noc_out_arcc_opcode;

  logic                                                             c_noc_out_bvalid;
  logic [mnm_pkg::MNM_UAXI_B_ID_WIDTH-1:0]                          c_noc_out_bid;
  logic [mnm_pkg::MNM_DAXI_B_USER_WIDTH-1:0]                        c_noc_out_buser;
  logic [mnm_pkg::MNM_DAXI_BUSER_NOC_ID_WIDTH-1:0]                  c_noc_out_bnocid;
  mnm_pkg::coord_id_t                                               c_noc_out_bsrcid;
  mnm_pkg::coord_id_t                                               c_noc_out_btgtid;
  logic [mnm_pkg::MNM_DAXI_BUSER_VC_WIDTH-1:0]                      c_noc_out_buservc;


  assign c_noc_out_is_ar_channel = (c_noc_out.channel == mnm_pkg::CNOC_CHANNEL_E_AR);
  assign c_noc_out_is_b_channel  = (c_noc_out.channel == mnm_pkg::CNOC_CHANNEL_E_B);
  
  assign c_noc_out_arvalid       = c_noc_out_valid && c_noc_out_is_ar_channel;
  assign c_noc_out_arid          = c_noc_out.payload.daxi_ar.id.iid;
  assign c_noc_out_arlen         = c_noc_out.payload.daxi_ar.len;
  assign c_noc_out_araddr        = c_noc_out.payload.daxi_ar.addr;
  assign c_noc_out_aruser        = c_noc_out.payload.daxi_ar.user;
  assign c_noc_out_arnocid       = c_noc_out.payload.daxi_ar.user.noc_id;
  assign c_noc_out_arsrcid       = c_noc_out.payload.daxi_ar.user.src_id;
  assign c_noc_out_artgtid       = c_noc_out.payload.daxi_ar.user.tgt_id;
  // assign c_noc_out_arhost        = c_noc_out.payload.daxi_ar.user.host;
  assign c_noc_out_arsize        = c_noc_out.payload.daxi_ar.user.size;
  assign c_noc_out_aruservc      = c_noc_out.payload.daxi_ar.user.vc;
  // assign c_noc_out_arcc_opcode   = c_noc_out.payload.daxi_ar.user.cc_opcode;

  assign c_noc_out_bvalid        = c_noc_out_valid && c_noc_out_is_b_channel;
  assign c_noc_out_bid           = c_noc_out.payload.daxi_b.id.iid;
  assign c_noc_out_buser         = c_noc_out.payload.daxi_b.user;
  assign c_noc_out_bnocid        = c_noc_out.payload.daxi_b.user.noc_id;
  assign c_noc_out_bsrcid        = c_noc_out.payload.daxi_b.user.src_id;
  assign c_noc_out_btgtid        = c_noc_out.payload.daxi_b.user.tgt_id;
  assign c_noc_out_buservc       = c_noc_out.payload.daxi_b.user.vc;