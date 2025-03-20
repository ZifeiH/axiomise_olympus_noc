module fbaxi_dnoc_checker
#(
  parameter DNOC_INPUT = 1,  // = 1: DNOC input; = 0: DNOC output, = 2: DNOC all asserts (monitor mode)

  // number of VCs, can differ between CRTR and IRTR
  parameter TOTAL_NUM_VCS = 2,
  parameter READ_VCS      = 1,
  parameter WRITE_VCS     = 1,

  // credit counter initial and minimum values
  parameter [TOTAL_NUM_VCS-1:0][cip_rtr_pkg::RTR_TX_DEPTH_W-1:0] CREDITS_INIT = {TOTAL_NUM_VCS{cip_rtr_pkg::RTR_TX_DEPTH_W'(6)}},
  parameter CREDITS_MIN = 1,  // minimum value for credit counter before requests can be sent out

  parameter CREDITS_INIT_LLC = 0, // (for initial value of credits array) if this =0 use CREDITS_INIT, !=0 use CREDITS_INIT_LLC

  // instantiated direction, default value -> no constraint on direction (and my_location is not used)
  // also only used if DNOC_INPUT = 1 (also if DNOC_INPUT = 0 and CREDITS_INIT_LLC != 0)
  parameter SRC_DIR = 6,

  // used to restrict which VCs are checked (in 'NO TURN' situations for North/South where lane is > 3)
  parameter USES_READ_VCS  = 1,
  parameter USES_WRITE_VCS = 1
)
(
  // System Signals
  clk,
  reset_n,

	// DNOC
  dnoc_valid,
  dnoc_credit_release,
  dnoc_bundle,

  my_location
);

  `ifdef ASSERT_OFF
    `define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 
  `endif

  localparam SKIP_CREDIT_RELEASE_CHECKS = 0;  // skip over any checks involving credit releases
  localparam MAX_INPUT_VALIDS = 0;            // if non-zero, limit total number of input valids seen so far to MAX_INPUT_VALIDS
  localparam NO_INPUT_VALIDS = 0;             // if non-zero, no input valids can happen
  localparam RESTRICT_LEN = 0;                // if non-zero, awlen and rlen can only take the values 2'b00 and 2'b01

  // for use when rtr_location is fixed
  localparam RTR_LOCATION_FIXED   =  0;
  localparam rtr_location_x_coord =  3;
  localparam rtr_location_y_coord = 10;
  localparam rtr_location_cip_id  =  0;

  // System Signals
  input logic clk;
  input logic reset_n;

  input logic dnoc_valid;
  input logic [TOTAL_NUM_VCS-1:0] dnoc_credit_release;
  input cip_pkg::data_noc_t dnoc_bundle;

  input cip_pkg::cip_grid_location_t my_location;

  `include "dnoc_properties.svh"

  genvar i;

  // indicator per VC if it is in use or not
  localparam [TOTAL_NUM_VCS-1:0] VALID_DNOC_VC = {{WRITE_VCS{1'(USES_WRITE_VCS)}},
                                                  {READ_VCS{1'(USES_READ_VCS)}}};
                                                  
  generate
  if (DNOC_INPUT == 1) begin : dnoc_in_checker

    localparam MAX_INPUT_VALIDS_W = $clog2(MAX_INPUT_VALIDS+1);
    if (NO_INPUT_VALIDS != 0) begin : no_input_valids

      /*@AXM  suppress all input DNOC valids  @*/
      `SV_ASSERT(FVPH_RTR_FV_am_no_input_valids, !dnoc_valid);

    end  // if (NO_INPUT_VALIDS != 0)
    else begin

      if (MAX_INPUT_VALIDS != 0) begin : max_input_valids

        logic [MAX_INPUT_VALIDS_W-1:0] input_valids_seen;

        always_ff @(posedge clk or negedge reset_n) begin
          if (!reset_n) begin
            input_valids_seen <= '0;
          end
          else if (dnoc_valid) begin
            input_valids_seen <= input_valids_seen == MAX_INPUT_VALIDS ? input_valids_seen
                                                                       : input_valids_seen + 1'b1;
          end
        end

        // 'dnoc_first' defined in dnoc_properties.svh, it indicates if beat is the first one in burst
        // for any burst in progress (started but not finished), allow remaining beats to happen

        /*@AXM  impose limit on number of input DNOC valids seen  @*/
        `SV_ASSERT(FVPH_RTR_FV_am_limit_on_input_valids, input_valids_seen == MAX_INPUT_VALIDS |-> !(dnoc_valid && dnoc_first));

      end  // if (MAX_INPUT_VALIDS != 0)

      // ttl

      /*@AXM  DNOC TTL value is always at least 1  @*/
      `SV_ASSERT (FVPH_RTR_FV_am_dnoc_ttl_always_at_least_1,     dnoc_ttl_always_at_least_1);

      /*@AXM  DNOC TTL value is always within maximum  @*/
      `SV_ASSERT (FVPH_RTR_FV_am_dnoc_ttl_always_within_maximum,     dnoc_ttl_always_within_maximum);

      /*@AXM  DNOC TTL value remains the same throughout a burst  @*/
      `SV_ASSERT (FVPH_RTR_FV_am_dnoc_ttl_same_throughout_burst, dnoc_ttl_same_throughout_burst);

      /*@AXM  DNOC VC value remains the same throughout a burst  @*/
      `SV_ASSERT (FVPH_RTR_FV_am_dnoc_vc_same_throughout_burst,  dnoc_vc_same_throughout_burst);

      if (SKIP_CREDIT_RELEASE_CHECKS == 0) begin : credit_release_checks

        // credit counter
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_credit_releases
          if (VALID_DNOC_VC[i]) begin
            `SV_ASSERT (FVPH_RTR_FV_as_dnoc_credit_releases_no_excess, dnoc_credit_releases_no_excess(i));
          end
        end 

        // each valid has credit
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_valids
          if (VALID_DNOC_VC[i]) begin
            /*@AXM  DNOC valid only sent if have sufficient DNOC credit  @*/
            `SV_ASSERT (FVPH_RTR_FV_am_dnoc_valid_with_sufficient_credit, dnoc_valid_with_sufficient_credit(i));
          end
        end

        `ifdef FORMAL  // liveness property, not handled by simulation
          // credit release
          for (i=0; i<TOTAL_NUM_VCS; i++) begin : eventual_credit_release
            if (VALID_DNOC_VC[i]) begin
              `SV_ASSERT (FVPH_RTR_FV_as_dnoc_credit_release_for_each_valid_liveness, dnoc_credit_release_for_each_valid_liveness(i));
            end
          end
        `endif  // ifdef FORMAL

        for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_reach_zero_credits
          if (VALID_DNOC_VC[i]) begin
            `SV_COVER (FVPH_RTR_FV_co_dnoc_credit_counter_can_reach_zero, dnoc_credit_counter_can_reach_zero(i));
          end
        end

        for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_go_from_zero_to_maximum_credits
          if (VALID_DNOC_VC[i]) begin
            `SV_COVER (FVPH_RTR_FV_co_dnoc_credit_counter_zero_to_maximum_liveness, dnoc_credit_counter_zero_to_maximum_liveness(i));
          end
        end

      end  // if (SKIP_CREDIT_RELEASE_CHECKS == 0)

      // direction constraints

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_NORTH) begin : direction_from_north
        /*@AXM  if DNOC source is from North, DNOC tgt_id does not go to North  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_id_not_northwards, dnoc_tgt_id_not_northwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_SOUTH) begin : direction_from_south
        /*@AXM  if DNOC source is from South, DNOC tgt_id does not go to South  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_id_not_southwards, dnoc_tgt_id_not_southwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_WEST) begin : direction_from_west
        /*@AXM  if DNOC source is from West, DNOC tgt_id does not go to West  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_id_not_westwards, dnoc_tgt_id_not_westwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_EAST) begin : direction_from_east
        /*@AXM  if DNOC source is from East, DNOC tgt_id does not go to East  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_id_not_eastwards, dnoc_tgt_id_not_eastwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_LEAF0) begin : direction_from_leaf0
        /*@AXM  if DNOC source is from Leaf0, DNOC tgt_id does not go to Leaf0  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_id_not_leaf0wards, dnoc_tgt_id_not_leaf0wards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_LEAF1) begin : direction_from_leaf1
        /*@AXM  if DNOC source is from Leaf1, DNOC tgt_id does not go to Leaf1  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_id_not_leaf1wards, dnoc_tgt_id_not_leaf1wards);
      end

      if (RTR_LOCATION_FIXED != 0) begin : rtr_location_fixed

        /*@AXM  DNOC my_location fixed to specific values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_fixed_to_specific_values, (my_location.xcoord == rtr_location_x_coord) &&
                                                                         (my_location.ycoord == rtr_location_y_coord) &&
                                                                         (my_location.cip_id == rtr_location_cip_id)  );

      end
      else begin : rtr_location_any

        /*@AXM  DNOC tgt_id.cip_id is always either 0 or 1  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_tgt_id_cip_id_is_0_or_1, dnoc_tgt_id_cip_id_is_0_or_1);

        /*@AXM  DNOC my_location keeps its initial value the same all the time after reset  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_fixed_from_reset, ##1 $stable(my_location));

        /*@AXM  DNOC my_location constrained to legal x- and y-coord values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_has_legal_values, (my_location.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START) &&
                                                                 (my_location.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END)   &&
                                                                 (my_location.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START) &&
                                                                 // NOTE: ycoord mustn't != Y_END (for CM RTR and IO RTR)
                                                                 (my_location.ycoord <  cip_pkg::CIP_RTR_GRID_COORD_Y_END)   );

        /*@AXM  DNOC my_location always has xcoord as the 'left leaf' (see Jira ticket AAF-544)  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_xcoord_is_odd_number, my_location.xcoord[0]);

        /*@AXM  DNOC my_location always has cip_id 0 or 1  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_cip_id_is_0_or_1, my_location.cip_id inside {2'b00, 2'b01});

      end

      if (USES_WRITE_VCS == 1) begin : write_channel

        // AXI AW+W channel

        /*@AXM  DNOC AW channel: valids are consecutive in a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awvalids_in_burst_are_consecutive, awvalids_in_burst_are_consecutive);

        /*@AXM  DNOC AW channel: addr value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awaddrs_in_burst_same_throughout, awaddrs_in_burst_same_throughout);

        /*@AXM  DNOC AW channel: cache value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awcaches_in_burst_same_throughout, awcaches_in_burst_same_throughout);

        /*@AXM  DNOC AW channel: lock value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awlocks_in_burst_same_throughout, awlocks_in_burst_same_throughout);

        /*@AXM  DNOC AW channel: id value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awids_in_burst_same_throughout, awids_in_burst_same_throughout);

        /*@AXM  DNOC AW channel: len value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awlens_in_burst_same_throughout, awlens_in_burst_same_throughout);

        if (RESTRICT_LEN != 0) begin : awlen_restriction
          /*@AXM  DNOC AW channel: len value can only be 2'b00 or 2'b01  @*/
          `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awlen_restricted, awlen_restricted);
        end

        /*@AXM  DNOC AW channel: user value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awusers_in_burst_same_throughout, awusers_in_burst_same_throughout);

        /*@AXM  DNOC W channel: user value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_wusers_in_burst_same_throughout, wusers_in_burst_same_throughout);

        /*@AXM  DNOC W channel: last gets asserted in correct place in a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_wlast_as_expected, wlast_as_expected);

        if (cip_pkg::CIP_DAXI_AW_ADDR_WIDTH > 12) begin : addr_width_more_than_12
          /*@AXM  DNOC AW channel: addr locations in a burst are all within the same 4kB page  @*/
          `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awaddr_burst_within_4kb_boundary, awaddr_burst_within_4kb_boundary);
        end

        /*@AXM  DNOC AW channel: src_id coords are within grid  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awsrcid_coords_within_grid, awsrcid_coords_within_grid);

        /*@AXM  DNOC AW channel: tgt_id coords are within grid  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awtgtid_coords_within_grid, awtgtid_coords_within_grid);

        /*@AXM  DNOC AW channel: wstrb_enc set when aw.user.host is 1  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awhost_wstrb_enc_value_is_legal, awhost_wstrb_enc_value_is_legal);

        /*@AXM  DNOC W channel: w.strb.beat_offset remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_wstrb_beat_offset_in_burst_same_throughout, wstrb_beat_offset_in_burst_same_throughout);

        /*@AXM  DNOC W channel: w.strb.size remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awsize_in_burst_same_throughout, awsize_in_burst_same_throughout);

        /*@AXM  DNOC W channel: w.strb.subf remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_wstrb_subf_in_burst_same_throughout, wstrb_subf_in_burst_same_throughout);

        /*@AXM  DNOC W channel: w.strb.rord remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_wstrb_rord_in_burst_same_throughout, wstrb_rord_in_burst_same_throughout);

        /*@AXM  DNOC AW channel: host_size field has a legal value  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awhost_size_field_value_is_legal, awhost_size_field_value_is_legal);

        /*@AXM  DNOC AW channel: awuser reduction_type field has a legal value  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awuser_reduction_type_value_is_legal, awuser_reduction_type_value_is_legal);

        /*@AXM  DNOC AW channel: awuser.vc has a legal value  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_awuser_vc_is_legal, awuser_vc_is_legal);

        // AW channel covers

        for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : aw_src_id_x_coord_value
          `SV_COVER (FVPH_RTR_FV_co_awuser_src_id_x_coord, awuser_src_id_x_coord(i));
        end

        for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : aw_src_id_y_coord_value
          `SV_COVER (FVPH_RTR_FV_co_awuser_src_id_y_coord, awuser_src_id_y_coord(i));
        end

        if (RTR_LOCATION_FIXED != 0) begin : limited_aw_tgt_id_x_coord_covers
          case (SRC_DIR)

            cip_rtr_pkg::NOC_DIR_EAST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END-2; i++) begin : east_aw_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_x_coord, awuser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_WEST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START+2; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : west_aw_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_x_coord, awuser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_LEAF0 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf0_aw_tgt_id_x_coord_value
                if (i != 3) begin : not_3
                  `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_x_coord, awuser_tgt_id_x_coord(i));
                end
              end

            cip_rtr_pkg::NOC_DIR_LEAF1 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf1_aw_tgt_id_x_coord_value
                if (i != 4) begin : not_4
                  `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_x_coord, awuser_tgt_id_x_coord(i));
                end
              end

            default :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : north_south_aw_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_x_coord, awuser_tgt_id_x_coord(i));
              end

          endcase
        end
        else begin : unlimited_aw_tgt_id_x_coord_covers
          for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : aw_tgt_id_x_coord_value
            `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_x_coord, awuser_tgt_id_x_coord(i));
          end
        end

        if (RTR_LOCATION_FIXED != 0) begin : limited_aw_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_NORTH) begin : north_aw_tgt_ycoord_value
            `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_y_coord, awuser_tgt_id_y_coord(cip_pkg::CIP_RTR_GRID_COORD_Y_END));
          end
          else begin : not_north_aw_tgt_id_y_coord_covers
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : aw_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_y_coord, awuser_tgt_id_y_coord(i));
            end
          end
        end
        else begin : unlimited_aw_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_SOUTH) begin : south_aw_tgt_ycoord_value
            // for southwards direction, tgt_id_y_coord is never at CIP_RTR_GRID_COORD_Y_END
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : aw_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_y_coord, awuser_tgt_id_y_coord(i));
            end
          end
          else begin : not_south_aw_tgt_id_y_coord_value
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : aw_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_awuser_tgt_id_y_coord, awuser_tgt_id_y_coord(i));
            end
          end
        end

        for (i=0; i<4; i++) begin : aw_noc_id_value
          `SV_COVER (FVPH_RTR_FV_co_awuser_noc_id, awuser_noc_id(i));
        end

        for (i=0; i<WRITE_VCS; i++) begin : aw_user_vc_value
          `SV_COVER (FVPH_RTR_FV_co_awuser_vc, awuser_vc(i));
        end

        if (RESTRICT_LEN != 0) begin : awlen_range_restricted
          for (i=0; i<2; i++) begin : awid_len_value
            `SV_COVER (FVPH_RTR_FV_co_awid_len, awid_len(i));
          end
        end
        else begin : awlen_not_restricted
          for (i=0; i<4; i++) begin : awid_len_value
            `SV_COVER (FVPH_RTR_FV_co_awid_len, awid_len(i));
          end
        end

        for (i=0; i<2; i++) begin : aw_user_host_value
          `SV_COVER (FVPH_RTR_FV_co_awuser_host, awuser_host(i));
        end

        for (i=0; i<7; i++) begin : awsize_value  // size = 7 is not legal (constrained out)
          `SV_COVER (FVPH_RTR_FV_co_awsize, awsize_is(i));
        end

        `SV_COVER (FVPH_RTR_FV_co_no_gaps_write_channel_write_channel, no_gaps_write_channel_write_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_1_write_channel_write_channel,   gap_1_write_channel_write_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_2_write_channel_write_channel,   gap_2_write_channel_write_channel);

      end  // if (USES_WRITE_VCS == 1)

      if (USES_READ_VCS == 1) begin : read_channel

        // AXI R channel

        /*@AXM  DNOC R channel: valids are consecutive in a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rvalids_in_burst_are_consecutive, rvalids_in_burst_are_consecutive);

        /*@AXM  DNOC R channel: id value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rids_in_burst_same_throughout, rids_in_burst_same_throughout);

        /*@AXM  DNOC R channel: len value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rlens_in_burst_same_throughout, rlens_in_burst_same_throughout);

        if (RESTRICT_LEN != 0) begin : rlen_restriction
          /*@AXM  DNOC R channel: len value can only be 2'b00 or 2'b01  @*/
          `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rlen_restricted, rlen_restricted);
        end

        /*@AXM  DNOC R channel: user value remains the same throughout a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rusers_in_burst_same_throughout, rusers_in_burst_same_throughout);

        /*@AXM  DNOC R channel: last gets asserted in correct place in a burst  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rlast_as_expected, rlast_as_expected);

        /*@AXM  DNOC R channel: tgt_id coords are within grid  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rtgtid_coords_within_grid, rtgtid_coords_within_grid);

        /*@AXM  DNOC R channel: rcc_lane row only has legal values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rcc_lane_is_legal_row, rcc_lane_is_legal_row);

        /*@AXM  DNOC R channel: rcc_lane column only has legal values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_dnoc_rcc_lane_is_legal_column, rcc_lane_is_legal_column);

        // R channel covers

        if (RTR_LOCATION_FIXED != 0) begin : limited_r_tgt_id_x_coord_covers
          case (SRC_DIR)

            cip_rtr_pkg::NOC_DIR_EAST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END-2; i++) begin : east_r_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_x_coord, ruser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_WEST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START+2; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : west_r_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_x_coord, ruser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_LEAF0 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf0_r_tgt_id_x_coord_value
                if (i != 3) begin : not_3
                  `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_x_coord, ruser_tgt_id_x_coord(i));
                end
              end

            cip_rtr_pkg::NOC_DIR_LEAF1 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf1_r_tgt_id_x_coord_value
                if (i != 4) begin : not_4
                  `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_x_coord, ruser_tgt_id_x_coord(i));
                end
              end

            default :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : north_south_r_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_x_coord, ruser_tgt_id_x_coord(i));
              end

          endcase
        end
        else begin : unlimited_r_tgt_id_x_coord_covers
          for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : r_tgt_id_x_coord_value
            `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_x_coord, ruser_tgt_id_x_coord(i));
          end
        end

        if (RTR_LOCATION_FIXED != 0) begin : limited_r_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_NORTH) begin : north_b_tgt_ycoord_value
            `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_y_coord, ruser_tgt_id_y_coord(cip_pkg::CIP_RTR_GRID_COORD_Y_END));
          end
          else begin : not_north_r_tgt_id_y_coord_covers
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : r_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_y_coord, ruser_tgt_id_y_coord(i));
            end
          end
        end
        else begin : unlimited_r_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_SOUTH) begin : south_r_tgt_ycoord_value
            // for southwards direction, tgt_id_y_coord is never at CIP_RTR_GRID_COORD_Y_END
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : r_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_y_coord, ruser_tgt_id_y_coord(i));
            end
          end
          else begin : not_south_r_tgt_id_y_coord_value
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : r_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_ruser_tgt_id_y_coord, ruser_tgt_id_y_coord(i));
            end
          end
        end

        for (i=0; i<4; i++) begin : r_noc_id_value
          `SV_COVER (FVPH_RTR_FV_co_ruser_noc_id, ruser_noc_id(i));
        end

        for (i=0; i<4; i++) begin : r_user_cc_opcode_value
          `SV_COVER (FVPH_RTR_FV_co_ruser_cc_opcode, ruser_cc_opcode(i));
        end

        for (i=0; i<13; i++) begin : rcc_dir_1_r_user_cc_lane_value
          `SV_COVER (FVPH_RTR_FV_co_rcc_dir_1_ruser_cc_lane, rcc_dir_1_ruser_cc_lane(i));
        end

        for (i=0; i<6; i++) begin : rcc_dir_0_r_user_cc_lane_value
          `SV_COVER (FVPH_RTR_FV_co_rcc_dir_0_ruser_cc_lane, rcc_dir_0_ruser_cc_lane(i));
        end

        for (i=0; i<9; i++) begin : r_user_pe_in_cc_clear
          `SV_COVER (FVPH_RTR_FV_co_ruser_pe_in_cc_clear, ruser_pe_in_cc_clear(i));
        end

        for (i=0; i<9; i++) begin : r_user_pe_in_cc_set
          `SV_COVER (FVPH_RTR_FV_co_ruser_pe_in_cc_set, ruser_pe_in_cc_set(i));
        end

        `SV_COVER (FVPH_RTR_FV_co_no_gaps_read_channel_read_channel,   no_gaps_read_channel_read_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_2_read_channel_read_channel,     gap_2_read_channel_read_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_1_read_channel_read_channel,     gap_1_read_channel_read_channel);

      end  // if (USES_READ_VCS == 1)

      if ((USES_READ_VCS == 1) && (USES_WRITE_VCS == 1)) begin : both_read_and_write_channel

        `SV_COVER (FVPH_RTR_FV_co_no_gaps_write_channel_read_channel,  no_gaps_write_channel_read_channel);
        `SV_COVER (FVPH_RTR_FV_co_no_gaps_read_channel_write_channel,  no_gaps_read_channel_write_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_1_write_channel_read_channel,    gap_1_write_channel_read_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_1_read_channel_write_channel,    gap_1_read_channel_write_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_2_write_channel_read_channel,    gap_2_write_channel_read_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_2_read_channel_write_channel,    gap_2_read_channel_write_channel);

      end  // if ((USES_READ_VCS == 1) && (USES_WRITE_VCS == 1))

    end

  end  // if (DNOC_INPUT == 1)
  else if (DNOC_INPUT == 0) begin : dnoc_out_checker

    // ttl
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_always_at_least_1,     dnoc_ttl_always_at_least_1);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_always_within_maximum,     dnoc_ttl_always_within_maximum);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_same_throughout_burst, dnoc_ttl_same_throughout_burst);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_vc_same_throughout_burst,  dnoc_vc_same_throughout_burst);

    if (SKIP_CREDIT_RELEASE_CHECKS == 0) begin : credit_release_checks

      // credit counter
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_credit_releases
        if (VALID_DNOC_VC[i]) begin
          /*@AXM  DNOC credit release signal never asserted more times than there were DNOC valids seen  @*/
          `SV_ASSERT (FVPH_RTR_FV_am_dnoc_credit_releases_no_excess, dnoc_credit_releases_no_excess(i));
        end
      end

      // each valid has credit
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_input_valids
        if (VALID_DNOC_VC[i]) begin
          `SV_ASSERT (FVPH_RTR_FV_as_dnoc_valid_with_sufficient_credit, dnoc_valid_with_sufficient_credit(i));
        end
      end

      `ifdef FORMAL  // liveness property, not handled by simulation
        // credit release
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : eventual_credit_release
          if (VALID_DNOC_VC[i]) begin
            /*@AXM  for every DNOC valid sent, a DNOC credit release will always eventually appear  @*/
            `SV_ASSERT (FVPH_RTR_FV_am_dnoc_credit_release_for_each_valid_liveness, dnoc_credit_release_for_each_valid_liveness(i));
          end
        end
      `endif  // ifdef FORMAL

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_reach_zero_credits
        if (VALID_DNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_dnoc_credit_counter_can_reach_zero, dnoc_credit_counter_can_reach_zero(i));
        end
      end

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_go_from_zero_to_maximum_credits
        if (VALID_DNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_dnoc_credit_counter_zero_to_maximum_liveness, dnoc_credit_counter_zero_to_maximum_liveness(i));
        end
      end

    end  // if (SKIP_CREDIT_RELEASE_CHECKS == 0)

    if (USES_WRITE_VCS == 1) begin : write_channel

      // AXI AW+W channel

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awvalids_in_burst_are_consecutive, awvalids_in_burst_are_consecutive);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awaddrs_in_burst_same_throughout,  awaddrs_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awcaches_in_burst_same_throughout, awcaches_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awlocks_in_burst_same_throughout,  awlocks_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awids_in_burst_same_throughout,    awids_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awlens_in_burst_same_throughout,   awlens_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awusers_in_burst_same_throughout,  awusers_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wusers_in_burst_same_throughout,   wusers_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wlast_as_expected,                 wlast_as_expected);

      if (cip_pkg::CIP_DAXI_AW_ADDR_WIDTH > 12) begin : addr_width_more_than_12
        `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awaddr_burst_within_4kb_boundary, awaddr_burst_within_4kb_boundary);
      end

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awsrcid_coords_within_grid, awsrcid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awtgtid_coords_within_grid, awtgtid_coords_within_grid);

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awhost_wstrb_enc_value_is_legal,            awhost_wstrb_enc_value_is_legal);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_beat_offset_in_burst_same_throughout, wstrb_beat_offset_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awsize_in_burst_same_throughout,            awsize_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_subf_in_burst_same_throughout,        wstrb_subf_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_rord_in_burst_same_throughout,        wstrb_rord_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awhost_size_field_value_is_legal,           awhost_size_field_value_is_legal);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awuser_reduction_type_value_is_legal,       awuser_reduction_type_value_is_legal);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awuser_vc_is_legal,                         awuser_vc_is_legal);

    end  // if (USES_WRITE_VCS == 1)

    if (USES_READ_VCS == 1) begin : read_channel

      // AXI R channel

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rvalids_in_burst_are_consecutive, rvalids_in_burst_are_consecutive);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rids_in_burst_same_throughout,    rids_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rlens_in_burst_same_throughout,   rlens_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rusers_in_burst_same_throughout,  rusers_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rlast_as_expected,                rlast_as_expected);

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rtgtid_coords_within_grid, rtgtid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rcc_lane_is_legal_row,     rcc_lane_is_legal_row);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rcc_lane_is_legal_column,  rcc_lane_is_legal_column);

    end  // if (USES_READ_VCS == 1)

  end  // if (DNOC_INPUT == 0)
  else if (DNOC_INPUT == 2) begin : dnoc_all_asserts

    // ttl
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_always_at_least_1,     dnoc_ttl_always_at_least_1);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_always_within_maximum,     dnoc_ttl_always_within_maximum);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_ttl_same_throughout_burst, dnoc_ttl_same_throughout_burst);
    `SV_ASSERT (FVPH_RTR_FV_as_dnoc_vc_same_throughout_burst,  dnoc_vc_same_throughout_burst);

    if (SKIP_CREDIT_RELEASE_CHECKS == 0) begin : credit_release_checks
      // credit counter
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_credit_releases
        if (VALID_DNOC_VC[i]) begin
          `SV_ASSERT (FVPH_RTR_FV_as_dnoc_credit_releases_no_excess, dnoc_credit_releases_no_excess(i));
        end
      end

      // each valid has credit
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_input_valids
        if (VALID_DNOC_VC[i]) begin
          `SV_ASSERT (FVPH_RTR_FV_as_dnoc_valid_with_sufficient_credit, dnoc_valid_with_sufficient_credit(i));
        end
      end

      `ifdef FORMAL  // liveness property, not handled by simulation
        // credit release
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : eventual_credit_release
          if (VALID_DNOC_VC[i]) begin
            `SV_ASSERT (FVPH_RTR_FV_as_dnoc_credit_release_for_each_valid_liveness, dnoc_credit_release_for_each_valid_liveness(i));
          end
        end
      `endif  // ifdef FORMAL

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_reach_zero_credits
        if (VALID_DNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_dnoc_credit_counter_can_reach_zero, dnoc_credit_counter_can_reach_zero(i));
        end
      end

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_go_from_zero_to_maximum_credits
        if (VALID_DNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_dnoc_credit_counter_zero_to_maximum_liveness, dnoc_credit_counter_zero_to_maximum_liveness(i));
        end
      end

    end  // if (SKIP_CREDIT_RELEASE_CHECKS == 0)

    if (USES_WRITE_VCS == 1) begin : write_channel

      // AXI AW+W channel

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awvalids_in_burst_are_consecutive, awvalids_in_burst_are_consecutive);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awaddrs_in_burst_same_throughout,  awaddrs_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awcaches_in_burst_same_throughout, awcaches_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awlocks_in_burst_same_throughout,  awlocks_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awids_in_burst_same_throughout,    awids_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awlens_in_burst_same_throughout,   awlens_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awusers_in_burst_same_throughout,  awusers_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wusers_in_burst_same_throughout,   wusers_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wlast_as_expected,                 wlast_as_expected);

      if (cip_pkg::CIP_DAXI_AW_ADDR_WIDTH > 12) begin : addr_width_more_than_12
        `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awaddr_burst_within_4kb_boundary, awaddr_burst_within_4kb_boundary);
      end

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awsrcid_coords_within_grid, awsrcid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awtgtid_coords_within_grid, awtgtid_coords_within_grid);

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awhost_wstrb_enc_value_is_legal,            awhost_wstrb_enc_value_is_legal);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_beat_offset_in_burst_same_throughout, wstrb_beat_offset_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awsize_in_burst_same_throughout,            awsize_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_subf_in_burst_same_throughout,        wstrb_subf_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_wstrb_rord_in_burst_same_throughout,        wstrb_rord_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awhost_size_field_value_is_legal,           awhost_size_field_value_is_legal);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awuser_reduction_type_value_is_legal,       awuser_reduction_type_value_is_legal);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_awuser_vc_is_legal,                         awuser_vc_is_legal);

    end  // if (USES_WRITE_VCS == 1)

    if (USES_READ_VCS == 1) begin : read_channel

      // AXI R channel

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rvalids_in_burst_are_consecutive, rvalids_in_burst_are_consecutive);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rids_in_burst_same_throughout,    rids_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rlens_in_burst_same_throughout,   rlens_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rusers_in_burst_same_throughout,  rusers_in_burst_same_throughout);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rlast_as_expected,                rlast_as_expected);

      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rtgtid_coords_within_grid, rtgtid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rcc_lane_is_legal_row,     rcc_lane_is_legal_row);
      `SV_ASSERT (FVPH_RTR_FV_as_dnoc_rcc_lane_is_legal_column,  rcc_lane_is_legal_column);

    end  // if (USES_READ_VCS == 1)

  end  // if (DNOC_INPUT == 2)
  endgenerate

endmodule // fbaxi_dnoc_checker
