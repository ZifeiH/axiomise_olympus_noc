module fbaxi_cnoc_checker
#(
  parameter CNOC_INPUT = 1,  // = 1: CNOC input, = 0: CNOC output, = 2: CNOC all asserts (monitor mode)

  // number of VCs, can differ between CRTR and IRTR
  parameter TOTAL_NUM_VCS = 4,
  parameter READ_VCS      = 3,
  parameter WRITE_VCS     = 1,

  // credit counter initial and minimum values
  parameter [TOTAL_NUM_VCS-1:0][cip_rtr_pkg::RTR_TX_DEPTH_W-1:0] CREDITS_INIT = {TOTAL_NUM_VCS{cip_rtr_pkg::RTR_TX_DEPTH_W'(6)}},
  parameter CREDITS_MIN = 1,  // minimum value for credit counter before requests can be sent out

  parameter CREDITS_INIT_LLC = 0, // (for initial value of credits array) if this =0 use CREDITS_INIT, !=0 use CREDITS_INIT_LLC

  // instantiated direction, default value -> no constraint on direction (and my_location is not used)
  // also only used if CNOC_INPUT = 1 (also if CNOC_INPUT = 0 and CREDITS_INIT_LLC != 0)
  parameter SRC_DIR = 6,

  // used to restrict which VCs are checked (in 'NO TURN' situations for North/South where lane is > 3)
  parameter USES_READ_VCS  = 1,
  parameter USES_WRITE_VCS = 1
)
(
  // System Signals
  clk,
  reset_n,

	// CNOC
	cnoc_valid,
  cnoc_credit_release,
  cnoc_bundle,

  my_location
);

  `ifdef ASSERT_OFF
    `define SV_ASSERT(name, prop) AST_``name : assert property (@(posedge clk) disable iff (!reset_n) prop); 
  `endif

  localparam SKIP_CREDIT_RELEASE_CHECKS = 0;  // skip over any checks involving credit releases
  localparam MAX_INPUT_VALIDS = 0;            // if non-zero, limit total number of input valids seen since reset to MAX_INPUT_VALIDS
  localparam NO_INPUT_VALIDS = 0;             // if non-zero, no input valids can happen 

  // for use when rtr_location is fixed
  localparam RTR_LOCATION_FIXED   =  0;
  localparam rtr_location_x_coord =  3;
  localparam rtr_location_y_coord = 10;
  localparam rtr_location_cip_id  =  0;

  // System Signals
  input logic clk;
  input logic reset_n;

  input logic cnoc_valid;
  input logic [TOTAL_NUM_VCS-1:0] cnoc_credit_release;
  input cip_pkg::control_noc_t cnoc_bundle;

  input cip_pkg::cip_grid_location_t my_location;

  `include "cnoc_properties.svh"

  genvar i;

  // indicator per VC if it is in use or not
  localparam [TOTAL_NUM_VCS-1:0] VALID_CNOC_VC = {{WRITE_VCS{1'(USES_WRITE_VCS)}},
                                                  {READ_VCS{1'(USES_READ_VCS)}}};

  generate
  if (CNOC_INPUT == 1) begin : cnoc_in_checker

    localparam MAX_INPUT_VALIDS_W = $clog2(MAX_INPUT_VALIDS+1);
    if (NO_INPUT_VALIDS != 0) begin : no_input_valids

      /*@AXM  suppress all input CNOC valids  @*/
      `SV_ASSERT(FVPH_RTR_FV_am_no_input_valids, !cnoc_valid);

    end  // if (NO_INPUT_VALIDS != 0)
    else begin

      if (MAX_INPUT_VALIDS != 0) begin : max_input_valids

        logic [MAX_INPUT_VALIDS_W-1:0] input_valids_seen;

        always_ff @(posedge clk or negedge reset_n) begin
          if (!reset_n) begin
            input_valids_seen <= '0;
          end
          else if (cnoc_valid) begin
            input_valids_seen <= input_valids_seen == MAX_INPUT_VALIDS ? input_valids_seen
                                                                       : input_valids_seen + 1'b1;
          end
        end

        /*@AXM  impose limit on number of input CNOC valids seen  @*/
        `SV_ASSERT(FVPH_RTR_FV_am_limit_on_input_valids, input_valids_seen == MAX_INPUT_VALIDS |-> !cnoc_valid);

      end  // if (MAX_INPUT_VALIDS != 0)

      // ttl
      /*@AXM  CNOC TTL value is always at least 1  @*/
      `SV_ASSERT (FVPH_RTR_FV_am_cnoc_ttl_always_at_least_1, cnoc_ttl_always_at_least_1);

      /*@AXM  CNOC TTL value is always at most 17  @*/
      `SV_ASSERT (FVPH_RTR_FV_am_cnoc_ttl_always_within_maximum, cnoc_ttl_always_within_maximum);

      if (SKIP_CREDIT_RELEASE_CHECKS == 0) begin : credit_release_checks

        // credit counter
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_credit_releases
          if (VALID_CNOC_VC[i]) begin
            `SV_ASSERT (FVPH_RTR_FV_as_cnoc_credit_releases_no_excess, cnoc_credit_releases_no_excess(i));
          end
        end

        // each valid has credit
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_valids
          if (VALID_CNOC_VC[i]) begin
            /*@AXM  only send CNOC valid if have enough credit  @*/
            `SV_ASSERT (FVPH_RTR_FV_am_cnoc_valid_with_sufficient_credit, cnoc_valid_with_sufficient_credit(i));
          end
        end

        `ifdef FORMAL  // liveness property, not handled by simulation
          // credit release
          for (i=0; i<TOTAL_NUM_VCS; i++) begin : eventual_credit_release
            if (VALID_CNOC_VC[i]) begin
              `SV_ASSERT (FVPH_RTR_FV_as_cnoc_credit_release_for_each_valid_liveness, cnoc_credit_release_for_each_valid_liveness(i));
            end
          end
        `endif  // ifdef FORMAL

        for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_reach_zero_credits
          if (VALID_CNOC_VC[i]) begin
            `SV_COVER (FVPH_RTR_FV_co_cnoc_credit_counter_can_reach_zero, cnoc_credit_counter_can_reach_zero(i));
          end
        end

        for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_go_from_zero_to_maximum_credits
          if (VALID_CNOC_VC[i]) begin
            `SV_COVER (FVPH_RTR_FV_co_cnoc_credit_counter_zero_to_maximum_liveness, cnoc_credit_counter_zero_to_maximum_liveness(i));
          end
        end

      end  // if (SKIP_CREDIT_RELEASE_CHECKS == 0)

      // direction constraints

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_NORTH) begin : direction_from_north
        /*@AXM  if CNOC source is from North, CNOC tgt_id does not go to North  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_tgt_id_not_northwards, cnoc_tgt_id_not_northwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_SOUTH) begin : direction_from_south
        /*@AXM  if CNOC source is from South, CNOC tgt_id does not go to South  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_tgt_id_not_southwards, cnoc_tgt_id_not_southwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_WEST) begin : direction_from_west
        /*@AXM  if CNOC source is from West, CNOC tgt_id does not go to West  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_tgt_id_not_westwards, cnoc_tgt_id_not_westwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_EAST) begin : direction_from_east
        /*@AXM  if CNOC source is from East, CNOC tgt_id does not go to East  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_tgt_id_not_eastwards, cnoc_tgt_id_not_eastwards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_LEAF0) begin : direction_from_leaf0
        /*@AXM  if CNOC source is from Leaf0, CNOC tgt_id does not go to Leaf0  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_tgt_id_not_leaf0wards, cnoc_tgt_id_not_leaf0wards);
      end

      if (SRC_DIR == cip_rtr_pkg::NOC_DIR_LEAF1) begin : direction_from_leaf1
        /*@AXM  if CNOC source is from Leaf1, CNOC tgt_id does not go to Leaf1  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_tgt_id_not_leaf1wards, cnoc_tgt_id_not_leaf1wards);
      end

      /*@AXM  CNOC tgt_id.cip_id is always either 0 or 1  @*/
      `SV_ASSERT (FVPH_RTR_FV_am_cnoc_tgt_id_cip_id_is_0_or_1, cnoc_tgt_id_cip_id_is_0_or_1);

      if (RTR_LOCATION_FIXED != 0) begin : rtr_location_fixed

        /*@AXM  CNOC my_location fixed to specific values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_fixed_to_specific_values, (my_location.xcoord == rtr_location_x_coord) &&
                                                                         (my_location.ycoord == rtr_location_y_coord) &&
                                                                         (my_location.cip_id == rtr_location_cip_id)  );

      end
      else begin : rtr_location_any

        /*@AXM  CNOC my_location keeps its initial value the same all the time after reset  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_fixed_from_reset, ##1 $stable(my_location));

        /*@AXM  CNOC my_location constrained to legal x- and y-coord values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_has_legal_values, (my_location.xcoord >= cip_pkg::CIP_RTR_GRID_COORD_X_START) &&
                                                                 (my_location.xcoord <= cip_pkg::CIP_RTR_GRID_COORD_X_END)   &&
                                                                 (my_location.ycoord >= cip_pkg::CIP_RTR_GRID_COORD_Y_START) &&
                                                                 // NOTE: ycoord mustn't != Y_END (for CM RTR and IO RTR)
                                                                 (my_location.ycoord <  cip_pkg::CIP_RTR_GRID_COORD_Y_END)   );

        /*@AXM  CNOC my_location always has xcoord as the 'left leaf' (see Jira ticket AAF-544)  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_xcoord_is_odd_number, my_location.xcoord[0]);

        /*@AXM  CNOC my_location always has cip_id 0 or 1  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_my_location_cip_id_is_0_or_1, my_location.cip_id inside {2'b00, 2'b01});

      end

      if (USES_WRITE_VCS == 1) begin : write_channel

        // AXI B channel

        /*@AXM  CNOC B channel: tgt_id coords are within grid  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_btgtid_coords_within_grid, btgtid_coords_within_grid);

        /*@AXM  CNOC B channel: user.vc only has legal values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_buser_vc_is_legal,         buser_vc_is_legal);


        // B channel covers

        if (RTR_LOCATION_FIXED != 0) begin : limited_b_tgt_id_x_coord_covers
          case (SRC_DIR)

            cip_rtr_pkg::NOC_DIR_EAST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END-2; i++) begin : east_b_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_x_coord, buser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_WEST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START+2; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : west_b_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_x_coord, buser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_LEAF0 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf0_b_tgt_id_x_coord_value
                if (i != 3) begin : not_3
                  `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_x_coord, buser_tgt_id_x_coord(i));
                end
              end

            cip_rtr_pkg::NOC_DIR_LEAF1 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf1_b_tgt_id_x_coord_value
                if (i != 4) begin : not_4
                  `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_x_coord, buser_tgt_id_x_coord(i));
                end
              end

            default :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : north_south_b_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_x_coord, buser_tgt_id_x_coord(i));
              end

          endcase
        end
        else begin : unlimited_b_tgt_id_x_coord_covers
          for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : b_tgt_id_x_coord_value
            `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_x_coord, buser_tgt_id_x_coord(i));
          end
        end

        if (RTR_LOCATION_FIXED != 0) begin : limited_b_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_NORTH) begin : north_b_tgt_ycoord_value
            `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_y_coord, buser_tgt_id_y_coord(cip_pkg::CIP_RTR_GRID_COORD_Y_END));
          end
          else begin : not_north_b_tgt_id_y_coord_covers
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : b_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_y_coord, buser_tgt_id_y_coord(i));
            end
          end
        end
        else begin : unlimited_b_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_SOUTH) begin : south_b_tgt_ycoord_value
            // for southwards direction, tgt_id_y_coord is never at CIP_RTR_GRID_COORD_Y_END
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : b_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_y_coord, buser_tgt_id_y_coord(i));
            end
          end
          else begin : not_south_b_tgt_id_y_coord_value
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : ar_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_buser_tgt_id_y_coord, buser_tgt_id_y_coord(i));
            end
          end
        end

        for (i=0; i<4; i++) begin : b_noc_id_value
          `SV_COVER (FVPH_RTR_FV_co_buser_noc_id, buser_noc_id(i));
        end

        for (i=0; i<WRITE_VCS; i++) begin : b_user_vc_value
          `SV_COVER (FVPH_RTR_FV_co_buser_vc, buser_vc(i));
        end

        `SV_COVER (FVPH_RTR_FV_co_no_gaps_write_channel_write_channel, no_gaps_write_channel_write_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_1_write_channel_write_channel,   gap_1_write_channel_write_channel);
        `SV_COVER (FVPH_RTR_FV_co_gap_2_write_channel_write_channel,   gap_2_write_channel_write_channel);

      end  // if (USES_WRITE_VCS == 1)

      if (USES_READ_VCS == 1) begin : read_channel

        // AXI AR channel

        /*@AXM  CNOC AR channel: host_size field has a legal value  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_arhost_size_field_is_legal, arhost_size_field_is_legal);

        if (cip_pkg::CIP_DAXI_AR_ADDR_WIDTH > 12) begin : addr_width_more_than_12
          /*@AXM  CNOC AR channel: addr locations in a burst are all within the same 4kB page  @*/
          `SV_ASSERT (FVPH_RTR_FV_am_cnoc_araddr_burst_within_4kb_boundary, araddr_burst_within_4kb_boundary);
        end

        /*@AXM  CNOC AR channel: src_id coords are within grid  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_arsrcid_coords_within_grid, arsrcid_coords_within_grid);

        /*@AXM  CNOC AR channel: tgt_id coords within grid  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_artgtid_coords_within_grid, artgtid_coords_within_grid);

        /*@AXM  CNOC AR channel: user.vc only has legal values  @*/
        `SV_ASSERT (FVPH_RTR_FV_am_cnoc_aruser_vc_is_legal, aruser_vc_is_legal);

        // AR channel covers

        for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : ar_src_id_x_coord_value
          `SV_COVER (FVPH_RTR_FV_co_aruser_src_id_x_coord, aruser_src_id_x_coord(i));
        end

        for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : ar_src_id_y_coord_value
          `SV_COVER (FVPH_RTR_FV_co_aruser_src_id_y_coord, aruser_src_id_y_coord(i));
        end

        if (RTR_LOCATION_FIXED != 0) begin : limited_ar_tgt_id_x_coord_covers
          case (SRC_DIR)

            cip_rtr_pkg::NOC_DIR_EAST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END-2; i++) begin : east_ar_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_x_coord, aruser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_WEST :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START+2; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : west_ar_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_x_coord, aruser_tgt_id_x_coord(i));
              end

            cip_rtr_pkg::NOC_DIR_LEAF0 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf0_ar_tgt_id_x_coord_value
                if (i != 3) begin : not_3
                  `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_x_coord, aruser_tgt_id_x_coord(i));
                end
              end

            cip_rtr_pkg::NOC_DIR_LEAF1 :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : leaf1_ar_tgt_id_x_coord_value
                if (i != 4) begin : not_4
                  `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_x_coord, aruser_tgt_id_x_coord(i));
                end
              end

            default :
              for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : north_south_ar_tgt_id_x_coord_value
                `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_x_coord, aruser_tgt_id_x_coord(i));
              end

          endcase
        end
        else begin : unlimited_ar_tgt_id_x_coord_covers
          for (i=cip_pkg::CIP_RTR_GRID_COORD_X_START; i<=cip_pkg::CIP_RTR_GRID_COORD_X_END; i++) begin : ar_tgt_id_x_coord_value
            `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_x_coord, aruser_tgt_id_x_coord(i));
          end
        end

        if (RTR_LOCATION_FIXED != 0) begin : limited_ar_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_NORTH) begin : north_ar_tgt_ycoord_value
            `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_y_coord, aruser_tgt_id_y_coord(cip_pkg::CIP_RTR_GRID_COORD_Y_END));
          end
          else begin : not_north_ar_tgt_id_y_coord_covers
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : ar_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_y_coord, aruser_tgt_id_y_coord(i));
            end
          end
        end
        else begin : unlimited_ar_tgt_id_y_coord_covers
          if (SRC_DIR == cip_rtr_pkg::NOC_DIR_SOUTH) begin : south_ar_tgt_ycoord_value
            // for southwards direction, tgt_id_y_coord is never at CIP_RTR_GRID_COORD_Y_END
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : ar_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_y_coord, aruser_tgt_id_y_coord(i));
            end
          end
          else begin : not_south_ar_tgt_id_y_coord_value
            for (i=cip_pkg::CIP_RTR_GRID_COORD_Y_START; i<=cip_pkg::CIP_RTR_GRID_COORD_Y_END; i++) begin : ar_tgt_id_y_coord_value
              `SV_COVER (FVPH_RTR_FV_co_aruser_tgt_id_y_coord, aruser_tgt_id_y_coord(i));
            end
          end
        end

        for (i=0; i<4; i++) begin : ar_noc_id_value
          `SV_COVER (FVPH_RTR_FV_co_aruser_noc_id, aruser_noc_id(i));
        end

        for (i=0; i<READ_VCS; i++) begin : ar_user_vc_value
          `SV_COVER (FVPH_RTR_FV_co_aruser_vc, aruser_vc(i));
        end

        for (i=0; i<4; i++) begin : ar_len_value
          `SV_COVER (FVPH_RTR_FV_co_arlen, arid_len(i));
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

  end  // if (CNOC_INPUT == 1)
  else if (CNOC_INPUT == 0) begin : cnoc_out_checker

    // ttl
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_ttl_always_at_least_1, cnoc_ttl_always_at_least_1);
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_ttl_always_within_maximum, cnoc_ttl_always_within_maximum);

    if (SKIP_CREDIT_RELEASE_CHECKS == 0) begin : credit_release_checks

      // credit counter
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_credit_releases
        if (VALID_CNOC_VC[i]) begin
          /*@AXM  CNOC credit release signal never asserted more times than there were CNOC valids seen  @*/
          `SV_ASSERT (FVPH_RTR_FV_am_cnoc_credit_releases_no_excess, cnoc_credit_releases_no_excess(i));
        end
      end

      // each valid has credit
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_valids
        if (VALID_CNOC_VC[i]) begin
          `SV_ASSERT (FVPH_RTR_FV_as_cnoc_valid_with_sufficient_credit, cnoc_valid_with_sufficient_credit(i));
        end
      end

     `ifdef FORMAL  // liveness property, not handled by simulation
        // credit release
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : eventual_credit_release
          if (VALID_CNOC_VC[i]) begin
            /*@AXM  for every CNOC valid sent, a CNOC credit release will always eventually appear  @*/
            `SV_ASSERT (FVPH_RTR_FV_am_cnoc_credit_release_for_each_valid_liveness, cnoc_credit_release_for_each_valid_liveness(i));
          end
        end
      `endif  // ifdef FORMAL

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_reach_zero_credits
        if (VALID_CNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_cnoc_credit_counter_can_reach_zero, cnoc_credit_counter_can_reach_zero(i));
        end
      end

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_go_from_zero_to_maximum_credits
        if (VALID_CNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_cnoc_credit_counter_zero_to_maximum_liveness, cnoc_credit_counter_zero_to_maximum_liveness(i));
        end
      end

    end  // if (SKIP_CREDIT_RELEASE_CHECKS == 0)

    if (USES_WRITE_VCS == 1) begin : write_channel

      // AXI B channel

      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_btgtid_coords_within_grid, btgtid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_buser_vc_is_legal,         buser_vc_is_legal);

    end  // if (USES_WRITE_VCS == 1)

    if (USES_READ_VCS == 1) begin : read_channel

      // AXI AR channel

      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_arhost_size_field_is_legal, arhost_size_field_is_legal);

      if (cip_pkg::CIP_DAXI_AR_ADDR_WIDTH > 12) begin : addr_width_more_than_12
        `SV_ASSERT (FVPH_RTR_FV_as_cnoc_araddr_burst_within_4kb_boundary, araddr_burst_within_4kb_boundary);
      end

      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_arsrcid_coords_within_grid, arsrcid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_artgtid_coords_within_grid, artgtid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_aruser_vc_is_legal,         aruser_vc_is_legal);

    end  // if (USES_READ_VCS == 1)

  end  // if (CNOC_INPUT == 0)
  else if (CNOC_INPUT == 2) begin : cnoc_all_asserts

    // ttl
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_ttl_always_at_least_1, cnoc_ttl_always_at_least_1);
    `SV_ASSERT (FVPH_RTR_FV_as_cnoc_ttl_always_within_maximum, cnoc_ttl_always_within_maximum);

    if (SKIP_CREDIT_RELEASE_CHECKS == 0) begin : credit_release_checks
      // credit counter
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_credit_releases
        if (VALID_CNOC_VC[i]) begin
          `SV_ASSERT (FVPH_RTR_FV_as_cnoc_credit_releases_no_excess, cnoc_credit_releases_no_excess(i));
        end
      end

      // each valid has credit
      for (i=0; i<TOTAL_NUM_VCS; i++) begin : not_too_many_valids
        if (VALID_CNOC_VC[i]) begin
          `SV_ASSERT (FVPH_RTR_FV_as_cnoc_valid_with_sufficient_credit, cnoc_valid_with_sufficient_credit(i));
        end
      end

     `ifdef FORMAL  // liveness property, not handled by simulation
        // credit release
        for (i=0; i<TOTAL_NUM_VCS; i++) begin : eventual_credit_release
          if (VALID_CNOC_VC[i]) begin
            `SV_ASSERT (FVPH_RTR_FV_as_cnoc_credit_release_for_each_valid_liveness, cnoc_credit_release_for_each_valid_liveness(i));
          end
        end
      `endif  // ifdef FORMAL

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_reach_zero_credits
        if (VALID_CNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_cnoc_credit_counter_can_reach_zero, cnoc_credit_counter_can_reach_zero(i));
        end
      end

      for (i=0; i<TOTAL_NUM_VCS; i++) begin : can_go_from_zero_to_maximum_credits
        if (VALID_CNOC_VC[i]) begin
          `SV_COVER (FVPH_RTR_FV_co_cnoc_credit_counter_zero_to_maximum_liveness, cnoc_credit_counter_zero_to_maximum_liveness(i));
        end
      end

    end  // if (SKIP_CREDIT_RELEASE_CHECKS == 0)

    if (USES_WRITE_VCS == 1) begin : write_channel

      // AXI B channel

      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_btgtid_coords_within_grid, btgtid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_buser_vc_is_legal,         buser_vc_is_legal);

    end  // if (USES_WRITE_VCS == 1)

    if (USES_READ_VCS == 1) begin : read_channel

      // AXI AR channel

      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_arhost_size_field_is_legal,       arhost_size_field_is_legal);

      if (cip_pkg::CIP_DAXI_AR_ADDR_WIDTH > 12) begin : addr_width_more_than_12
        `SV_ASSERT (FVPH_RTR_FV_as_cnoc_araddr_burst_within_4kb_boundary, araddr_burst_within_4kb_boundary);
      end

      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_arsrcid_coords_within_grid, arsrcid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_artgtid_coords_within_grid, artgtid_coords_within_grid);
      `SV_ASSERT (FVPH_RTR_FV_as_cnoc_aruser_vc_is_legal,         aruser_vc_is_legal);

    end  // if (USES_READ_VCS == 1)

  end  // if (CNOC_INPUT == 2)
  endgenerate

endmodule // fbaxi_cnoc_checker
