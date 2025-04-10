<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>4</insertion-point-position>
  <wave>
    <expr>clk</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr>&lt;&lt;Target&gt;&gt;::tx</expr>
    <label>&lt;&lt;Target&gt;&gt;::tx</label>
    <wave>
      <expr>noc_in[0].channel</expr>
      <label/>
      <radix>noc_in[0].channel</radix>
    </wave>
    <wave>
      <expr>noc_in_valid[0]</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave>
    <expr>u_mnm_dnoc_routing_sva.noc_in[0].channel</expr>
    <label/>
    <radix>noc_in[0].channel</radix>
  </wave>
  <wave collapsed="true">
    <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.vc</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr>rtr_location</expr>
    <label>rtr_location</label>
    <radix/>
    <group collapsed="true">
      <expr>rtr_location.chip_id</expr>
      <label>rtr_location.chip_id</label>
      <radix/>
      <wave>
        <expr>rtr_location.chip_id.x</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>rtr_location.chip_id.y</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>rtr_location.chip_id.z</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <wave collapsed="true">
      <expr>rtr_location.xcoord</expr>
      <label/>
      <radix>dec</radix>
    </wave>
    <wave collapsed="true">
      <expr>rtr_location.ycoord</expr>
      <label/>
      <radix>dec</radix>
    </wave>
    <group collapsed="false">
      <expr>rtr_location.orientation</expr>
      <label>rtr_location.orientation</label>
      <radix/>
      <wave>
        <expr>rtr_location.orientation.flip_ew</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>rtr_location.orientation.flip_ns</expr>
        <label/>
        <radix/>
      </wave>
    </group>
  </group>
  <group collapsed="true">
    <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id</expr>
    <label>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id</label>
    <radix/>
    <group collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.chip_id</expr>
      <label>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.chip_id</label>
      <radix/>
      <wave>
        <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.chip_id.x</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.chip_id.y</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.chip_id.z</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <wave collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.xcoord</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.ycoord</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.src_id.zcoord</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id</expr>
    <label>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id</label>
    <radix/>
    <group collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.chip_id</expr>
      <label>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.chip_id</label>
      <radix/>
      <wave>
        <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.chip_id.x</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.chip_id.y</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.chip_id.z</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <wave collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.xcoord</expr>
      <label/>
      <radix>dec</radix>
    </wave>
    <wave collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.ycoord</expr>
      <label/>
      <radix>dec</radix>
    </wave>
    <wave collapsed="true">
      <expr>u_mnm_dnoc_routing_sva.noc_in[0].payload.daxi_combo_aw_w.aw.user.tgt_id.zcoord</expr>
      <label/>
      <radix>dec</radix>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>main.east0_lane.rx_east0.rx_destid</expr>
    <label/>
    <radix>main.east0_lane.rx_east0.rx_destid</radix>
  </wave>
</wavelist>
