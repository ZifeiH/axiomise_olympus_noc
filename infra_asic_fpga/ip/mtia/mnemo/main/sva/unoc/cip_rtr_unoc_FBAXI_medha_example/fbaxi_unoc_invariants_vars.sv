///////////////////////////////////////////////////
/// File: fbaxi_unoc_invariants_vars.sv
/// This file contains variables needed for invariants
///////////////////////////////////////////////////

cip_pkg::utility_noc_t tx_rd_mux_vc_out;
cip_pkg::utility_noc_t [5:0] [4:0] u_tx_perSrc_perVc_dfifo_out;
cip_pkg::utility_noc_t [4:0] tx_rd_mux_rx_out;
cip_pkg::utility_noc_t sdata [4:0][5:0] ;
wire [5:0] u_tx_rd_mux_rx_sel0;
wire [5:0] u_tx_rd_mux_rx_sel1;
wire [5:0] u_tx_rd_mux_rx_sel2;
wire [5:0] u_tx_rd_mux_rx_sel3;
wire [5:0] u_tx_rd_mux_rx_sel4;

wire [4:0] dfifo_pop1;
wire [4:0] dfifo_pop2;
wire [4:0] dfifo_pop3;


if (DIR == 0) begin : north

assign tx_rd_mux_vc_out = `UNOC_IRTR_N_TX.u_tx_rd_mux_vc.out;

assign dfifo_pop1 = dfifo_pop[1][5:1];
assign dfifo_pop2 = dfifo_pop[2][5:1];
assign dfifo_pop3 = dfifo_pop[3][5:1];

for(j = 0; j < 6; j++) begin
    for(i = 0; i < 5; i++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign u_tx_perSrc_perVc_dfifo_out[j][i] = `UNOC_IRTR_N_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.out;
    end
end

for(i = 0; i < 5; i++) begin
    assign tx_rd_mux_rx_out[i] = `UNOC_IRTR_N_TX.genblk3[i].u_tx_rd_mux_rx.out;
end



for(i = 0; i < 5; i++) begin
    for(j = 0; j < 6; j++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign sdata[i][j] = `UNOC_IRTR_N_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.flop_based.selected_data;
    end
end


for(j = 0; j < 6; j++) begin
    assign u_tx_rd_mux_rx_sel0[j] = `UNOC_IRTR_N_TX.genblk3[0].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel1[j] = `UNOC_IRTR_N_TX.genblk3[1].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel2[j] = `UNOC_IRTR_N_TX.genblk3[2].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel3[j] = `UNOC_IRTR_N_TX.genblk3[3].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel4[j] = `UNOC_IRTR_N_TX.genblk3[4].u_tx_rd_mux_rx.sel[j];
end

end
else if (DIR == 2) begin : south


assign tx_rd_mux_vc_out = `UNOC_IRTR_S_TX.u_tx_rd_mux_vc.out;

assign dfifo_pop1 = {dfifo_pop[1][5:3], dfifo_pop[1][1:0]};
assign dfifo_pop2 = {dfifo_pop[2][5:3], dfifo_pop[2][1:0]};
assign dfifo_pop3 = {dfifo_pop[3][5:3], dfifo_pop[3][1:0]};


for(j = 0; j < 6; j++) begin
    for(i = 0; i < 5; i++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign u_tx_perSrc_perVc_dfifo_out[j][i] = `UNOC_IRTR_S_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.out;
    end
end


for(i = 0; i < 5; i++) begin
    assign tx_rd_mux_rx_out[i] = `UNOC_IRTR_S_TX.genblk3[i].u_tx_rd_mux_rx.out;
end



for(i = 0; i < 5; i++) begin
    for(j = 0; j < 6; j++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign sdata[i][j] = `UNOC_IRTR_S_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.flop_based.selected_data;
    end
end


for(j = 0; j < 6; j++) begin
    assign u_tx_rd_mux_rx_sel0[j] = `UNOC_IRTR_S_TX.genblk3[0].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel1[j] = `UNOC_IRTR_S_TX.genblk3[1].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel2[j] = `UNOC_IRTR_S_TX.genblk3[2].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel3[j] = `UNOC_IRTR_S_TX.genblk3[3].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel4[j] = `UNOC_IRTR_S_TX.genblk3[4].u_tx_rd_mux_rx.sel[j];
end

end
else if (DIR == 1) begin : west

assign dfifo_pop1 = {dfifo_pop[1][5:2], dfifo_pop[1][0]};
assign dfifo_pop2 = {dfifo_pop[2][5:2], dfifo_pop[2][0]};
assign dfifo_pop3 = {dfifo_pop[3][5:2], dfifo_pop[3][0]};


assign tx_rd_mux_vc_out = `UNOC_IRTR_W_TX.u_tx_rd_mux_vc.out;


for(j = 0; j < 6; j++) begin
    for(i = 0; i < 5; i++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign u_tx_perSrc_perVc_dfifo_out[j][i] = `UNOC_IRTR_W_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.out;
    end
end


for(i = 0; i < 5; i++) begin
    assign tx_rd_mux_rx_out[i] = `UNOC_IRTR_W_TX.genblk3[i].u_tx_rd_mux_rx.out;
end



for(i = 0; i < 5; i++) begin
    for(j = 0; j < 6; j++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign sdata[i][j] = `UNOC_IRTR_W_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.flop_based.selected_data;
    end
end


for(j = 0; j < 6; j++) begin
    assign u_tx_rd_mux_rx_sel0[j] = `UNOC_IRTR_W_TX.genblk3[0].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel1[j] = `UNOC_IRTR_W_TX.genblk3[1].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel2[j] = `UNOC_IRTR_W_TX.genblk3[2].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel3[j] = `UNOC_IRTR_W_TX.genblk3[3].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel4[j] = `UNOC_IRTR_W_TX.genblk3[4].u_tx_rd_mux_rx.sel[j];
end

end
else if (DIR == 3) begin : east

assign tx_rd_mux_vc_out = `UNOC_IRTR_E_TX.u_tx_rd_mux_vc.out;


assign dfifo_pop1 = {dfifo_pop[1][5:4], dfifo_pop[1][2:0]};
assign dfifo_pop2 = {dfifo_pop[2][5:4], dfifo_pop[2][2:0]};
assign dfifo_pop3 = {dfifo_pop[3][5:4], dfifo_pop[3][2:0]};

for(j = 0; j < 6; j++) begin
    for(i = 0; i < 5; i++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
        assign u_tx_perSrc_perVc_dfifo_out[j][i] = `UNOC_IRTR_E_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.out;
    end
end


for(i = 0; i < 5; i++) begin
    assign tx_rd_mux_rx_out[i] = `UNOC_IRTR_E_TX.genblk3[i].u_tx_rd_mux_rx.out;
end



for(i = 0; i < 5; i++) begin
    for(j = 0; j < 6; j++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
        assign sdata[i][j] = `UNOC_IRTR_E_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.flop_based.selected_data;
    end
end


for(j = 0; j < 6; j++) begin
    assign u_tx_rd_mux_rx_sel0[j] = `UNOC_IRTR_E_TX.genblk3[0].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel1[j] = `UNOC_IRTR_E_TX.genblk3[1].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel2[j] = `UNOC_IRTR_E_TX.genblk3[2].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel3[j] = `UNOC_IRTR_E_TX.genblk3[3].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel4[j] = `UNOC_IRTR_E_TX.genblk3[4].u_tx_rd_mux_rx.sel[j];
end

end
else if (DIR == 4) begin : fi0


assign tx_rd_mux_vc_out = `UNOC_CRTR_FI0_TX.u_tx_rd_mux_vc.out;

assign dfifo_pop1 = {dfifo_pop[1][5], dfifo_pop[1][3:0]};
assign dfifo_pop2 = {dfifo_pop[2][5], dfifo_pop[2][3:0]};
assign dfifo_pop3 = {dfifo_pop[3][5], dfifo_pop[3][3:0]};

for(j = 0; j < 6; j++) begin
    for(i = 0; i < 5; i++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign u_tx_perSrc_perVc_dfifo_out[j][i] = `UNOC_CRTR_FI0_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.out;
    end
end


for(i = 0; i < 5; i++) begin
    assign tx_rd_mux_rx_out[i] = `UNOC_CRTR_FI0_TX.genblk3[i].u_tx_rd_mux_rx.out;
end



for(i = 0; i < 5; i++) begin
    for(j = 0; j < 6; j++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign sdata[i][j] = `UNOC_CRTR_FI0_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.flop_based.selected_data;
    end
end


for(j = 0; j < 6; j++) begin
    assign u_tx_rd_mux_rx_sel0[j] = `UNOC_CRTR_FI0_TX.genblk3[0].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel1[j] = `UNOC_CRTR_FI0_TX.genblk3[1].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel2[j] = `UNOC_CRTR_FI0_TX.genblk3[2].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel3[j] = `UNOC_CRTR_FI0_TX.genblk3[3].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel4[j] = `UNOC_CRTR_FI0_TX.genblk3[4].u_tx_rd_mux_rx.sel[j];
end

end
else if (DIR == 5) begin : fi1


assign tx_rd_mux_vc_out = `UNOC_IRTR_FI1_TX.u_tx_rd_mux_vc.out;

assign dfifo_pop1 = {dfifo_pop[1][4:0]};
assign dfifo_pop2 = {dfifo_pop[2][4:0]};
assign dfifo_pop3 = {dfifo_pop[3][4:0]};

for(j = 0; j < 6; j++) begin
    for(i = 0; i < 5; i++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign u_tx_perSrc_perVc_dfifo_out[j][i] = `UNOC_IRTR_FI1_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.out;
    end
end


for(i = 0; i < 5; i++) begin
    assign tx_rd_mux_rx_out[i] = `UNOC_IRTR_FI1_TX.genblk3[i].u_tx_rd_mux_rx.out;
end



for(i = 0; i < 5; i++) begin
    for(j = 0; j < 6; j++) begin
            if(!((i == 0 || i == 1 || i == 2) && j == DIR))
                assign sdata[i][j] = `UNOC_IRTR_FI1_TX.genblk1[j].genblk1[i].genblk1.u_tx_perSrc_perVc_dfifo.flop_based.selected_data;
    end
end


for(j = 0; j < 6; j++) begin
    assign u_tx_rd_mux_rx_sel0[j] = `UNOC_IRTR_FI1_TX.genblk3[0].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel1[j] = `UNOC_IRTR_FI1_TX.genblk3[1].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel2[j] = `UNOC_IRTR_FI1_TX.genblk3[2].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel3[j] = `UNOC_IRTR_FI1_TX.genblk3[3].u_tx_rd_mux_rx.sel[j];
    assign u_tx_rd_mux_rx_sel4[j] = `UNOC_IRTR_FI1_TX.genblk3[4].u_tx_rd_mux_rx.sel[j];
end

end
