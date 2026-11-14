`timescale 1ns/1ps

//==============================================================================
// Module 3: Vector landing unit — W_VEC parallel 16-axis RNS slices (TTP)
// Each slice instantiates 16 combinational Dual-Adder cells (no divider).
//==============================================================================
module ttp_vector_landing_unit #(
    parameter int unsigned W_VEC = 32
) (
    input  logic [71:0]                r_anchor_bus,  // Anchor phase x_* on T^16
    input  logic [71:0]                delta_rom [1:W_VEC], // Constants x(2s) mod p_i
    input  logic [$clog2(W_VEC+1)-1:0] delta_n_req,  // Rank deficit delta_N
    output logic [$clog2(W_VEC+1):0]   landing_offset_even // 2 * sum(1(S(j) < delta_N))
);
    localparam int unsigned CW = $clog2(W_VEC+1);

    // Axis geometry: bit widths, moduli and 72-bit offsets for the 16 prime axes
    localparam int unsigned W_ARR [16] =
        '{1, 2, 3, 3, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6};
    localparam int unsigned P_ARR [16] =
        '{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53};
    localparam int unsigned OFFSET [16] =
        '{0, 1, 3, 6, 9, 13, 17, 22, 27, 32, 37, 42, 48, 54, 60, 66};

    logic [W_VEC:1] diode_mask;
    logic [CW-1:0] prefix_cnt [0:W_VEC-1];
    logic [CW-1:0] step_count;

    genvar s;
    genvar i;

    // 1. Parallel evaluation of all W_VEC shifts x_* + 2s in one combinational pass
    generate
        for (s = 1; s <= W_VEC; s++) begin : gen_parallel_slices
            logic [15:0] slice_open;

            for (i = 0; i < 16; i++) begin : gen_rns_cells
                localparam int unsigned Wi = W_ARR[i];
                localparam int unsigned Pi = P_ARR[i];
                localparam int unsigned Oi = OFFSET[i];

                /* verilator lint_off UNUSED */
                logic [Wi-1:0] unused_next;
                /* verilator lint_on UNUSED */

                ttp_dual_adder_cell #(
                    .W (Wi),
                    .P (Pi)
                ) u_cell (
                    .r_in       (r_anchor_bus[Oi +: Wi]),
                    .delta_in   (delta_rom[s][Oi +: Wi]),
                    .r_next     (unused_next),
                    .diode_open (slice_open[i])
                );
            end

            assign diode_mask[s] = &slice_open;
        end
    endgenerate

    // 2. Prefix summation S(j) and branchless reduction of formula (7.17)
    always_comb begin
        prefix_cnt[0] = '0;
        for (int j = 1; j < W_VEC; j++) begin
            prefix_cnt[j] = prefix_cnt[j-1] + {{(CW-1){1'b0}}, diode_mask[j]};
        end

        step_count = '0;
        for (int j = 0; j < W_VEC; j++) begin
            if (prefix_cnt[j] < delta_n_req) begin
                step_count = step_count + 1'b1;
            end
        end
        landing_offset_even = {step_count, 1'b0}; // Multiplication by 2 via a left shift
    end
endmodule
