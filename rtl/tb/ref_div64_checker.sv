//==============================================================================
// Reference 64-bit divisibility checker for the Yosys synthesis comparison.
// Uses the standard Verilog remainder operator (%) against the 16 TTP primes.
//==============================================================================
module ref_div64_checker (
    input  logic [63:0] n,
    output logic [15:0] div_mask,
    output logic        all_coprime
);
    assign div_mask[0]  = (n % 2  == 0);
    assign div_mask[1]  = (n % 3  == 0);
    assign div_mask[2]  = (n % 5  == 0);
    assign div_mask[3]  = (n % 7  == 0);
    assign div_mask[4]  = (n % 11 == 0);
    assign div_mask[5]  = (n % 13 == 0);
    assign div_mask[6]  = (n % 17 == 0);
    assign div_mask[7]  = (n % 19 == 0);
    assign div_mask[8]  = (n % 23 == 0);
    assign div_mask[9]  = (n % 29 == 0);
    assign div_mask[10] = (n % 31 == 0);
    assign div_mask[11] = (n % 37 == 0);
    assign div_mask[12] = (n % 41 == 0);
    assign div_mask[13] = (n % 43 == 0);
    assign div_mask[14] = (n % 47 == 0);
    assign div_mask[15] = (n % 53 == 0);
    assign all_coprime  = ~|div_mask;
endmodule
