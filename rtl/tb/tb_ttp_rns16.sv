`timescale 1ns/1ps

//==============================================================================
// Self-checking testbench for the TTP RNS-16 RTL.
//
//  1. Exhaustive Dual-Adder check for P = 2, 3, 5, 53.
//  2. 16-channel Phase-Diode core: 10,000 sequential steps from reference
//     points, checked against gcd(n, M16) == 1 (M16 = 53#).
//  3. Vector landing unit: reference model and next-prime landing checks.
//
// Build:  --binary --sv --Wall --timing --top-module tb_ttp_rns16
//==============================================================================
module tb_ttp_rns16;

    logic clk = 1'b0;
    always #5 clk <= ~clk;

    int unsigned checks = 0;
    int unsigned errors = 0;

    localparam longint unsigned ANCHORS [6] = '{64'd1001, 64'd1025, 64'd1501, 64'd2001,
                                                 64'd1000000, 64'd1000000000000};

    task automatic check(input logic cond, input string msg);
        checks++;
        if (!cond) begin
            errors++;
            $display("ERROR [%0t]: %s", $time, msg);
        end
    endtask

    //--------------------------------------------------------------------------
    // 1. Exhaustive Dual-Adder cells
    //--------------------------------------------------------------------------
    logic [0:0] r2_in, d2_in, r2_next;
    logic       o2;
    logic [1:0] r3_in, d3_in, r3_next;
    logic       o3;
    logic [2:0] r5_in, d5_in, r5_next;
    logic       o5;
    logic [5:0] r53_in, d53_in, r53_next;
    logic       o53;

    ttp_dual_adder_cell #(.W(1), .P(2))  dut_p2  (.r_in(r2_in),  .delta_in(d2_in),  .r_next(r2_next),  .diode_open(o2));
    ttp_dual_adder_cell #(.W(2), .P(3))  dut_p3  (.r_in(r3_in),  .delta_in(d3_in),  .r_next(r3_next),  .diode_open(o3));
    ttp_dual_adder_cell #(.W(3), .P(5))  dut_p5  (.r_in(r5_in),  .delta_in(d5_in),  .r_next(r5_next),  .diode_open(o5));
    ttp_dual_adder_cell #(.W(6), .P(53)) dut_p53 (.r_in(r53_in), .delta_in(d53_in), .r_next(r53_next), .diode_open(o53));

    task automatic test_dual_adders;
        for (int r = 0; r < 2; r++) begin
            for (int d = 0; d < 2; d++) begin
                r2_in = 1'(r); d2_in = 1'(d); #1;
                check(r2_next == 1'((r + d) % 2),
                      $sformatf("dual P=2 r=%0d d=%0d", r, d));
                check(o2 == (((r + d) % 2) != 0),
                      $sformatf("diode P=2 r=%0d d=%0d", r, d));
            end
        end
        for (int r = 0; r < 3; r++) begin
            for (int d = 0; d < 3; d++) begin
                r3_in = 2'(r); d3_in = 2'(d); #1;
                check(r3_next == 2'((r + d) % 3),
                      $sformatf("dual P=3 r=%0d d=%0d", r, d));
                check(o3 == (((r + d) % 3) != 0),
                      $sformatf("diode P=3 r=%0d d=%0d", r, d));
            end
        end
        for (int r = 0; r < 5; r++) begin
            for (int d = 0; d < 5; d++) begin
                r5_in = 3'(r); d5_in = 3'(d); #1;
                check(r5_next == 3'((r + d) % 5),
                      $sformatf("dual P=5 r=%0d d=%0d", r, d));
                check(o5 == (((r + d) % 5) != 0),
                      $sformatf("diode P=5 r=%0d d=%0d", r, d));
            end
        end
        for (int r = 0; r < 53; r++) begin
            for (int d = 0; d < 53; d++) begin
                r53_in = 6'(r); d53_in = 6'(d); #1;
                check(r53_next == 6'((r + d) % 53),
                      $sformatf("dual P=53 r=%0d d=%0d", r, d));
                check(o53 == (((r + d) % 53) != 0),
                      $sformatf("diode P=53 r=%0d d=%0d", r, d));
            end
        end
        $display("  dual-adder exhaustive checks: P=2,3,5,53 passed");
    endtask

    //--------------------------------------------------------------------------
    // 2. Phase-Diode RNS-16 core
    //--------------------------------------------------------------------------
    // M16 = 53# = 32589158477190044730 > 2^64
    localparam logic [127:0] M16 = 128'h1C443F2F861D29C3A;

    function automatic logic [71:0] pack_state(input logic [127:0] n);
        logic [71:0] s;
        s = '0;
        s[0  +: 1] = 1'(n % 2);
        s[1  +: 2] = 2'(n % 3);
        s[3  +: 3] = 3'(n % 5);
        s[6  +: 3] = 3'(n % 7);
        s[9  +: 4] = 4'(n % 11);
        s[13 +: 4] = 4'(n % 13);
        s[17 +: 5] = 5'(n % 17);
        s[22 +: 5] = 5'(n % 19);
        s[27 +: 5] = 5'(n % 23);
        s[32 +: 5] = 5'(n % 29);
        s[37 +: 5] = 5'(n % 31);
        s[42 +: 6] = 6'(n % 37);
        s[48 +: 6] = 6'(n % 41);
        s[54 +: 6] = 6'(n % 43);
        s[60 +: 6] = 6'(n % 47);
        s[66 +: 6] = 6'(n % 53);
        return s;
    endfunction

    function automatic logic [71:0] pack_delta_one;
        logic [71:0] s;
        s = '0;
        s[0]        = 1'b1;
        s[1  +: 2]  = 2'd1;
        s[3  +: 3]  = 3'd1;
        s[6  +: 3]  = 3'd1;
        s[9  +: 4]  = 4'd1;
        s[13 +: 4]  = 4'd1;
        s[17 +: 5]  = 5'd1;
        s[22 +: 5]  = 5'd1;
        s[27 +: 5]  = 5'd1;
        s[32 +: 5]  = 5'd1;
        s[37 +: 5]  = 5'd1;
        s[42 +: 6]  = 6'd1;
        s[48 +: 6]  = 6'd1;
        s[54 +: 6]  = 6'd1;
        s[60 +: 6]  = 6'd1;
        s[66 +: 6]  = 6'd1;
        return s;
    endfunction

    function automatic logic [15:0] expected_channels(input logic [127:0] n);
        logic [15:0] m;
        m[0]  = (n % 2  != 0);
        m[1]  = (n % 3  != 0);
        m[2]  = (n % 5  != 0);
        m[3]  = (n % 7  != 0);
        m[4]  = (n % 11 != 0);
        m[5]  = (n % 13 != 0);
        m[6]  = (n % 17 != 0);
        m[7]  = (n % 19 != 0);
        m[8]  = (n % 23 != 0);
        m[9]  = (n % 29 != 0);
        m[10] = (n % 31 != 0);
        m[11] = (n % 37 != 0);
        m[12] = (n % 41 != 0);
        m[13] = (n % 43 != 0);
        m[14] = (n % 47 != 0);
        m[15] = (n % 53 != 0);
        return m;
    endfunction

    // For squarefree M16 = 53#, gcd(n, M16) == 1 iff no p_i divides n.
    // This is the exact gcd condition without a 128-bit Euclid loop.
    function automatic logic expected_all_open(input logic [127:0] n);
        return &expected_channels(n);
    endfunction

    function automatic logic [127:0] gcd128(input logic [127:0] a, input logic [127:0] b);
        logic [127:0] x, y, t;
        x = a;
        y = b;
        while (y != 0) begin
            t = x % y;
            x = y;
            y = t;
        end
        return x;
    endfunction

    logic        rst_n, load_en, step_en;
    logic [71:0] r_init_bus, delta_bus, r_state_bus;
    logic [15:0] channel_open;
    logic        all_open;

    ttp_phase_diode_rns16 dut_rns (
        .clk          (clk),
        .rst_n        (rst_n),
        .load_en      (load_en),
        .step_en      (step_en),
        .r_init_bus   (r_init_bus),
        .delta_bus    (delta_bus),
        .r_state_bus  (r_state_bus),
        .channel_open (channel_open),
        .all_open     (all_open)
    );

    task automatic run_rns_reference(input logic [127:0] n0, input int unsigned steps, input string label);
        logic [127:0] n;
        logic [127:0] n_next;
        logic [15:0] exp_mask;
        n = n0;

        rst_n = 1'b0;
        load_en = 1'b0;
        step_en = 1'b0;
        r_init_bus = '0;
        delta_bus = '0;
        repeat (3) @(posedge clk);
        #1;
        check(r_state_bus == '0, {label, ": reset state"});
        rst_n = 1'b1;

        r_init_bus = pack_state(n0);
        load_en = 1'b1;
        @(posedge clk);
        #1;
        load_en = 1'b0;
        check(r_state_bus == pack_state(n0), {label, ": load state"});

        delta_bus = pack_delta_one();
        step_en = 1'b1;
        #1;
        for (int k = 0; k < steps; k++) begin
            // The diode tree is combinational on r_next_bus, so before the
            // clock edge all_open already refers to the next state n+1.
            n_next = n + 1;
            exp_mask = expected_channels(n_next);
            check(channel_open == exp_mask,
                  $sformatf("%s: channel_open step %0d", label, k));
            check(all_open == (&exp_mask),
                  $sformatf("%s: all_open step %0d", label, k));
            if ((k % 997 == 0) || (k == steps - 1)) begin
                check(((gcd128(n_next, M16) == 1) == (&exp_mask)),
                      $sformatf("%s: gcd(M16) step %0d", label, k));
            end
            n = n_next;
            @(posedge clk);
            #1;
            check(r_state_bus == pack_state(n),
                  $sformatf("%s: r_state step %0d", label, k));
        end
        step_en = 1'b0;
        @(posedge clk);
        #1;
    endtask

    //--------------------------------------------------------------------------
    // 3. Vector landing unit
    //--------------------------------------------------------------------------
    logic [71:0] r_anchor_bus;
    logic [71:0] delta_rom [1:32];
    logic [5:0]  delta_n_req;
    logic [6:0]  landing_offset_even;

    ttp_vector_landing_unit #(.W_VEC(32)) dut_vec (
        .r_anchor_bus        (r_anchor_bus),
        .delta_rom           (delta_rom),
        .delta_n_req         (delta_n_req),
        .landing_offset_even (landing_offset_even)
    );

    function automatic logic [6:0] expected_landing(input logic [127:0] n0, input logic [5:0] req);
        logic [31:0] mask;
        logic [5:0]  prefix;
        int unsigned cnt;
        mask = '0;
        for (int s = 1; s <= 31; s++) begin
            mask[s] = expected_all_open(n0 + 2 * s);
        end
        prefix = '0;
        cnt = 0;
        for (int j = 0; j < 32; j++) begin
            if (j > 0) begin
                prefix = prefix + {{5{1'b0}}, mask[j]};
            end
            if (prefix < req) begin
                cnt++;
            end
        end
        return 7'(2 * cnt);
    endfunction

    function automatic logic is_prime64(input logic [63:0] n);
        if (n < 2) return 1'b0;
        for (int d = 2; d * d <= n; d++) begin
            if (n % 64'(d) == 0) return 1'b0;
        end
        return 1'b1;
    endfunction

    // delta_rom is constant; drive it at time 0.  Verilator 5.020 does not
    // propagate later procedural updates of an unpacked-array input port to
    // the generated slice cells, so this initialization must precede delays.
    initial begin
        for (int s = 1; s <= 32; s++) begin
            delta_rom[s] = pack_state(128'(2 * s));
        end
    end

    task automatic run_vector_tests;
        for (int a = 0; a < 6; a++) begin
            logic [127:0] n0;
            n0 = 128'(ANCHORS[a]);
            r_anchor_bus = pack_state(n0);
            for (int req = 0; req <= 32; req++) begin
                delta_n_req = 6'(req);
                #1;
                check(landing_offset_even == expected_landing(n0, 6'(req)),
                      $sformatf("vector anchor=%0d req=%0d dut=%0d exp=%0d",
                                ANCHORS[a], req, landing_offset_even,
                                expected_landing(n0, 6'(req))));
            end

            // Next-prime landing for the small anchors (n0 + 2s < 53^2).
            if (ANCHORS[a] < 2809) begin
                int first_s = 0;
                for (int s = 1; s <= 31; s++) begin
                    if (expected_all_open(n0 + 2 * s) && (first_s == 0)) begin
                        first_s = s;
                    end
                end
                check(first_s > 0, $sformatf("vector anchor=%0d: no open shift", ANCHORS[a]));
                if (first_s > 0) begin
                    delta_n_req = 6'd1;
                    #1;
                    check(landing_offset_even == 7'(2 * first_s),
                          $sformatf("vector anchor=%0d: first landing", ANCHORS[a]));
                    check(is_prime64(64'(n0 + 128'(landing_offset_even))),
                          $sformatf("vector anchor=%0d: landing is prime", ANCHORS[a]));
                end
            end
        end
        $display("  vector landing checks: 6 anchors x 33 requests passed");
    endtask

    //--------------------------------------------------------------------------
    // Main
    //--------------------------------------------------------------------------
    initial begin
        $display("==============================================================================");
        $display("TTP RNS-16 SELF-CHECKING TESTBENCH");
        $display("M16 = 53# = 32589158477190044730 = 128'h%h", M16);
        $display("==============================================================================");

        test_dual_adders();
        $display("  phase-diode references: 1, 1e6, 1e12, 2e19, 2^64-1 (10,000 steps each)");
        run_rns_reference(128'd1, 10000, "n0=1");
        run_rns_reference(128'd1000000, 10000, "n0=1e6");
        run_rns_reference(128'd1000000000000, 10000, "n0=1e12");
        run_rns_reference(128'd20000000000000000000, 10000, "n0=2e19");
        run_rns_reference(128'd18446744073709551615, 10000, "n0=2^64-1");
        run_vector_tests();

        $display("==============================================================================");
        if (errors == 0) begin
            $display("TB PASS: %0d checks, 0 errors", checks);
        end else begin
            $display("TB FAIL: %0d checks, %0d errors", checks, errors);
        end
        $display("==============================================================================");
        $finish;
    end

endmodule
