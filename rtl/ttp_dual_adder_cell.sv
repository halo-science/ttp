`timescale 1ns/1ps

//==============================================================================
// Модуль 1: Бескомпараторная ячейка Dual-Adder и локальный Фазовый Диод (TTP)
// Формально верифицированный эквивалент: TTP.dualAdder (ToroidalMetricsAndRNS.lean)
//==============================================================================
module ttp_dual_adder_cell #(
    parameter int unsigned W = 6,
    parameter int unsigned P = 53
) (
    input  logic [W-1:0] r_in,        // Текущий вычет r_i in [0, P-1]
    input  logic [W-1:0] delta_in,    // Модулярный шаг delta_i in [0, P-1]
    output logic [W-1:0] r_next,      // Новый вычет (r_i + delta_i) mod P
    output logic         diode_open   // Флаг PhaseDiodeOpen: r_next != 0
);
    // Предвычисленная на этапе синтеза константа дополнения C_i = 2^W - P
    localparam logic [W:0] COMP_C = (W+1)'((1 << W) - P);

    // Параллельное вычисление прямой (S0) и смещённой (S1) сумм без компаратора
    logic [W-1:0] sum_direct;
    logic [W:0]   sum_shifted;

    assign sum_direct  = r_in + delta_in;
    assign sum_shifted = {1'b0, r_in} + {1'b0, delta_in} + COMP_C;

    // Мультиплексор 2:1 управляется напрямую старшим битом переноса sum_shifted[W]
    assign r_next     = sum_shifted[W] ? sum_shifted[W-1:0] : sum_direct;

    // Локальный Фазовый Диод: ИЛИ по всем битам выходного вычета
    assign diode_open = |r_next;
endmodule
