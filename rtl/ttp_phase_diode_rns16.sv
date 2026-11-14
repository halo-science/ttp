`timescale 1ns/1ps

module ttp_phase_diode_rns16 (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        load_en,
    input  logic        step_en,
    input  logic [71:0] r_init_bus,   // Начальный вектор вычетов по 16 осям
    input  logic [71:0] delta_bus,    // Вектор приращений шага delta_i = Delta mod p_i
    output logic [71:0] r_state_bus,  // Текущее состояние на торе T^16
    output logic [15:0] channel_open, // Поканальная маска открытых диодов
    output logic        all_open      // Глобальный выход дерева Фазового Диода D_16
);
    logic [71:0] r_next_bus;

    // Explicit channel instantiations keep the RTL compatible with the
    // Yosys 0.33 SystemVerilog frontend (no unpacked-array localparams).
    ttp_dual_adder_cell #(.W(1), .P(2))  u_ch0  (.r_in(r_state_bus[0  +: 1]), .delta_in(delta_bus[0  +: 1]), .r_next(r_next_bus[0  +: 1]), .diode_open(channel_open[0]));
    ttp_dual_adder_cell #(.W(2), .P(3))  u_ch1  (.r_in(r_state_bus[1  +: 2]), .delta_in(delta_bus[1  +: 2]), .r_next(r_next_bus[1  +: 2]), .diode_open(channel_open[1]));
    ttp_dual_adder_cell #(.W(3), .P(5))  u_ch2  (.r_in(r_state_bus[3  +: 3]), .delta_in(delta_bus[3  +: 3]), .r_next(r_next_bus[3  +: 3]), .diode_open(channel_open[2]));
    ttp_dual_adder_cell #(.W(3), .P(7))  u_ch3  (.r_in(r_state_bus[6  +: 3]), .delta_in(delta_bus[6  +: 3]), .r_next(r_next_bus[6  +: 3]), .diode_open(channel_open[3]));
    ttp_dual_adder_cell #(.W(4), .P(11)) u_ch4  (.r_in(r_state_bus[9  +: 4]), .delta_in(delta_bus[9  +: 4]), .r_next(r_next_bus[9  +: 4]), .diode_open(channel_open[4]));
    ttp_dual_adder_cell #(.W(4), .P(13)) u_ch5  (.r_in(r_state_bus[13 +: 4]), .delta_in(delta_bus[13 +: 4]), .r_next(r_next_bus[13 +: 4]), .diode_open(channel_open[5]));
    ttp_dual_adder_cell #(.W(5), .P(17)) u_ch6  (.r_in(r_state_bus[17 +: 5]), .delta_in(delta_bus[17 +: 5]), .r_next(r_next_bus[17 +: 5]), .diode_open(channel_open[6]));
    ttp_dual_adder_cell #(.W(5), .P(19)) u_ch7  (.r_in(r_state_bus[22 +: 5]), .delta_in(delta_bus[22 +: 5]), .r_next(r_next_bus[22 +: 5]), .diode_open(channel_open[7]));
    ttp_dual_adder_cell #(.W(5), .P(23)) u_ch8  (.r_in(r_state_bus[27 +: 5]), .delta_in(delta_bus[27 +: 5]), .r_next(r_next_bus[27 +: 5]), .diode_open(channel_open[8]));
    ttp_dual_adder_cell #(.W(5), .P(29)) u_ch9  (.r_in(r_state_bus[32 +: 5]), .delta_in(delta_bus[32 +: 5]), .r_next(r_next_bus[32 +: 5]), .diode_open(channel_open[9]));
    ttp_dual_adder_cell #(.W(5), .P(31)) u_ch10 (.r_in(r_state_bus[37 +: 5]), .delta_in(delta_bus[37 +: 5]), .r_next(r_next_bus[37 +: 5]), .diode_open(channel_open[10]));
    ttp_dual_adder_cell #(.W(6), .P(37)) u_ch11 (.r_in(r_state_bus[42 +: 6]), .delta_in(delta_bus[42 +: 6]), .r_next(r_next_bus[42 +: 6]), .diode_open(channel_open[11]));
    ttp_dual_adder_cell #(.W(6), .P(41)) u_ch12 (.r_in(r_state_bus[48 +: 6]), .delta_in(delta_bus[48 +: 6]), .r_next(r_next_bus[48 +: 6]), .diode_open(channel_open[12]));
    ttp_dual_adder_cell #(.W(6), .P(43)) u_ch13 (.r_in(r_state_bus[54 +: 6]), .delta_in(delta_bus[54 +: 6]), .r_next(r_next_bus[54 +: 6]), .diode_open(channel_open[13]));
    ttp_dual_adder_cell #(.W(6), .P(47)) u_ch14 (.r_in(r_state_bus[60 +: 6]), .delta_in(delta_bus[60 +: 6]), .r_next(r_next_bus[60 +: 6]), .diode_open(channel_open[14]));
    ttp_dual_adder_cell #(.W(6), .P(53)) u_ch15 (.r_in(r_state_bus[66 +: 6]), .delta_in(delta_bus[66 +: 6]), .r_next(r_next_bus[66 +: 6]), .diode_open(channel_open[15]));

    // Дерево Фазового Диода глубины log2(16) = 4 (редукция И по всем 16 осям)
    assign all_open = &channel_open;

    // Синхронное обновление регистрового файла за 1 такт без межканального переноса
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_state_bus <= 72'd0;
        end else if (load_en) begin
            r_state_bus <= r_init_bus;
        end else if (step_en) begin
            r_state_bus <= r_next_bus;
        end
    end
endmodule
