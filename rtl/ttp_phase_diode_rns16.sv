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
    localparam int unsigned W_ARR [16] = '{1, 2, 3, 3, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6};
    localparam int unsigned P_ARR [16] = '{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53};
    localparam int unsigned OFFSET[16] = '{0, 1, 3, 6, 9, 13, 17, 22, 27, 32, 37, 42, 48, 54, 60, 66};

    logic [71:0] r_next_bus;

    genvar i;
    generate
        for (i = 0; i < 16; i++) begin : gen_rns_channels
            localparam int unsigned Wi = W_ARR[i];
            localparam int unsigned Pi = P_ARR[i];
            localparam int unsigned Oi = OFFSET[i];

            ttp_dual_adder_cell #(
                .W (Wi),
                .P (Pi)
            ) u_cell (
                .r_in       (r_state_bus[Oi +: Wi]),
                .delta_in   (delta_bus  [Oi +: Wi]),
                .r_next     (r_next_bus [Oi +: Wi]),
                .diode_open (channel_open[i])
            );
        end
    endgenerate

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
