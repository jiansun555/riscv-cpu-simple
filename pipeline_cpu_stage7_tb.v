`timescale 1ns / 1ps

module pipeline_cpu_stage7_tb;

    reg clk, rst;

    cpu_pipeline_stage7 cpu_inst ( .clk(clk), .rst(rst) );

    // 加载新的指令文件
    initial begin
        $readmemh("mul_test.mem", cpu_inst.dp.imem.rom);
    end

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    initial begin
        $display("Pipeline CPU Stage 7 (Multiplier) Testbench Starting...");

        rst = 1; #20;
        rst = 0;
        $display("Reset released. Starting program execution.");

        // 运行足够长的时间以完成程序
        #200;

        $display("\n--- Checking Final State ---");
        // mul x5, x3, x4  (7 * -3 = -21)
        check_reg(5, 32'hFFFFFFEB); 
        // mul x6, x1, x2  (10 * 20 = 200)
        check_reg(6, 32'h000000C8);

        $display("\nPipeline CPU Stage 7 Testbench Finished.");
        $finish;
    end

    // 辅助任务: 检查寄存器值
    task check_reg;
        input [4:0] addr;
        input signed [31:0] expected_value;
        integer val;
    begin
        val = cpu_inst.dp.rf.registers[addr];
        if (val == expected_value) begin
            $display("Register x%0d: PASSED (Value: %h, Expected: %h)", addr, val, expected_value);
        end else begin
            $display("Register x%0d: FAILED (Value: %h, Expected: %h)", addr, val, expected_value);
        end
    end
    endtask

    // (可选) 增加调试打印
    always @(posedge clk) begin
        if (!rst && cpu_inst.dp.id_instruction != 0 && cpu_inst.dp.id_instruction != 32'h00000013) begin
            $display("-------------------- TIME: %0t --------------------", $time);
            $display("PC=%h, ID_instr=%h, EX_instr=%h(mul?%b), MEM_instr=%h, WB_instr=%h", 
                cpu_inst.dp.pc_current, 
                cpu_inst.dp.id_instruction, 
                cpu_inst.dp.ex_reg_write ? cpu_inst.dp.ex_rd : 5'bxxxxx, cpu_inst.dp.ex_is_mul,
                cpu_inst.dp.mem_reg_write ? cpu_inst.dp.mem_rd : 5'bxxxxx,
                cpu_inst.dp.wb_reg_write ? cpu_inst.dp.wb_rd : 5'bxxxxx);
            $display("Stall signals: PCWrite=%b, IF_ID_Write=%b, ID_EX_Bubble=%b",
                cpu_inst.dp.pc_write, cpu_inst.dp.if_id_write, cpu_inst.dp.id_ex_bubble);
        end
    end

endmodule