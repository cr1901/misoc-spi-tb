initial assume ($rst("sys") == 1);

always @* begin
    /* if (($dut(m.spi.bits.n_read) == 0) && ($dut(m.spi.bits.n_write) == 0)) begin
        assert (\$find(m.spi.bits.write0) == 0);
    end */

    if (($dut(m._active.status) == 1)) begin
        assume ($dut(m.bus.bus.we) == 0);
    end

    // User's responsibility to query pending.
    if ((pending == 1)) begin
        assume(data_write_re == 0);
    end
end

//assert property ()
assert property (spi_cnt <= spi_load);

// Temporary assumptions
assume property (clk_div_read_storage == 5);
assume property (clk_div_write_storage == 3);
assume property (clk_polarity_storage == 0);


// Ensure sys_clk is always ticking.
reg last_clk = 0;
always @(\$global_clock) begin
    last_clk <= $clk("sys");
    assume(last_clk != $clk("sys"));
end
