initial assume ($rst("sys") == 1);

always @* begin
    /* if (($dut(m.spi.bits.n_read) == 0) && ($dut(m.spi.bits.n_write) == 0)) begin
        assert ($find(m.spi, "write0") == 0);
    end */

    if (($dut(m._active.status) == 1)) begin
        assume ($dut(m.bus.bus.we) == 0);
    end

    // User's responsibility to query pending.
    if ($find(m, "pending") == 1)) begin
        assume($dut(m._data_write.re) == 0);
    end
end

//assert property ()
assert property ($find(m.spi.cg, "cnt") <= $dut(m.spi.cg.load));

// Temporary assumptions
assume property ($dut(m._clk_div_read.storage) == 5);
assume property ($dut(m._clk_div_write.storage) == 3);
assume property ($dut(m._clk_polarity.storage) == 0);


// Ensure sys_clk is always ticking.
reg last_clk = 0;
always @(\$global_clock) begin
    last_clk <= $clk("sys");
    assume(last_clk != $clk("sys"));
end
