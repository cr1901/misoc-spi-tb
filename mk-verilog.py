from migen import *
from misoc.interconnect.csr_bus import *
from misoc.cores.spi import SPIMaster

class _TestPads:
    def __init__(self):
        self.cs_n = Signal(2)
        self.clk = Signal()
        self.mosi = Signal()
        self.miso = Signal()

class _TestTristate(Module):
    def __init__(self, t):
        oe = Signal()
        self.comb += [
            t.target.eq(t.o),
            oe.eq(t.oe),
            t.i.eq(t.o),
        ]


if __name__ == "__main__":
    from migen.fhdl.specials import Tristate

    pads = _TestPads()
    dut = SPIMaster(pads)
    dut.comb += pads.miso.eq(pads.mosi)
    dut.submodules.bus = bus = CSRBank(dut.get_csrs())
    from migen.fhdl.verilog import convert

    r = convert(dut, ios = {pads.clk, pads.cs_n, pads.mosi, pads.miso,
                            dut.bus.bus.adr, dut.bus.bus.we, dut.bus.bus.dat_r,
                            dut.bus.bus.dat_w})

    lines = str(r).rsplit("\n",3)[0]  # Remove "endmodule" so I can put my proofs next.

    # Append proofs. Try to query namespace if possible.
    gn = r.ns.get_name
    proofs = """
// Assumptions and assertions follow:

`ifdef FORMAL
initial assume ({rst} == 1);

always @* begin
    if (({} == 0) && ({} == 0)) begin
        assert (spi_write0 == 0);
    end

    if (({act} == 1)) begin
        assume ({we} == 0);
    end
end



// Temporary assumptions
assume property (clk_div_read_storage == 1);
assume property (clk_div_write_storage == 0);
assume property (clk_polarity_storage == 0);
assume property (spi_cnt <= spi_load);

// Clock fix
reg last_clk = 0;
always @($global_clock) begin
    last_clk <= {clk};
    assume(last_clk != {clk});
end
`endif

// End assumptions and assertions

""".format(
gn(dut.spi.bits.n_read), gn(dut.spi.bits.n_write),
act=gn(dut._active.status), we=gn(dut.bus.bus.we),
rst=gn(ResetSignal()),
clk=gn(ClockSignal()),
)

    with open("spi-master.v", "w") as fp:
        fp.write(lines + proofs + "endmodule\n")
