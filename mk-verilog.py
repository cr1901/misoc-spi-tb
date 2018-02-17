from migen import *
from misoc.interconnect.csr_bus import *
from misoc.cores.spi import SPIMaster
import mival

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
    # from migen.fhdl.verilog import convert

    # r = convert(dut, ios = {pads.clk, pads.cs_n, pads.mosi, pads.miso,
    #                         dut.bus.bus.adr, dut.bus.bus.we, dut.bus.bus.dat_r,
    #                         dut.bus.bus.dat_w})
    r = mival.annotate(dut, "asserts.v", ios = {pads.clk, pads.cs_n, pads.mosi, pads.miso,
                            dut.bus.bus.adr, dut.bus.bus.we, dut.bus.bus.dat_r,
                            dut.bus.bus.dat_w})
    r.write("spi-master.v")
