PROJECT=spi-master

check: $(PROJECT).smt2
	yosys-smtbmc -s z3 -t 20 --dump-smt2 $(PROJECT)_bmc.smt2 --dump-vcd $(PROJECT)_bmc.vcd $(PROJECT).smt2
	yosys-smtbmc -s z3 -i -t 20 --dump-smt2 $(PROJECT)_tmp.smt2 --dump-vcd $(PROJECT)_tmp.vcd $(PROJECT).smt2

$(PROJECT).smt2: $(PROJECT).v
	yosys -ql spi.yslog -s formal.ys

spi-master.v: mk-verilog.py
	python3 mk-verilog.py

clean::
	rm -f spi.yslog $(PROJECT)_*.* $(PROJECT).smt2 spi_sim.* spi-master.v
