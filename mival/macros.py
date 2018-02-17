$macro(dut, field)\
$py(tmp = r.ns.get_name(field))\
$(tmp)\
$endmacro\
\
$macro(rst, name)\
$py(tmp = r.ns.get_name(ResetSignal(name)))\
$(tmp)\
$endmacro\
\
$macro(clk, name)\
$py(tmp = r.ns.get_name(ClockSignal(name)))\
$(tmp)\
$endmacro\
\
$#$macro(global_clock)\
$#"\$global_clock"\
$#$endmacro\
