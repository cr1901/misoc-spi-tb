import os.path
from operator import itemgetter

from migen import *
from migen.fhdl.structure import _Fragment
from migen.fhdl.conv_output import ConvOutput
from migen.fhdl.verilog import convert
import pyexpander.lib as pyexl
import pyexpander.parser as pyexp


# class MivalParser()


# Wrapper class over Migen's verilog ConvOutput class to
# annotate output with formal properties.
class MivalConvOutput(ConvOutput):
    def __init__(self, conv_output_or_none=None):
        ConvOutput.__init__(self)
        self.asserts = ""

    def set_asserts(self, asserts):
        self.asserts = asserts

    def strip_endmodule(self):
        # Remove "endmodule" so assertions will follow.
        return str(self.main_source).rsplit("\n",3)[0]

    def mk_assert_str(self):
        r = """
// Assumptions and assertions follow:

`ifdef FORMAL
"""
        r += self.asserts
        r += """`endif

// End assumptions and assertions

"""
        return r

    def __str__(self):
        r = self.strip_endmodule() + "\n"
        r += self.mk_assert_str() + "\n"
        for filename, content in sorted(self.data_files.items(),
                                        key=itemgetter(0)):
            r += filename + ":\n" + content
        return r

    def write(self, main_filename):
        with open(main_filename, "w") as f:
            f.write(self.strip_endmodule() + self.mk_assert_str() + "endmodule\n")
        for filename, content in self.data_files.items():
            with open(filename, "w") as f:
                f.write(content)


def annotate(module_or_conv, asserts, **kwargs):
    if isinstance(module_or_conv, ConvOutput):
        raise NotImplementedError("ConvOutput as input not yet supported.")
    elif isinstance(module_or_conv, Module) or isinstance(module_or_conv, _Fragment):
        # We need the namespace object to convert Migen names to Verilog names.
        # We may also need the _Fragment/Module to retrieve non-member vars.
        old_conv = convert(module_or_conv, **kwargs)

        # Parse asserts using pyexpander.
        macros = pyexl.parseFile(os.path.join(os.path.dirname(__file__), "macros.py"), False)
        parse_list = pyexl.parseFile(asserts, False)
        # pyexp.pprint(parse_list)
        (assert_list, _) = pyexl.processToList(macros + parse_list,
            external_definitions = {
                "m" : module_or_conv,
                "r" : old_conv,
                "gn" : old_conv.ns.get_name,
                "ResetSignal" : ResetSignal,
                "ClockSignal" : ClockSignal
            },
            auto_continuation=True,
            # include_paths = [os.path.dirname(__file__)]
        )
        assert_str = "".join(assert_list)

        new_conv = MivalConvOutput()
        new_conv.main_source = old_conv.main_source
        new_conv.data_files = old_conv.data_files

        # FIXME: Possibility to detect conflicts and bail with user
        # declarations in asserts that conflict w/ Migen namespace?
        new_conv.ns = old_conv.ns
        new_conv.set_asserts(assert_str)
        return new_conv
    else:
        raise ValueError("Expected ConvOutput, Module, or _Fragment from Migen")
