import os.path
from operator import itemgetter

from migen import *
from migen.fhdl.structure import *
from migen.fhdl.structure import _Assign, _Operator, _Fragment, _Slice
from migen.fhdl.conv_output import ConvOutput
from migen.fhdl.verilog import convert
import pyexpander.lib as pyexl
import pyexpander.parser as pyexp


# Internal signals that aren't members of a module are still in the namespace.
# Make a best effort to search for it.
# TODO: Improve chances of success. Also try looking for anonymous submodules.
def find_signal(m, name):
    def recurse_until_signal(fr):
        def flatten_or_extend(ls, new):
            if isinstance(new, list):
                ls.extend(new)
            else:
                ls.append(new)

        sigs = []
        # print(fr)
        if isinstance(fr, _Assign):
            for op in (fr.l, fr.r):
                if not isinstance(op, Signal):
                    flatten_or_extend(sigs, recurse_until_signal(op))
                else:
                    flatten_or_extend(sigs, op)
            return sigs

        elif isinstance(fr, _Operator):
            for op in fr.operands:
                if not isinstance(op, Signal):
                    flatten_or_extend(sigs, recurse_until_signal(op))
                else:
                    flatten_or_extend(sigs, op)
            return sigs

        elif isinstance(fr, If):
            for op in (fr.cond, fr.t, fr.f):
                if not isinstance(op, Signal):
                    flatten_or_extend(sigs, recurse_until_signal(op))
                else:
                    flatten_or_extend(sigs, op)
            return sigs

        elif isinstance(fr, list):
            for l in fr:
                if not isinstance(l, Signal):
                    flatten_or_extend(sigs, recurse_until_signal(l))
                else:
                    flatten_or_extend(sigs, l)
            return sigs

        elif isinstance(fr, (_Slice, Constant)):
            # Constant isn't a named signal, and no more recursion can be
            # done, so return.
            return []

        else:
            raise ValueError("Unknown node encountered: " + str(type(fr)))

    found_sigs = []
    for fr in m._fragment.comb:
        found_sigs.extend(recurse_until_signal(fr))

    for _, fr in m._fragment.sync.items():
        found_sigs.extend(recurse_until_signal(fr))

    candidates = []
    ids = set()
    for sig in found_sigs:
        if sig.backtrace[-1][0] == name:
            if not id(sig) in ids:
                candidates.append(sig)
                ids |= {id(sig)}

    if len(candidates) == 0:
        raise ValueError("Unable to identify possible signal candidate. You must manually write out signal name.")
    elif len(candidates) > 1:
        raise ValueError("More than one possible signal candidate. You must manually write out signal name.")
    else:
        return candidates[0]



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
                "fs" : find_signal,
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
