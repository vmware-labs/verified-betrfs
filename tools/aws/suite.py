# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

import os

class Value:
    def __init__(self, label, param_value):
        self.label = label
        self.param_value = param_value

    def __repr__(self):
        return "#(%s)" % self.label

class Variable:
    def __init__(self, label, type, values):
        self.label = label
        self.type = type
        self.values = values
        for value in self.values:
            value.variable = self

    def __repr__(self):
        return "$(%s)" % self.label

class Variant:
    def __init__(self, suite, values):
        self.suite = suite
        self.values = values
        self.valmap = dict([(value.variable, value) for value in values])
        self.make_label()

    def make_label(self):
        parts = []
        for val in self.values:
            val_label_set = self.suite.value_label_set_for_variable_label(val.variable.label)
            if len(val_label_set)>1:
                parts.append("%s" % val.label)
        self.label_ = "-".join(parts)

    def get_label(self):
        return self.label_

    def __repr__(self):
        return self.get_label()

    def outfile(self):
        return "expresults/%s-%s.data" % (self.suite.label, self.get_label())

    def vars_of_type(self, type_label):
        return [val.variable for val in self.values if val.variable.type == type_label]

    def value_by_name(self, label):
        match = [val for val in self.values if val.variable.label == label]
        assert len(match)==1
        return match[0]

    def git_branch(self):
        return self.valmap[self.vars_of_type("git_branch")[0]].param_value

    def infrastructure_branch(self):
        return self.valmap[self.vars_of_type("infrastructure_branch")[0]].param_value

    def run_veri_params(self):
        return [self.valmap[var].param_value for var in self.vars_of_type("run_veri")]

class BaseSuite:
    def __init__(self, label):
        self.label = label

    def png_filename(self):
        return "%s.png" % self.label

    def plot_command(self):
        return " ".join([
            "tools/plot/perf-compare.py",
            "output=%s" % self.png_filename()] + [variant.get_label()+"="+variant.outfile() for variant in self.variants])

    def logpath(self):
        return os.path.join("logs", self.label+".log")

class Suite(BaseSuite):
    def __init__(self, label, *variables):
        super().__init__(label)
        self.variables = variables
        self.variables_by_label = dict([(v.label,v) for v in self.variables])
        self.variants = self.make_variants(self.variables)

    def vars_of_type(self, type):
        return [var for var in self.variables if var.type==type]

    def value_label_set_for_variable_label(self, var_label):
        try:
            var = self.variables_by_label[var_label]
            return set([val.label for val in var.values])
        except KeyError:
            return set()

    def make_variants(self, variables):
        if len(variables) == 1:
            result = [Variant(self, [value]) for value in variables[0].values]
        else:
            variants = []
            for value in variables[0].values:
                for sub_variant in self.make_variants(variables[1:]):
                    variants.append(Variant(self, [value] + sub_variant.values))
            result = variants
        return result

class ConcatSuite(BaseSuite):
    def __init__(self, label, *suites):
        super().__init__(label)
        self.suites = suites
        self.variants = []
        for suite in self.suites:
            for variant in suite.variants:
                self.variants.append(Variant(self, variant.values))

    def value_label_set_for_variable_label(self, var_label):
        val_label_set = set()
        for sub_suite in self.suites:
            val_label_set = val_label_set.union(sub_suite.value_label_set_for_variable_label(var_label))
        return val_label_set
