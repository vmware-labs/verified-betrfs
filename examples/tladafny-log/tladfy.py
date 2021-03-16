# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import sys, re
from parsy import seq, string, regex, generate

whitespace = regex(r'\s*').mark().tag('whitespace')
identifier = regex(r'[A-Za-z_]\w*').mark().tag('identifier')
block_open = string('{').mark().tag('syntax')
block_close = string('}').mark().tag('syntax')

@generate
def block():
    return (yield seq(block_open, block_contents, block_close).mark().tag('block'))

comment_line = regex(r'^\s*//[^\n]*', re.MULTILINE).mark().tag('comment')
comment_multiline = regex(r'\s*/\*((?!\*/)(.|\n))*\*/\s*').mark().tag('comment')
dafny_code = regex(r'((?!/\*)[^{}\n])+').mark().tag('dafny_code')
params = regex(r'[^)\n]*').mark().tag('params')
state_machine_line = seq(whitespace, string('state').mark().tag('keyword'), whitespace, string('machine').mark().tag('keyword'), whitespace, \
        string('k').mark().tag('keyword'), whitespace, string('(').mark().tag('syntax'), params, string(')').mark().tag('syntax'), whitespace, \
        string('s').mark().tag('keyword'), whitespace, string('(').mark().tag('syntax'), params, string(')').mark().tag('syntax'), whitespace, \
        string('step').mark().tag('keyword'), whitespace, string('(').mark().tag('syntax'), params, string(')').mark().tag('syntax'), whitespace).mark().tag('tla.statemachine')
init_line = seq(whitespace, string('init').mark().tag('keyword'), whitespace).mark().tag('tla.init')
step_line = seq(whitespace, string('step').mark().tag('keyword'), whitespace, identifier, whitespace, \
        string('(').mark().tag('syntax'), params, string(')').mark().tag('syntax'), whitespace).mark().tag('tla.step')
block_line = comment_line | state_machine_line | init_line | step_line | dafny_code | string('\n').mark().tag('whitespace')
block_contents = (block | block_line.at_least(1) | comment_multiline).at_least(1).mark().tag('blockcontents')

before_module = regex(r'((?!module)(.|\n))*').mark().tag('beforemodule')
module = seq(whitespace, regex('module').mark().tag('keyword'), whitespace, identifier, whitespace, block).mark().tag('module')

file_ = seq(before_module, module.many(), whitespace)

type_name = regex(r'[A-Za-z_](\w|\.)*').mark().tag('identifier')

@generate
def type_params():
    return (yield seq(string('<'), type_name, seq(whitespace, string(','), whitespace, type_name, whitespace, type_params.optional(), whitespace).many(), string('>')))

formal_arg = seq(identifier, whitespace, string(':').mark().tag('colon'), whitespace, type_name, whitespace, seq(type_params, whitespace).optional())
formal_args = seq(formal_arg.optional(), whitespace, seq(string(',').mark().tag('comma') >> whitespace >> formal_arg).many())

# test
contents = sys.stdin.read()

parse_tree = file_.parse(contents)

def emit(text, contents):
    for element in contents:
        if isinstance(element, list):
            text = emit(text, element)
        else:
            (name, marked) = element
            (start, inner, end) = marked
            if isinstance(inner, list):
                text = emit(text, inner)
            else:
                text += inner
    return text



def walk(contents, machine_step_params):
    has_state_machine = False
    state_machine_indent = None
    collected_steps = []
    for element in contents:
        if isinstance(element, list):
            (element_has_state_machine, element_state_machine_indent, element_collected_steps, element_step_params) = walk(element, machine_step_params)
            has_state_machine |= element_has_state_machine
            if state_machine_indent is None:
                state_machine_indent = element_state_machine_indent
            if machine_step_params == '':
                machine_step_params = element_step_params
            collected_steps.extend(element_collected_steps)
        else:
            (name, marked) = element
            (start, inner, end) = marked
            if name == "tla.statemachine":
                has_state_machine = True

                indent = inner[0]
                state_machine_indent = indent

                inner.pop(1) # whitespace
                inner.pop(1) # "state"
                inner.pop(1) # whitespace
                inner.pop(1) # "machine"

                (_, (k_open_start, k_open_code, k_open_end)) = inner.pop(1)
                inner.insert(1, ('tladfy', (k_open_start, 'datatype Constants = Constants', k_open_end)))

                inner.pop(6) # whitespace
                inner.insert(6, indent)

                (_, (s_open_start, s_open_code, s_open_end)) = inner.pop(7)
                inner.insert(7, ('tladfy', (s_open_start, 'datatype Variables = Variables', s_open_end)))

                inner.pop(12) # step
                inner.pop(12) # 
                inner.pop(12) # 
                inner.pop(12) # (
                machine_step_params = inner.pop(12)[1][1] # step_params
                inner.pop(12) # )

            elif name == "tla.init":
                (_, (init_open_start, init_open_code, init_open_end)) = inner.pop(1)
                inner.insert(1, ('tladfy', (init_open_start, 'predicate Init(k: Constants, s: Variables)', init_open_end)))

            elif name == "tla.step":
                (_, (step_open_start, step_open_code, step_open_end)) = inner.pop(1)
                inner.insert(1, ('tladfy', (step_open_start, 'predicate', step_open_end)))

                (_, (step_params_start, step_params_code, step_params_end)) = inner.pop(6)
                step_gen_code = 'k: Constants, s: Variables, s\': Variables' + \
                        (', ' if machine_step_params.strip() != '' else '') + machine_step_params + \
                        (', ' if step_params_code.strip() != '' else '') + step_params_code
                inner.insert(6, ('tladfy', (step_params_start, step_gen_code, step_params_end)))

                collected_steps.append((inner[3][1][1], step_params_code))

            if isinstance(inner, list):
                (inner_has_state_machine, inner_state_machine_indent, inner_collected_steps, inner_step_params) = walk(inner, '')
                if inner_has_state_machine:
                    assert(name == "blockcontents")
                    # inner.append(inner_state_machine_indent)
                    indent_str = inner_state_machine_indent[1][1].replace('\n', '')

                    datatype_decl = "\n" + indent_str + "datatype Step =\n" + \
                        "\n".join([ "{}  | {}Step({})".format(indent_str, ident, params) for ident, params in inner_collected_steps ]) + "\n\n"

                    param_names = []
                    for ident, params in inner_collected_steps:
                        parsed = formal_args.parse(params)

                        flat_parsed = [parsed[0]] if parsed[0] is not None else []
                        flat_parsed.extend(x[0] for x in (parsed[2] if len(parsed) > 2 else []))

                        param_names.append(", ".join([x[0][1][1] for x in flat_parsed]))

                    nextstep_names = zip(inner_collected_steps, param_names)

                    step_params_parsed = formal_args.parse(inner_step_params)
                    flat_step_params_parsed = [step_params_parsed[0]] if step_params_parsed[0] is not None else []
                    flat_step_params_parsed.extend(x[0] for x in (step_params_parsed[2] if len(step_params_parsed) > 2 else []))
                    machine_step_args = ", ".join([x[0][1][1] for x in flat_step_params_parsed])

                    nextstep = indent_str + "predicate NextStep(k: Constants, s: Variables, s': Variables{}{}, step: Step)\n".format(', ' if inner_step_params.strip() != '' else '', inner_step_params) + \
                            indent_str + "{\n" + \
                            indent_str + "  match step {\n" + \
                            "\n".join(["{}    case {}Step({}) => {}(k, s, s'{}{}{}{})".format(indent_str, ident, pnames, ident, ', ' if machine_step_args.strip() != '' else '', machine_step_args, ', ' if pnames.strip() != "" else '', pnames) for ((ident, params), pnames) in nextstep_names]) + "\n" + \
                            indent_str + "  }\n" + \
                            indent_str + "}\n"

                    predicate_next = indent_str + "predicate Next(k: Constants, s: Variables, s': Variables{}{})".format(', ' if inner_step_params.strip() != '' else '', inner_step_params) + "\n" + \
                            indent_str + "{" + "\n" + \
                            indent_str + "  exists step :: NextStep(k, s, s'{}{}, step)".format(', ' if machine_step_args.strip() != '' else '', machine_step_args) + "\n" + \
                            indent_str + "}" + "\n"

                    inner.append(('tladfy', (None, [
                        ('tladfy', (None, datatype_decl, None)),
                        ('tladfy', (None, nextstep, None)),
                        ('tladfy', (None, predicate_next, None)),
                        ('tladfy', (None, '\n', None))
                    ], None)))

                    machine_step_params = ''
            else:
                pass

    return (has_state_machine, state_machine_indent, collected_steps, machine_step_params)

walk(parse_tree, '')

text = ""
text = emit(text, parse_tree)
print(text)

