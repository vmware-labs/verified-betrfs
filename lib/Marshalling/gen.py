import jinja2
import sys

try:
    count = int(sys.argv[2])
    target = sys.argv[1]
    assert count >= 2
    assert target in {"tuple", "union"}
except:
    print(f"example usage: python {sys.argv[0]} tuple 2")
    sys.exit(0)

templateLoader = jinja2.FileSystemLoader(searchpath="./")
templateEnv = jinja2.Environment(loader=templateLoader)

if target == "tuple":
    TEMPLATE_FILE = 'tuple.jinja2'
else:
    TEMPLATE_FILE = 'union.jinja2'

t = templateEnv.get_template(TEMPLATE_FILE)

esize = hex(0x1_0000_0000_0000_0000 // (count-1))

print(t.render(count=count, esize=esize))
