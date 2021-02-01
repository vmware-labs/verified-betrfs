import jinja2
import sys

try:
    count = int(sys.argv[1])
    assert count >= 2
except:
    count = 2

templateLoader = jinja2.FileSystemLoader(searchpath="./")
templateEnv = jinja2.Environment(loader=templateLoader)
TEMPLATE_FILE = 'tuple.jinja2'
t = templateEnv.get_template(TEMPLATE_FILE)

esize = hex(0x1_0000_0000_0000_0000 // (count-1))

print(t.render(count=count, esize=esize))
