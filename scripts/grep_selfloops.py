import sys
import re

symbol_re = re.compile(r'>([\*01])<')
edge_re = re.compile(r'-?\d+ -> -?\d+')


self_loop_count = 0
for line in sys.stdin.readlines():
    edge_match = edge_re.search(line)
    if edge_match:
        edge = edge_match.group(0)
        fragments = list(map(str.strip, edge.split('->')))
        if fragments[0] == fragments[1]:
            self_loop_count += 1
            symbol = symbol_re.findall(line)
            print(symbol)
print(self_loop_count)
