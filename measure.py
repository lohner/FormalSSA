#!/usr/bin/env python3

import sys
import collections
import re

times = collections.defaultdict(lambda: 0.0)
phis = collections.defaultdict(lambda: 0)

for line in sys.stdin:
    m = re.match(r'(.*) (\d+\.\d+)', line)
    if m:
        times[m.group(1)] += float(m.group(2))
    m = re.match(r'(.*) (\d+)$', line)
    if m:
        phis[m.group(1)] += int(m.group(2))

for name, time in sorted(times.items()):
    print("{} {:.3f}".format(name, time))
for name, count in sorted(phis.items()):
    print("{} {:d}".format(name, count))
