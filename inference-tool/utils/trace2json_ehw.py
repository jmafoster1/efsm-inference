import json
import re
import sys
from itertools import groupby

TRACE_FILE = sys.argv[1]
OUTPUT_FILE = f"{TRACE_FILE}.json"
GROUPS_FILE = f"{TRACE_FILE}_groups.json"

params = r"(\w+)(\(([\w,]*)\))*"
event_re = re.compile(f"{params}(/{params})")


def cast(x):
    try:
        return int(x)
    except ValueError:
        try:
            return float(x)
        except ValueError:
            return str(x)

trace = []
with open(TRACE_FILE) as f:
    for line in f:
        line = line.strip()
        if line.endswith("Omega") or line.startswith("#"):
            continue
        match = event_re.match(line)
        assert match, f"Could not match event {line}"
        label = match.group(1)
        inputs = match.group(3).split(",") if match.group(3) else []
        outputs = match.group(7).split(",") if match.group(7) else []
        event = {"label": label, "inputs": [cast(x) for x in inputs], "outputs": [cast(x) for x in outputs]}
        trace.append(event)

trace_grouper = [{
    "label": event['label'],
    "inputs": tuple([type(ip).__name__[0].upper() for ip in event['inputs']]),
    "outputs": tuple([type(ip).__name__[0].upper() for ip in event['outputs']])
    } for event in trace]

start = 0
groups = []
for k, g in groupby(trace_grouper):
    g = list(g)
    k['transitions'] = [[x] for x in range(start, start + len(g))]
    groups.append(k)
    start += len(g)


with open(OUTPUT_FILE, 'w') as f:
    print(json.dumps([trace], indent=2), file=f)

with open(GROUPS_FILE, 'w') as f:
    print(json.dumps(groups, indent=2), file=f)
