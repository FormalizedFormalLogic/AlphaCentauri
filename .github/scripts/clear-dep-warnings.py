#!/usr/bin/env python3
"""Drop Lake's cached diagnostics for a dependency's build.

Lake replays each module's cached log on every downstream build, so a dependency's own warnings
would reach a `lake build ... --wfail` here as if they were ours. Emptying the `log` array of
each `.trace` drops the replay and leaves the `.olean` untouched.

Takes the dependency's build directory, e.g. `.lake/packages/Foundation/.lake/build`.
"""

import json
import pathlib
import sys

if len(sys.argv) != 2:
    sys.exit(f"usage: {sys.argv[0]} <build directory>")
root = pathlib.Path(sys.argv[1])
cleared = 0
for trace in root.rglob("*.trace"):
    try:
        cached = json.loads(trace.read_text())
    except (ValueError, OSError):
        continue
    if cached.get("log"):
        cached["log"] = []
        trace.write_text(json.dumps(cached))
        cleared += 1
print(f"cleared warning cache in {cleared} trace(s) under {root}")
