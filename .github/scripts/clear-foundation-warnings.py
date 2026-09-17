#!/usr/bin/env python3
"""Drop Lake's cached diagnostics for the Foundation build.

Lake replays each module's cached log on every downstream build, so Foundation's own warnings
would reach a `lake build ... --wfail` here as if they were ours. Emptying the `log` array of
each `.trace` drops the replay and leaves the `.olean` untouched.
"""

import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".lake/packages/Foundation/.lake/build")
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
print(f"cleared warning cache in {cleared} Foundation trace(s)")
