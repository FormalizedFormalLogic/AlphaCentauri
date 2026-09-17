#!/usr/bin/env python3
"""Move a package pinned by revision in `lakefile.toml` onto our Lean toolchain.

Lake builds every dependency under the root `lean-toolchain`, so a package that reads Lean's
internals — Forgive, the axiom audit — only compiles at a revision written for that toolchain.
This rewrites its `rev` to the newest commit of its repository carrying the same toolchain, which
is what a hand-made pin picks anyway.

    pin-to-toolchain.py lakefile.toml Forgive leanprover/lean4:v4.34.0

Prints what it did and leaves the file alone when nothing matches: the bump then goes red and is
repaired like any other.
"""

import json
import os
import re
import sys
import tomllib
import urllib.error
import urllib.request


def get(url):
    request = urllib.request.Request(url)
    token = os.environ.get("GITHUB_TOKEN")
    if token and url.startswith("https://api.github.com/"):
        request.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(request) as response:
        body = response.read().decode()
    return json.loads(body) if url.startswith("https://api.github.com/") else body


def main(lakefile, package, toolchain):
    text = open(lakefile).read()
    required = [r for r in tomllib.loads(text).get("require", []) if r.get("name") == package]
    if not required:
        sys.exit(f"{lakefile} requires no package named {package}")
    slug = re.sub(r"^https://github\.com/|\.git$", "", required[0]["git"])

    # Each commit touching `lean-toolchain` opens a window that the next one closes, so the newest
    # commit under a toolchain is the parent of the change that replaced it.
    changes = get(f"https://api.github.com/repos/{slug}/commits?path=lean-toolchain&per_page=100")
    pin = None
    for i, change in enumerate(changes):
        if get(f"https://raw.githubusercontent.com/{slug}/{change['sha']}/lean-toolchain").strip() != toolchain:
            continue
        pin = changes[i - 1]["parents"][0]["sha"] if i else get(
            f"https://api.github.com/repos/{slug}/commits?per_page=1")[0]["sha"]
        break
    if pin is None:
        print(f"{package}: no commit of {slug} carries {toolchain}; leaving its pin alone")
        return

    block = re.search(rf'(\[\[require\]\]\s*\nname\s*=\s*"{re.escape(package)}".*?)(?=\n\[|\Z)', text, re.S)
    if block is None:
        sys.exit(f"cannot find the [[require]] block for {package} in {lakefile}")
    moved, count = re.subn(r'(rev\s*=\s*")[^"]*(")', rf"\g<1>{pin}\g<2>", block.group(1), count=1)
    if count == 0:
        sys.exit(f"the [[require]] block for {package} has no rev to move")
    if moved == block.group(1):
        print(f"{package}: already at {pin[:8]} for {toolchain}")
        return
    open(lakefile, "w").write(text[: block.start(1)] + moved + text[block.end(1):])
    print(f"{package}: pinned at {pin[:8]}, the newest commit of {slug} carrying {toolchain}")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(f"usage: {sys.argv[0]} <lakefile.toml> <package> <toolchain>")
    main(*sys.argv[1:])
