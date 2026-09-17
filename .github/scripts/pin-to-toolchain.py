#!/usr/bin/env python3
"""Pin a `lakefile.toml` dependency to the tag naming our Lean toolchain.

Lake builds every dependency under the root `lean-toolchain`, so a package that reads Lean's
internals — Forgive, the axiom audit — only compiles at a revision written for that toolchain.
Such repositories tag each toolchain they support, and that tag is the pin.

    pin-to-toolchain.py lakefile.toml Forgive leanprover/lean4:v4.34.0

Leaves the file alone when there is no such tag: the bump then goes red and is repaired like any
other pull request.
"""

import json
import os
import re
import sys
import tomllib
import urllib.error
import urllib.request


def tagged(slug, tag):
    request = urllib.request.Request(f"https://api.github.com/repos/{slug}/git/ref/tags/{tag}")
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        request.add_header("Authorization", f"Bearer {token}")
    try:
        with urllib.request.urlopen(request) as response:
            return json.load(response)["ref"] == f"refs/tags/{tag}"
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return False
        raise


def main(lakefile, package, toolchain):
    text = open(lakefile).read()
    required = [r for r in tomllib.loads(text).get("require", []) if r.get("name") == package]
    if not required:
        sys.exit(f"{lakefile} requires no package named {package}")
    slug = re.sub(r"^https://github\.com/|\.git$", "", required[0]["git"])
    tag = toolchain.rsplit(":", 1)[-1]

    if not tagged(slug, tag):
        print(f"{package}: {slug} has no tag {tag}; leaving its pin alone")
        return
    block = re.search(rf'(\[\[require\]\]\s*\nname\s*=\s*"{re.escape(package)}".*?)(?=\n\[|\Z)', text, re.S)
    if block is None:
        sys.exit(f"cannot find the [[require]] block for {package} in {lakefile}")
    moved, count = re.subn(r'(rev\s*=\s*")[^"]*(")', rf"\g<1>{tag}\g<2>", block.group(1), count=1)
    if count == 0:
        sys.exit(f"the [[require]] block for {package} has no rev to move")
    open(lakefile, "w").write(text[: block.start(1)] + moved + text[block.end(1):])
    print(f"{package}: pinned at {slug}'s {tag}" + ("" if moved != block.group(1) else ", unchanged"))


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(f"usage: {sys.argv[0]} <lakefile.toml> <package> <toolchain>")
    main(*sys.argv[1:])
