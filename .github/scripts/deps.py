#!/usr/bin/env python3
"""Answer questions about `lakefile.toml`, so no workflow repeats what it says.

    deps.py slug lakefile.toml Foundation
    deps.py pin-tag lakefile.toml Forgive leanprover/lean4:v4.34.0

`slug` prints the `owner/name` a package is resolved from. `pin-tag` moves a package onto the tag
naming our toolchain — Lake builds every dependency under the root `lean-toolchain`, and a package
reading Lean's internals only compiles at a revision written for it — and leaves the pin alone
when there is no such tag.
"""

import json
import os
import re
import sys
import tomllib
import urllib.error
import urllib.request


def require(lakefile, package):
    text = open(lakefile).read()
    for required in tomllib.loads(text).get("require", []):
        if required.get("name") == package:
            return text, required
    sys.exit(f"{lakefile} requires no package named {package}")


def slug(lakefile, package):
    _, required = require(lakefile, package)
    print(re.sub(r"^https://github\.com/|\.git$", "", required["git"]))


def tagged(repository, tag):
    request = urllib.request.Request(f"https://api.github.com/repos/{repository}/git/ref/tags/{tag}")
    if token := os.environ.get("GITHUB_TOKEN"):
        request.add_header("Authorization", f"Bearer {token}")
    try:
        with urllib.request.urlopen(request) as response:
            return json.load(response)["ref"] == f"refs/tags/{tag}"
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return False
        raise


def pin_tag(lakefile, package, toolchain):
    text, required = require(lakefile, package)
    repository = re.sub(r"^https://github\.com/|\.git$", "", required["git"])
    tag = toolchain.rsplit(":", 1)[-1]
    if not tagged(repository, tag):
        print(f"{package}: {repository} has no tag {tag}; leaving its pin alone")
        return
    block = re.search(rf'(\[\[require\]\]\s*\nname\s*=\s*"{re.escape(package)}".*?)(?=\n\[|\Z)', text, re.S)
    moved, count = re.subn(r'(rev\s*=\s*")[^"]*(")', rf"\g<1>{tag}\g<2>", block.group(1), count=1)
    if count == 0:
        sys.exit(f"the [[require]] block for {package} has no rev to move")
    open(lakefile, "w").write(text[: block.start(1)] + moved + text[block.end(1):])
    print(f"{package}: pinned at {repository}'s {tag}")


COMMANDS = {"slug": slug, "pin-tag": pin_tag}

if __name__ == "__main__":
    command = COMMANDS.get(sys.argv[1] if len(sys.argv) > 1 else "")
    if command is None:
        sys.exit(f"usage: {sys.argv[0]} {' | '.join(COMMANDS)} <lakefile.toml> <package> [...]")
    command(*sys.argv[2:])
