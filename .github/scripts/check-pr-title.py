#!/usr/bin/env python3
"""Check a pull request title against the conventions in docs/workflow.md.

Usage: check-pr-title.py [TITLE]   (falls back to $PR_TITLE)
"""

import os
import re
import sys

TYPES = ("add", "fix", "refactor", "doc", "ci", "chore")
MAX_LENGTH = 100

# Greek, mathematical Greek (bold/sans/italic planes) and Unicode subscripts.
GREEK = re.compile(r"[Ͱ-Ͽἀ-῿\U0001d6a8-\U0001d7cb]")
SUBSCRIPT = re.compile(r"[₀-ₜ]")
ASCII_MATH = re.compile(r"\b(Delta|Sigma|Pi|Gamma|Phi|Psi|Omega|Theta|Lambda)_")


def strip_spans(title: str) -> str:
    """Blank out `code` and $math$ spans, so only bare prose is checked."""
    out = list(title)
    for pattern in (r"`[^`]*`", r"\$[^$]*\$"):
        for m in re.finditer(pattern, title):
            for i in range(m.start(), m.end()):
                out[i] = " "
    return "".join(out)


def check(title: str) -> list[str]:
    errors = []

    if not title.strip():
        return ["the title is empty"]
    if title != title.strip():
        errors.append("the title has leading or trailing whitespace")
    if title.endswith("."):
        errors.append("the title ends with a period")
    if len(title) > MAX_LENGTH:
        errors.append(f"the title is {len(title)} characters, over the {MAX_LENGTH} allowed")

    scope = re.match(r"^([A-Za-z]+)\(([^)]*)\):", title)
    if scope:
        errors.append(
            f"the title carries a '({scope.group(2)})' scope; write "
            f"'{scope.group(1)}: <subject>' instead"
        )
    elif not re.match(rf"^({'|'.join(TYPES)}): \S", title):
        head = title.split(":", 1)[0] if ":" in title else title
        errors.append(
            f"the title must start with '<type>: ' where <type> is one of "
            f"{' | '.join(TYPES)} (found {head!r})"
        )

    bare = strip_spans(title)
    if GREEK.search(bare):
        errors.append(
            "a Greek letter appears outside backticks and TeX; write mathematics as "
            "'$\\Sigma_n$' and Lean notation in backticks"
        )
    if SUBSCRIPT.search(bare):
        errors.append(
            "a Unicode subscript appears outside backticks and TeX; write '$\\Delta_1$', "
            "never 'Δ₁'"
        )
    if ASCII_MATH.search(bare):
        errors.append(
            "mathematics is spelled out in ASCII; write '$\\Delta_1$', never 'Delta_1'"
        )
    if bare.count("`") % 2:
        errors.append("the title has an unmatched backtick")
    if bare.count("$"):
        errors.append("the title has an unmatched '$'")

    return errors


def main() -> int:
    title = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("PR_TITLE", "")
    errors = check(title)
    if not errors:
        print(f"check-pr-title: ok ({title})")
        return 0
    print(f"check-pr-title: {title!r} does not follow docs/workflow.md", file=sys.stderr)
    for e in errors:
        print(f"  - {e}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
