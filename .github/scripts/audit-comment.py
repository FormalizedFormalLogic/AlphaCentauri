#!/usr/bin/env python3
"""Render the axiom audit's JSON report as the Markdown posted on a pull request.

Usage: audit-comment.py [REPORT]   (default: .lake/audit.json)

`lake exe forgive` writes the report as JSON only; how to present it is the auditing project's
business, and this is ours. See https://github.com/FormalizedFormalLogic/forgive.
"""

import json
import sys

HEADING = "## Axiom audit"
# The comment is posted whole, and GitHub rejects one over 65536 characters. The forgiven list is
# the part that grows without bound; the uncapped list is `forgive.yml` itself.
FORGIVEN_SHOWN = 150


def code(s: str) -> str:
    return f"`{s}`"


def codes(xs: list[str]) -> str:
    return ", ".join(code(x) for x in xs) if xs else "none"


def decl_table(rows: list[dict]) -> str:
    head = "| Declaration | Disallowed axioms |\n|---|---|\n"
    return head + "".join(f"| {code(r['declaration'])} | {codes(r['axioms'])} |\n" for r in rows)


def did_not_run(msg: str) -> str:
    return f"{HEADING}\n\n| | |\n|---|---|\n| **Status** | ❌ did not run |\n\n```\n{msg}\n```\n"


def render(r: dict) -> str:
    if "error" in r:
        return did_not_run(r["error"])
    violations, errors = r["violations"], r["forgiveErrors"]
    debt, forgiven = r["debt"], r["forgiven"]
    forgive_file = r["forgiveFile"]
    if r["ok"]:
        status = "✅ clean"
    else:
        status = ", ".join(
            part
            for part in (
                f"❌ {len(violations)} violation(s)" if violations else "",
                f"❌ {len(errors)} problem(s) in {code(forgive_file)}" if errors else "",
            )
            if part
        )
    roots = ", ".join(code(x) for x in r["roots"])
    md = f"{HEADING}\n\n| | |\n|---|---|\n"
    md += f"| **Status** | {status} |\n"
    md += f"| **Audited** | {r['audited']} declaration(s) under {roots} |\n"
    md += f"| **Allowed axioms** | {codes(r['allowed'])} |\n"
    md += f"| **Unproved statements** | {len(debt)} |\n"
    if violations:
        md += f"\n### Violations ({len(violations)})\n\n" + decl_table(violations)
    if errors:
        md += f"\n### Problems in {code(forgive_file)} ({len(errors)})\n\n"
        md += "".join(f"- {e}\n" for e in errors)
    if debt:
        md += f"\n### Unproved statements ({len(debt)})\n\n"
        md += (
            "The axioms this library declares in place of a proof, most depended-on first. "
            "The count is how many other audited declarations reach the axiom, so it ranks the "
            "statements by how much of the library rests on them.\n\n"
        )
        md += "| Statement | Dependent declarations |\n|---|---|\n"
        md += "".join(f"| {code(d['axiom'])} | {d['dependents']} |\n" for d in debt)
    if forgiven:
        shown = forgiven[:FORGIVEN_SHOWN]
        md += f"\n<details><summary>Forgiven by {code(forgive_file)}"
        md += f" ({len(forgiven)} declaration(s))</summary>\n\n" + decl_table(shown)
        if len(shown) < len(forgiven):
            md += f"\n… and {len(forgiven) - len(shown)} more;"
            md += f" the full list is {code(forgive_file)}.\n"
        md += "\n</details>\n"
    return md


def main() -> None:
    path = sys.argv[1] if len(sys.argv) > 1 else ".lake/audit.json"
    try:
        with open(path, encoding="utf-8") as f:
            report = json.load(f)
    except (OSError, ValueError) as e:
        sys.stdout.write(did_not_run(f"{path}: {e}"))
        return
    sys.stdout.write(render(report))


if __name__ == "__main__":
    main()
