# List available recipes
default:
    @just --list

# Build the library (Foundation is built from source on first run; Mathlib comes from the cache)
build:
    lake exe cache get
    lake build

# Audit AlphaCentauri for sorry/native_decide/unauthorized axioms, honouring the allowlist
# axiom_debt.yml (requires `lake build` first; see Audit/Main.lean)
axiom-audit:
    lake exe audit

# Forbid `sorry`: none in the Lean sources, and `sorryAx` forgiven nowhere in axiom_debt.yml.
# An unproved statement is an `axiom` under its own name instead (see docs/conventions.md).
# Needs yq (https://github.com/mikefarah/yq); the jq-based kislyuk/yq understands the same query.
no-sorry:
    #!/usr/bin/env bash
    set -euo pipefail
    if grep -rnE '\bsorry' --include='*.lean' AlphaCentauri.lean AlphaCentauri; then
        echo >&2 "no-sorry: 'sorry' is not allowed; declare the unproved statement as an 'axiom'"
        echo >&2 "no-sorry: under the name its theorem will keep and list it in axiom_debt.yml"
        exit 1
    fi
    if ! command -v yq >/dev/null 2>&1; then
        echo >&2 "no-sorry: yq is required to check axiom_debt.yml (https://github.com/mikefarah/yq)"
        exit 1
    fi
    if [ "$(yq '[.. | select(. == "sorryAx")] | length' axiom_debt.yml)" != 0 ]; then
        echo >&2 "no-sorry: axiom_debt.yml forgives 'sorryAx'; forgive the axiom's own name instead"
        exit 1
    fi
    echo "no-sorry: ok"

# Regenerate AlphaCentauri.lean to import all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --lib AlphaCentauri --module

# Install the git hooks that run the CI checks before a push (needs lefthook: https://lefthook.dev)
hooks:
    lefthook install
