# List available recipes
default:
    @just --list

# Build the library (Foundation is built from source on first run; Mathlib comes from the cache)
build:
    lake exe cache get
    lake build

# Audit AlphaCentauri for sorry/native_decide/unauthorized axioms, honouring the allowlist
# forgive.yml (requires `lake build` first; see Audit/Main.lean)
axiom-audit:
    lake exe audit

# Forbid `sorry`: none in the Lean sources, and `sorryAx` forgiven nowhere in forgive.yml.
# An unproved statement is an `axiom` under its own name instead (see docs/conventions.md).
# Needs yq (https://github.com/mikefarah/yq); the jq-based kislyuk/yq understands the same query.
no-sorry:
    #!/usr/bin/env bash
    set -euo pipefail
    if grep -rnE '\bsorry' --include='*.lean' AlphaCentauri.lean AlphaCentauri; then
        echo >&2 "no-sorry: 'sorry' is not allowed; declare the unproved statement as an 'axiom'"
        echo >&2 "no-sorry: under the name its theorem will keep and list it in forgive.yml"
        exit 1
    fi
    if ! command -v yq >/dev/null 2>&1; then
        echo >&2 "no-sorry: yq is required to check forgive.yml (https://github.com/mikefarah/yq)"
        exit 1
    fi
    if [ "$(yq '[.. | select(. == "sorryAx")] | length' forgive.yml)" != 0 ]; then
        echo >&2 "no-sorry: forgive.yml forgives 'sorryAx'; forgive the axiom's own name instead"
        exit 1
    fi
    echo "no-sorry: ok"

# Check a pull request title against the conventions in docs/workflow.md
check-pr-title title:
    PR_TITLE={{ quote(title) }} python3 .github/scripts/check-pr-title.py

# Generate the theory zoo as pages/zoo/arithmetic.{png,pdf} (needs typst and graphviz)
zoo:
    lake build Foundation zoo_arithmetic
    lake exe zoo_arithmetic Zoo/arithmetic.json
    mkdir -p pages/zoo
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.png
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.pdf

# Regenerate AlphaCentauri.lean to import all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --lib AlphaCentauri --module

# Install the git hooks that run the CI checks before a push (needs lefthook: https://lefthook.dev)
hooks:
    lefthook install
