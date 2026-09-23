default:
    @just --list

cache:
    lake exe cache get
    LAKE_CONFIG=lake-cache.toml lake cache get --service ffl --max-revs=100 \
      --repo FormalizedFormalLogic/Foundation --package Foundation \
      || echo "Foundation's cache is incomplete; the build will compile the rest from source"
    LAKE_CONFIG=lake-cache.toml lake cache get --service ffl --max-revs=100 \
      --repo FormalizedFormalLogic/AlphaCentauri \
      || echo "AlphaCentauri's cache is incomplete; the build will compile the rest from source"

build: cache
    lake build

axiom-audit:
    lake exe forgive AlphaCentauri --json .lake/audit.json

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

check-pr-title title:
    PR_TITLE={{ quote(title) }} python3 .github/scripts/check-pr-title.py

zoo:
    lake exe zoo_arithmetic AlphaCentauriZoo/arithmetic.json
    mkdir -p pages/zoo
    typst compile AlphaCentauriZoo/arithmetic.typ pages/zoo/arithmetic.png
    typst compile AlphaCentauriZoo/arithmetic.typ pages/zoo/arithmetic.pdf

mk-all:
    lake exe mk_all --lib AlphaCentauri --module

hooks:
    lefthook install
