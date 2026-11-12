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

open-problems: libertinus
    lake exe open_problems pages/open-problems/open-problems.json
    yq --output-format=json . references.yml \
      | python3 AlphaCentauriOpenProblems/references.py > pages/open-problems/references.json
    cp AlphaCentauriOpenProblems/index.html AlphaCentauriOpenProblems/index.css pages/open-problems/

# Libertinus, the fonts of the statements on the list of open problems, from its pinned release.
libertinus_release := "https://github.com/alerque/libertinus/releases/download/v7.051/Libertinus-7.051.zip"
libertinus_sha256 := "4d9be29b5cb380c35af8ba967abcc752ad1e07be1f738a9789c33e0dd7478c92"

libertinus:
    #!/usr/bin/env python3
    import hashlib, pathlib, urllib.request, zipfile
    archive = pathlib.Path(".lake/Libertinus.zip")
    def valid():
        return archive.exists() and hashlib.sha256(archive.read_bytes()).hexdigest() == "{{ libertinus_sha256 }}"
    if not valid():
        archive.parent.mkdir(exist_ok=True)
        urllib.request.urlretrieve("{{ libertinus_release }}", archive)
        assert valid(), "the downloaded Libertinus release does not match its checksum"
    fonts = pathlib.Path("pages/open-problems/fonts")
    fonts.mkdir(parents=True, exist_ok=True)
    wanted = {"LibertinusSerif-Regular", "LibertinusSerif-Italic", "LibertinusSerif-Bold",
              "LibertinusSerif-BoldItalic", "LibertinusMath-Regular"}
    with zipfile.ZipFile(archive) as z:
        for name in z.namelist():
            path = pathlib.PurePosixPath(name)
            if path.parent.name == "WOFF2" and path.stem in wanted:
                (fonts / path.name).write_bytes(z.read(name))
            elif path.name == "OFL.txt":
                (fonts / "Libertinus-OFL.txt").write_bytes(z.read(name))

import-graph:
    lake exe graph --to AlphaCentauri import_graph.png import_graph.pdf import_graph.html

mk-all:
    lake exe mk_all --lib AlphaCentauri --module

hooks:
    lefthook install
