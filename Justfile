# List available recipes
default:
    @just --list

# Build the library (Foundation is built from source on first run; Mathlib comes from the cache)
build:
    lake exe cache get
    lake build

# Audit AlphaCentauri for sorry/native_decide/unauthorized axioms, honouring the allowlist
# audit_sorry.yml (requires `lake build` first; see Audit/Main.lean)
axiom-audit:
    lake exe audit

# Regenerate AlphaCentauri.lean to import all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --lib AlphaCentauri --module

# Install the git hooks that run the CI checks before a push (needs lefthook: https://lefthook.dev)
hooks:
    lefthook install
