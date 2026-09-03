# List available recipes
default:
    @just --list

# Build the library (Foundation is built from source on first run; Mathlib comes from the cache)
build:
    lake exe cache get
    lake build

# Audit AlphaCentauri for sorry/native_decide/unauthorized axioms (requires `lake build` first)
axiom-audit:
    lake exe axiom-audit --root AlphaCentauri

# Regenerate AlphaCentauri.lean to import all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --lib AlphaCentauri --module
