# Coding conventions

AlphaCentauri follows **Foundation's contribution guidelines**: [`index.md`](index.md),
[`style.md`](style.md), and [`refactoring.md`](refactoring.md) in this directory are copied
verbatim from the `contribute/` directory of
[Foundation](https://github.com/FormalizedFormalLogic/Foundation/tree/master/contribute), at
the commit pinned in `lake-manifest.json` when they were copied:

- source: https://github.com/FormalizedFormalLogic/Foundation/tree/a77e4e903062c05ce502e331f7215a5a07cb780a/contribute
- commit: `a77e4e903062c05ce502e331f7215a5a07cb780a`
- license: Apache-2.0 (Foundation's)

- [`index.md`](index.md): the flow to the main branch, PR titles and the commit convention,
  pre-submission checks, disclosure of AI involvement.
- [`style.md`](style.md): proof style, naming of intermediate steps, comments and docstrings,
  citations, `grind`, no `sorry`, `set_option`.
- [`refactoring.md`](refactoring.md): priorities and rules for writing and refactoring proofs.

Those documents are the authority; AlphaCentauri follows them as written. This file does not
restate them; it records only where AlphaCentauri differs or adds. Where the two conflict,
Foundation's guidelines win, and the conflict is reported as a `meta` issue. When the Foundation
pin is bumped, re-copy the three files above in the same PR if they changed upstream, and update
the commit noted above.

Where they say "Foundation", read "Foundation, and AlphaCentauri"; where they name
Foundation-specific files (`Foundation.lean`, `references.bib`, `just` recipes), the
counterparts here are the ones named below.

The reason is practical: material developed here is meant to move into Foundation without a
rewrite, so it is written as if it were already there.

## AlphaCentauri-specific additions

- **Module system.** Every file opts into the Lean module system exactly as Foundation does:
  it starts with `module`, imports are `public import`, and the module docstring precedes
  `@[expose] public section`.
- **Root module.** `AlphaCentauri.lean` imports every module and is regenerated with
  `just mk-all` (`lake exe mk_all --lib AlphaCentauri --module`); CI checks it.
- **Warnings are errors.** The library builds with `warningAsError = true` and Foundation's
  linter set (`lakefile.toml`). A warning is fixed, not suppressed.
- **Citations.** The citation keys are `HP98` and `Lin97` (see `README.md`), cited at the end
  of the docstring in Foundation's form, one line per key:
  ```
  - [HP98, Theorem I.2.4]
  - [Lin97, Lemma 5.2]
  ```
  There is no `references.bib` here yet; when one is added it follows Foundation's
  `bibtool` formatting.
- **Reuse before restating.** Foundation's theories, notations, definability classes, and the
  hierarchy are the vocabulary. A definition that duplicates a Foundation definition under a
  new name is rejected in review. If Foundation's API is missing or awkward, open a
  `foundation` issue rather than working around it.
- **AI disclosure.** As in Foundation: every commit carries a `Co-Authored-By` trailer for the
  model, and the PR body says an AI agent wrote it. Here that is the normal case, not the
  exception, so every PR body says so explicitly.

## Checks before opening a pull request

```bash
lake build            # no errors, no warnings
just axiom-audit      # no sorry, no axiom outside the allowlist
just mk-all           # AlphaCentauri.lean up to date
```
