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
- **Linters.** The library builds with Foundation's linter set (`lakefile.toml`). Warnings are not
  errors, since a statement formalized with `sorry` must build; a warning is still fixed, not
  suppressed, and review treats one as a finding.
- **Citations.** The bibliography is [`references.yml`](../references.yml) at the repository
  root, written in [Hayagriva](https://github.com/typst/hayagriva) YAML rather than
  Foundation's BibTeX `references.bib`; there is no `bibtool` step, the file is edited by
  hand and kept sorted by key. Its keys are the citation keys (`HP98`, `Lin97`, `AB05`, see
  `README.md`), cited at the end of the docstring in Foundation's form, one line per key:
  ```
  - [HP98, Theorem I.2.4]
  - [Lin97, Lemma 5.2]
  ```
  A key used in a docstring must have an entry in `references.yml`; add the entry in the same
  pull request.
- **No `sorry`; unproved statements are axioms.** Foundation's guidelines forbid `sorry` in
  finished work. AlphaCentauri forbids it outright, including in the statement-only stage of
  [`workflow.md`](workflow.md): a statement that is not proved yet is declared as an `axiom`
  under the name its theorem will keep, and recorded in [`axiom_debt.yml`](../axiom_debt.yml)
  forgiving that name. The reason is legibility of the audit — an `axiom` is reported under its
  own name, so the report says which unproved results a declaration leans on, where every
  `sorry` collapses into one anonymous `sorryAx`. Proving the statement turns the `axiom` into a
  `theorem` and deletes its entry; a `sorry` that would sit inside a proof becomes its own named
  axiom for the fact it stands for.
- **Reuse before restating.** Foundation's theories, notations, definability classes, and the
  hierarchy are the vocabulary. A definition that duplicates a Foundation definition under a
  new name is rejected in review. If Foundation's API is missing or awkward, open a
  `foundation` issue rather than working around it.
- **AI disclosure.** As in Foundation: every commit carries a `Co-Authored-By` trailer for the
  model, and the PR body says an AI agent wrote it. Here that is the normal case, not the
  exception, so every PR body says so explicitly.

## Checks before opening a pull request

```bash
lake build            # no errors; fix the warnings
just axiom-audit      # no axiom outside the allowlist, except what axiom_debt.yml forgives
just no-sorry         # no `sorry` in the sources, no `sorryAx` in axiom_debt.yml
just mk-all           # AlphaCentauri.lean up to date
```
