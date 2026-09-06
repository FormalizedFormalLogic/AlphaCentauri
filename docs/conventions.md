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
Foundation's guidelines win, and the conflict is reported in an issue — with one standing
exception: [`style.md`](style.md)'s citation rule requires a docstring to say so and explain why
when a definition or theorem has no source; AGENTS.md's "Cite the source" rule instead has such
a declaration omit the docstring outright, unless a genuinely useful statement-level explanation
remains. AGENTS.md's rule wins here. When the Foundation pin is bumped, re-copy the three files
above in the same PR if they changed upstream, and update the commit noted above.

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
  under the name its theorem will keep, and recorded in [`forgive.yml`](../forgive.yml)
  forgiving that name. The reason is legibility of the audit — an `axiom` is reported under its
  own name, so the report says which unproved results a declaration leans on, where every
  `sorry` collapses into one anonymous `sorryAx`. Proving the statement turns the `axiom` into a
  `theorem` and deletes its entry; a `sorry` that would sit inside a proof becomes its own named
  axiom for the fact it stands for.
- **An `axiom` can silently drop a hypothesis.** Lean pulls a `variable`-bound instance argument
  into a declaration only when the declaration's own type mentions it; an `axiom` has no body to
  mention it indirectly, so a hypothesis like `[U.Δ₁]` or `[𝗜𝚺₁ ⪯ T]` can vanish from the type
  without any error — the resulting statement is *stronger* than intended, and neither
  `lake build`, `lake exe audit`, nor `just mk-all` catches it. This happened in PR #107 and was
  fixed in PR #112. A `statement-formalized` PR must run `#check @Name` on every `axiom` it adds
  and confirm the printed type keeps every intended hypothesis.
- **Reuse before restating.** Foundation's theories, notations, definability classes, and the
  hierarchy are the vocabulary. A definition that duplicates a Foundation definition under a
  new name is rejected in review. If Foundation's API is missing or awkward, say so in the
  issue you are working on rather than working around it; a human takes it upstream.
- **AI disclosure.** As in Foundation: every commit carries a `Co-Authored-By` trailer for the
  model, and the PR body says an AI agent wrote it. Here that is the normal case, not the
  exception, so every PR body says so explicitly.

## Checks before opening a pull request

```bash
lake build            # no errors; fix the warnings
just axiom-audit      # no axiom outside the allowlist, except what forgive.yml forgives
just no-sorry         # no `sorry` in the sources, no `sorryAx` in forgive.yml
just mk-all           # AlphaCentauri.lean up to date
```

A `statement-formalized` PR additionally runs `#check @Name` on every `axiom` it adds — see
"An `axiom` can silently drop a hypothesis" above.
