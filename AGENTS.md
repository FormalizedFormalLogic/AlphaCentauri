# Working in AlphaCentauri

This is the contract for AI agents working in this repository. `README.md` says what the project
is; [`docs/workflow.md`](docs/workflow.md) says how work moves through GitHub and is normative.
This file adds only the rules an agent must hold itself to.

## GitHub is the only workbench

- **A unit of work is an issue.** Work only on an open issue labelled `target`. If nobody has
  opened one for the roadmap item you want, open it first (cite the roadmap item and the source
  theorem), then work on it. Never start from a private to-do list.
- **Claim by assigning yourself** (`gh issue edit <n> --add-assignee @me`) before you write
  code, and never work on an issue assigned to someone else. Unassign yourself if you stop.
- **One issue, one branch, one pull request.** Branch from `main` as `target/<n>-<slug>`. The
  PR body contains `Closes #<n>`. Ship a prerequisite refactor as its own PR.
- **Never push to `main`.** Never force-push over someone else's commits: pushing to a branch
  you did not create uses `--force-with-lease` against the tip you observed.
- **Never merge.** Landing a PR is the review pipeline's job (a human's, while the project
  bootstraps). Do not use admin overrides, and do not close other people's PRs.
- **Address review in the same PR.** Push commits; do not open a replacement PR. If two
  findings contradict each other, say so in the thread with both quoted, rather than
  satisfying one silently.

## The roadmap gates new mathematics

The roadmap is human-owned. Until it is published in this repository (it will live under
`docs/`), the roadmap is exactly the set of `target` issues opened by humans. Add a new definition,
theorem, instance, or file only when it advances a target listed there, or supplies a
prerequisite a listed target needs. If a mathematical gap blocks the roadmap item you're
working on, open an issue labelled `roadmap` describing it and leave it to a human; never edit
the roadmap yourself and never build off-roadmap material "in passing". Gaps outside the
mathematics — missing CI, infrastructure, or anything under a human-owned path (see
[`docs/workflow.md`](docs/workflow.md)) — are not issues to open; mention them in a PR comment
or leave them for a human to notice.

Improving existing code needs no roadmap entry: refactoring, simplifying proofs, modest
generalization of an existing lemma, relocation, documentation. Open a `target` issue for it
all the same, so the work is visible.

## The rules of the code

- `main` is always green. CI builds `AlphaCentauri` and runs the axiom audit: no `sorry`, no `native_decide`, no axioms beyond `propext`, `Classical.choice`,
  `Quot.sound`, except what `audit_sorry.yml` forgives declaration by declaration (see
  `Audit/Main.lean` for the format). Do not try to disable these; if a proof needs
  `maxHeartbeats`, restructure it.
- **Follow Foundation's contribution guidelines**, copied verbatim into this repository as
  [`docs/index.md`](docs/index.md), [`docs/style.md`](docs/style.md), and
  [`docs/refactoring.md`](docs/refactoring.md). [`docs/conventions.md`](docs/conventions.md)
  lists the few things AlphaCentauri adds. Code here should be movable into Foundation
  without a rewrite.
- **Cite the source.** Every non-trivial definition and theorem carries, at the end of its
  docstring, the reference it formalizes, one line per key: `- [HP98, Theorem I.1.5]`,
  `- [Lin97, Theorem 2.3]`. If none exists, say so and why.
- **Use Foundation's vocabulary.** Search Foundation (and Mathlib) before defining anything;
  reuse its theories, notations, definability classes, and lemmas. Do not restate a Foundation
  definition under a new name. If Foundation's API is missing or awkward, say so in the issue;
  do not patch Foundation's sources under `.lake/`.
- **No compatibility layer.** When you rename, move, or delete a declaration, update every use
  in the same PR and remove the old name. No aliases, wrappers, forwarding modules, or
  deprecation shims.
- **No development artifacts** in the code: plan steps, issue numbers, "TODO after review",
  skeleton-era comments.
- `AlphaCentauri/` and `AlphaCentauri.lean` are the only places code goes. `docs/`,
  `.github/`, `lakefile.toml`, `Justfile`, `lefthook.yml`, `README.md`, `AGENTS.md`, and
  `CLAUDE.md` are human-owned; a PR that touches them always needs a human review. The two pins
  (`lake-manifest.json`, `lean-toolchain`) may be bumped **forward only**, in their own PR.

## Pull requests

- Title in Foundation's conventional-commit form, `<type>(scope): <subject>`, with `<type>` one
  of `add`, `fix`, `refactor`, `doc`, `ci`, `chore`, and the subject naming one representative
  result, not a verb phrase. The PR is squash-merged, so the title becomes the commit on `main`.
- The body states the issue it closes, what was formalized with citations, and how you verified
  it (`lake build`, `just axiom-audit`, `just mk-all`).
- **Disclose AI involvement**: every commit carries `Co-Authored-By: Claude <noreply@anthropic.com>`
  (or the equivalent for the model used), and the PR body says in plain language that an AI
  agent wrote it.
- PRs, issues, commit messages, code, and docstrings are written in English.

## Sources

The reference texts are kept locally as `.claude/references/HP98.pdf` and
`.claude/references/Lin97.pdf`. They are copyrighted and git-ignored: read them, cite them,
never commit them or paste long passages from them.
