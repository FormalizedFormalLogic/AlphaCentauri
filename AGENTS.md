# Working in AlphaCentauri

This is the contract for AI agents working in this repository. `README.md` says what the project
is; [`docs/workflow.md`](docs/workflow.md) says how work moves through GitHub and is normative.
This file adds only the rules an agent must hold itself to.

## Setup

Proof work uses the `lean4` plugin (marketplace `lean4-skills`, providing `/lean4:autoprove` etc.)
and the `lean-lsp` MCP server (defined in `.mcp.json`; requires `uv` and `ripgrep`):

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```

## GitHub is the only workbench

- **A unit of work is an issue.** Work only on an open issue. Humans open the issues for new
  mathematics; never start from a private to-do list.
- **Claim by assigning yourself** (`gh issue edit <n> --add-assignee @me`) before you write
  code, and never work on an issue assigned to someone else. Unassign yourself if you stop.
- **One issue, one branch, one pull request.** Branch from `main` as `<n>-<slug>`. The
  PR body contains `Closes #<n>`. Ship a prerequisite refactor as its own PR.
- **Never push to `main`.** Never force-push over someone else's commits: pushing to a branch
  you did not create uses `--force-with-lease` against the tip you observed.
- **Don't merge without being told to.** Landing a PR is the review pipeline's job (a human's,
  while the project bootstraps); merge only once the user has explicitly told you to for that
  PR. Do not use admin overrides, and do not close other people's PRs.
- **Address review in the same PR.** Push commits; do not open a replacement PR. If two
  findings contradict each other, say so in the thread with both quoted, rather than
  satisfying one silently.

## Humans decide what mathematics gets formalized

The open issues are the plan, and humans write them. Add a new definition, theorem, instance,
or file only when an open issue asks for it, or it is a prerequisite that issue needs. If a
mathematical gap blocks the issue you're working on, say so in that issue's thread and leave
it to a human; never open an issue for new mathematics yourself and never build off-issue
material "in passing". Gaps outside the mathematics — missing CI, infrastructure, or anything
under a human-owned path (see [`docs/workflow.md`](docs/workflow.md)) — are not issues to
open; mention them in a PR comment or leave them for a human to notice.

Improving existing code needs no human-opened issue: refactoring, simplifying proofs, modest
generalization of an existing lemma, relocation, documentation. Open an issue for it all the
same, so the work is visible.

## The rules of the code

- `main` is always green; see [`docs/workflow.md`](docs/workflow.md#ci) for what CI checks. Never
  try to disable a check; if a proof needs `maxHeartbeats`, restructure it instead.
- **Never write `sorry`.** A statement you have not proved is declared as an `axiom` under the
  name the theorem will keep, and listed in `forgive.yml` forgiving that name; proving it
  later turns the `axiom` into a `theorem` and deletes the entry. That way the audit names the
  unproved results a declaration leans on instead of collapsing them all into `sorryAx`. A
  `sorry` inside a proof is extracted into its own named axiom for the fact it stands for. CI
  rejects `sorry` in the sources and `sorryAx` in `forgive.yml` (`just no-sorry`). An `axiom` has
  no body, so Lean silently drops any `variable` instance argument its type doesn't mention: run
  `#check @Name` on every `axiom` you add and confirm the printed type keeps every intended
  hypothesis (see [`docs/conventions.md`](docs/conventions.md)).
- **Follow Foundation's contribution guidelines**, copied verbatim into this repository as
  [`docs/index.md`](docs/index.md), [`docs/style.md`](docs/style.md), and
  [`docs/refactoring.md`](docs/refactoring.md). [`docs/conventions.md`](docs/conventions.md)
  lists the few things AlphaCentauri adds. Code here should be movable into Foundation
  without a rewrite.
- **Cite the source.** Every non-trivial definition and theorem carries, at the end of its
  docstring, the reference it formalizes, one line per key: `- [HP98, Theorem I.1.5]`,
  `- [Lin97, Theorem 2.3]`. If none exists, omit the docstring unless a concise
  statement-level explanation is useful; never add prose merely to say that a result is routine
  or has no source.
- **Keep docstrings informative, not redundant.** A docstring may state only what its declaration
  says, never how or why its proof works; omit it when it merely repeats or paraphrases the
  declaration, unless a citation or a genuinely useful statement-level explanation remains. In
  docstrings, write hierarchy classes in Lean notation, e.g. `𝚷-[m + 1]`, not `𝚷ₘ₊₁`.
- **Use Foundation's vocabulary.** Search Foundation (and Mathlib) before defining anything; see
  [`docs/conventions.md`](docs/conventions.md) ("Reuse before restating") for the rule. Never
  patch Foundation's sources under `.lake/`.
- **Generic material goes to `AlphaCentauri/Vorspiel/`.** A lemma that mentions none of the
  notions the module is about — a Mathlib or Foundation gap, a transfer principle, a coding
  identity — belongs in its own `Vorspiel` module, not next to the theorem that first needed it.
- **No compatibility layer.** When you rename, move, or delete a declaration, update every use
  in the same PR and remove the old name. No aliases, wrappers, forwarding modules, or
  deprecation shims.
- **No development artifacts** in the code: plan steps, issue numbers, "TODO after review",
  skeleton-era comments.
- `AlphaCentauri/` and `AlphaCentauri.lean` are the only places code goes. `docs/`,
  `.github/`, `lakefile.toml`, `Justfile`, `lefthook.yml`, `README.md`, `AGENTS.md`, and
  `CLAUDE.md` (a symlink to `AGENTS.md`) are human-owned; a PR that touches them always needs a
  human review. The two pins (`lake-manifest.json`, `lean-toolchain`) may be bumped
  **forward only**, in their own PR.

## Pull requests

Title, body, and AI-disclosure conventions are in
[`docs/workflow.md`](docs/workflow.md#pull-requests); the title becomes the commit message on
`main`, so follow them exactly. PRs, issues, commit messages, code, and docstrings are written
in English.

## Sources

The reference texts are kept locally as `.claude/references/HP98.pdf` and
`.claude/references/Lin97.pdf`. They are copyrighted and git-ignored: read them, cite them,
never commit them or paste long passages from them.
