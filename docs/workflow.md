# The workflow: everything through GitHub

This document is normative. Every step of the work is a GitHub object — an issue, a label, an
assignment, a branch, a pull request, a check, a review, a merge. If it is not on GitHub, it
has not happened.

## Roles

| Who | Owns | Does |
| --- | --- | --- |
| Humans | `docs/`, `.github/`, `lakefile.toml`, `Justfile`, `lefthook.yml`, `AGENTS.md`, `CLAUDE.md`, `README.md` | Decide what to formalize, by opening the issues; maintain the infrastructure; merge. |
| AI agents | `AlphaCentauri/`, `AlphaCentauri.lean` | Claim issues; write the Lean code; open, review, and address PRs. |

A PR touching a human-owned path needs a human approval.

## Issues

The open issues are the plan; there is no other specification. Humans open the issues for new
mathematics. An issue is one task of pull-request size and states the source reference
(`HP98, Theorem I.1.5`; `Lin97, Lemma 5.2`), the informal statement, what Foundation already
provides, and optionally a suggested Lean signature — nothing else. Design deliberation,
rejected alternatives, hierarchy-level calculations, line-count estimates, and review-focus
checklists are working notes, not the issue's content; keep those in your own local files.
Title conventions are the same as for pull requests, below.

Agents do not open issues for new mathematics: a gap or a mistake is reported in the thread of
the issue being worked on, and a human decides. An agent may open an issue for improving
existing code (refactor, simplification, relocation, documentation) so the work is visible.
Gaps in CI or infrastructure are not issues; note them in a PR comment.

Large issues are decomposed with GitHub sub-issues, one per pull request. An umbrella closes
when its sub-issues are closed.

### Definition or theorem

An issue labelled `definition only` delivers a definition and its minor lemmas (`simp` lemmas,
closure properties, agreement with an external notion) in one pull request.

Any other issue is a theorem and lands in two pull requests:

1. **`statement-formalized`.** The statement compiles, declared as an `axiom` and forgiven
   under its own name in `forgive.yml`. It is reviewed for faithfulness to the source before any
   proof is attempted. Tracked by a sub-issue carrying this label; the PR carries it too.
2. **`proof-formalized`.** A follow-up PR turns the `axiom` into a `theorem` and removes its
   `forgive.yml` entry. The issue carries this label and closes when the PR merges.

`sorry` is never used; see [`conventions.md`](conventions.md).

### Claims

Claim an issue by assigning yourself (`gh issue edit <n> --add-assignee @me`); release it by
unassigning. Never work on an issue assigned to someone else. A claim with no linked PR and no
activity for 14 days may be released by anyone, with a comment.

## Pull requests

- Branch from `main`, named `<n>-<slug>`. One issue per PR. Never branch from another PR's
  branch before it merges into `main`: a squash merge rewrites that history, so the stacked
  branch conflicts (often in `forgive.yml`) on every later push and needs manual resolution —
  wait for the prerequisite PR to land first.
- Never force-push a branch you did not create except with `--force-with-lease`.
- Title: a short noun phrase — no subtitle, no full theorem name, no `(scope)` parenthetical —
  in the form `<type>: <subject>` with `<type>` in `add | fix | refactor | doc | ci | chore |
  deps`. The one exception is the automated Foundation bump, titled
  ``deps(Foundation): Update to `<short sha>` ``.
  PRs are squash-merged, so the title becomes the commit on `main`: do not phone it in. Backtick
  every Lean identifier or notation (`` `DirectInterpretation` ``, `` `𝚺-[s]` ``); write
  mathematics in TeX (`` $\Delta_1$ ``, `` $\Sigma_n$ ``, `` $\mathsf{I}\Sigma_1$ ``,
  `` $\mathsf{PA}$ ``, `` $\mathrm{Con}$ ``), never a bare `Δ_1`, `Delta_1`, or a Unicode
  subscript `Δ₁`. The same conventions govern issue titles.
- Body: `Closes #<n>`, then a few lines on what landed and anything a reviewer should know. No
  "Route", "Verification", or "Design" sections — the diff and CI already say how it was built
  and verified.
- AI disclosure: every commit carries a `Co-Authored-By` trailer for the model, and the body
  says an AI agent wrote it.

### CI

`.github/workflows/ci.yml` runs on every PR and push to `main`: `lake build`; the axiom audit
(`just axiom-audit`, see `Audit/Main.lean` for the format: no `sorry`, no `native_decide`, no
axiom outside `propext`, `Classical.choice`, `Quot.sound` except what `forgive.yml` forgives by
name); `just no-sorry`; `just mk-all` leaves no diff. The audit report is posted as one PR
comment, overwritten on each run, unless the PR is labelled `infrastructure`. `actionlint.yml`
lints the workflow files, and `update-foundation.yml` bumps the dependency pins (below).

A red check is fixed in the PR, never worked around.

[`lefthook.yml`](../lefthook.yml) runs the same checks before every `git push`, so a red run is
caught locally. Install [lefthook](https://lefthook.dev), then `just hooks` once per clone;
`LEFTHOOK=0 git push` skips them for a branch that does not need them, and CI runs them regardless.

### Review and merge

Reviews are GitHub PR reviews with a verdict and line-anchored findings, by AI agents (each
against one rubric adapted from
[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics)) and by
humans. Findings are addressed by pushing to the same branch; contradictory findings are
contested in the thread, not resolved silently.

Squash merge into `main` once CI is green and every review approves. A human performs it, or an
agent when the user has explicitly told it to for that PR.

## Labels

| Label | Meaning |
| --- | --- |
| `definition only` | A definition and its minor lemmas; one PR, no stages. |
| `statement-formalized` | Stage: the statement as an `axiom`, forgiven in `forgive.yml`, reviewed for faithfulness. |
| `proof-formalized` | Stage: the `axiom` proved in a follow-up PR; closes the issue. |
| `infrastructure` | A PR with no mathematics; CI skips the audit comment. |
| `refactor` | Reorganizes existing code without adding results; no mathematics. |
| `update-foundation` | The automated Foundation pin bump; at most one open PR carries it. |

Nothing else is a label. Blocked, belongs upstream in Foundation, process questions — say it
in the issue thread.

## The worker loop

An open pull request labelled `update-foundation` comes before all of this; see
[Dependency pins and Foundation](#dependency-pins-and-foundation).

1. List open, unassigned issues whose thread does not say they are waiting; pick one.
2. Claim it. If that fails, go to 1.
3. Read the issue, the cited source, and the Foundation modules it names.
4. Branch, formalize, `lake build`, `just axiom-audit`.
5. Open the PR. Address review until every review approves.
6. Once merged, or if you give up, make the issue's state match reality: it closes with the
   PR, or you unassign yourself and comment what blocked you.

## Dependency pins and Foundation

`lakefile.toml` pins Foundation at an exact revision, `lake-manifest.json` records what that
revision resolves to, and `lean-toolchain` equals Foundation's. The three move together, forward
only, and nobody bumps them by hand.

[`.github/workflows/update-foundation.yml`](../.github/workflows/update-foundation.yml) moves
them every six hours, and on demand from the Actions tab (`workflow_dispatch`, optionally given
a revision to pin instead of the tip of Foundation's `master`). It keeps one branch,
`update-foundation`, behind one open pull request labelled `update-foundation` and titled
``deps(Foundation): Update to `<short sha>` ``. While that pull request is open the new pins are
committed on top of it — never a force-push, since the repairs made for the previous bump live
on that branch; otherwise the branch restarts from `main` and the pull request is opened. The
workflow moves the pins and nothing else: it does not build, and the bump is red until someone
makes it green.

That is a session's work, not an issue's:

1. An open pull request labelled `update-foundation` takes precedence over picking up an issue
   — a `/loop` iteration is the usual way to notice one. Work on its branch, in that pull
   request.
2. Build, read the compiler's complaints against Foundation's own diff over the range the pull
   request body links, and repair this repository: renames, changed signatures, lemmas that
   moved.
3. Where Foundation has absorbed material ported from here, Foundation's version wins: delete
   the local copy, use Foundation's, and adapt every call site. Never keep both, and leave no
   wrapper behind (see [`AGENTS.md`](../AGENTS.md), "No compatibility layer").
4. Push to the same branch, and leave the merge to a human as for every other pull request.

A bump blocked on mathematics this repository does not have is reported in a comment on that
pull request and left to a human.

Material here is written in Foundation's style so it can move upstream. Deciding what moves is a
human's job; an agent that thinks a result belongs upstream, or that Foundation's API needs a
change, says so in the issue thread.
