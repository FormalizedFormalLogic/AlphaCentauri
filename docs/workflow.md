# The workflow: everything through GitHub

This document is normative. It specifies how work moves through AlphaCentauri, and the answer
to "how do we do X here" is always some GitHub object: an issue, a label, an assignment, a
branch, a pull request, a check, a review, a merge. There is no side channel. If it is not on
GitHub, it has not happened.

## Roles

| Who | Owns | Does |
| --- | --- | --- |
| Humans | `docs/`, `.github/`, `lakefile.toml`, `Justfile`, `lefthook.yml`, `AGENTS.md`, `CLAUDE.md`, `README.md` | Write and review the roadmap; maintain the infrastructure and the review rubrics; merge. |
| AI agents | `AlphaCentauri/`, `AlphaCentauri.lean` | Open target issues from the roadmap; claim them; write the Lean code; open PRs; review PRs; address reviews. |

Ownership is a rule of this document for now; enforcing it mechanically (`CODEOWNERS`, branch
protection on `main`) is set up once the repository is on GitHub. The intended enforcement: a
PR touching a human-owned path needs a human approval; a PR touching only AI-owned paths needs
green CI and an approving review.

## The objects

### Roadmap

The roadmap is the specification. It surveys the source texts ([HP98], [Lin97]) chapter by
chapter against what Foundation already has, and marks what is wanted here. It is drafted by
humans outside the repository and published under `docs/` when ready; from then on it changes
only through pull requests that a human reviews. Until it is published, the roadmap is the set
of `target` issues that humans have opened. Agents that find a mathematical gap or a mistake in
it open an issue with the `roadmap` label; they do not edit it. Gaps outside the mathematics —
CI, infrastructure, or anything under a human-owned path (see Roles above) — are not issues to
open; note them in a PR comment or leave them for a human to notice.

### Target: an issue with the `target` label

A target is one formalization task of pull-request size: a theorem with its lemmas, a
definition with its basic API, a refactor. The issue states

- the source reference (e.g. `HP98, Theorem I.1.5`, or `Lin97, Lemma 5.2`), and the roadmap
  item it advances;
- the informal statement;
- what Foundation already provides that it depends on (module and declaration names);
- optionally a suggested Lean signature.

Humans open targets when they add roadmap items; agents open targets when they decompose a
roadmap item into PR-sized pieces. A target that turns out to be wrong, too large, or already
in Foundation is closed with a comment saying why.

### Classification: `definition only` or a theorem

Every target is a theorem unless it carries the `definition only` label:

- **`definition only`**: a definition (or an API for a definition Foundation already has) together
  with the minor lemmas that come with it, such as `simp` lemmas, closure properties, and agreement
  with an external notion. One pull request, one review.
- **theorem** (the default, no label of its own): a theorem or a substantial lemma. It passes
  through the two stages below.

### Two stages for a theorem

A theorem is formalized in two stages, each landing as its own pull request:

1. **Statement-formalized.** The statement is written in Foundation's vocabulary and compiles,
   declared as an `axiom` rather than proved, and listed under its own name in `axiom_debt.yml`
   (see the gate below). It is reviewed **for faithfulness to the source** before any proof is
   attempted, because a proof of the wrong statement is worthless. This stage is tracked by a
   sub-issue of the target issue, labelled `statement-formalized`, and its pull request carries
   the same label. Once CI is green and review approves, it merges into `main` like any other
   pull request — the axiom is expected to land, forgiven under its own name.
2. **Proof-formalized.** A follow-up pull request, branched from `main` after the statement has
   landed, turns each `axiom` into a `theorem` with a proof and removes the corresponding
   `axiom_debt.yml` entries. The target issue itself carries `proof-formalized` and closes when
   this pull request merges.

`sorry` is never used. A statement declared as an `axiom` carries its own name into the audit, so
the report says exactly which unproved results a declaration leans on; every `sorry` in the
library would instead collapse into one anonymous `sorryAx`. The rule is mechanical: `sorryAx` is
forgiven nowhere, and CI checks that it appears neither in the sources nor in `axiom_debt.yml`.

### Sub-issues

Large targets are decomposed with GitHub sub-issues rather than with prose: the umbrella issue
lists its work items, each pull-request-sized item is a sub-issue, and each target issue that
isn't `definition only` has a `statement-formalized` sub-issue. An umbrella closes when all of
its sub-issues are closed and its headline statement is proof-formalized.

### Claim: an assignment

To claim a target, assign yourself to the issue:

```bash
gh issue edit <n> --add-assignee @me
```

An assigned issue belongs to its assignee. To release it, unassign yourself. A claim with no
linked pull request and no activity for **14 days** is stale, and anyone may unassign it with
a comment saying so. A claim is a cooperative signal, not a lock; the hard guard against lost
work is the branch rule below.

### Branch and pull request

- Branch from `main`, named `target/<n>-<slug>`. Pushing to a branch you did not create uses
  `git push --force-with-lease=<branch>:<observed-tip>`, never a plain force push.
- One issue per pull request; the body starts with `Closes #<n>`.
- The title is in Foundation's form `<type>(scope): <subject>` with `<type>` in
  `add | fix | refactor | doc | ci | chore`. PRs are squash-merged, so the title is the
  commit message on `main`.
- The body states: the issue it closes; what was formalized, with citations; how it was
  verified; AI disclosure.
- Every commit carries a `Co-Authored-By` trailer for the model used.

### The gate: GitHub Actions

`.github/workflows/ci.yml` runs on every pull request and every push to `main`:

1. `lake build` of `AlphaCentauri` against the pinned Foundation;
2. `lake exe audit` (`just axiom-audit`, the script in `Audit/Main.lean`): no `sorry`, no
   `native_decide`, no axiom outside `propext`, `Classical.choice`, `Quot.sound`, except what
   `axiom_debt.yml` forgives, one declaration at a time (a statement formalized as an `axiom` is
   listed there forgiving its own name, and every declaration built on it names it);
3. `just no-sorry`: no `sorry` in the sources and no `sorryAx` in `axiom_debt.yml`;
4. `AlphaCentauri.lean` imports every module (`just mk-all` leaves no diff).

The audit also writes its report to `.lake/audit.json` and `.lake/audit.md`; on a pull request
CI posts the Markdown as one comment, overwritten on every run, unless the PR is labelled
`infrastructure`.

`.github/workflows/actionlint.yml` is separate and runs only when a workflow file itself changes:
[actionlint](https://github.com/rhysd/actionlint) checks `.github/workflows/` for schema,
expression, action-input, and shell errors.

A red check is never worked around; it is fixed in the PR. The code itself follows Foundation's
contribution guidelines, see [`conventions.md`](conventions.md).

### Review: a pull-request review

Once CI is green, the PR is reviewed. Reviews are posted as GitHub PR reviews with a verdict
(`approve` or `request changes`) and line-anchored findings. Reviewers are

- **AI review agents**, each judging one angle against a fixed rubric. The rubrics are adapted
  from [TauCetiReview](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics)
  (correctness, reuse, scope, attribution, API design, generality, placement, naming,
  documentation, proof quality) and will live under `docs/review/`; until then those rubrics
  apply as written, with "Mathlib / Tau Ceti" read as "Mathlib / Foundation / AlphaCentauri".
- **Humans**, at any time, on anything.

The author addresses findings by pushing to the same branch; the reviewer re-reviews the new
head. A `/review` comment by a human re-triggers review. Contradictory findings are contested
in the thread with both quoted, not resolved by silently picking one.

### Merge

Squash merge into `main`, once CI is green on the head commit and every review on that commit
approves. While the project bootstraps, a human performs the merge; automatic merging for
PRs that touch only AI-owned paths is the intended end state.

## Labels

| Label | Meaning |
| --- | --- |
| `target` | A formalization target; the unit of work. |
| `roadmap` | A problem with, or a proposed addition to, the roadmap. Human decision. |
| `meta` | The process or the infrastructure. |
| `infrastructure` | A PR touching CI, tooling, or another human-owned path and no mathematics; CI skips the axiom-audit comment on it. |
| `blocked` | Waits on another issue or on a change in Foundation; the blocker is linked. |
| `foundation` | Needs a change upstream in Foundation; a human takes it there. |
| `keep` | Opt out of automatic stale-claim release and automatic closing. |
| `definition only` | The target delivers a definition and the minor lemmas that come with it. |
| `statement-formalized` | Stage: formalize the statement only (declared as an `axiom`, forgiven by name in `axiom_debt.yml`), reviewed for faithfulness, merges once approved. |
| `proof-formalized` | Stage: turn the `axiom`s into proved theorems in a follow-up pull request; the issue closes when the proof is complete and CI is green. |

They are created on the GitHub repository by hand when it is set up; issue templates and a
label script may follow later.

## The worker loop

An autonomous agent working here does the following, and nothing outside it:

1. List open, unassigned `target` issues that are not `blocked`; pick one.
2. Claim it (assign yourself). If the assignment fails or someone else is now assigned, go to 1.
3. Read the issue, the roadmap item, the cited source, and the Foundation modules it names.
4. Branch `target/<n>-<slug>` from `main`; formalize; `lake build`; `just axiom-audit`.
5. Open the PR with `Closes #<n>`, the body described above, and AI disclosure. Wait for CI.
6. Address review findings by pushing to the branch until every review approves.
7. Once merged, or if you give up, make the issue's state match reality: it closes with the
   PR, or you unassign yourself and comment what blocked you.

## Dependency pins

`lake-manifest.json` pins the exact Foundation commit, and `lean-toolchain` must equal
Foundation's. Bumping them is welcome, **forward only**, as its own PR titled
`chore: bump Foundation to <short sha>`, with any resulting fixes in the same PR. A bump never
moves a pin backward and never edits `lakefile.toml`.

## Feeding back into Foundation

AlphaCentauri is developed against Foundation's API and in Foundation's style so that material
can be moved upstream. Deciding what moves, and opening the Foundation pull request, is a
human's job; an agent that believes a result belongs upstream says so in the issue with the
`foundation` label.
