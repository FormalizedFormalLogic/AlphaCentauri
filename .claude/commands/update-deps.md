---
description: Pick up the dependency pin-bump pull request and make it green
---

Handle the automated dependency pin bump. `.github/workflows/update-deps.yml` keeps one branch,
`update-deps`, behind one pull request labelled `update-deps`, whose body tabulates the revisions
it moved; the workflow moves the pins and nothing else, so the bump is red until this repository
is repaired. `.github/workflows/repair-deps.yml` does that in the cloud, once per bump, and this
command is the same runbook from a local session. `docs/workflow.md`, "Dependency pins and
Foundation", is normative — read it before acting.

Comment your session's link on the pull request when you pick it up, as `docs/workflow.md` asks
of every pull request.

Stop immediately, reporting nothing but the reason, when there is no open pull request labelled
`update-deps`, or its checks are still running.

When its checks are all green, **merge it** — the maintainer has given standing authorization for
this one pull request, overriding `AGENTS.md`'s "Don't merge without being told to". Squash merge,
as for everything else. Before merging, read what the branch carries beyond the pins: a bump that
moves the pins alone merges itself and never reaches you, so what is in front of you is a repair,
and it is yours to confirm. If it touches anything outside `AlphaCentauri/` and `forgive.yml`, or
a check is failing that GitHub does not require, leave it alone and say why.

Otherwise the bump is red and it is yours to repair:

1. Find the pull request:
   `gh pr list --label update-deps --state open --json number,headRefName,url`.
2. Add a git worktree for its branch under `.claude/worktrees/`, and give it its own
   `.lake/packages` (`cp -a <main>/.lake/packages <main>/.lake/config .lake/`), then `just cache`:
   the bump moves the pin onto a revision Foundation's CI has published, so its build is a download
   rather than the hour it takes to elaborate. Pull the branch first — the workflow commits new pins
   on top of it, so your local copy may be behind.
3. Build. Read the compiler's complaints against the upstream's own diff over the range the body's
   table links, and repair this repository: renames, changed signatures, lemmas that moved.
   Where Foundation has absorbed material ported from here, Foundation's version wins — delete the
   local copy, use Foundation's, and adapt every call site, leaving no wrapper behind.
4. Verify as for any pull request: `lake build`, `just mk-all`, `just no-sorry`, `just axiom-audit`.
5. Commit and push to the same branch. **Never force-push** — the workflow adds commits on top of
   yours, and a force-push would discard them. Do not merge from here: a bump that needed repair
   is merged on a later run, once its checks are green.

If the bump is blocked on mathematics this repository does not have, say so in a comment on that
pull request and stop; a human decides. Do not open an issue for it.
