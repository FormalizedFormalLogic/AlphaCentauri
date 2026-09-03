# AlphaCentauri

AlphaCentauri is an experiment in **autonomous AI formalization of the metamathematics of
first-order arithmetic**, built on top of
[Foundation](https://github.com/FormalizedFormalLogic/Foundation), the Lean 4 library of
mathematical logic of the [Formalized Formal Logic](https://github.com/FormalizedFormalLogic)
organization.

Humans write the roadmap: what to formalize, from which source, in what order. AI agents write,
review, and maintain the Lean code. **Every step of that work is carried out on GitHub**: a unit
of work is an issue, a contribution is a pull request, the gate is GitHub Actions, and the
verdict is a pull-request review. Nothing counts until it is visible there. The model is
[Tau Ceti](https://github.com/TauCetiProject/TauCeti), scaled down to a single repository and a
single subject.

## Scope

The metamathematics of first-order arithmetic as presented in two standard texts:

- **[HP98]** P. Hájek, P. Pudlák, *Metamathematics of First-Order Arithmetic*, Perspectives in
  Logic, 1998.
- **[Lin97]** P. Lindström, *Aspects of Incompleteness*, Lecture Notes in Logic 10, 1997.

Foundation already provides the arithmetical theories ($\mathsf{PA^-}$, $\mathsf{IOpen}$,
$\mathsf{I\Sigma_n}$, $\mathsf{I\Delta_0 + \Omega_1}$, $\mathsf{Q}$, $\mathsf{R_0}$,
$\mathsf{TA}$, …), definability and the arithmetical hierarchy, exponentiation, hereditarily
finite sets, and the incompleteness theorems. AlphaCentauri formalizes what those books prove
*about* such theories and Foundation does not yet have, developed against Foundation's API and
in Foundation's house style, so that whatever proves reusable can be moved into Foundation by
its maintainers. The roadmap is human-owned and is not yet published in this repository; until it
is, humans open the target issues directly.

## How work happens: GitHub is the workbench

The complete process is specified in [`docs/workflow.md`](docs/workflow.md); the contract for AI
agents is [`AGENTS.md`](AGENTS.md); the code follows Foundation's contribution guidelines, see
[`docs/conventions.md`](docs/conventions.md). In one screen:

1. **Roadmap** (human-owned): a survey of [HP98] and [Lin97] against what Foundation has, and
   the list of what is wanted. It is drafted outside the repository and will be published here,
   under `docs/`, once it is ready; from then on it changes only by human-reviewed pull requests.
2. **Targets are issues.** Each formalization target is a GitHub issue with the `target` label,
   citing the roadmap item and the theorem it comes from. The issue is the unit of work.
3. **Claims are assignments.** An agent claims a target by assigning itself to the issue, and
   releases it by unassigning. Nobody works on an issue assigned to someone else.
4. **Contributions are pull requests**, one issue per PR, from a branch of `main`, with
   `Closes #<issue>` in the body, a Foundation-style title, and disclosure of AI involvement.
5. **CI is the gate.** `main` is always green: the library builds, has no `sorry`, no axioms
   outside the standard allowlist beyond the unproved statements recorded by name in
   [`axiom_debt.yml`](axiom_debt.yml), and no warnings.
6. **Review is a PR review.** Reviewers (AI agents against fixed rubrics, and humans) post
   `approve` / `request changes` on the PR. Addressing findings means pushing to the same PR.
7. **Merge is a squash merge** into `main`, performed by a human while the project bootstraps.

## Repository layout

| Path | Owner | Contents |
| --- | --- | --- |
| `AlphaCentauri/`, `AlphaCentauri.lean` | AI | The Lean library. |
| `docs/` | Humans | The GitHub-based process (`workflow.md`, normative); Foundation's contribution guidelines (`index.md`, `style.md`, `refactoring.md`, vendored) and what this repository adds (`conventions.md`); the roadmap once published. |
| `AGENTS.md`, `CLAUDE.md` | Humans | The contract for AI agents. |
| `.github/`, `lakefile.toml`, `Justfile`, `lefthook.yml` | Humans | Infrastructure (CI and the local pre-push hooks). |
| `references.yml` | Shared | The bibliography for docstring citations, in Hayagriva YAML. |
| `axiom_debt.yml` | AI | The outstanding debt: every statement formalized but not yet proved, declared as an `axiom` and listed here under its own name. |
| `lake-manifest.json`, `lean-toolchain` | Shared | Pins; forward-only bumps are welcome as their own PR. |

## Building

Foundation is a git dependency without a public build cache, so the first build compiles it from
source; Mathlib comes from its cache.

```bash
lake exe cache get   # Mathlib oleans
lake build           # builds Foundation (first time only), then AlphaCentauri
just axiom-audit     # the axiom allowlist
just no-sorry        # sorry-freeness
```

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain) and must match Foundation's.

### Pre-push checks

[`lefthook.yml`](lefthook.yml) runs the same checks CI does — `mk_all`, `lake build`, the axiom
audit, the `sorry` check, and `actionlint` if it is installed — before every `git push`, so a red
CI run is caught locally. Install [lefthook](https://lefthook.dev) (`go install github.com/evilmartians/lefthook@latest`,
or your package manager), then register the hooks once per clone:

```bash
just hooks           # = lefthook install
```

`LEFTHOOK=0 git push` skips them for a push that does not need them (a docs-only branch, say);
CI runs them regardless.

## Related projects

- [Foundation](https://github.com/FormalizedFormalLogic/Foundation): the library this project
  builds on and feeds back into.
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
  [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap),
  [TauCetiReview](https://github.com/TauCetiProject/TauCetiReview): the AI-authored,
  human-directed Lean library whose process this project adapts.

## License

Apache-2.0, like Foundation.
