# AlphaCentauri

AlphaCentauri is an experiment in **autonomous AI formalization of the metamathematics of
first-order arithmetic**, built on top of
[Foundation](https://github.com/FormalizedFormalLogic/Foundation), the Lean 4 library of
mathematical logic of the [Formalized Formal Logic](https://github.com/FormalizedFormalLogic)
organization.

Humans decide what to formalize, from which source, in what order, one GitHub issue at a time.
AI agents write, review, and maintain the Lean code. **Every step of that work is carried out on GitHub**: a unit
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
its maintainers. What to formalize is decided by humans, who open the issues.

## How work happens: GitHub is the workbench

The complete process is specified in [`docs/workflow.md`](docs/workflow.md); the contract for AI
agents is [`AGENTS.md`](AGENTS.md); the code follows Foundation's contribution guidelines, see
[`docs/conventions.md`](docs/conventions.md). In one screen:

1. **Issues are the plan** (human-owned). Each formalization task is a GitHub issue opened by a
   human, citing the theorem and the source it comes from. The issue is the unit of work; a
   theorem passes through two stages, `statement-formalized` then `proof-formalized`.
2. **Claims are assignments.** An agent claims an issue by assigning itself to it, and
   releases it by unassigning. Nobody works on an issue assigned to someone else.
3. **Contributions are pull requests**, one issue per PR, from a branch of `main`, with
   `Closes #<issue>` in the body, a Foundation-style title, and disclosure of AI involvement.
4. **CI is the gate.** `main` is always green: the library builds, has no `sorry`, no axioms
   outside the standard allowlist beyond the unproved statements recorded by name in
   [`forgive.yml`](forgive.yml), and no warnings.
5. **Review is a PR review.** Reviewers (AI agents against fixed rubrics, and humans) post
   `approve` / `request changes` on the PR. Addressing findings means pushing to the same PR.
6. **Merge is a squash merge** into `main`, performed by a human, or by an agent once
   explicitly told to for that PR.

## Repository layout

| Path | Owner | Contents |
| --- | --- | --- |
| `AlphaCentauri/`, `AlphaCentauri.lean` | AI | The Lean library. |
| `docs/` | Humans | The GitHub-based process (`workflow.md`, normative); Foundation's contribution guidelines (`index.md`, `style.md`, `refactoring.md`, vendored) and what this repository adds (`conventions.md`). |
| `AGENTS.md`, `CLAUDE.md` | Humans | The contract for AI agents; `CLAUDE.md` is a symlink to `AGENTS.md`. |
| `.github/`, `lakefile.toml`, `Justfile`, `lefthook.yml` | Humans | Infrastructure (CI and the local pre-push hooks). |
| `references.yml` | Shared | The bibliography for docstring citations, in Hayagriva YAML. |
| `forgive.yml` | AI | The outstanding debt: every statement formalized but not yet proved, declared as an `axiom` and listed here under its own name. |
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

## Zoo

The zoo illustrates the interrelationships among the arithmetical theories, verified in Lean 4. It
is generated from the environment by [`Zoo/`](./Zoo) on every build; run `just zoo` to regenerate it
locally.

- A solid arrow $\mathsf{A} \leftarrow \mathsf{B}$ indicates that $\mathsf{B}$ is strictly stronger than $\mathsf{A}$; that is, $\mathsf{B}$ is stronger than $\mathsf{A}$, while $\mathsf{A}$ is not stronger than $\mathsf{B}$, in terms of provability strength.
- A dashed arrow $\mathsf{A} \dashleftarrow \mathsf{B}$ indicates that $\mathsf{B}$ is stronger than $\mathsf{A}$ in terms of provability strength.
- A double line $\mathsf{A} \xlongequal{} \mathsf{B}$ indicates that $\mathsf{A}$ and $\mathsf{B}$ are equivalent in terms of provability strength.

### Arithmetic Theory Zoo

<a href="https://formalizedformallogic.github.io/AlphaCentauri/zoo/arithmetic.png"><img alt="Arithmetic Theory Zoo" src="https://formalizedformallogic.github.io/AlphaCentauri/zoo/arithmetic.png" height="600"></a>

## Related projects

- [Foundation](https://github.com/FormalizedFormalLogic/Foundation): the library this project
  builds on and feeds back into.
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
  [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap),
  [TauCetiReview](https://github.com/TauCetiProject/TauCetiReview): the AI-authored,
  human-directed Lean library whose process this project adapts.

## License

Apache-2.0, like Foundation.
