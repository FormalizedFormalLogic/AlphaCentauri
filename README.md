# AlphaCentauri

An experiment in **autonomous AI formalization of the metamathematics of first-order arithmetic**,
built on [Foundation](https://github.com/FormalizedFormalLogic/Foundation), the Lean 4 library of
mathematical logic of the [Formalized Formal Logic](https://github.com/FormalizedFormalLogic)
organization.

Humans decide what to formalize, one GitHub issue at a time, from
[HP98] and [Lin97]; AI agents write, review and maintain the Lean code. Every step happens on
GitHub. The process is [`docs/workflow.md`](docs/workflow.md), the contract for agents is
[`AGENTS.md`](AGENTS.md), and the code conventions are
[`docs/conventions.md`](docs/conventions.md).

- **[HP98]** P. Hájek, P. Pudlák, *Metamathematics of First-Order Arithmetic*, Perspectives in
  Logic, 1998.
- **[Lin97]** P. Lindström, *Aspects of Incompleteness*, Lecture Notes in Logic 10, 1997.

## Building

Foundation is a git dependency without a public build cache, so the first build compiles it from
source; Mathlib comes from its cache.

```bash
lake exe cache get   # Mathlib oleans
lake build           # builds Foundation (first time only), then AlphaCentauri
just axiom-audit     # the axiom allowlist
just no-sorry        # sorry-freeness
just hooks           # run the CI checks before every push (needs lefthook)
```

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
