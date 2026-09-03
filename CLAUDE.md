# AlphaCentauri: agent instructions

Read [`AGENTS.md`](./AGENTS.md) first; it is the contract for every AI agent working in this repository.
Then read [`docs/workflow.md`](./docs/workflow.md) (how work moves through GitHub) before opening an issue or a pull request. New mathematics is gated by the roadmap; until it is published in this repository, work only on
`target` issues opened by a human.

Before writing or refactoring proofs, read Foundation's contribution guidelines, copied verbatim into this repository as [`docs/index.md`](./docs/index.md), [`docs/style.md`](./docs/style.md), and [`docs/refactoring.md`](./docs/refactoring.md), and [`docs/conventions.md`](./docs/conventions.md) for what this repository adds.

## Setup

Proof work uses the `lean4` plugin (marketplace `lean4-skills`, providing `/lean4:autoprove` etc.) and the `lean-lsp` MCP server (defined in `.mcp.json`; requires `uv` and `ripgrep`):

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```
