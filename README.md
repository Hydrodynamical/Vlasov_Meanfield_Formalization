# A Formalization of the Mean-Field Derivation of the Vlasov Equation

A Lean 4 / Mathlib formalization of the mean-field derivation of the Vlasov
equation — forward well-posedness, Dobrushin's 1979 stability estimate, the
mean-field limit, and a short-window superposition principle (weak solutions
are Lagrangian) — together with the paper reporting how it was built:
AI-assisted, in about a month, framed as a formalization game.

- **Paper**: [PAPER.pdf](PAPER.pdf) (source: [PAPER.tex](PAPER.tex))
- **Lean development**: [`Vlasov/`](Vlasov/) — about 22,000 lines, zero
  `sorry`, Lean v4.29.1 + Mathlib (both pinned)
- **Blueprint site**: [hydrodynamical.github.io/Vlasov_Meanfield_Formalization](https://hydrodynamical.github.io/Vlasov_Meanfield_Formalization/)
  — the development as an annotated dependency graph, statements extracted
  from the Lean proofs
- **API documentation**: [the same site, under /docs](https://hydrodynamical.github.io/Vlasov_Meanfield_Formalization/docs/index.html)
  — doc-gen4 pages for every declaration, searchable, with source links to
  the exact commit

## The theorems

| Paper | Lean declaration | Source |
|---|---|---|
| Theorem 1.3 — forward well-posedness | `vlasovWellPosedness` | [CharacteristicFlow.lean:12517](Vlasov/Vlasov/OT/CharacteristicFlow.lean#L12517) |
| Definition 1.4 — $W_1$ by Kantorovich–Rubinstein duality | `wasserstein1` | [Wasserstein.lean:62](Vlasov/Vlasov/OT/Wasserstein.lean#L62) |
| Theorem 1.5 — Dobrushin stability (1979) | `dobrushin` | [CharacteristicFlow.lean:12907](Vlasov/Vlasov/OT/CharacteristicFlow.lean#L12907) |
| Corollary 1.6 — mean-field limit | `meanFieldLimit` | [Basic.lean:1628](Vlasov/Vlasov/Basic.lean#L1628) |
| Theorem 1.7 — superposition: weak ⟹ Lagrangian | `weak_isLagrangianVlasovSolutionOn` | [WeakToLagrangian.lean:4541](Vlasov/Vlasov/OT/WeakToLagrangian.lean#L4541) |

The full artifact inventory, with the trust story, is
[formalize/ARTIFACTS.md](formalize/ARTIFACTS.md); a mathematics ↔ Lean
correspondence table is
[formalize/codebase-outline.md](formalize/codebase-outline.md).

## Build and check the certificate

```bash
cd Vlasov
lake exe cache get   # pull precompiled Mathlib (skipping this compiles Mathlib from source)
lake build
lake env lean ../formalize/certification/footprint-check.lean
```

The second command is the certificate. For each of the three headline theorems
it must print exactly

```
[propext, Classical.choice, Quot.sound]
```

— Lean's three standard axioms, no `sorryAx`, no project-specific axioms. A
green build alone is not the certificate; the axiom footprint is.

## Build the paper

```bash
latexmk -xelatex -interaction=nonstopmode -halt-on-error PAPER.tex
```

XeLaTeX is required (the Lean listings use `fontspec`); all fonts ship with
TeX Live, so nothing needs installing. `PAPER.pdf` is checked in, so this
step is optional.

## What else is here

| Path | Contents |
|---|---|
| [`Vlasov/`](Vlasov/) | the Lean package — see its [README](Vlasov/README.md) for the module map |
| [`formalize/`](formalize/) | the build record: pipeline docs, per-session agent logs, plan sidecars, session-planning documents ([`planning/`](formalize/planning/)), certification tooling ([`certification/`](formalize/certification/)), and the retrospective data and scripts behind the paper's figures ([`retrospective/`](formalize/retrospective/)) |
| [`CLAUDE.md`](CLAUDE.md) | the standing instruction file $\mathcal{G}$ of the paper — the lesson series (L/P/M/B) accumulated across the build |
| [`.claude/agents/`](.claude/agents/) | the eight sub-agent specifications |
| [`formalize.sh`](formalize.sh) | the driver script coordinating the sub-agents |

The development's 362-commit build history is itself data: the paper's
Section 4 figures are regenerated from it by
`python3 formalize/retrospective/analyze.py`.

## License

[Apache 2.0](LICENSE).
