# Formalization coverage report

Generated: 2026-05-24
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 7
- Other warnings: 9
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` | present |
| eq:newton | equation | `IsNewtonSolution` | present |
| ass:W | assumption | `class AssW` | present |
| def:empirical | definition | `empiricalMeasure`, `empiricalMeasure_isProbabilityMeasure`, `empiricalMeasureCurve` | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present-with-sorry |
| eq:weak-eq | equation | `WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

**Coverage ratio: 13 / 13 items present (7 sorry warnings remain across 3 declarations).**

Status key:
- `present` — declaration found, no sorry warnings
- `present-with-sorry` — declaration found, one or more sorry warnings (either in the body or in a helper)
- `missing` — no corresponding Lean declaration located

## Sorry inventory

### `weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)

Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

| # | Name | Line (decl) | Sorry line | Difficulty | Deps | Status |
|---|------|------------|------------|-----------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | — | 1 | (none) | **proved** |
| 2 | `hasDerivAt_phi_along_trajectory` | 241 | 255 | 3 | (none) | **sorry** |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 262 | 278 | 3 | `empiricalMeasure_integral_eq`, `hasDerivAt_phi_along_trajectory` | **sorry** |
| 4 | `diagonalCorrection_eq` | 285 | 301 | 2 | `hasDerivAt_empiricalIntegral_sum` | **sorry** |
| 5 | `diagonalCorrection_bound` | 306 | 314 | 1 | `diagonalCorrection_eq` | **sorry** |

Residual glue: line 382 (branch `HasDerivAt`, first `?_` branch of the `refine` combinator);
composes [`hasDerivAt_empiricalIntegral_sum`, `diagonalCorrection_eq`].
`tactic_sketch` is present in the plan (see `residual_glue.tactic_sketch` in the JSON).
The bound branch (second `?_`) is already closed: `exact diagonalCorrection_bound N gradW X V gradVφ t`.

Note: the build reports sorry-warning on line 334 (the `theorem` keyword) because the body
contains a `sorry` at line 382. This is Lean's standard behaviour — the warning attaches to the
declaration head.

### Non-decomposed sorries

| Enclosing declaration | Line (decl) | Tex label | Notes |
|-----------------------|------------|-----------|-------|
| `vlasovWellPosedness` | 505 | thm:vlasov-wp | Entire proof is a single `sorry`; no decomposition plan yet. Requires existence/uniqueness theory for measure-valued transport equations (Picard iteration in Wasserstein space or method of characteristics). Mathlib does not currently have this. |
| `dobrushin` | 614 | thm:dobrushin | Entire proof is a single `sorry`; no decomposition plan yet. Requires Gronwall inequality applied to a Wasserstein-1 estimate; the key analytic ingredient `\|∇W*ρ − ∇W*σ\|_∞ ≤ L·W₁(ρ,σ)` needs a Mathlib coupling/duality argument. |

## Recommended next steps

### Decomposed parent: `weakEvolutionEmpiricalMeasure`

Topological order (leaves first), lowest difficulty first within each layer:

1. **Discharge `empiricalMeasure_integral_eq`** (difficulty 1; no deps) — **already proved.**
   Hints: `MeasureTheory.integral_finset_sum`, `MeasureTheory.integral_dirac`,
   `MeasureTheory.Measure.smul_apply`, `MeasureTheory.integral_smul_measure`.

2. **Discharge `diagonalCorrection_bound`** (difficulty 1; depends on `diagonalCorrection_eq`
   which is still sorry — but `diagonalCorrection_bound`'s tactic only *calls* `diagonalCorrection_eq`
   by name, so the bound can be proved once `diagonalCorrection_eq` is in place).
   Hints: `abs_inner_le_norm`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_card_nsmul`,
   `le_iSup`.

3. **Discharge `diagonalCorrection_eq`** (difficulty 2; depends on `hasDerivAt_empiricalIntegral_sum`).
   This is the "add and subtract the diagonal" algebraic identity.
   Hints: `Finset.sum_ite`, `Finset.sum_compl_add_sum`, `inner_sub_left`,
   `inner_neg_left`, `inner_smul_left`.
   Attack order is independent of `hasDerivAt_empiricalIntegral_sum` since the statement is
   purely algebraic — a free variable stands in for the particle configurations.

4. **Discharge `hasDerivAt_phi_along_trajectory`** (difficulty 3; no deps).
   Chain rule for a smooth test function composed with a C¹ trajectory.
   Hints: `HasDerivAt.inner`, `HasFDerivAt.comp`, `HasDerivAt.prodMk`,
   `ContDiff.hasFDerivAt`.

5. **Discharge `hasDerivAt_empiricalIntegral_sum`** (difficulty 3; depends on
   `empiricalMeasure_integral_eq` — proved — and `hasDerivAt_phi_along_trajectory` — step 4).
   Differentiate under the finite empirical-measure integral using the per-particle chain rule
   and `HasDerivAt.sum` + `HasDerivAt.const_smul`.
   Hints: `HasDerivAt.sum`, `HasDerivAt.const_smul`, `HasDerivAt.congr_deriv`.

6. **Discharge the residual glue at line 382** (HasDerivAt branch of `weakEvolutionEmpiricalMeasure`).
   The plan's `tactic_sketch` provides a near-complete script:
   ```
   have hd := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ t
   have heq := diagonalCorrection_eq N gradW X V gradVφ t
   rw [heq] at hd
   convert hd using 2
   ring
   ```
   This is the fastest-path sorry to close: once steps 4 and 5 are proved, the prover may be
   able to close it in one build cycle by running the sketch verbatim.

### Non-decomposed sorries

- **`vlasovWellPosedness` (thm:vlasov-wp, line 505):** Highest mathematical value but lowest
  tractability in the current Mathlib. Requires a full existence-uniqueness theory for
  measure-valued solutions of transport equations (Picard iteration in Wasserstein space,
  or method of characteristics). Recommended approach: decompose using the sorry-decomposer
  agent before attempting a proof. Potential Mathlib anchors:
  `MeasureTheory.Measure.map`, `MeasureTheory.ProbabilityMeasure`,
  ODE uniqueness results (`ODE.IVP` or `Mathlib.Analysis.ODE.Gronwall`).

- **`dobrushin` (thm:dobrushin, line 614):** Medium tractability — the structure is clear
  (Gronwall on a Wasserstein-1 differential inequality) but requires:
  (a) the estimate `‖∇W*ρ − ∇W*σ‖_∞ ≤ L·W₁(ρ,σ)` (Lipschitz constant of the force field
  w.r.t. the measure argument), and (b) Gronwall's lemma applied to an ENNReal-valued
  function. Potential Mathlib anchors: `gronwall` (Mathlib.Analysis.ODE.Gronwall`),
  `MeasureTheory.Measure.wasserstein`, `LipschitzWith.dist_le_mul`.
  Recommended: decompose with sorry-decomposer before attempting.
