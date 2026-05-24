# Formalization coverage report

Generated: 2026-05-24
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 7
- Other warnings: 7 (unused section vars, unused simp arg, unused variables)
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

Status values: `present` (fully proved), `present-with-sorry` (declaration present, proof incomplete), `present-stubbed` (placeholder definition), `commented-out`, `missing`.

**Summary: 13/13 outline items present (0 missing). 3 top-level declarations carry sorries.**

Notes on individual items:

- `eq:HN` / `hamiltonianN` — fully proved noncomputable definition; no sorry.
- `eq:newton` / `IsNewtonSolution` — Prop-valued predicate, no proof required.
- `ass:W` / `class AssW` + `gradient_zero_of_even` — fully proved helper lemma (even W implies gradient at 0 vanishes).
- `def:empirical` — `empiricalMeasure` is a complete noncomputable def; `empiricalMeasure_isProbabilityMeasure` is fully proved; `empiricalMeasureCurve` is a complete def.
- `prop:weak` / `weakEvolutionEmpiricalMeasure` — decomposed; see Sorry inventory below.
- `eq:weak-eq` / `WeakEvolutionEq` — Prop-valued predicate wrapping the distributional identity; no proof required.
- `cor:empirical-vlasov` / `empiricalMeasureSolvesVlasov` — fully proved (delegates to `weakEvolutionEmpiricalMeasure` and `gradient_zero_of_even`; no residual sorry in the corollary itself).
- `eq:vlasov` / `IsVlasovSolution` — Prop-valued predicate; no proof required.
- `thm:vlasov-wp` / `vlasovWellPosedness` — single top-level sorry; no decomposition plan.
- `eq:char` — three declarations (`IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward`); all complete (Prop predicates or noncomputable defs with no sorry).
- `thm:dobrushin` / `dobrushin` — single top-level sorry; no decomposition plan.
- `eq:dobrushin` / `DobrushinStabilityEstimate` — Prop-valued predicate; no proof required.
- `cor:mfl` / `meanFieldLimit` — fully proved (uses `hDobrushin` as an axiom-like hypothesis and closes by a squeeze argument with `ENNReal.Tendsto.const_mul`; no sorry).

## Sorry inventory

### `weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/weakEvolutionEmpiricalMeasure.json`

| # | Name | Line (decl) | Difficulty | Deps | Status |
|---|------|-------------|-----------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 241 | 3 | (none) | sorry |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 262 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | sorry |
| 4 | `diagonalCorrection_eq` | 285 | 2 | hasDerivAt_empiricalIntegral_sum | sorry |
| 5 | `diagonalCorrection_bound` | 306 | 1 | diagonalCorrection_eq | sorry |

Residual glue: line 382 (branch `HasDerivAt (first ?_ branch of the refine combinator)`); composes [`hasDerivAt_empiricalIntegral_sum`, `diagonalCorrection_eq`]. tactic_sketch present in plan.

Status: helper #1 (`empiricalMeasure_integral_eq`) is proved (no build warning). Helpers #2–#5 and the residual glue each carry a sorry (build warnings at lines 241, 262, 285, 306, 334 respectively).

### Non-decomposed sorries (flat table)

| Declaration | Line (decl) | Tex label | Status |
|-------------|-------------|-----------|--------|
| `vlasovWellPosedness` | 505 | thm:vlasov-wp | present-with-sorry |
| `dobrushin` | 614 | thm:dobrushin | present-with-sorry |

## Recommended next steps

### Decomposed parent: `weakEvolutionEmpiricalMeasure` (prop:weak)

Attack helpers in topological order (leaves first), lowest difficulty first within each layer:

1. **Discharge `diagonalCorrection_bound`** (difficulty 1; depends on `diagonalCorrection_eq` by name only in the plan — the statement is self-contained and can be attacked independently).
   Hints: `abs_inner_le_norm`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_card_nsmul`, `le_iSup`.
   The bound follows from Cauchy-Schwarz on each summand and the counting argument (1/N²) · N = 1/N.

2. **Discharge `hasDerivAt_phi_along_trajectory`** (difficulty 3; no deps; independent of all other helpers).
   Hints: `HasDerivAt.inner`, `HasFDerivAt.comp`, `HasDerivAt.prodMk`, `ContDiff.hasFDerivAt`.
   Strategy: apply the chain rule for `HasDerivAt` through the smooth function φ composed with the particle trajectory `(X · i, V · i)`, then identify the Euclidean inner products with `fderiv` evaluated at the velocity and acceleration.

3. **Discharge `hasDerivAt_empiricalIntegral_sum`** (difficulty 3; depends on helpers #1 proved + #2 above).
   Hints: `HasDerivAt.sum`, `HasDerivAt.const_smul`, `HasDerivAt.congr_deriv`.
   Strategy: use `empiricalMeasure_integral_eq` to reduce the integral to a finite sum, differentiate term-by-term with `hasDerivAt_phi_along_trajectory`, then specialise the acceleration `a t i` to the Newton force.

4. **Discharge `diagonalCorrection_eq`** (difficulty 2; depends on `hasDerivAt_empiricalIntegral_sum`).
   Hints: `Finset.sum_ite`, `Finset.sum_compl_add_sum`, `inner_sub_left`, `inner_neg_left`, `inner_smul_left`.
   Strategy: extend the sum from `Σ_{j≠i}` to `Σ_j` and subtract the diagonal `j=i` contribution (which is `∇W(0)`); the off-diagonal part reconstitutes the convolution with the spatial marginal.

5. **Discharge the residual glue** at line 382 (difficulty: machine-executable; `tactic_sketch` present in plan).
   The plan's `tactic_sketch` is:
   ```
   have hd := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ t
   have heq := diagonalCorrection_eq N gradW X V gradVφ t
   rw [heq] at hd
   convert hd using 2
   ring
   ```
   This should close in one build cycle once helpers #3 and #4 are proved.

### Non-decomposed sorries

- **`vlasovWellPosedness`** (thm:vlasov-wp; single sorry): The highest-value open goal. Requires constructing a global-in-time narrowly-continuous probability-measure-valued solution to the Vlasov equation. The standard proof proceeds via the characteristic ODE (`IsCharacteristicFlow`), which is already defined. Key missing Mathlib API: a Picard-Lindelöf theorem for ODEs in infinite-dimensional spaces, or a fixed-point argument over the Wasserstein space. Short-term path: invoke `dobrushin` (once proved) as the uniqueness component; for existence, construct the characteristic flow by the Carathéodory ODE theorem applied to the Lipschitz velocity field `gradW`.

- **`dobrushin`** (thm:dobrushin; single sorry): Tractable given the existing infrastructure. The proof needs: (a) construct coupled characteristic flows for `f` and `g`; (b) estimate `d/dt W₁(f_t, g_t)` using the key Lipschitz bound `‖∇W*ρ − ∇W*σ‖_∞ ≤ L · W₁(ρ,σ)` (requires relating the local `wasserstein1` definition to Mathlib's Kantorovich duality); (c) close by Gronwall. The Gronwall lemma `GronwallBound` is available in Mathlib. The main gap is the Lipschitz-convolution estimate and the identification of `wasserstein1` with the Mathlib `MeasureTheory.Measure.FiniteWasserstein` API.
