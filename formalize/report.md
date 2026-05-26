# Formalization coverage report

Generated: 2026-05-25
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 6
- Other warnings: 16
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
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present-with-sorry |
| eq:vlasov | equation | `IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

Status key: `present` = fully proved, `present-with-sorry` = declared and structurally correct but
contains at least one `sorry`, `commented-out` = skipped with TODO comment, `missing` = no
corresponding declaration found.

Summary: 13/13 outline items are present; 4 items contain at least one sorry.

---

## Sorry inventory

### `weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)

Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

This theorem was decomposed by the sorry-decomposer agent.  The helper graph
shows 6 helpers plus a residual-glue sorry inside the parent's body.

Helper statuses are read directly from the build's sorry-warning lines (not
from any stored field in the plan):

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | sorry |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 344 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 384 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | sorry |
| 6 | `diagonalCorrection_bound` | 415 | 2 | 4 | (none) | sorry |

`Score = 6 - Difficulty`; the residual glue row (below) gets a fixed Score = 4.

Residual glue: line 510 (branch `HasDerivAt (first ?_ branch of the refine combinator)`);
Score 4; composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq].
tactic_sketch present in plan.

Because the residual glue is inside `weakEvolutionEmpiricalMeasure`'s body, the
build reports its sorry at the parent declaration line (448) rather than line 510.
The actual sorry is the first `?_` branch of the `refine` at line 510.

### Other (non-decomposed) sorries — flat table

| Declaration | Line | Tex label | Notes |
|-------------|------|-----------|-------|
| `vlasovWellPosedness` | 638 | thm:vlasov-wp | Full existence-uniqueness for Vlasov; requires Mathlib API for `𝒫_1` and narrow continuity not yet stable |
| `dobrushin` | 747 | thm:dobrushin | Dobrushin stability theorem; requires Wasserstein-1 contraction + Gronwall; placeholder `wasserstein1` used |

Note: `empiricalMeasureSolvesVlasov` (cor:empirical-vlasov) and `meanFieldLimit` (cor:mfl) carry
no *new* sorries — they depend on `weakEvolutionEmpiricalMeasure` and `dobrushin` respectively
and propagate those sorries transitively, but their own proof bodies are complete (they close
under sorry'd hypotheses).  The build reports sorry warnings for cor:mfl via propagation
only; the meanFieldLimit proof body itself is fully written.

---

## Recommended next steps

The recommendations below are ordered by ascending difficulty (Score descending), with
ties broken by leaf-first (empty deps ahead of non-empty), then ascending line number.
Helpers 1, 2, and 4 are already proved and are omitted.

### Decomposed parent: `weakEvolutionEmpiricalMeasure`

**1. Discharge the residual glue at line 510 (effective difficulty 2, Score 4).**
   The plan supplies a machine-executable `tactic_sketch`; the prover's fast path
   may close it in one build cycle:

   ```
   have hd := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ hφ_smooth
     gradXφ gradVφ hgradXφ hgradVφ t
   have heq := diagonalCorrection_eq N gradW X V gradVφ t
   rw [heq] at hd
   convert hd using 2
   ring
   ```

   This glue composes `hasDerivAt_empiricalIntegral_sum` (currently sorry'd at line 305)
   and `diagonalCorrection_eq` (currently sorry'd at line 384).  In Lean, sorry'd names
   are treated as opaque references, so the residual glue can be attempted independently
   of the helper statuses — Lean will accept the glue tactic once the types match, even
   if the dependencies are still sorry'd.

**2. Discharge `diagonalCorrection_eq` (helper 5; difficulty 1, Score 5; no blocking deps
   since `convolveFunctionMeasure_empiricalSpatial_eq` is already proved).**
   The plan supplies a proof sketch:

   ```
   have hconv : ∀ i : Fin N,
       convolveFunctionMeasure gradW
           (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i) =
         (1 / (N : ℝ)) • ∑ j : Fin N, gradW (X t i - X t j) := fun i =>
     convolveFunctionMeasure_empiricalSpatial_eq N gradW hgradW_meas X V t i
   simp_rw [hconv]
   have hext : ∀ i : Fin N,
       (∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else (0 : PhysSpace d))
       = (∑ j : Fin N, gradW (X t i - X t j)) - gradW 0 := ...
   simp_rw [hext, inner_sub_left, inner_smul_left]
   ring
   ```

   Mathlib hints: `Finset.sum_ite_ne`, `Finset.sum_compl_add_sum`, `inner_sub_left`,
   `inner_neg_left`, `inner_smul_left`.

**3. Discharge `diagonalCorrection_bound` (helper 6; difficulty 2, Score 4; no deps).**
   The plan supplies a proof sketch using Cauchy-Schwarz per summand and N counting.
   Mathlib hints: `abs_inner_le_norm`, `Finset.abs_sum_le_sum_abs`,
   `Finset.sum_le_card_nsmul`, `le_ciSup`, `Real.le_sSup`.

   The `BddAbove` hypotheses are already threaded through as parameters; the key
   calculation is `(1/N²) * N = 1/N` after `Finset.sum_le_card_nsmul`.

**4. Discharge `hasDerivAt_empiricalIntegral_sum` (helper 3; difficulty 3, Score 3;
   deps: helpers 1 and 2, both proved).**
   The plan supplies a proof sketch:

   ```
   have hφ_fderiv : ∀ z, HasFDerivAt φ (fderiv ℝ φ z) z := fun z =>
     (hφ_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
   simp_rw [fun s => empiricalMeasure_integral_eq N (X s) (V s) φ]
   refine HasDerivAt.const_mul _ ?_
   exact HasDerivAt.sum fun i _ =>
     hasDerivAt_phi_along_trajectory N X V hSol.1 _ hSol.2 φ
       (fderiv ℝ φ) hφ_fderiv gradXφ gradVφ hgradXφ hgradVφ t i
   ```

   Mathlib hints: `HasDerivAt.sum`, `HasDerivAt.const_smul`, `HasDerivAt.congr_deriv`.
   Note: `hSol.1` and `hSol.2` split the conjunction in `IsNewtonSolution`; the proof
   sketch omits `hgradW_meas` (it is not needed for this helper — measurability is only
   needed by `diagonalCorrection_eq`).

### Non-decomposed sorries

**5. Discharge `vlasovWellPosedness` (thm:vlasov-wp; difficulty: high).**
   Full measure-valued well-posedness for the nonlinear Vlasov equation requires a
   Picard iteration or a fixed-point argument in the space of narrowly continuous
   probability-measure curves.  The Mathlib API for Wasserstein / narrow topology is
   still developing.  Suggested approach: prove existence via the characteristic-flow
   fixed-point construction encoded in `IsCharacteristicFlow` +
   `IsCharacteristicFlowSelfConsistent`; use the Dobrushin estimate for uniqueness.
   This is a major formalization effort; decompose further before attempting.

**6. Discharge `dobrushin` (thm:dobrushin; difficulty: high).**
   The Dobrushin 1979 stability theorem requires:
   - A Gronwall lemma applied to `d/dt W_1(f_t, g_t) ≤ C · W_1(f_t, g_t)`.
   - The key estimate `‖∇W * ρ − ∇W * σ‖_∞ ≤ L · W_1(ρ, σ)` (Lipschitz
     continuity of the convolution operator in Wasserstein distance).
   - Coupling of two characteristic flows and tracking their separation.
   The local `wasserstein1` definition (KR dual formula, ENNReal-valued) may need
   lemmas establishing its basic properties (triangle inequality, symmetry, etc.)
   before the main estimate can be stated and proved.  Consider decomposing this
   theorem into sub-helpers before attacking it directly.
