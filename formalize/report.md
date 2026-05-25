# Formalization coverage report

Generated: 2026-05-25
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 7
- Other warnings: 14
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` | present-proved |
| eq:newton | equation | `IsNewtonSolution` | present-proved |
| ass:W | assumption | `class AssW` | present-proved |
| def:empirical | definition | `empiricalMeasure`, `empiricalMeasure_isProbabilityMeasure`, `empiricalMeasureCurve` | present-proved |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present-with-sorry |
| eq:weak-eq | equation | `WeakEvolutionEq` | present-proved |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present-with-sorry |
| eq:vlasov | equation | `IsVlasovSolution` | present-proved |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present-proved |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present-proved |
| cor:mfl | corollary | `meanFieldLimit` | present-proved |

Notes on coverage decisions:
- `eq:HN`, `eq:newton`, `ass:W`, `def:empirical`, `eq:weak-eq`, `eq:vlasov`, `eq:char`, `eq:dobrushin` carry no sorries; their declarations are fully proved or are purely definitional.
- `prop:weak` (`weakEvolutionEmpiricalMeasure`) is a decomposed parent with 6 helpers; 2 helpers are proved, 4 are still sorried, and the residual glue is sorried.
- `cor:empirical-vlasov` (`empiricalMeasureSolvesVlasov`) is present and its own proof body is complete, but it calls `weakEvolutionEmpiricalMeasure` which is sorried, hence `present-with-sorry` propagates.
- `thm:vlasov-wp` and `thm:dobrushin` are present but their proofs are single `sorry`.
- `cor:mfl` (`meanFieldLimit`) is fully proved (the squeeze argument is complete; it calls `dobrushin` only through a hypothesis `hDobrushin`, not directly).

---

## Sorry inventory

### `Vlasov.weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)

Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

| # | Name | Decl line | Sorry line | Difficulty | Score | Deps | Status |
|---|------|-----------|-----------|-----------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | — | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | — | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 321 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | sorry |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 344 | 351 | 3 | 3 | (none) | sorry |
| 5 | `diagonalCorrection_eq` | 363 | 379 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | sorry |
| 6 | `diagonalCorrection_bound` | 393 | 403 | 2 | 4 | (none) | sorry |

`Score = 6 − Difficulty` for helpers; the residual glue row (below) gets a fixed `Score = 4` matching the prover spec.

Residual glue: line 481 (branch `HasDerivAt (first ?_ branch of the refine combinator)`); Score 4; composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. tactic_sketch present in plan.

---

### Flat sorry table (non-decomposed)

| Declaration | Line | Tex label | Status |
|-------------|------|-----------|--------|
| `vlasovWellPosedness` | 625 | thm:vlasov-wp | present-with-sorry |
| `dobrushin` | 734 | thm:dobrushin | present-with-sorry |

---

## Recommended next steps

### Decomposed parent: `weakEvolutionEmpiricalMeasure`

Helpers ordered by ascending difficulty (Score descending), leaf-first within ties; proved helpers omitted; residual glue ranked at effective difficulty 2 (Score 4) ahead of difficulty-2 helpers.

1. **Residual glue at line 481 (Score 4)** — branch `HasDerivAt (?_ branch)`. Has a machine-executable `tactic_sketch` in the plan; the prover's fast path may close it in one build cycle once `hasDerivAt_empiricalIntegral_sum` and `diagonalCorrection_eq` are proved. Sketch:
   ```
   have hd := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ t
   have heq := diagonalCorrection_eq N gradW X V gradVφ t
   rw [heq] at hd
   convert hd using 2
   ring
   ```

2. **`diagonalCorrection_bound`** (difficulty 2, Score 4; no deps; sorry at line 403). Pure estimation: Cauchy-Schwarz on each summand via `abs_inner_le_norm`, then `Finset.abs_sum_le_sum_abs` + `Finset.sum_le_card_nsmul` to count N terms, with `(1/N²)·N = 1/N`. Requires the `BddAbove` hypotheses already present in the signature to make the `ciSup` expressions meaningful. Mathlib hints: `abs_inner_le_norm`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_card_nsmul`, `le_ciSup`, `Real.le_sSup`.

3. **`diagonalCorrection_eq`** (difficulty 1, Score 5; depends on `convolveFunctionMeasure_empiricalSpatial_eq` which is still sorried — but Lean treats the sorry'd name as an opaque reference, so this helper can be attacked independently; sorry at line 379). Pure inner-product algebra: extend `Σ_{j≠i}` to `Σⱼ` via `Finset.sum_ite_ne` / `Finset.sum_compl_add_sum`, distribute `inner_sub_left`/`inner_smul_left`, recognise the convolution-form factor. Mathlib hints: `Finset.sum_ite_ne`, `Finset.sum_compl_add_sum`, `inner_sub_left`, `inner_neg_left`, `inner_smul_left`.

4. **`convolveFunctionMeasure_empiricalSpatial_eq`** (difficulty 3, Score 3; no deps; sorry at line 351). API-navigation chain: `Measure.map_smul` pushes `Prod.fst` through the ENNReal scalar; `Measure.map_add` + finset induction distributes over the Dirac sum; `integral_smul_measure` + `integral_finset_sum_measure` + `integral_dirac'` collapse integration to point evaluations. Mathlib hints: `MeasureTheory.Measure.map_smul`, `MeasureTheory.Measure.map_add`, `MeasureTheory.integral_smul_measure`, `MeasureTheory.integral_finset_sum_measure`, `MeasureTheory.integral_dirac'`, `MeasureTheory.Measure.sum_smul_dirac`.

5. **`hasDerivAt_empiricalIntegral_sum`** (difficulty 3, Score 3; depends on `empiricalMeasure_integral_eq` (proved) and `hasDerivAt_phi_along_trajectory` (proved); sorry at line 321). Combine the two proved helpers: rewrite `∫ φ d(empiricalMeasureCurve N X V s)` to `(1/N) * Σᵢ φ(Xᵢ,Vᵢ)` via `empiricalMeasure_integral_eq`, differentiate the finite sum via `HasDerivAt.sum` + `HasDerivAt.const_smul` applying `hasDerivAt_phi_along_trajectory` at each particle, then substitute the Newton acceleration `a t i = -(1/N) • Σ_{j≠i} gradW(X t i - X t j)` from `hSol`. Mathlib hints: `HasDerivAt.sum`, `HasDerivAt.const_smul`, `HasDerivAt.congr_deriv`.

### Non-decomposed sorries

6. **`vlasovWellPosedness`** (thm:vlasov-wp; line 625). Highest-value missing proof. Existence via Picard/Cauchy-Lipschitz on the self-consistent characteristic ODE (Lipschitz force field from AssW); uniqueness via the Dobrushin estimate. This requires substantial Mathlib ODE API (`ContinuousDynamicalSystem` / `IsPicardLindelof`) and is not yet supported by existing Mathlib stubs for the self-consistent fixed-point structure. Recommend leaving as sorry until `dobrushin` is proved and the ODE infrastructure is assessed.

7. **`dobrushin`** (thm:dobrushin; line 734). High-value but requires Wasserstein-1 API (currently a local placeholder `wasserstein1`), a coupling construction for two characteristic flows, and a Gronwall inequality argument. Key estimate `|∇W * ρ − ∇W * σ|_∞ ≤ L · W_1(ρ, σ)` needs the `LipschitzWith L gradW` hypothesis (present in signature). Mathlib's `MeasureTheory.ProbabilityMeasure.FiniteWasserstein` API is still developing; recommend using the local `wasserstein1` definition and proving the Gronwall step via `GronwallBound` or `gronwall_inequality` if available.
