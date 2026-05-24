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
| def:empirical (none) | definition | `empiricalMeasure`, `empiricalMeasure_isProbabilityMeasure`, `empiricalMeasureCurve` | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present-with-sorry |
| eq:weak-eq | equation | `WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

**Summary: 13/13 outline items present. 3 items carry sorry (prop:weak via helpers, thm:vlasov-wp, thm:dobrushin).**

Status key:
- `present` — declaration exists, no sorry in its proof.
- `present-with-sorry` — declaration exists but the proof (or a helper) uses `sorry`.
- `present-stubbed` — declaration is a `def`/`Prop`-valued wrapper; no proof obligation yet.
- `missing` — no corresponding declaration found.

Notes:
- `eq:HN`, `eq:newton`, `ass:W`, `def:empirical` are fully proved (no sorry warnings).
- `eq:weak-eq`, `eq:vlasov`, `eq:char`, `eq:dobrushin` are `def`/`Prop`-valued wrappers with no sorry obligation.
- `cor:empirical-vlasov` (`empiricalMeasureSolvesVlasov`) and `cor:mfl` (`meanFieldLimit`) are **fully proved** — both build cleanly with no sorry warning.
- `gradient_zero_of_even`, `empiricalMeasure_isProbabilityMeasure`, `empiricalMeasure_integral_eq` are fully proved helper lemmas.

---

## Sorry inventory

### `weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)
Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

| # | Name | Line | Difficulty | Deps | Status |
|---|------|------|------------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 241 | 3 | (none) | sorry |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 262 | 3 | `empiricalMeasure_integral_eq`, `hasDerivAt_phi_along_trajectory` | sorry |
| 4 | `diagonalCorrection_eq` | 285 | 2 | `hasDerivAt_empiricalIntegral_sum` | sorry |
| 5 | `diagonalCorrection_bound` | 315 | 2 | `diagonalCorrection_eq` | sorry |

Residual glue: line 400 (branch `HasDerivAt (first ?_ branch of the refine combinator)`);
composes [`hasDerivAt_empiricalIntegral_sum`, `diagonalCorrection_eq`].
tactic_sketch present in plan.

---

### Non-decomposed sorries

| Enclosing declaration | Line | Tex label | Notes |
|-----------------------|------|-----------|-------|
| `vlasovWellPosedness` | 528 | thm:vlasov-wp | Existence and uniqueness for the Vlasov PDE; requires characteristic flow fixed-point and Mathlib PDE infrastructure not yet in scope. |
| `dobrushin` | 637 | thm:dobrushin | Dobrushin stability theorem; requires Gronwall inequality applied to Wasserstein-1 distance via coupling of characteristic flows; depends on `wasserstein1` placeholder API. |

---

## Recommended next steps

### Decomposed parent: `weakEvolutionEmpiricalMeasure` (prop:weak)

The five helpers form a linear dependency chain. Topological order (leaves first),
lowest difficulty first within each layer:

1. **Discharge `empiricalMeasure_integral_eq`** (difficulty 1; no deps) — ALREADY PROVED.
   No action needed.

2. **Discharge `hasDerivAt_phi_along_trajectory`** (difficulty 3; no deps;
   hints: `HasDerivAt.inner`, `HasFDerivAt.comp`, `HasDerivAt.prodMk`,
   `ContDiff.hasFDerivAt`).
   This is a pure chain-rule calculation: compose the derivative of `(X t i, V t i)`
   (given by `hX` and `hV`) through the smooth test function `φ` using
   `ContDiff.hasFDerivAt` to get the Fréchet derivative, then project onto
   `gradXφ` and `gradVφ` via `HasDerivAt.inner`.  `HasDerivAt.prodMk` assembles
   the pair trajectory derivative.  No Newton specialisation required at this step;
   the acceleration `a` is left as a free parameter.

3. **Discharge `hasDerivAt_empiricalIntegral_sum`** (difficulty 3; depends on
   `empiricalMeasure_integral_eq` (proved) and `hasDerivAt_phi_along_trajectory`
   (still sorry — but the call site only invokes it by name, so this helper can be
   attacked in parallel once its deps are clear);
   hints: `HasDerivAt.sum`, `HasDerivAt.const_smul`, `HasDerivAt.congr_deriv`).
   Strategy: rewrite the integral using `empiricalMeasure_integral_eq` to get a
   finite sum, differentiate term-by-term with `HasDerivAt.sum`, apply
   `hasDerivAt_phi_along_trajectory` at each particle (substituting the Newton
   acceleration), then collect with `HasDerivAt.const_smul`.

4. **Discharge `diagonalCorrection_eq`** (difficulty 2; depends on
   `hasDerivAt_empiricalIntegral_sum`;
   hints: `Finset.sum_ite`, `Finset.sum_compl_add_sum`, `inner_sub_left`,
   `inner_neg_left`, `inner_smul_left`).
   Pure algebra: split `Σ_{j≠i}` to `Σ_j − (j=i term)`, recognise the full
   sum as the convolution with the empirical spatial marginal, and isolate the
   diagonal `j=i` term as `gradW 0`.

5. **Discharge `diagonalCorrection_bound`** (difficulty 2; depends on
   `diagonalCorrection_eq`;
   hints: `abs_inner_le_norm`, `Finset.abs_sum_le_sum_abs`,
   `Finset.sum_le_card_nsmul`, `le_ciSup`, `Real.le_sSup`).
   Apply Cauchy-Schwarz (`abs_inner_le_norm`) on each summand, bound the sum
   by N times the sup via `Finset.sum_le_card_nsmul`, then cancel one factor of
   N against the N^2 denominator.  The `BddAbove` hypotheses are already
   threaded through the theorem signature; use `le_ciSup` to connect pointwise
   norms to the conditional supremum.

6. **Discharge the residual glue at line 400** — a `tactic_sketch` is available
   in the plan and is likely machine-executable in one build cycle:
   ```
   have hd := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ
                hφ_smooth gradXφ gradVφ hgradXφ hgradVφ t
   have heq := diagonalCorrection_eq N gradW X V gradVφ t
   rw [heq] at hd
   convert hd using 2
   ring
   ```

### Non-decomposed sorries

7. **Discharge `vlasovWellPosedness`** (thm:vlasov-wp, difficulty: high).
   Highest-value but hardest: requires constructing the characteristic flow as a
   contraction mapping on a function space, proving uniqueness via Gronwall, and
   narrowly-continuous regularity.  The main Mathlib gap is a ready-made
   `ODE.exists_unique_solution` for Lipschitz vector fields on infinite-dimensional
   measure spaces.  Recommended approach: reduce to finite-dimensional ODE
   existence (Picard-Lindelöf via `ODE.IVP_exists_and_unique`) applied to the
   characteristic system, then push forward by `Measure.map`.  A sorry-decomposer
   pass on this theorem would help identify the smallest tractable sub-goals.

8. **Discharge `dobrushin`** (thm:dobrushin, difficulty: high).
   Key ingredient: `|∇W * ρ − ∇W * σ|_∞ ≤ L · W₁(ρ, σ)` (Lipschitz estimate
   for the force field), then Gronwall applied to the Wasserstein distance between
   two characteristic flows.  Mathlib has `gronwall_bound` in
   `Mathlib.Analysis.ODE.Gronwall`; the Wasserstein-1 API is still maturing
   (placeholder `wasserstein1` definition used here).  Consider splitting off:
   (a) the Lipschitz-force lemma as a separate helper, (b) the coupling estimate
   as a second helper, (c) the Gronwall application as the glue.  A
   sorry-decomposer pass is recommended before attempting the full proof.
