# Formalization coverage report

Generated: 2026-05-25
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status
- Result: success
- Sorry warnings: 5
- Other warnings: 16
- Errors: 0

## Coverage
| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` | present |
| eq:newton | equation | `IsNewtonSolution` | present |
| ass:W | assumption | `class AssW` | present |
| def:empirical | definition | `empiricalMeasure`, `empiricalMeasureCurve`, `empiricalMeasure_isProbabilityMeasure` | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present-with-sorry |
| eq:weak-eq | equation | `WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

Status key: `present` = fully proved (no sorry); `present-with-sorry` = declared and type-correct but one or more proof obligations remain as `sorry`.

**Summary: 13/13 outline items present. 10/13 fully proved, 3/13 present-with-sorry.**

---

## Sorry inventory

### `weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)
Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | sorry |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 344 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 384 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 462 | 2 | 4 | (none) | sorry |

Score = 6 − Difficulty. The residual glue row below gets a fixed Score = 4.

Residual glue: line 557 (branch `HasDerivAt (first ?_ branch of the refine combinator)`); Score 4;
composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. tactic_sketch present in plan.

---

### Non-decomposed sorries (flat table)

| Declaration | Line | Tex label | Notes |
|-------------|------|-----------|-------|
| `vlasovWellPosedness` | 685 | thm:vlasov-wp | Full existence-and-uniqueness for Vlasov; requires Mathlib API for narrowly continuous measure-valued flows |
| `dobrushin` | 794 | thm:dobrushin | Dobrushin stability theorem; requires Gronwall inequality + Wasserstein-1 coupling argument |

---

## Recommended next steps

### Decomposed parent: `weakEvolutionEmpiricalMeasure` (prop:weak)

Ordering: ascending Score (highest tractability first), ties broken by leaf-first then ascending
line number. Residual glue (Score 4, with machine-executable `tactic_sketch`) ranks ahead of
difficulty-2 helpers at the same score. Helpers 1, 2, 4, 5 are already `proved` and are omitted.

1. **Discharge the residual glue at line 557** (Score 4) — has a machine-executable `tactic_sketch`
   in the plan; the prover's fast path may close it in one build cycle.

   Sketch from plan:
   ```lean
   have hd := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ t
   have heq := diagonalCorrection_eq N gradW X V gradVφ t
   rw [heq] at hd
   convert hd using 2
   ring
   ```
   Note: both `hasDerivAt_empiricalIntegral_sum` (the dep) and `diagonalCorrection_eq` are
   invoked only by name; the residual glue is independently attackable even while helper 3 is
   still sorry.

2. **Discharge `diagonalCorrection_bound`** (difficulty 2, Score 4; no deps;
   hints: `abs_inner_le_norm`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_card_nsmul`,
   `le_ciSup`, `Real.le_sSup`).

   The plan supplies a full `proof_sketch`:
   ```lean
   have h_supW : ‖gradW 0‖ ≤ ⨆ x, ‖gradW x‖ := le_ciSup hgradW_bdd 0
   have h_supV : ∀ i : Fin N, ‖gradVφ (X t i, V t i)‖ ≤ ⨆ z, ‖gradVφ z‖ := fun i =>
     le_ciSup hgradVφ_bdd (X t i, V t i)
   have h_term : ∀ i : Fin N,
       ‖@inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))‖ ≤
         (⨆ x, ‖gradW x‖) * ⨆ z, ‖gradVφ z‖ := fun i =>
     (abs_inner_le_norm _ _).trans
       (mul_le_mul h_supW (h_supV i) (norm_nonneg _)
         (le_trans (norm_nonneg _) h_supW))
   have h_sum : |∑ i : Fin N, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
       ≤ N * ((⨆ x, ‖gradW x‖) * ⨆ z, ‖gradVφ z‖) := by
     refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
     rw [show (N : ℝ) = (Finset.univ.card : ℝ) by simp [Finset.card_univ]]
     exact Finset.sum_le_card_nsmul _ _ _ (fun i _ => h_term i) |>.trans_eq (by simp [nsmul_eq_mul])
   have hN_pos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
   rw [abs_mul, abs_of_nonneg (by positivity)]
   calc (1 / (N : ℝ)^2) * |∑ i, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
       ≤ (1 / (N : ℝ)^2) * (N * ((⨆ x, ‖gradW x‖) * ⨆ z, ‖gradVφ z‖)) :=
           mul_le_mul_of_nonneg_left h_sum (by positivity)
     _ = (1 / (N : ℝ)) * ((⨆ x, ‖gradW x‖) * ⨆ z, ‖gradVφ z‖) := by field_simp; ring
     _ = (1 / (N : ℝ)) * (⨆ x, ‖gradW x‖) * ⨆ z, ‖gradVφ z‖ := by ring
   ```

3. **Discharge `hasDerivAt_empiricalIntegral_sum`** (difficulty 3, Score 3; depends on
   `empiricalMeasure_integral_eq` and `hasDerivAt_phi_along_trajectory` — both already proved,
   so all deps are satisfied; independent attack-order applies in any case;
   hints: `HasDerivAt.sum`, `HasDerivAt.const_smul`, `HasDerivAt.congr_deriv`).

   Plan `proof_sketch`:
   ```lean
   have hφ_fderiv : ∀ z, HasFDerivAt φ (fderiv ℝ φ z) z := fun z =>
     (hφ_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
   simp_rw [fun s => empiricalMeasure_integral_eq N (X s) (V s) φ]
   refine HasDerivAt.const_mul _ ?_
   exact HasDerivAt.sum fun i _ =>
     hasDerivAt_phi_along_trajectory N X V hSol.1 _ hSol.2 φ
       (fderiv ℝ φ) hφ_fderiv gradXφ gradVφ hgradXφ hgradVφ t i
   ```
   Note: `simp_rw` with a function rewriting `s` may need `show` or `conv` adjustment if
   Lean's elaborator cannot unify the `s` binder; try `fun s => show (1 / N) * ∑ i, φ ...`
   as an intermediate step.

### Non-decomposed sorries

4. **`vlasovWellPosedness`** (thm:vlasov-wp, line 685, Score 1 / very hard) —
   Requires constructing a unique narrowly-continuous measure-valued solution to a
   nonlinear transport equation. The standard approach (via Dobrushin/characteristic
   flow + Banach fixed-point in W_1) is self-referential with `dobrushin` below.
   Mathlib does not yet have a narrowly-continuous flow theorem in this generality.
   Recommended approach: introduce an `IsNarrowlyContinuous` predicate (or use
   `MeasureTheory.ProbabilityMeasure` topology), then assert existence via sorry-stubbing
   a Picard iteration; uniqueness follows from `dobrushin` once that is proved.
   This sorry is high-difficulty and likely requires new Mathlib API.

5. **`dobrushin`** (thm:dobrushin, line 794, Score 1 / very hard) —
   The Dobrushin exponential stability estimate. Requires:
   (a) A Gronwall inequality for measure-valued flows (available in Mathlib as
   `gronwall_bound` for scalar ODEs; the measure version is non-trivial);
   (b) The key Lipschitz estimate `‖∇W * ρ − ∇W * σ‖_∞ ≤ L · W_1(ρ, σ)` (provable
   from `LipschitzWith L gradW` and the Kantorovich–Rubinstein duality);
   (c) The coupling argument via characteristic flows (requires `IsCharacteristicFlow`
   and `IsCharacteristicFlowSelfConsistent` instances).
   Suggested first step: prove the key Lipschitz estimate for the convolution as a
   standalone lemma, then connect it to the Gronwall framework.
   Mathlib hints: `MeasureTheory.Measure.lipschitz_convolution_of_lipschitz`,
   `gronwall_bound`, `ENNReal.ofReal_le_ofReal`, `Real.exp_le_exp`.
