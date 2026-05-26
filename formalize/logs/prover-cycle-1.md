## 2026-05-23T00:00:00Z · most-tractable · weakEvolutionEmpiricalMeasure

**Result:** failure
**Iterations:** 2/8
**Sorry count:** 3 → 3 (no change; reverted)

### Score breakdown (most-tractable selection)
- `weakEvolutionEmpiricalMeasure` (line 277): Score 4/10. Statement has existential conclusion `∃ r`, so we can provide a concrete witness. But requires (a) proving `HasDerivAt` of an integral against an empirical measure, and (b) proving a remainder bound. Both are non-trivial.
- `vlasovWellPosedness` (line 414): Score 1/10. PDE existence/uniqueness, requires Picard-Lindelof in measure space. Very hard.
- `dobrushin` (line 523): Score 2/10. Gronwall + Wasserstein estimate. Blocked on missing Wasserstein API and Gronwall for measure-valued functions.

Selected `weakEvolutionEmpiricalMeasure` as most tractable (score 4/10).

### What didn't work

- **Iteration 1**: Tried scaffold with `hintegral` (∫ φ d(empiricalMeasureCurve) = (1/N) * ∑ i, φ(X s i, V s i)) proved via `simp` with `integral_smul_measure`, `integral_finset_sum_measure`, `integral_dirac`. Build failed: line 281 `unsolved goals` (simp didn't close the `hintegral` goal — `integral_finset_sum_measure` requires an integrability hypothesis not provided). Also line 301 application type mismatch in the `HasFDerivAt` step.

- **Iteration 2**: Tried `refine` with explicit witness `r := (1/N²) * ∑ i, inner (gradW 0) (gradVφ (X t i, V t i))` and `rfl` for the first conjunct, leaving two `sorry` subgoals. This builds successfully (3 sorries remain: the original theorem now has 2 internal sorries, plus the two other theorems). This is not a net decrease in sorry count (3 → 3), so we cannot finalize this way.

### Core blockers

1. **`HasDerivAt` of `∫ φ d(empiricalMeasureCurve N X V s)` at s = t**: Requires (a) rewriting the empirical-measure integral as a finite sum via `integral_smul_measure` + `integral_finset_sum_measure` + `integral_dirac` (requires measurability and integrability side conditions), then (b) applying `HasDerivAt` through the finite sum via `HasDerivAt.sum` and the chain rule for each `φ(X s i, V s i)`, which requires knowing `HasFDerivAt φ` and combining with `HasDerivAt` of `(X s i, V s i)` via product map. The chain rule for a product-space path into a scalar function requires `HasFDerivAt.comp_hasDerivAt` or `HasDerivAt.comp`. This is ~15–20 tactic lines even on a good day.

2. **Remainder bound**: `|(1/N²) * ∑ i, inner (gradW 0) (gradVφ ...)| ≤ (1/N) * ⊔ x, ‖gradW x‖ * ⊔ z, ‖gradVφ z‖` — provable but requires Cauchy-Schwarz + finite sum bound + iSup bound, ~8–10 steps.

Both subgoals must be proved within the same run to achieve a net sorry reduction, making this too complex for 8 × 3-tactic-line edits.

### Wished-for Mathlib API
- A lemma `HasDerivAt_integral_empiricalMeasure` or similar that directly gives `HasDerivAt` of `∫ φ d(empiricalMeasureCurve N X V s)` in terms of the point evaluations `φ(X s i, V s i)`, bypassing the need to assemble integrability hypotheses manually.

---

## 2026-05-24T00:00:00Z · prop:weak · empiricalMeasure_integral_eq

**Result:** success
**Iterations:** 3/8
**Sorry count:** 8 → 7

### Selection (most-tractable)

Plan-aware lookup fired: `formalize/plans/weakEvolutionEmpiricalMeasure.json`.
Helper `Vlasov.empiricalMeasure_integral_eq` has `difficulty: 1`, no deps.
Score = 6 - 1 = 5 (highest among all candidates). Selected as target.

### Final proof

```lean
lemma empiricalMeasure_integral_eq (N : ℕ) [NeZero N]
    (X V : Fin N → PhysSpace d)
    (φ : PhaseSpace d → ℝ) :
    ∫ z, φ z ∂(empiricalMeasure N X V) =
      (1 / (N : ℝ)) * ∑ i : Fin N, φ (X i, V i) := by
  simp only [empiricalMeasure]
  rw [integral_smul_measure]
  rw [integral_finset_sum_measure (fun i _ => integrable_dirac (by simp))]
  simp [integral_dirac, ENNReal.toReal_div, ENNReal.toReal_natCast, smul_eq_mul]
```

### Lookup trail

- `integral_smul_measure` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1035`
- `integral_finset_sum_measure` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1018`
- `integrable_dirac` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:288`

### What didn't work

- Iteration 1: tried `simp only [integral_smul_measure, integral_finset_sum ...]` with wrong integrability witness (passed AEStronglyMeasurable instead of Integrable). Also `integral_finset_sum` is for summing functions, not measures.
- Iteration 2: tried `integral_finset_sum_measure` in simp set but it was unused (simp did not fire); `integral_smul_measure` in simp left a disjunctive goal `... ∨ N = 0`.
- Iteration 3: switched to `rw` for both steps; `simp` finished with `integral_dirac` and arithmetic lemmas.

## 2026-05-25T00:00:00Z · hasDerivAt_phi_along_trajectory · Vlasov.hasDerivAt_phi_along_trajectory

**Result:** success
**Iterations:** 4/8
**Sorry count:** 8 → 7

### Candidate table (Mode B)

| Sorry (decl name) | Plan | Difficulty | Score | Source |
|---|---|---|---|---|
| `hasDerivAt_phi_along_trajectory` (line 251) | weakEvolutionEmpiricalMeasure.json | 1 | 5 | plan-aware |
| `diagonalCorrection_eq` (line 331) | weakEvolutionEmpiricalMeasure.json | 1 | 5 | plan-aware (has sorry dep) |
| `diagonalCorrection_bound` (line 361) | weakEvolutionEmpiricalMeasure.json | 2 | 4 | plan-aware |
| `weakEvolutionEmpiricalMeasure` residual glue (line 394) | weakEvolutionEmpiricalMeasure.json | — | 4 | plan-aware-residual |
| `hasDerivAt_empiricalIntegral_sum` (line 273) | weakEvolutionEmpiricalMeasure.json | 3 | 3 | plan-aware |
| `convolveFunctionMeasure_empiricalSpatial_eq` (line 312) | weakEvolutionEmpiricalMeasure.json | 3 | 3 | plan-aware |
| `vlasovWellPosedness` (line 577) | (none) | — | 1 | rubric |
| `dobrushin` (line 686) | (none) | — | 1 | rubric |

Selected `hasDerivAt_phi_along_trajectory` (score 5, leaf, no deps). `diagonalCorrection_eq` also scores 5 but depends on `convolveFunctionMeasure_empiricalSpatial_eq` which is still sorry.

### Final proof

```lean
  -- Step 1: curve derivative
  have hcurve : HasDerivAt (fun s => (X s i, V s i)) (V t i, a t i) t :=
    (hX t i).prodMk (hV t i)
  -- Step 2: compose φ through the curve
  have hcomp : HasDerivAt (fun s => φ (X s i, V s i))
      ((φ' (X t i, V t i)) (V t i, a t i)) t :=
    (hφ_fderiv (X t i, V t i)).comp_hasDerivAt t hcurve
  -- Step 3: rewrite the derivative value
  convert hcomp using 1
  -- Step 4: show φ'(z)(V,a) = ⟨V, gradXφ z⟩ + ⟨a, gradVφ z⟩
  set z := (X t i, V t i)
  -- partial x: HasFDerivAt (fun x => φ(x, z.2)) (φ' z ∘L inl ℝ _ _) z.1
  have hpX : HasFDerivAt (fun x => φ (x, z.2))
      ((φ' z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) z.1 :=
    (hφ_fderiv z).comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  have hpV : HasFDerivAt (fun v => φ (z.1, v))
      ((φ' z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) z.2 :=
    (hφ_fderiv z).comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)
  simp only [hgradXφ z, hgradVφ z]
  have hgX : @inner ℝ (PhysSpace d) _ (V t i) (gradient (fun x => φ (x, z.2)) z.1) =
      fderiv ℝ (fun x => φ (x, z.2)) z.1 (V t i) := by
    rw [inner_gradient_right hpX.differentiableAt]
    simp [RCLike.conj_eq_iff_re, conj_trivial]
  have hgV : @inner ℝ (PhysSpace d) _ (a t i) (gradient (fun v => φ (z.1, v)) z.2) =
      fderiv ℝ (fun v => φ (z.1, v)) z.2 (a t i) := by
    rw [inner_gradient_right hpV.differentiableAt]
    simp [RCLike.conj_eq_iff_re, conj_trivial]
  rw [hgX, hgV, hpX.fderiv, hpV.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp [Prod.mk_add_mk]
```

### Lookup trail
- `HasDerivAt.prodMk` — standard Mathlib, FDeriv/Prod.lean
- `HasFDerivAt.comp_hasDerivAt` — FDeriv/Comp.lean
- `hasFDerivAt_prodMk_left`, `hasFDerivAt_prodMk_right` — FDeriv/Prod.lean
- `inner_gradient_right` — Gradient/Basic.lean:278
- `HasFDerivAt.fderiv` — standard
- `ContinuousLinearMap.inl_apply`, `ContinuousLinearMap.inr_apply` — standard

### What didn't work
- iteration 1: `rw [hgradXφ z, hgradVφ z]` failed (pattern not found with `rw`, needed `simp only`)
- iteration 2: `rw [← hpX.hasGradientAt.fderiv_apply]` failed (gradient form mismatch — `hasGradientAt` needs derivative in `toDual` form)
- iteration 3: `rw [inner_gradient_right ...]` + `simp [conj_trivial]` succeeded for the inner product steps; final `simp [map_add]` failed
- iteration 4: replaced with `rw [← map_add]; simp [Prod.mk_add_mk]` — succeeded
## 2026-05-25T00:00:00Z · wassersteinGronwallCoupling_ennreal_mul_comm · Vlasov.wassersteinGronwallCoupling_ennreal_mul_comm

**Result:** success
**Iterations:** 2/8 (1 fast-path attempt + 1 iteration)
**Sorry count:** 12 → 11

### Candidate table

| Sorry (decl name) | Plan | Difficulty | Score | Source | Sketch? |
|-------------------|------|-----------|-------|--------|---------|
| `wassersteinGronwallCoupling_ennreal_mul_comm` | MathlibTODO_wassersteinGronwallCoupling.json | 1 | 5 | plan-aware | Y |
| `wasserstein1_ofReal_exp_monotone` | dobrushin.json | 1 | 5 | plan-aware | Y |
| `wassersteinGronwallCoupling_gronwall_le` | MathlibTODO_wassersteinGronwallCoupling.json | 2 | 4 | plan-aware | N |
| `wassersteinGronwallCoupling_ofReal_le` | MathlibTODO_wassersteinGronwallCoupling.json | 2 | 4 | plan-aware | N |
| `dobrushin_C_choice` | dobrushin.json | 2 | 4 | plan-aware | N |
| `dobrushin_package_exists` | dobrushin.json | 2 | 4 | plan-aware | Y |
| MathlibTODO_wassersteinGronwallCoupling residual | MathlibTODO_wassersteinGronwallCoupling.json | - | 4 | plan-aware-residual | Y |
| dobrushin residual | dobrushin.json | - | 4 | plan-aware-residual | Y |
| `wassersteinGronwallCoupling_real_bound` | MathlibTODO_wassersteinGronwallCoupling.json | 3 | 3 | plan-aware | N |
| `convolveDiff_norm_le` | dobrushin.json | 4 | 2 | plan-aware | N |
| `dobrushin_ennreal_bound` | dobrushin.json | 4 | 2 | plan-aware | N |
| `vlasovWellPosedness` | (none) | - | 1 | rubric | N |

Top pick: `wassersteinGronwallCoupling_ennreal_mul_comm` (Score 5, Sketch Y, line 975).

### Final proof

```lean
lemma wassersteinGronwallCoupling_ennreal_mul_comm
    (δ : ℝ) (hδ : 0 ≤ δ) (C t : ℝ) :
    ENNReal.ofReal (δ * Real.exp (C * t)) =
      ENNReal.ofReal (Real.exp (C * t)) * ENNReal.ofReal δ := by
  rw [ENNReal.ofReal_mul hδ, mul_comm]
```

### Lookup trail
- `ENNReal.ofReal_mul` — `.lake/packages/mathlib/Mathlib/Data/ENNReal/Real.lean:297`

### What didn't work
- fast path: sketch had `mul_comm` as last line as a term, not a tactic — Lean reports "unknown tactic". Reverted.
- iteration 1: `rw [ENNReal.ofReal_mul hδ, mul_comm]` — SUCCESS
