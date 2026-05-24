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

