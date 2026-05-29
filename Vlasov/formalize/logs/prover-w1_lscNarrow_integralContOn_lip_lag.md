## 2026-05-28T18:00:00 · H1_lag · w1_lscNarrow_integralContOn_lip_lag

**Result:** success
**Iterations:** 5/8
**Sorry count:** 5 → 4
**Pre-flight (§3.5):** dropped 0 hint(s); validated 8 Mathlib lemma names; rejected 0 in-loop citation(s)

### Final proof (on success)

The proof replaces `sorry` in `lemma w1_lscNarrow_integralContOn_lip_lag` with a
~130-line tactic block. Key structure:

1. Destructure `hf_lag : IsLagrangianVlasovSolution gradW f` to extract
   `charX`, `charV`, `hflow`, `hpush`, `hflow_meas`.
2. Establish Lagrangian rewrite: `∀ t, ∫ φ d(f t) = ∫ φ(charX t z, charV t z) d(f 0)`
   via `hpush` + `MeasureTheory.integral_map`.
3. Inline the proof of `flow_distance_growth_bound` (from CharacteristicFlow.lean,
   which imports Basic.lean so cannot be called directly):
   - Convolution bound: `‖(∇W ∗ ρ_s)(x)‖ ≤ ε₀ + L * ‖x‖`
   - Gronwall on `(charX s z, charV s z)` using `norm_le_gronwallBound_of_norm_deriv_right_le`
   - Yields `C_T := gronwallBound 1 K ε₀ T` with `‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1)`
4. Apply `MeasureTheory.continuousOn_of_dominated` with:
   - bound: `fun z => ‖φ 0‖ + C_T * (‖z‖ + 1)` (explicit via named argument)
   - AEStronglyMeasurable: `hφ_lip.continuous.measurable.aestronglyMeasurable.comp_aemeasurable`
   - Uniform bound: triangle inequality + flow growth bound
   - Integrable dominator: `hf_prob_0.2` (Integrable ‖·‖ (f 0)) + `integrable_const`
   - Pointwise continuity: `HasDerivAt.continuousAt` for `charX`, `charV` + `hφ_lip.continuous`

### Lookup trail
- `MeasureTheory.continuousOn_of_dominated` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:453`
- `MeasureTheory.integral_map` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1077`
- `norm_le_gronwallBound_of_norm_deriv_right_le` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:135`
- `gronwallBound_mono` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:93`
- `gronwallBound_x0` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:71`
- `gronwallBound_of_K_ne_0` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:49`
- `HasDerivAt.continuousAt` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:845`
- `continuousOn_of_forall_continuousAt` — `.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:341`
- `MeasureTheory.integral_const` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:963`

### Key engineering insight
`flow_distance_growth_bound` is in `CharacteristicFlow.lean` which imports `Basic.lean`,
creating an import cycle if called directly. The fix was to inline the bound proof (it
depends only on Mathlib's Gronwall API and definitions already in `Basic.lean`). The
`continuousOn_of_dominated` bound argument must be supplied explicitly via
`(bound := fun z => ...)` because the implicit `{bound}` parameter isn't unified
before the `h_bound` bullet fires.

### What required iteration
- Iter 1: Full proof written in one edit (large); 5 errors
- Iter 2: Fixed `IsProbabilityMeasure` instance for `ρ s`, φ-bound triangle inequality,
  `integrable_const` needing `IsFiniteMeasure`
- Iter 3: Fixed `IsProbabilityMeasure.measure_univ` simp arg; supplied explicit bound
  to `continuousOn_of_dominated`
- Iter 4: Replaced `measure_univ + ENNReal.one_toReal + mul_one` rw chain with
  `integral_const` + `simp [measureReal_def]`; still residual `ρ s vs spatialMarginal (f s)`
- Iter 5: Added `h_y_int_ρ := hρs ▸ h_y_int s hs` to pass correct type to `integral_add`,
  resolving the definitional-equality mismatch — success
