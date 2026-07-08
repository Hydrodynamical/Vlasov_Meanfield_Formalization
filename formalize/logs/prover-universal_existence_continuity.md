## 2026-05-30T[session] · Stage6-Conjunct4 · vlasovWellPosedness_universal_existence

**Result:** success (with 1 authorized sub-sub-sorry for t₀=0 boundary case)
**Iterations:** 6/8
**Sorry count:** 10 → 10 (declaration-level count unchanged; internal sorry reduced from 2 to 1 within the declaration, per user authorization)
**Pre-flight (§3.5):** dropped 0 hints (no plan file applies); validated 0 sketch lemmas; rejected 0 in-loop citations

### Final proof (on success)

The two `sorry` stubs in `vlasovWellPosedness_universal_existence` at Conjunct 3 and Conjunct 4 were replaced with substantive proofs. Conjunct 3 (IsLagrangianVlasovSolutionOn for the glued f) was fully proved. Conjunct 4 (narrow continuity) was proved for the interior case (t₀ > 0) with one authorized sub-sub-sorry for the boundary case (t₀ = 0).

**Conjunct 3 key steps:**
1. `h_agree_fN : ∀ t ∈ Icc 0 T_target, f t = sol N t` via `h_agree` (uniqueness) + `Nat.ceil_mono` + `Nat.ceil_natCast`
2. Extract `charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N` from `h_sol_lag N`
3. IsVlasovSolutionOn: use `h_from_N.congr_of_eventuallyEq h_eq` then `simp only [h_agree_fN t ...]` to transfer sol N → f in derivative body
4. IsCharacteristicFlowOn: manually construct using `simp only [h_agree_fN t ...]` to rewrite `f t = sol N t` in velocity ODE
5. Pushforward: `rw [h_agree_fN t ht, h_f0_solN]` then `h_push_N`
6. AEMeasurable: `rw [h_f0_solN]; exact h_aemeas_N s ...`

**Conjunct 4 key steps (interior t₀ > 0):**
1. Set `N = ⌈t₀⌉₊ + 1`, establish `hIcc_mem : Icc 0 N ∈ nhdsWithin t₀ (Ici 0)`
2. Prove `h_integral_eq : ∀ t ∈ Icc 0 N, ∫ g ∂f t = ∫ g (charX_N t ·, charV_N t ·) ∂f₀` via pushforward + `integral_map`
3. Apply DCT `continuousWithinAt_of_dominated` for `fun t => ∫ z, g (charX_N t z, charV_N t z) ∂f₀`
   - AEStronglyMeasurable via `hg_cont.measurable.comp_aemeasurable (h_sol_init N ▸ h_aemeas_N t ...)`
   - Bound via `hgC : ∀ z, ‖g z‖ ≤ C` (from `Bornology.IsBounded.subset_closedBall + Metric.mem_closedBall + Real.dist_eq + Real.norm_eq_abs`)
   - Integrable bound: `integrable_const C` (f₀ is IsProbabilityMeasure hence IsFiniteMeasure)
   - Pointwise continuity: HasDerivAt → continuousAt for charX_N, charV_N at t₀ ∈ Ioo 0 (N+1)
4. Transfer via `ContinuousWithinAt.congr_of_eventuallyEq` using `h_integral_eq`
5. Lift from Icc 0 N to Ici 0 via `ContinuousWithinAt.mono_of_mem_nhdsWithin hIcc_mem`

**Sub-sub-sorry (t₀ = 0):** Right-continuity at t=0 requires the characteristic flow (charX t z, charV t z) → z as t → 0⁺. This needs boundary ODE regularity at t=0 beyond what IsCharacteristicFlowOn exposes (only HasDerivAt on Ioo 0 T is given). This is the Friction-5 / B-series watch-list pattern.

### Lookup trail

- `Nat.ceil_natCast` — `.lake/packages/mathlib/Mathlib/Algebra/Order/Floor/Semiring.lean:218`
- `integral_map` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1077`
- `Measurable.aestronglyMeasurable` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:247`
- `continuousWithinAt_of_dominated` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:431`
- `ContinuousWithinAt.congr_of_eventuallyEq` — `.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:380`
- `ContinuousWithinAt.mono_of_mem_nhdsWithin` — `.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:232`
- `integrable_const` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:162`
- `Real.dist_eq` — `.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:1107`
- `Real.norm_eq_abs` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:56`
- `eq_or_lt_of_le` — `.lake/packages/mathlib/Mathlib/Order/Basic.lean:249`

### Pre-flight rejections (in-loop)

- `MeasureTheory.Measure.le_of_forall_pos_le_add` — zero matches; replaced with `integrable_const C` (which works directly since `IsProbabilityMeasure → IsFiniteMeasure`)
- `eq_or_gt_of_le` — zero matches; replaced with `LE.le.eq_or_lt` (alias for `eq_or_lt_of_le`)

### What didn't work

- Iteration 1: 6 initial errors from the previous session's edit; required multiple rounds of fixes
- Iteration 2: `rw [h_agree_t] at h_from_N` failed (let-binding prevents pattern matching); replaced with `simp only [h_agree_fN t ...]`
- Iteration 3: `apply Filter.Tendsto.congr'` with wrong bullet order + wrong `continuousWithinAt_of_dominated` AEStronglyMeasurable argument; restructured to use `ContinuousWithinAt.congr_of_eventuallyEq` + `mono_of_mem_nhdsWithin`
- Iteration 4: `Measure.le_of_forall_pos_le_add` phantom lemma; fixed to `integrable_const C`
- Iteration 5: `AEMeasurable.aestronglyMeasurable` needed `h_sol_init N ▸` to change measure from `sol N 0` to `f₀`; also `(h_integral_eq t ht).symm` had wrong direction for `congr_of_eventuallyEq`
- Iteration 6: Build succeeded
