## 2026-05-28T00:00:00Z · flow_distance_growth_bound · flow_distance_growth_bound (second attempt — SUCCESS)

**Result:** success
**Iterations:** 4/8
**Sorry count:** 2 → 1 (CharacteristicFlow.lean: line 143 gone; line 2252 untouched)
**Pre-flight (§3.5):** dropped 0 hints; validated 12 lemma names; rejected 0 in-loop citations

### Final proof (on success)

The proof uses `gronwallBound 1 (1 + L) (‖gradW 0‖ + L * M_ρ) T` as the uniform C_T witness.

Structure:
1. **Witness**: `C_T = gronwallBound 1 K ε₀ T` with `K = 1+L`, `ε₀ = ‖gradW 0‖ + L*M_ρ`. Non-negativity: from `gronwallBound_mono` applied to `[0, T]` + `gronwallBound_x0 = 1`.
2. **Convolution bound** (main lemma, ~30 lines): `‖conv(ρ s) x‖ ≤ ε₀ + L * ‖x‖`. Uses:
   - `Integrable.mono'` to get `Integrable (fun y => ‖x - y‖)` from `h_y_int` via triangle.
   - Pointwise Lipschitz bound `‖gradW(x-y)‖ ≤ ‖gradW 0‖ + L*‖x-y‖` via `norm_add_le` + triangle.
   - `integral_mono` + `integral_add` + `integral_const_mul` to compute the integral.
3. **Gronwall inputs**: `ContinuousOn` from `HasDerivAt.continuousAt.prodMk`; `HasDerivWithinAt` from `HasDerivAt.prodMk.hasDerivWithinAt`; derivative norm bound from convolution bound.
4. **Final factoring**: `gronwallBound ‖z‖ K ε₀ T ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1)` via `gronwallBound_of_K_ne_0` + `nlinarith` with `exp ≥ 0` and `exp - 1 ≥ 0`.

```lean
theorem flow_distance_growth_bound ... := by
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  use gronwallBound 1 K ε₀ T
  refine ⟨?_, ?_⟩
  · have hmono := gronwallBound_mono (by norm_num : (0:ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  · intro t ht z
    have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
        ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := ...
    have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T) :=
      continuousOn_of_forall_continuousAt fun s _ =>
        (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
    have h_deriv : ∀ s ∈ Set.Ico 0 T, HasDerivWithinAt ... :=
      fun s _ => ((hflow_x s z).prodMk (hflow_v s z)).hasDerivWithinAt
    have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
      h_f_cont h_deriv h_init h_bound t ht
    simp only [sub_zero] at h_grw
    calc ‖(charX t z, charV t z)‖
        ≤ gronwallBound ‖z‖ K ε₀ t := h_grw
      _ ≤ gronwallBound ‖z‖ K ε₀ T := gronwallBound_mono (norm_nonneg _) hε₀_nn hK_pos.le ht.2
      _ ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1) := by
          rw [gronwallBound_of_K_ne_0 hK_pos.ne', gronwallBound_of_K_ne_0 hK_pos.ne']
          simp only [one_mul]
          nlinarith [norm_nonneg z, Real.exp_nonneg (K * T), ...]
```

### Lookup trail
- `norm_le_gronwallBound_of_norm_deriv_right_le` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:135`
- `gronwallBound_of_K_ne_0` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:49`
- `gronwallBound_mono` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:93`
- `gronwallBound_x0` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:71`
- `HasDerivAt.prodMk` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean:51`
- `HasDerivAt.hasDerivWithinAt` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:382`
- `HasDerivAt.continuousAt` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:845`
- `ContinuousAt.prodMk` — `.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:346`
- `continuousOn_of_forall_continuousAt` — `.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:341`
- `norm_integral_le_integral_norm` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:943`
- `integral_mono` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:644`
- `integral_add` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:238`
- `integral_const_mul` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:297`
- `Integrable.mono'` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:100`
- `Integrable.const_mul` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1031`
- `aestronglyMeasurable_id` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:442`
- `Real.one_le_exp` — `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:277`
- `Prod.norm_def` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean:234`

### Key insights for this second attempt

- **Root cause of first failure**: missing `h_y_int : Integrable (fun y => ‖y‖) (ρ t)` in signature. Adding it unblocked everything.
- **aestronglyMeasurable_id**: used as `aestronglyMeasurable_id` (not `aestronglyMeasurable_id.norm`) for `fun y => y`, then compose with `.norm` and `.sub aestronglyMeasurable_const`.
- **linarith vs norm triangle**: `‖a‖ ≤ ‖b‖ + ‖a - b‖` needed `norm_add_le (a - b) b` + `sub_add_cancel` simp.
- **Gronwall factoring**: `gronwallBound_of_K_ne_0` on BOTH sides, then `nlinarith` with `norm_nonneg z`, `exp_nonneg`, and `mul_nonneg` witnesses for the cross-terms.
- **K > 0** always (K = 1 + L ≥ 1), so no case split needed.

---

## 2026-05-29T01:04:24Z · flow_distance_growth_bound · flow_distance_growth_bound

**Result:** failure
**Iterations:** 1/8 (plus extensive pre-iteration analysis)
**Sorry count:** 7 → 7 (no change after revert)
**Pre-flight (§3.5):** dropped 0 hints; validated 16 lemma names; rejected 0 in-loop citations

### Target

`theorem flow_distance_growth_bound` in `Vlasov/OT/CharacteristicFlow.lean` (line 127).

Goal:
```
∃ C_T, 0 ≤ C_T ∧
  ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
    ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1)
```

### Proof strategy attempted

The mathematical content (per the docstring): apply Gronwall's inequality to the pair
`f_z(t) = (charX t z, charV t z)` viewed as a function `ℝ → PhysSpace d × PhysSpace d`.
The Gronwall derivative bound requires:
```
‖f_z'(t)‖ = max(‖charV t z‖, ‖conv(ρ t)(charX t z)‖)
           ≤ (L+1) * ‖f_z(t)‖ + B
```
where `B = ‖gradW 0‖ + L * M_ρ` is a constant, via the integral bound:
```
‖conv(ρ t)(x)‖ ≤ ‖gradW 0‖ + L * ‖x‖ + L * M_ρ
```
(using Lipschitz of `gradW`, triangle inequality, and `∫ ‖y‖ dρ t ≤ M_ρ`).

### The integrability gap (why it fails)

The integral bound step requires `integral_mono_of_nonneg` with upper bound
`fun y => ‖gradW 0‖ + L * (‖x‖ + ‖y‖)`, which needs:
```
Integrable (fun y => L * ‖y‖) (ρ t)
```
i.e., `Integrable (fun y => ‖y‖) (ρ t)`.

**This cannot be derived from the theorem's hypotheses.** The relevant hypotheses are:
- `hM_ρ t ht : ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ` — this provides a BOUND on the integral, but in
  Lean/Mathlib, the Bochner integral of a non-integrable function is 0. So `hM_ρ` is
  satisfied vacuously (as `0 ≤ M_ρ`) when `‖y‖` is NOT integrable w.r.t. `ρ t`. The
  hypothesis does NOT establish integrability.
- `h_int t x : Integrable (fun y => gradW (x - y)) (ρ t)` for all x — this gives
  integrability of `gradW(x - ·)` but NOT of `‖·‖`, because Lipschitz gives an UPPER
  bound `‖gradW(x-y)‖ ≤ ‖gradW 0‖ + L * ‖x-y‖` (useless for deducing integrability of
  the lower-bounding function `‖y‖`), and no LOWER bound exists without coercivity of
  `gradW`.

### All alternative approaches explored

1. **Lipschitz at 0**: `‖conv t x‖ ≤ ‖conv t 0‖ + L * ‖x‖` via `convolveFunctionMeasure_lipschitz_in_x`. Then bound `‖conv t 0‖ = ‖∫ gradW(-y) dρ t‖ ≤ ∫ ‖gradW(-y)‖ dρ t ≤ ‖gradW 0‖ + L * M_ρ`. The last step requires `integral_mono_of_nonneg` with upper bound `fun y => ‖gradW 0‖ + L * ‖y‖` — same integrability gap.

2. **Reverse triangle**: `‖gradW(-y)‖ ≤ ‖gradW(x-y)‖ + L * ‖x‖` for any fixed x, so `∫ ‖gradW(-y)‖ dρ t ≤ ∫ ‖gradW(x-y)‖ dρ t + L * ‖x‖`. This avoids `‖y‖` integrability! The upper bound `fun y => ‖gradW(x-y)‖ + L*‖x‖` IS integrable from `h_int t x`. **BUT** the resulting bound `‖conv t x‖ ≤ 2L * ‖x‖ + ∫ ‖gradW(x-y)‖ dρ t` still has `∫ ‖gradW(x-y)‖ dρ t` depending on the state `charX t z`, so the Gronwall constant ε is not fixed.

3. **Split integrable / not integrable**: By cases on whether `Integrable (fun y => ‖y‖) (ρ t)`. The "not integrable" case gives no useful bound on `∫ ‖gradW(-y)‖ dρ t`.

4. **Variable ε Gronwall**: Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le` requires a fixed constant `ε`, not a function of `t`.

5. **Energy via lintegral**: `hM_ρ` is stated in terms of Bochner integral; switching to `lintegral` might recover integrability via `MeasureTheory.integrable_of_lintegral_lt_top`, but `hM_ρ` is about the Bochner integral (= 0 when not integrable), not `lintegral`.

### What didn't work

- iteration 1: Inserted ~130-line proof attempt. Multiple errors:
  - `integral_mono_ae` with wrong argument order/type
  - `ENNReal.one_toReal` (should be `ENNReal.toReal_one`)
  - Invalid field `sub_const` applied to `And` type (not `Integrable`)
  - `linarith` failures on arithmetic bounds
  - Root cause: needed `Integrable (fun y => ‖y‖) (ρ t)` which is not available
- Reverted to checkpoint after exhausting analysis.

### Lookup trail

- `norm_le_gronwallBound_of_norm_deriv_right_le` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:135`
- `gronwallBound` (definition) — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:43`
- `gronwallBound_of_K_ne_0` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:49`
- `gronwallBound_mono` — `.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean:93`
- `HasDerivAt.hasDerivWithinAt` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:382`
- `HasDerivAt.continuousOn` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:851`
- `HasDerivAt.prodMk` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean:51`
- `Prod.norm_def` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean:234`
- `norm_integral_le_integral_norm` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:943`
- `integral_mono_ae` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:636`
- `integral_mono_of_nonneg` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:648`
- `integral_add` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:238`
- `integral_const` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:963`
- `integral_const_mul` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:297`
- `ENNReal.toReal_one` — `.lake/packages/mathlib/Mathlib/Data/ENNReal/Basic.lean:273` (NOT `ENNReal.one_toReal`)
- `integrable_const` — requires `IsFiniteMeasure`, satisfied by `IsProbabilityMeasure`

### Wished-for Mathlib API / fix needed

**Root fix**: Add `h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y => ‖y‖) (ρ t)` as a
hypothesis to `flow_distance_growth_bound`. With this addition, the proof closes in ~30
lines following the Gronwall sketch:
1. Set K := L + 1, B := ‖gradW 0‖ + L * M_ρ, C_T := exp(K*T) * (1 + B/K).
2. For each z, apply `norm_le_gronwallBound_of_norm_deriv_right_le` to `fun t => (charX t z, charV t z)`.
3. The derivative bound `‖f'(t)‖ ≤ K * ‖f(t)‖ + B` uses:
   - `‖charV t z‖ ≤ ‖f(t)‖` (by Prod.norm_def)
   - `‖conv t (charX t z)‖ ≤ ‖gradW 0‖ + L * ‖charX t z‖ + L * M_ρ` (via `h_y_int + integral_mono`)
   - Combined: `max(‖charV‖, ‖conv‖) ≤ (L+1)*‖f‖ + B`
4. Bound `gronwallBound (‖z‖+1) K B t ≤ C_T * (‖z‖+1)` by `gronwallBound_of_K_ne_0`.

**Alternatively**: Replace `hM_ρ` with a stronger hypothesis using `lintegral`:
`hM_ρ : ∀ t ∈ Set.Icc 0 T, ∫⁻ y, ‖y‖₊ ∂(ρ t) ≤ ENNReal.ofReal M_ρ`
This implies Bochner integrability of `‖·‖` via `integrable_of_lintegral_lt_top`.

**Call site impact**: At the Dobrushin call site, `h_y_int` follows immediately from
`HasFiniteFirstMoment`, which is already assumed there. The additional hypothesis is
mathematically natural.
