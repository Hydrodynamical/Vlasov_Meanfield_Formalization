## 2026-05-28T12:00:00 · SC.8_lag · vlasov_trajectory_lipschitz_bound_lag (second attempt)

**Result:** success
**Iterations:** 8/8 (edit iterations; several builds per edit)
**Sorry count:** 2 → 1 (CharacteristicFlow.lean: line 2281 closed, line 2255 remains)
**Pre-flight (§3.5):** validated 8 Mathlib lemmas; dropped 0 plan hints;
rejected 1 in-loop citation (`Filter.eventually_of_forall` → `Filter.Eventually.of_forall`)

### Final proof (on success)

The proof constructs `nhd := Set.Ioo (t/2) (t + 1/2)` (valid for `t > 0`)
and `bound z := M_φ * (K * C_T + ε₀) * (‖z‖ + 1)` where:
- `C_T` comes from `flow_distance_growth_bound` applied at `T := t + 1`
- `M_φ` bounds `‖fderiv ℝ φ ·‖` uniformly via `Continuous.bounded_above_of_compact_support`
- `K = 1 + L`, `ε₀ = ‖gradW 0‖ + L * M_ρ` (same Gronwall constants)

Key steps:
1. `nhd ∈ nhds t` by `Ioo_mem_nhds` (valid since `t/2 < t < t + 1/2`)
2. `nhd ⊆ Icc 0 (t+1)` since `s ∈ Ioo (t/2) (t+1/2)` implies `s > 0` and `s < t+1`
3. Lipschitz: `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` on `convex_Ioo`
   - `HasDerivWithinAt` from chain rule: `HasFDerivAt.comp_hasDerivAt` gives
     `HasDerivAt (φ ∘ flow_s z) (fderiv φ (flow_s z) (speed_s z)) s`
   - Norm bound: `ContinuousLinearMap.le_opNorm` + flow bound + conv bound
4. Integrability: `(hf₀_fm.const_mul _).add (integrable_const _)`

### Lookup trail
- `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` — MeanValue.lean:701 (in `namespace Convex`)
- `Ioo_mem_nhds` — OrderClosed.lean:728
- `Continuous.bounded_above_of_compact_support` — Normed/Group/Bounded.lean:158
- `HasCompactSupport.fderiv` — FDeriv/Const.lean:388 (needs `(𝕜 := ℝ)` explicitly)
- `ContDiff.continuous_fderiv` — ContDiff/Defs.lean:1241
- `HasFDerivAt.comp_hasDerivAt` — Deriv/Comp.lean:389
- `ContinuousLinearMap.le_opNorm` — (validated in FDeriv/Symmetric.lean usage)
- `coe_nnnorm'` — Normed/Group/Basic.lean:382
- `Prod.norm_def` — Normed/Group/Constructions.lean:234 (one-arg form)
- `Filter.Eventually.of_forall` — correct name (replacing `Filter.eventually_of_forall`)

### Pre-flight rejections (in-loop)
- `Filter.eventually_of_forall` — zero matches; used `Filter.Eventually.of_forall`
- `NNReal.coe_nnnorm` — zero matches; used `coe_nnnorm'` instead
- `Prod.norm_def _ _` (two-arg form) — type error; `Prod.norm_def` takes one arg

### What was subtle
- The `simp only [Prod.norm_def, ...]` call was simplifying `‖z‖` (for `z : PhaseSpace d`)
  into `max ‖z.1‖ ‖z.2‖`, causing `linarith` to fail on the final bound. Fixed by
  using `rw [Prod.norm_def]` + `simp only [Prod.fst, Prod.snd, norm_neg]` instead.
- `HasCompactSupport.fderiv` needs `(𝕜 := ℝ)` to synthesize `NontriviallyNormedField`.
- The nlinarith hints for `M_φ * (K * C_T + ε₀) * (‖z‖ + 1) ≥ M_φ * (K * C_T * (‖z‖+1) + ε₀)`
  needed `mul_nonneg hM_φ_nn hε₀_nn` explicitly.

---

## 2026-05-28T00:00:00 · SC.8_lag · vlasov_trajectory_lipschitz_bound_lag

**Result:** failure
**Iterations:** 0/8
**Sorry count:** 2 → 2 (unchanged)
**Pre-flight (§3.5):** validated 5 Mathlib lemmas; dropped 0 plan hints; rejected 0 in-loop citations

### What didn't work

No edit was attempted. Extensive mathematical analysis revealed that the proof
is NOT completable with the given hypotheses alone.

**The gap**: The conclusion requires `∃ nhd ∈ nhds t, ...` — a full neighborhood
of `t` (in the standard real-line topology). For any `t ≥ 0`, any set `nhd ∈ nhds t`
must contain some open interval `(t - ε, t + ε)`, which for `t < ε` includes
negative time-values.

The proof strategy (following the task's suggested approach):
1. Apply `flow_distance_growth_bound` with `T = t + 1` to get `C_T`.
2. Bound `‖fderiv ℝ φ ·‖` by `C_φ` using `HasCompactSupport.fderiv` +
   `Continuous.bounded_above_of_compact_support`.
3. For `s ∈ nhd`, bound `‖speed_s z‖ = ‖(charV s z, -conv_s(charX s z))‖` using
   the Gronwall bound from `flow_distance_growth_bound`, giving:
   `‖speed_s z‖ ≤ K * C_T * (‖z‖ + 1) + ε₀`
4. Apply `lipschitzOnWith_of_nnnorm_hasDerivWithin_le` to conclude.

Step 3 requires `h_y_int s hs : Integrable (‖·‖) (ρ s)` and
`hM_ρ s hs : ∫ ‖y‖ ∂ρ_s ≤ M_ρ`, which are provided only for
`s ∈ Set.Icc 0 (t + 1)` (positive times).

**The `t = 0` obstacle**: For `t = 0`, any `nhd ∈ nhds 0` contains `(-δ, δ)` for
some `δ > 0`. For `s ∈ (-δ, 0)`, the bound on `‖conv_s(x)‖` requires
`∫ ‖y‖ ∂ρ_s ≤ M_ρ` for `s < 0`, which is NOT provided by `hM_ρ` (only covers
`[0, t+1]`). Without this moment bound, `‖conv_s(charX s z)‖` cannot be bounded
by a function integrable in `z`.

**Why `t > 0` works**: For `t > 0`, choose `nhd = Set.Ioo 0 (t+1)`. Then:
- `nhd ∈ nhds t` since `0 < t < t+1` (uses `Ioo_mem_nhds`). ✓
- All `s ∈ nhd` satisfy `s > 0`, so `h_y_int s hs` applies. ✓
- The bound `bound z = C_φ * (K' * C_T * (‖z‖+1) + ε₀)` is integrable. ✓
- `lipschitzOnWith_of_nnnorm_hasDerivWithin_le` closes the Lipschitz claim. ✓

**Why `t = 0` fails**: With any `nhd ∈ nhds 0`, negative `s` appear, requiring
moment bounds `∫ ‖y‖ ∂ρ_s` for `s < 0`. The hypothesis `hM_ρ` only covers `[0, 1]`.

**Alternatives explored and rejected**:
1. Using `h_int s 0` to bound `conv_s(0)` without moment bounds — fails because
   `h_int` gives only finiteness (not a bound in terms of `‖z‖`).
2. Backward Gronwall (applying `norm_le_gronwallBound_of_norm_deriv_right_le` to
   the time-reversed flow) — requires the same negative-time moment bounds.
3. Using the compact support of `φ` to restrict to flows in a bounded region —
   the backward Gronwall to show `‖z‖ ≤ C` when `F_z(s) ∈ tsupport φ` also
   requires `ε₀` which depends on `M_ρ` at negative times.
4. Using `∀ᵐ z ∂f₀` to skip problematic `z` — doesn't help since the failure
   is in the measure `ρ_s` (not in `z`).

**The docstring note**: The SC.8 docstring already says "May require widening with
an `h_speed_bound` hypothesis at the wrapper level (deferred per the plan)."
This confirms the proof is expected to require additional hypotheses.

### Fix required

Add a hypothesis covering moment bounds for negative times:
```
(hM_ρ_back : ∀ s ∈ Set.Icc (-1) 0, ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
(h_y_int_back : ∀ s ∈ Set.Icc (-1) 0, Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
```
Or alternatively change `ht_nn : 0 ≤ t` to `ht_pos : 0 < t` (the proof works
cleanly for `t > 0` with `nhd = Set.Ioo 0 (t+1)`).

### Wished-for Mathlib API
- None (the gap is in the problem statement, not in Mathlib API).

### Validated Mathlib lemmas (for future reference)
- `lipschitzOnWith_of_nnnorm_hasDerivWithin_le` — MeanValue.lean:701
- `Ioo_mem_nhds` — OrderClosed.lean:728
- `Continuous.bounded_above_of_compact_support` — Normed/Group/Bounded.lean:158
- `HasCompactSupport.fderiv` — FDeriv/Const.lean:388
- `ContDiff.continuous_fderiv` — ContDiff/Defs.lean:1241
