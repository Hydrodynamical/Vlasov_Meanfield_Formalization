## 2026-05-28T00:00:00Z · (none) · w1_lscNarrow_integralContOn_lip_lag

**Result:** failure — structurally blocked (Outcome B)
**Iterations:** 1/6 (comment-only edit; proof cannot close)
**Sorry count:** 5 → 5 (unchanged; file reverted to checkpoint)
**Pre-flight (§3.5):** validated 0 plan hints; validated 2 sketch lemmas
  (`MeasureTheory.continuousOn_of_dominated` — confirmed at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:453`;
   `MeasureTheory.integral_map` — confirmed at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1077`);
  rejected 0 in-loop citations.

### Lookup trail
- `MeasureTheory.continuousOn_of_dominated` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:453`
- `MeasureTheory.integral_map` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1077`
- `HasDerivAt.continuousAt` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:845`
- `Continuous.prodMk` — `.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:140`

### What didn't work (structural analysis)

**Outcome B: single named gap — `flow_distance_growth_bound`**

The proof strategy via the Lagrangian transformation is sound and compiles up to the dominator step:

**Step 1** (Destructure): `hf_lag : IsLagrangianVlasovSolution gradW f` destructs to give
`charX, charV : ℝ → PhaseSpace d → PhysSpace d`,
`hflow : IsCharacteristicFlow gradW (fun t => spatialMarginal (f t)) charX charV`,
`hpush : ∀ t, f t = Measure.map (fun z => (charX t z, charV t z)) (f 0)`,
`hflow_meas : ∀ s, AEMeasurable (fun z => (charX s z, charV s z)) (f 0)`.

**Step 2** (Lagrangian rewrite via `integral_map`): For each t,
```
∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0)
```
This rewrites the goal to `ContinuousOn (fun t => ∫ z, φ (charX t z, charV t z) ∂(f 0)) (Set.Icc 0 T)`,
where the measure `f 0` is now FIXED. `integral_map` requires `hflow_meas t` (AEMeasurable of the flow map) and AEStronglyMeasurable of φ under the pushforward (which follows from φ continuous + measurability of the map).

**Step 3** (DCT via `continuousOn_of_dominated`): Apply with `F t z = φ (charX t z, charV t z)`, `μ = f 0`.

- **(a) AEStronglyMeasurable for each t**: Follows from `hflow_meas t` (AEMeasurable of `z ↦ (charX t z, charV t z)`) + `hφ_lip.continuous.aestronglyMeasurable`. Sound.

- **(b) Pointwise ContinuousOn in t for ae z**: For each fixed z, `t ↦ charX t z` has `HasDerivAt` at every t (`hflow.2.1 t z`), hence is continuous at every t via `HasDerivAt.continuousAt`. Similarly `charV`. `Continuous.prodMk` gives joint continuity; composing with `hφ_lip.continuous` gives continuity of `t ↦ φ(charX t z, charV t z)`. ContinuousOn follows. Sound.

- **(c) Integrable dominator**: **BLOCKED**. Need `flow_distance_growth_bound`:
  ```
  ∃ C_T : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
    ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1)
  ```
  Given this, 1-Lipschitz φ gives `|φ(charX t z, charV t z)| ≤ |φ(0,0)| + C_T * (‖z‖ + 1)`,
  and the dominator `z ↦ |φ(0,0)| + C_T * (‖z‖ + 1)` is integrable against `f 0` because
  `‖z‖` is integrable by `hf_prob_0.2` and `f 0` is a probability measure.

**Why the dominator gap is real**: `flow_distance_growth_bound` is a Gronwall-type estimate on the characteristic ODE (charX velocity = charV, charV velocity = -(∇W * ρ_t)(charX t z)). The velocity field involves `convolveFunctionMeasure gradW (ρ t)`, which depends on `gradW`. The hypothesis `gradW : PhysSpace d → PhysSpace d` carries NO Lipschitz or linear-growth assumption in this lemma (unlike `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` which assumes `LipschitzWith L gradW`). Without a growth bound on `gradW`, the ODE solution can blow up in finite time, and no uniform bound on the flow exists.

**Fix**: Add `∃ C_T, ∀ t ∈ Set.Icc 0 T, ∀ z, ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1)` as a hypothesis (possibly derivable from `LipschitzWith L gradW`), or strengthen `IsLagrangianVlasovSolution` to include this bound.

**Wish-list Mathlib API**: `ODE.flow_linear_growth_bound` — for ODEs `ẋ = F(t,x)` where `F` has at most linear growth `‖F(t,x)‖ ≤ L(‖x‖ + 1)`, the flow satisfies `‖Φ(t,x₀)‖ ≤ (‖x₀‖ + 1)e^{Lt} - 1`. This is essentially Gronwall applied to `d/dt ‖x(t)‖ ≤ L(‖x(t)‖ + 1)`.
