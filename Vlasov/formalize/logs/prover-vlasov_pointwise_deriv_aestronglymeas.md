## 2026-05-28 · SC.7 · vlasov_pointwise_deriv_aestronglymeas

**Result:** success
**Iterations:** 3/8
**Sorry count:** 2 → 1 (CharacteristicFlow.lean; SC.8 remains)
**Pre-flight (§3.5):** dropped 0 hint(s); validated 0 sketch lemma(s) from plan; rejected 0 in-loop citation(s)

### Final proof

```lean
  -- The integrand factors as g ∘ (fun z => (charX t z, charV t z)), where
  -- g : PhaseSpace d → ℝ is the same continuous function as in the wrapper's
  -- h_integrand_aesm (g y = ⟨y.2, gradXφ y⟩ - ⟨convolve y.1, gradVφ y⟩).
  -- Step 1: establish that gradXφ and gradVφ are continuous (same argument as wrapper).
  have hfderiv_X : ∀ z : PhaseSpace d,
      fderiv ℝ (fun x => φ (x, z.2)) z.1 =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) :=
    fun z => by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
        hasFDerivAt_prodMk_left z.1 z.2
      exact (h1.comp z.1 h2).fderiv
  have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 := funext hgradXφ
  have hfderiv_V : ∀ z : PhaseSpace d,
      fderiv ℝ (fun v => φ (z.1, v)) z.2 =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) :=
    fun z => by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      exact (h1.comp z.2 h2).fderiv
  have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 := funext hgradVφ
  -- Step 2: show that g : PhaseSpace d → ℝ is continuous.
  have hg_cont : Continuous (fun y : PhaseSpace d =>
      @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
      - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y)) := by
    apply Continuous.sub
    · apply Continuous.inner continuous_snd
      simp_rw [heqX, gradient, hfderiv_X]
      exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        ((ContinuousLinearMap.isBoundedLinearMap_comp_right
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
          (hφ_smooth.continuous_fderiv (by simp)))
    · apply Continuous.inner
      · exact (hconv_cont t).comp continuous_fst
      · simp_rw [heqV, gradient, hfderiv_V]
        exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
          ((ContinuousLinearMap.isBoundedLinearMap_comp_right
            (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
            (hφ_smooth.continuous_fderiv (by simp)))
  -- Step 3: the integrand equals g ∘ flow. Apply Continuous.comp_aestronglyMeasurable.
  exact hg_cont.comp_aestronglyMeasurable h_flow_meas_t.aestronglyMeasurable
```

### Structural analysis

The task description said the proof shape is "identical" to the wrapper's `h_integrand_aesm`, but this was not quite right. The key structural difference:

- Wrapper's `h_integrand_aesm` integrates over `y : PhaseSpace d` where `y.1` and `y.2` are directly the integration variable's components. The integrand is a continuous function of `y`, so `Continuous.aestronglyMeasurable` applies directly.

- SC.7 integrates over `z : PhaseSpace d` (initial condition), with `charX t z` and `charV t z` as the phase-space point. The integrand is `g ∘ (charX t, charV t)` where `g` is the same continuous function. Proving AEStronglyMeasurable of a composition requires AEStronglyMeasurability of the inner function `(charX t, charV t)`.

Since SC.7's original signature had no measurability hypothesis on the flow, the proof was blocked. The fix:
1. Added `h_flow_meas_t : AEMeasurable (fun z : PhaseSpace d => (charX t z, charV t z)) f₀` as a new explicit parameter (after `t`).
2. Updated the single call site in `vlasovSolutionViaPushforward_isVlasovSolution` (line ~2162) to pass `(h_flow_meas t)` — this variable was already available in the wrapper's scope.

The proof then goes:
1. Prove `gradXφ` continuous via `HasFDerivAt.comp hasFDerivAt_prodMk_left` + `InnerProductSpace.toDual.symm.continuous ∘ ContinuousLinearMap.isBoundedLinearMap_comp_right ∘ ContDiff.continuous_fderiv` (verbatim from wrapper).
2. Prove `gradVφ` continuous symmetrically with `inr` instead of `inl`.
3. Show the outer function `g y = ⟨y.2, gradXφ y⟩ - ⟨convolve y.1, gradVφ y⟩` is continuous via `Continuous.sub` + two applications of `Continuous.inner`, using `continuous_snd`, `continuous_fst`, `hconv_cont t`.
4. Conclude via `hg_cont.comp_aestronglyMeasurable h_flow_meas_t.aestronglyMeasurable`.

The key bridge: `AEMeasurable.aestronglyMeasurable` (Mathlib, requires `SecondCountableTopology` on the target space — satisfied for `PhysSpace d × PhysSpace d = EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)`).

### Lookup trail (validated lemmas)
- `hasFDerivAt_prodMk_left` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:74`
- `hasFDerivAt_prodMk_right` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:79`
- `ContinuousLinearMap.isBoundedLinearMap_comp_right` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:384`
- `ContDiff.continuous_fderiv` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1241`
- `Continuous.comp_aestronglyMeasurable` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:208`
- `AEMeasurable.aestronglyMeasurable` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:437`
- `AEStronglyMeasurable.inner` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean:50`
- `continuous_inner` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Continuous.lean:63`
- `InnerProductSpace.toDual` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`

### Lean-idiom observation

`AEMeasurable f μ → AEStronglyMeasurable f μ` requires `[SecondCountableTopology (range type)]`. For EuclideanSpace (finite-dimensional over ℝ), this holds automatically. The bridge `.aestronglyMeasurable` is the key missing piece when working with compositions of continuous functions with AE-measurable flows.
