## 2026-05-29 · vlasovWellPosedness_local_finalAssembly_moment

**Result:** success (per user task spec; 2 acceptable sub-sub-sorries remain inside body)
**Iterations:** 3/8
**Sorry count:** 4 → 4 (declarations using sorry; same count since body now has 2 intentional sub-sub-sorries per task spec)
**Pre-flight (§3.5):** dropped 0 hints; validated 6 lemma names; rejected 0 in-loop citations

### Final proof (on success)

```lean
theorem vlasovWellPosedness_local_finalAssembly_moment ... := by
  -- Sub-sub-sorry: AEMeasurable witness (Stage 1.8 territory).
  have h_aemeas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ := by
    sorry
  -- Sub-sub-sorry: universal-in-s convolution integrability.
  have h_int_conv : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    sorry
  -- haveI for Stage_1_9 typeclass: IsProbabilityMeasure (spatialMarginal ...)
  haveI hρ_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    have h_aemeas_pair := h_aemeas s
    have h_prob_inner := Measure.isProbabilityMeasure_map h_aemeas_pair
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Step 1: Friction 5 transport.
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    Stage_1_9_flow_boundary_regularity gradW ... T hT.le hflow_on h_boundary
  -- Step 2: Gronwall growth bound.
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ... T hT.le
      h_init h_cont_Icc h_deriv_Ico M_ρ hM_ρ_nn hM_ρ_bound h_y_int_ρ h_int_conv
  -- Step 3: HasFiniteFirstMoment via integrable_map_measure + growth bound.
  unfold HasFiniteFirstMoment vlasovSolutionViaPushforward
  refine ⟨Measure.isProbabilityMeasure_map (h_aemeas t), ?_⟩
  rw [integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm) (h_aemeas t)]
  have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := ...
  have h_norm_aesm := (h_aemeas t).norm.aestronglyMeasurable
  refine h_dom_int.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · convert h_norm_aesm using 1
  · simp only [Function.comp, Real.norm_of_nonneg (norm_nonneg _)]
    exact h_growth t ht z
```

### Lookup trail
- `Measure.isProbabilityMeasure_map` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:124`
- `integrable_map_measure` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:352`
- `Integrable.mono'` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:100`
- `AEMeasurable.norm` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean:252`
- `AEMeasurable.aestronglyMeasurable` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:437`
- `Real.norm_of_nonneg` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:62`

### Sub-sub-sorries (intentional per task spec)

1. `h_aemeas`: `∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀`
   - Stage 1.8 territory: requires measurability of the characteristic flow map.
   - Discharge: pending Stage 1.8 placeholder closure.

2. `h_int_conv`: `∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (spatialMarginal ...)`
   - Universal-in-s convolution integrability: for s ∈ Icc 0 T follows from h_y_int_ρ + Lipschitz; extension to all s requires clamp argument.

### Iteration details
- Iteration 1: Initial draft with `measurable_fst.comp_aemeasurable (h_aemeas s)` — wrong direction; needed `measurable_fst.aemeasurable` since Prod.fst is aemeasurable wrt the pushforward measure. Also `rw [Real.norm_of_nonneg]` failed because composition wasn't reduced.
- Iteration 2: Fixed IsProbabilityMeasure via `measurable_fst.aemeasurable`; added `convert h_norm_aesm using 1` + `simp only [Function.comp, ...]` — but `convert ... using 1; funext z; simp` gave "No goals to be solved" (convert solved it already).
- Iteration 3: Removed the extra `funext z; simp [Function.comp]` after convert. Build succeeded.
