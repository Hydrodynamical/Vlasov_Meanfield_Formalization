## 2026-05-28T00:00:00Z · SC.6 · vlasov_compose_flow_integrable_at

**Result:** success  
**Iterations:** 7/8 (including 6 failed iterations diagnosing the parameter-order bug)  
**Sorry count:** 3 → 2 (in CharacteristicFlow.lean; Basic.lean unchanged at 4)  
**Pre-flight (§3.5):** dropped 0 hint(s); validated 4 lemma names; rejected 1 in-loop citation (`Filter.eventually_of_forall` — zero matches; used `Filter.Eventually.of_forall` instead)

### Final proof (on success)
```lean
lemma vlasov_compose_flow_integrable_at
    {d : ℕ} [NeZero d]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (φ : PhaseSpace d → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_compact : HasCompactSupport φ)
    (t : ℝ)
    (h_flow_meas_t : AEMeasurable
      (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) :
    Integrable (fun z => φ (charX t z, charV t z)) f₀ := by
  obtain ⟨C, hC⟩ := hφ_cont.bounded_above_of_compact_support hφ_compact
  exact Integrable.of_bound
    (hφ_cont.comp_aestronglyMeasurable h_flow_meas_t.aestronglyMeasurable)
    C (Filter.Eventually.of_forall (fun z => hC _))
```

Also fixed call site in `vlasovSolutionViaPushforward_isVlasovSolution` (swapped `(h_flow_meas t) t` → `t (h_flow_meas t)` to match new parameter order).

### Lookup trail
- `Continuous.bounded_above_of_compact_support` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean:158`
- `Integrable.of_bound` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:171`
- `Continuous.comp_aestronglyMeasurable` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:208`
- `AEMeasurable.aestronglyMeasurable` — `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:437`
- `Filter.Eventually.of_forall` — `.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:640`

### Pre-flight rejections (in-loop)
- `Filter.eventually_of_forall` — zero matches; used `Filter.Eventually.of_forall` (the correct renamed form) instead.

### Root cause of the 6 failed iterations
The original lemma declaration had `(h_flow_meas_t : AEMeasurable (fun z => (charX t z, charV t z)) f₀)` BEFORE `(t : ℝ)`. Lean 4 auto-bound `t` as an implicit `{t✝ : ℝ}` placed before `h_flow_meas_t`, making `h_flow_meas_t` reference `t✝` while the goal used the explicit `(t : ℝ)`. Inside the proof body, `t✝` and `t` are distinct free variables with no equational relationship, making the sorry impossible to discharge without connecting them.

**Fix**: swapped `(t : ℝ)` to come BEFORE `h_flow_meas_t` in the declaration. Now `t` is bound before `h_flow_meas_t`'s type is elaborated, so there is only one `t` in scope. The call site in the wrapper theorem also needed updating (swapping the positional arguments from `(h_flow_meas t) t` to `t (h_flow_meas t)`).

### Relevance to project catalogue
This is a new failure mode not in L1–L5: **auto-bound-implicit parameter-order bug**. When a Lean 4 lemma declares `(h : P t)` before `(t : ℝ)`, the `t` gets auto-bound as a ghost implicit `t✝` distinct from the explicit `t`. This makes the sorry unprovable from inside the proof body even though all call sites correctly unify them. Mitigation: always declare time/index parameters BEFORE hypotheses that mention them.
