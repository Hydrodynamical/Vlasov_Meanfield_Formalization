# Phase 1.5 — Functional-Analytic Decomposition: Design Document

**Session**: 2026-05-31, post-`de2eb62`. Single deliverable: this design doc.
No Lean changes. Sub-sub-sorry counts unchanged.

**Goal**: separate the project's MathlibTODO inventory into (a) pure
functional-analytic theorems (the genuine Mathlib OT contribution arc) and
(b) Vlasov-specific composition lemmas (project-internal bridges that
consume pure-FA MathlibTODOs as abstract inputs).

---

## Inventory + Per-Placeholder Categorization

### 1. `MathlibTODO_cauchyW1_hasNarrowLimit` (Basic.lean L1148)

**Statement** (atom-level):
```
Cauchy in W₁ for a sequence (ν n) of probability measures on PhysSpace d
+ uniform first-moment bound → ∃ μ with IsProbabilityMeasure μ + first
moment ≤ M + Filter.Tendsto (wasserstein1 (ν n) μ) atTop (𝓝 0)
```

**Hypotheses**: generic measure sequence, IsProbabilityMeasure, moment
bound — **no** project-specific terms.

**Callsites**: Basic.lean (2: definition + planning note), CharFlow.lean
(3: VlasovMeasureCurve packaging in `picard_iterate_bundlesAs_VlasovMeasureCurve`).

**Category**: **Pure-FA**. The statement uses only generic OT + measure-
theory primitives.

**Decomposition**: None needed.

---

### 2. `MathlibTODO_convolveContinuousAtOfNarrowMoment` (Basic.lean L1448)

**Statement** (atom-level):
```
Given gradW : PhysSpace d → PhysSpace d Lipschitz, μ : ℝ → Measure
(PhysSpace d) probability-valued, t₀, x : PhysSpace d, and:
  - h_narrow : ∀ g bounded continuous, ContinuousAt (∫ g d(μ t)) at t₀
  - h_mom_cont : ContinuousAt (∫ ‖y‖ d(μ t)) at t₀
  - moment + convolution integrability
⊢ ContinuousAt (convolveFunctionMeasure gradW (μ t) x) at t₀
```

**Hypotheses**: generic gradW (no `AssW` or other Vlasov tagging),
generic μ. The hypothesis surface is pure-FA — narrow continuity stated
as an abstract property, not derived from Vlasov dynamics.

**Callsites**: Basic.lean (1: definition). No CharFlow use yet (planned
for Sorry 9 substantive close).

**Category**: **Pure-FA**. The placeholder's statement abstracts gradW
and μ to generic objects; `convolveFunctionMeasure` is a generic
operator. No Vlasov-specific instantiation.

**Decomposition**: None needed.

---

### 3. `MathlibTODO_W1ContOn_lscNarrow` (Basic.lean L1710)

**Statement** (atom-level):
```
Given gradW, f g : ℝ → Measure (PhaseSpace d), IsVlasovSolution gradW f,
IsVlasovSolution gradW g, HasFiniteFirstMoment per t, T ≥ 0
⊢ LowerSemicontinuousOn (wasserstein1 (f t) (g t)) (Set.Icc 0 T)
```

**Hypotheses**: `IsVlasovSolution gradW _` — project-specific.

**Callsites**: Basic.lean (7: definition + consumer `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` at L1830). CharFlow.lean (0).

**Category**: **Mixed**. The underlying mathematics is "W₁ is LSC along
narrowly continuous probability-measure curves with uniform first moment
bound." Pure-FA. The current statement uses `IsVlasovSolution` only as a
*source* of narrow continuity + moment regularity.

**Decomposition target** (pure-FA):
```
theorem MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    (f g : ℝ → Measure α) [∀ t, IsProbabilityMeasure (f t)]
    [∀ t, IsProbabilityMeasure (g t)]
    (T : ℝ) (hT : 0 ≤ T)
    (hf_narrow : ∀ (φ : α → ℝ), Continuous φ → Bornology.IsBounded (Set.range φ) →
        ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T))
    (hg_narrow : ∀ (φ : α → ℝ), Continuous φ → Bornology.IsBounded (Set.range φ) →
        ContinuousOn (fun t => ∫ z, φ z ∂(g t)) (Set.Icc 0 T))
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z => ‖z‖) (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z => ‖z‖) (g t)) :
    LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T)
```

**Project-internal composition lemma**:
```
lemma w1ContOn_lscNarrow_via_pureFA
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f) (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  -- Derive narrow continuity from IsVlasovSolution + HasDerivAt.continuousAt.
  -- Apply MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves.
  sorry  -- Composition target; closes trivially once pure-FA placeholder is in place.
```

**Callsite update**: `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (L1805+) currently calls `MathlibTODO_W1ContOn_lscNarrow` directly; update to call `w1ContOn_lscNarrow_via_pureFA`.

---

### 4. `MathlibTODO_W1ContOn_uscNarrow` (Basic.lean L1725)

**Statement** (atom-level):
```
Same shape as item 3 but for UpperSemicontinuousOn, with additional
hypothesis LipschitzWith L gradW.
```

**Hypotheses**: `IsVlasovSolution gradW _` + Lipschitz gradW — project-
specific.

**Callsites**: Basic.lean (4: definition + consumer
`MathlibTODO_wassersteinGronwallCoupling_W1ContOn` at L1833).
CharFlow.lean (1: pre-Stage-4 reference).

**Category**: **Mixed**. Underlying mathematics: W₁-USC for measure
flows generated by Lipschitz vector fields satisfying the continuity
equation. Pure-FA via characteristic-flow coupling.

**Decomposition target** (pure-FA):
```
theorem MathlibTODO_w1UpperSemicontinuousAlongLipschitzMeasureFlow
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    (b : ℝ → α → α)  -- Vector field, Lipschitz in α uniformly in t
    (L : NNReal) (hL : ∀ t, LipschitzWith L (b t))
    (f g : ℝ → Measure α) [∀ t, IsProbabilityMeasure (f t)] [∀ t, IsProbabilityMeasure (g t)]
    -- Each curve satisfies the continuity equation for b:
    (hf_cont_eq : ContinuityEquationWith b f)
    (hg_cont_eq : ContinuityEquationWith b g)
    (hf_mom : ∀ t, Integrable (fun z => ‖z‖) (f t))
    (hg_mom : ∀ t, Integrable (fun z => ‖z‖) (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    UpperSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T)
```

Note: `ContinuityEquationWith` is a hypothetical Mathlib predicate that
captures "(d/dt) f t = -div(b t · f t)" weakly. May need to be its own
small definition in Basic.lean's pure-FA section.

**Project-internal composition lemma**:
```
lemma w1ContOn_uscNarrow_via_pureFA
    (gradW : ...) (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ...) (hf : IsVlasovSolution gradW f) (hg : IsVlasovSolution gradW g) ... :
    UpperSemicontinuousOn ... := by
  -- Vlasov vector field b(t, z) := (z.2, -∇W ∗ ρ_t)(z.1) is Lipschitz.
  -- IsVlasovSolution implies the continuity equation for b.
  -- Apply MathlibTODO_w1UpperSemicontinuousAlongLipschitzMeasureFlow.
  sorry
```

**Callsite update**: `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (L1833) updates similarly to item 3.

---

### 5. `MathlibTODO_wassersteinGronwallCoupling_derivBound` (Basic.lean L1844)

**Statement** (atom-level):
```
For two Vlasov solutions f, g + Lipschitz gradW + finite moments + a
constant C with L ≤ C, T ≥ 0:
  ∀ s ∈ Set.Ico 0 T, ∀ r > C * W₁(f s, g s).toReal,
    ∃ᶠ z in nhdsWithin s (Ioi s),
      ((W₁(f z, g z).toReal - W₁(f s, g s).toReal) / (z - s)) < r
```
(right-derivative liminf bound on the W₁ difference, used for Gronwall.)

**Hypotheses**: `IsVlasovSolution` + Lipschitz gradW.

**Callsites**: Basic.lean (3: definition + 2 consumers in the assembled
Gronwall theorem `wassersteinGronwallCoupling` and `dobrushin` corollary).

**Category**: **Mixed**. Underlying mathematics: right-derivative bound
on W₁ between two probability-measure flows generated by Lipschitz vector
fields, derived via characteristic-flow coupling.

**Decomposition target** (pure-FA):
```
theorem MathlibTODO_w1RightDerivBoundAlongLipschitzMeasureFlow
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    (b : ℝ → α → α) (L : NNReal) (hL : ∀ t, LipschitzWith L (b t))
    (f g : ℝ → Measure α) [∀ t, IsProbabilityMeasure (f t)] [∀ t, IsProbabilityMeasure (g t)]
    (hf_cont_eq : ContinuityEquationWith b f) (hg_cont_eq : ContinuityEquationWith b g)
    (hf_mom : ∀ t, Integrable (fun z => ‖z‖) (f t))
    (hg_mom : ∀ t, Integrable (fun z => ‖z‖) (g t))
    (C : ℝ) (hC : 0 < C) (hCL : (L : ℝ) ≤ C)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ r : ℝ,
      C * (wasserstein1 (f s) (g s)).toReal < r →
      ∃ᶠ z in nhdsWithin s (Set.Ioi s),
        (z - s)⁻¹ * ((wasserstein1 (f z) (g z)).toReal -
                     (wasserstein1 (f s) (g s)).toReal) < r
```

**Project-internal composition lemma**:
```
lemma wassersteinGronwallCoupling_derivBound_via_pureFA
    -- (same Vlasov-specific signature as the current MathlibTODO) := by
  -- Build the b-vector-field from gradW + ρ_s convolution.
  -- IsVlasovSolution implies ContinuityEquationWith b.
  -- Apply MathlibTODO_w1RightDerivBoundAlongLipschitzMeasureFlow.
  sorry
```

---

### 6. `MathlibTODO_dobrushin_uniqueness_On` (CharFlow.lean L8360)

**Statement** (atom-level):
```
For two IsVlasovSolutionOn solutions f, g on [0, T] with same initial
data and finite moments:
  ∀ t ∈ Set.Icc 0 T, f t = g t
```

**Hypotheses**: `IsVlasovSolutionOn` (project-specific) + finite moments
+ same initial data.

**Callsites**: CharFlow.lean (4: definition + Stage 8 uniqueness body
+ comment references).

**Category**: **Vlasov-specific** as currently stated, **but** decomposable
to a corollary of item 5's decomposed pure-FA derivBound. Specifically:
W₁(f 0, g 0) = 0 (same initial data) + Gronwall bound from
`MathlibTODO_w1RightDerivBoundAlongLipschitzMeasureFlow` ⟹ W₁(f t, g t) ≤ 0
⟹ f t = g t (W₁ = 0 characterizes measure equality for Polish-space
probability measures).

**Decomposition target**: **No new pure-FA placeholder**. This is a
*Vlasov-specific composition* of:
- Item 5's decomposed pure-FA (`MathlibTODO_w1RightDerivBoundAlongLipschitzMeasureFlow`).
- A known Mathlib fact (`wasserstein1_eq_zero_iff` or similar).

Project-internal composition lemma:
```
lemma dobrushin_uniqueness_On
    -- (same signature as the current MathlibTODO, dropping the MathlibTODO_ prefix) := by
  -- Apply localized version of MathlibTODO_w1RightDerivBoundAlongLipschitzMeasureFlow
  -- with C = L + 1 (or similar).
  -- Gronwall integration gives W₁(f t, g t) ≤ W₁(f 0, g 0) * exp((L+1) * t) = 0.
  -- W₁ = 0 → f t = g t.
  sorry  -- Composes pure-FA stability with W₁-zero characterization.
```

**Callsite update**: Stage 8 (`vlasovWellPosedness_uniqueness` body) updates to call `dobrushin_uniqueness_On` (no prefix).

---

### 7. `MathlibTODO_vlasovTrajectoryLipschitzBound` (CharFlow.lean L2679)

**Statement** (atom-level):
```
For the characteristic flow (charX, charV) generated by gradW + ρ,
+ smooth compact-support φ, + IsCharacteristicFlow:
  ∃ nhd ∈ 𝓝 t, ∃ bound : PhaseSpace d → ℝ,
    (∀ᵐ z ∂f₀, LipschitzOnWith |bound z| (s ↦ φ(charX s z, charV s z)) nhd)
    ∧ Integrable bound f₀
```

**Hypotheses**: `IsCharacteristicFlow` — project-specific.

**Callsites**: CharFlow.lean (2: definition + `vlasovSolutionViaPushforward_isVlasovSolution` consumer at L3146).

**Category**: **Mixed**. Underlying pure-FA: per-z Lipschitz bound on
trajectories of an ODE flow with Lipschitz RHS, composed with a smooth
compact-support test function.

**Decomposition target** (pure-FA):
```
theorem MathlibTODO_lipschitzFlowTrajectoryLipBound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (b : ℝ → α → α) (L : NNReal) (hL : ∀ t, LipschitzWith L (b t))
    (Φ : ℝ → α → α)  -- The flow generated by b
    (hflow : ∀ z, HasDerivAt (fun t => Φ t z) (b t (Φ t z)) t)
    (μ : Measure α)
    (φ : α → ℝ) (hφ : ContDiff ℝ ⊤ φ) (hφ_compact : HasCompactSupport φ)
    (t : ℝ) :
    ∃ nhd ∈ 𝓝 t, ∃ bound : α → ℝ,
      (∀ᵐ z ∂μ, LipschitzOnWith (Real.nnabs (bound z))
          (fun s => φ (Φ s z)) nhd) ∧
      Integrable bound μ
```

Note: The Vlasov version's flow has the *pair* `(charX, charV)`, but the
pure-FA version abstracts to a single ODE flow `Φ` on a joint state space.

**Project-internal composition lemma**:
```
lemma vlasovTrajectoryLipschitzBound_via_pureFA := by
  -- Vlasov phase-space flow Φ t z := (charX t z, charV t z) on PhaseSpace d.
  -- The joint vector field b(t, z) := (z.2, -∇W ∗ ρ_t(z.1)) is Lipschitz
  -- with constant max(1, L).
  -- IsCharacteristicFlow's HasDerivAt clauses combine to HasDerivAt for Φ.
  -- Apply MathlibTODO_lipschitzFlowTrajectoryLipBound.
  sorry
```

---

### 8. `MathlibTODO_picardFlowAEMeasurable` (CharFlow.lean L6172)

**Statement** (atom-level):
```
For (charX, charV) satisfying IsCharacteristicFlowOn on Ioo 0 T × univ:
  ∀ s, AEMeasurable (fun z => (charX s z, charV s z)) μ
for any measure μ.
```

**Hypotheses**: `IsCharacteristicFlowOn` — project-specific.

**Callsites**: CharFlow.lean (2: definition + `_picard_fixedPointFlow.h_aemeas_out` consumer at L6504).

**Category**: **Mixed**. Underlying pure-FA per user's worked example:
ODE flow with Lipschitz RHS is continuous-in-initial-condition (Picard
regularity), hence Borel-measurable, hence AEMeasurable against any
measure.

**Decomposition target** (pure-FA):
```
theorem MathlibTODO_lipschitzFlowAEMeasurable
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [MeasurableSpace α] [BorelSpace α]
    (b : ℝ → α → α) (L : NNReal) (hL : ∀ t, LipschitzWith L (b t))
    (Φ : ℝ → α → α)
    (hflow : ∀ z, ∀ t : ℝ, HasDerivAt (fun s => Φ s z) (b t (Φ t z)) t)
    (μ : Measure α) :
    ∀ s, AEMeasurable (Φ s) μ
```

**Project-internal composition lemma**:
```
lemma picardCharFlow_aemeasurable := by
  -- Build joint flow Φ from (charX, charV) on PhaseSpace d.
  -- IsCharacteristicFlowOn implies the HasDerivAt premise for Φ.
  -- Apply MathlibTODO_lipschitzFlowAEMeasurable.
  sorry
```

---

## Aggregate

**Categorization summary**:
- **Pure-FA, no decomposition**: 2 (`cauchyW1_hasNarrowLimit`,
  `convolveContinuousAtOfNarrowMoment`).
- **Mixed, decomposes**: 5 (`W1ContOn_lscNarrow`, `W1ContOn_uscNarrow`,
  `wassersteinGronwallCoupling_derivBound`, `vlasovTrajectoryLipschitzBound`,
  `picardFlowAEMeasurable`).
- **Vlasov-specific, reclassifies to project-internal**: 1
  (`dobrushin_uniqueness_On`).

**End-of-Phase-1.5 inventory**:
- **Pure-FA MathlibTODOs**: 2 (existing) + 5 (decomposed) = **7 total**.
- **Project-internal composition lemmas (new)**: 5 (one per decomposed
  mixed) + 1 (reclassified dobrushin) = **6 new project-internal
  declarations**.

**Sorry-count trajectory**:
- Before Phase 1.5: 11 declarations using sorry (8 MathlibTODO + 3 project-internal containing sub-sub-sorries).
- After Phase 1.5: ~16 declarations using sorry expected (7 pure-FA MathlibTODO + 6 new project-internal compositions + 3 unchanged project-internal containers). **Net +5 declarations**.

This is the trade-off the user's brief anticipates: slight raw sorry-count increase in exchange for substantially cleaner inventory separation. The 6 new project-internal composition lemmas each close trivially once their pure-FA MathlibTODO input is in scope (one-line `apply` + minor data unpacking).

**Cleanup-document inventory** (post Phase 1.5):
- **Mathlib OT contribution arc**: 7 pure-FA MathlibTODOs.
  - Bucket-1 (Villani-standard, single-PR): cauchyW1_hasNarrowLimit,
    convolveContinuousAtOfNarrowMoment, w1LowerSemicontinuousAlongNarrowMomentCurves,
    lipschitzFlowAEMeasurable, lipschitzFlowTrajectoryLipBound.
  - Bucket-2 (requires continuity-equation API): w1UpperSemicontinuousAlongLipschitzMeasureFlow,
    w1RightDerivBoundAlongLipschitzMeasureFlow.
- **Vlasov-specific bridge work**: 6 project-internal composition lemmas
  (close via Phase 2-4 substantive work composing pure-FA + Vlasov
  context).

The Mathlib PR drafting order is now cleanly defined: bucket-1 first
(focused single-theorem PRs), bucket-2 second (after the continuity-
equation predicate `ContinuityEquationWith` lands in Mathlib).

---

## Phase 1.5 COMPLETION status (2026-05-31)

**Status**: complete across Sessions 1 + 2 + 3.  All 8 original
placeholders processed.  Final inventory matches design projection.

**Sessions 1 + 2 + 3 commit chain**:
* `1f04d0d` (Session 1): design document.
* `78773ac` (Session 2 item 1): picardFlowAEMeasurable decomposed.
* `31ee66d` (Session 2 item 2): vlasovTrajectoryLipschitzBound decomposed.
* `ecd6130` (Session 2 item 3): dobrushin_uniqueness_On reclassified.
* `f8453c8` (Session 2 item 4): W1ContOn_lscNarrow decomposed.
* `dc5db0e` (Session 2 status + item 5 deferral).
* `93ac461` (Session 3 item 5): W1ContOn_uscNarrow + derivBound decomposed.

**Final inventory** (16 declarations using sorry total):
* **Pure-FA MathlibTODOs (Mathlib OT contribution arc)**: 7.
  - cauchyW1_hasNarrowLimit (bucket-1).
  - convolveContinuousAtOfNarrowMoment (bucket-1).
  - w1LowerSemicontinuousAlongNarrowMomentCurves (bucket-1).
  - w1UpperSemicontinuousAlongLagrangianFlows (bucket-2).
  - w1RightDerivBoundAlongLagrangianFlows (bucket-2).
  - lipschitzFlowTrajectoryLipBound (bucket-1).
  - lipschitzFlowAEMeasurable (bucket-1).
* **Project-internal compositions (Phase 2-4 targets, sorry'd)**: 6.
  - w1ContOn_lscNarrow_via_pureFA, w1ContOn_uscNarrow_via_pureFA,
    wassersteinGronwallCoupling_derivBound_via_pureFA (Basic.lean).
  - vlasovTrajectoryLipschitzBound, picardCharFlow_aemeasurable,
    dobrushin_uniqueness_On (CharFlow.lean).
* **Project-internal substantive containers (Phase 2-4 targets)**: 3.
  - _picard_fixedPointFlow (5 sub-sub-sorries inside).
  - _glue_step (1 sub-sub-sorry: h_cont_g).
  - _universal_existence (1 sub-sub-sorry: Stage 6 t=0).

**Sorry trajectory**:
* Pre-Phase-1.5: 11 declarations (8 MathlibTODO + 3 substantive containers).
* Post-Phase-1.5: 16 declarations (matches design projection).
* Net: +5 (per design doc's trade-off — cleaner inventory in exchange for
  slight raw count increase).

**Cleanup-document framing strengthened**: 7 pure-FA MathlibTODOs form
a clean, self-contained Mathlib OT contribution arc, separated from
6 Vlasov-specific bridge work compositions and 3 critical-path
substantive containers.

**Bucket structure for Mathlib PRs**:
* Bucket-1 (single-PR, Villani-standard): 5 placeholders.
* Bucket-2 (requires characteristic-flow coupling infrastructure): 2
  placeholders.

**Forward look — Phase 2-4 closure trajectory (post Phase 1.5)**:
* Phase 2: Sorry 3 (`_picard_fixedPointFlow.hq_lt`) — deferred from
  previous arc; ~1-2 sessions for the M-dependent hypothesis propagation
  design + close.
* Phase 3: cheap Picard closures (sorries 4, 5, 6, 8) + composition
  lemma trivial closes (the 6 new Phase 1.5 compositions all close in
  one-liner pattern once pure-FA inputs are in scope; collectively a
  single session).
* Phase 4: substantive Picard sequence, h_cont_g (multi-commit),
  Stage 6 t=0.

Total remaining sessions: ~6-8 to MathlibTODO-only state with the
decomposed inventory.

**Phase B sequencing decision** (still pending): the Phase 1.5 separation
significantly strengthens cleanup-document framing.  The strategic
conversation should revisit this decision before Phase A endpoint.
Current recommendation lean: cleanup-document-first sequencing.

---

## Session 2 execution status (2026-05-31)

**Items completed in Session 2** (4 of 5):
* **Item 1** (`picardFlowAEMeasurable`): decomposed.  Commit `78773ac`.
  * Pure-FA: `MathlibTODO_lipschitzFlowAEMeasurable`.
  * Project-internal: `picardCharFlow_aemeasurable`.
* **Item 2** (`vlasovTrajectoryLipschitzBound`): decomposed.  Commit `31ee66d`.
  * Pure-FA: `MathlibTODO_lipschitzFlowTrajectoryLipBound`.
  * Project-internal: `vlasovTrajectoryLipschitzBound`.
* **Item 3** (`dobrushin_uniqueness_On`): reclassified.  Commit `ecd6130`.
  * No new pure-FA (composes against to-be-decomposed item 5).
  * Project-internal: `dobrushin_uniqueness_On` (no `MathlibTODO_` prefix).
* **Item 4** (`W1ContOn_lscNarrow`): decomposed.  Commit `f8453c8`.
  * Pure-FA: `MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves`.
  * Project-internal: `w1ContOn_lscNarrow_via_pureFA`.

**Item 5 deferred to Session 3 (per P2 protocol)**:
combined `W1ContOn_uscNarrow` + `wassersteinGronwallCoupling_derivBound`.

**P2 firing rationale**: both placeholders' pure-FA form requires a way
to express "the measure curves `f, g` are evolutionarily compatible with
a Lipschitz vector field `b`."  Two candidate formulations:

* **Option A: Continuity Equation predicate.** Define
  `ContinuityEquationWith b μ := ∀ t, ∂_t (∫ φ dμ_t) = ∫ ⟨∇φ, b t⟩ dμ_t`
  weakly.  Then pure-FA item 5's hypothesis is
  `ContinuityEquationWith b f ∧ ContinuityEquationWith b g`.

* **Option B: Lagrangian Pushforward formulation.** Define a structure
  / predicate that says "f t = (Φ t)_# f 0 where Φ is the flow of b."
  Matches `IsLagrangianVlasovSolution`'s pushforward equation directly.
  Pure-FA item 5's hypothesis becomes the abstracted version of this
  pushforward property.

**Decision pending**: which option to commit to.  Option A is closer to
Villani's standard formulation; Option B is closer to the project's
existing `IsLagrangianVlasovSolutionOn` structure.  Either choice
introduces a NEW project-internal predicate that other placeholders may
also use, so the choice has architectural weight.

**Session 3 deliverable** (when scheduled):
1. Predicate-design decision (Option A vs B).
2. Define the chosen predicate in Basic.lean.
3. Decompose item 5 into pure-FA + project-internal compositions using
   the predicate.
4. Update closure-plan and planning-notes accordingly.

**Session 2 sorry trajectory**:
* Declarations using sorry: 11 → 14 (+3 net from 4 completed items;
  item 3 was a rename so net 0; items 1, 2, 4 each net +1).
* Pure-FA MathlibTODOs: 7 → 10 (+3 from items 1, 2, 4).
* Project-internal compositions (sorry'd): 0 → 4 (items 1, 2, 3, 4).
* Old mixed MathlibTODOs: 5 → 2 (removed: picardFlowAEMeasurable,
  vlasovTrajectoryLipschitzBound, dobrushin_uniqueness_On,
  W1ContOn_lscNarrow.  Remaining: W1ContOn_uscNarrow,
  wassersteinGronwallCoupling_derivBound — Session 3 targets).

After Session 3 closes item 5, projected total:
* Declarations using sorry: 14 → 16 (+2 from item 5's combined
  decomposition).
* Pure-FA MathlibTODOs: 10 → 12 (+2 from item 5's two pure-FA splits).
* Project-internal compositions: 4 → 6 (+2 from item 5).

This matches the original design-doc projection of ~16 declarations
end-of-Phase-1.5.

---

## Original Execution Plan for Session 2 (reference; partially superseded by status above)

**Per-placeholder decomposition order** (cheapest first):

1. **Item 8 (`picardFlowAEMeasurable`)**: simplest pure-FA decomposition;
   no complicating Vlasov vector-field shape. Single commit. ~50 lines added.

2. **Item 7 (`vlasovTrajectoryLipschitzBound`)**: similar to item 8 but
   with the smooth compact-support φ composition. Single commit. ~60 lines added.

3. **Item 6 (`dobrushin_uniqueness_On`)**: reclassification to project-
   internal; no new pure-FA placeholder. Single commit. ~30 lines added
   (mostly comment/docstring update + composition body sketch).

4. **Item 3 (`W1ContOn_lscNarrow`)**: introduce pure-FA placeholder +
   composition. Single commit. ~70 lines added.

5. **Items 4 + 5 (`W1ContOn_uscNarrow`, `wassersteinGronwallCoupling_derivBound`)**:
   require defining `ContinuityEquationWith` predicate. Either decompose
   together in one commit (~120 lines added) or defer the predicate
   definition to a separate small commit first.

**Estimated Session 2 budget**: ~330 lines added total across ~5-6
commits. Build green after each commit.

**Risk**: items 4 + 5 introduce a new predicate (`ContinuityEquationWith`).
If the predicate's exact form needs iteration, defer to Session 3 with
a focused predicate-design discussion. Per P2: if the predicate-design
surfaces complexity, document and pause.

---

## Discipline notes

**No substantive sub-sub-sorry closures in Phase 1.5**: the 6 project-
internal composition lemmas land with sorry'd bodies; their closure is
Phase 2-4 substantive work (mostly trivial composition lines, but
deferred to maintain Phase 1.5's statement-level focus).

**P1 active during Session 2 execution**: each decomposition's pure-FA
statement requires atom-level verification that the abstraction preserves
mathematical content. Borderline cases pause for re-examination.

**P5 active during Session 2 execution**: if a "pure-FA" statement is
discovered mid-decomposition to still depend on Vlasov-specifics,
re-categorize.

**No new MathlibTODO additions during Session 2**: if a decomposition
surfaces a *new* gap, document as pending placeholder candidate; don't
add as part of Phase 1.5.

---

## Forward look

After Phase 1.5 (Sessions 1 + 2 [+ 3]): the closure plan's Phase 2-4
work executes against the decomposed interface. The 6 new project-internal
composition lemmas close via simple one-line `apply` patterns; the
existing project-internal substantive declarations
(`_picard_fixedPointFlow`, `_glue_step`, `_universal_existence`) close
via Phase 2-4 substantive work.

Total remaining sessions to MathlibTODO-only state with the decomposed
inventory: ~6-9 focused sessions (Phase 2-4 per closure plan + this
Phase 1.5 setup).

**Phase B sequencing decision** (still pending from planning-notes.md):
the cleaner pure-FA / project-internal separation makes the cleanup
document's external-presentation framing substantially stronger. This
weighs in favor of cleanup-document-first sequencing post-Phase-A
(the document can highlight the 7 pure-FA MathlibTODOs as the project's
Mathlib OT contribution arc, with the Vlasov-specific bridge work
documented as project-internal narrative).
