/-
Coupling-based Wasserstein-1 distance.

This is the first installment of the OT infrastructure that would eventually
close the three remaining `MathlibTODO_*` placeholders in `Vlasov/Basic.lean`
(`_W1ContOn_lscNarrow`, `_W1ContOn_uscNarrow`, `_derivBound`).  All three
gaps reduce to a chain of three missing pieces:

  1. Couplings and the Monge-Kantorovich definition of `W_1`.        ← this file
  2. Existence of optimal couplings (Prokhorov tightness + LSC cost). ← TODO
  3. Full Kantorovich-Rubinstein duality:
       `wasserstein1_dual = wasserstein1_coupling` as equality.       ← TODO

This file provides (1) and the **easy direction** of (3) — the inequality
`wasserstein1_dual μ ν ≤ wasserstein1_coupling μ ν`.  The reverse direction
(the genuine KR theorem) requires Hahn-Banach extension + a duality
argument that is deferred to a follow-up file.

Why the easy direction matters: once it's available, the dobrushin
proof can switch from the dual-formula bound (which requires the hard
direction of KR for upper-bounding W_1 by a coupling cost) to a
coupling-cost bound, modulo just the one remaining duality piece.  This
isolates the trust in a single place rather than spreading it across
the three `lsc`/`usc`/`derivBound` placeholders.

See `formalize/DESIGN.md` for the overall design choices.
-/

import Vlasov.Basic

/-
**Mathlib-upstream targeting note.**  The contents of this file —
`IsCoupling`, `wasserstein1_coupling`, the easy direction of KR,
`IsCoupling.map`, and `wasserstein1_pushforward_le_iInf` — are all
domain-independent OT on pseudometric spaces.  When eventually
contributed upstream, the natural home is
`Mathlib/MeasureTheory/Wasserstein/Coupling.lean` under
`namespace MeasureTheory`.  We keep `namespace Vlasov` for now so the
project remains self-contained.  The hard direction of KR
(Hahn-Banach + Prokhorov tightness for optimal coupling existence)
is also Mathlib-worthy but a several-month project; we explicitly
defer it and route the dobrushin proof around it via the easy
direction + pushforward chain instead.
-/

namespace Vlasov

open MeasureTheory ProbabilityTheory ENNReal
open scoped ProbabilityTheory

/-! ## Couplings -/

/-- A coupling of measures `μ` on `α` and `ν` on `β` is a measure `π` on the
product space whose marginals are exactly `μ` and `ν`.

We use the convention that `Prod.fst` is the `α`-marginal and `Prod.snd` is
the `β`-marginal. -/
def IsCoupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (π : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop :=
  Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν

/-! ## Coupling-based Wasserstein-1 distance -/

/-- The coupling-based Wasserstein-1 distance: infimum of `∫⁻ edist(x,y) dπ(x,y)`
over all couplings `π` of `(μ, ν)`.  This is the Monge-Kantorovich definition,
to be compared with the dual definition `wasserstein1` (in `Vlasov/Basic.lean`)
via Kantorovich-Rubinstein duality.

We use the Lebesgue lower integral `∫⁻` of `edist` (extended distance, valued
in `ℝ≥0∞`) rather than the Bochner integral `∫` of `dist` (valued in `ℝ`).
This is the standard OT convention: a coupling π whose cost is non-integrable
contributes `⊤` to the infimum (rather than the Bochner junk-value 0), so the
infimum correctly identifies the OT-optimal coupling.  Returns `⊤` if no
coupling exists. -/
noncomputable def wasserstein1_coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ENNReal :=
  ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
    ∫⁻ z, edist z.1 z.2 ∂π

/-! ## Kantorovich-Rubinstein: easy direction

The dual-formula `wasserstein1` is at most the coupling-formula
`wasserstein1_coupling`.  This is the *one-line proof* in the OT literature:
for any 1-Lipschitz `φ` and any coupling `π`:

  ∫φ d(μ - ν) = ∫(φ x - φ y) dπ ≤ ∫ |φ x - φ y| dπ ≤ ∫ dist(x,y) dπ.

The reverse inequality is the hard direction of KR (Hahn-Banach extension);
it is deferred to a follow-up file.
-/

/-- KR easy direction.  Under finite-moment assumptions on `μ` and `ν`, the
dual-formula `wasserstein1 μ ν` is bounded above by the coupling-formula
`wasserstein1_coupling μ ν`.

**Proof strategy** (full proof TODO).  By `iSup_le` and `le_iInf`, it suffices
to show that for every 1-Lipschitz `φ` and every coupling `π` of (μ, ν):
`ENNReal.ofReal (∫φ dμ − ∫φ dν) ≤ ∫⁻ edist z.1 z.2 ∂π`.

Two cases:
  - `∫⁻ edist z.1 z.2 ∂π = ⊤`: trivially `_ ≤ ⊤`.  This case is handled.
  - `∫⁻ edist z.1 z.2 ∂π < ⊤`: requires the substantive work:
      (a) `edist`-integrability of `π` implies `dist`-integrability;
      (b) by `Measure.IsCoupling` marginals and `integral_map`,
          `∫φ dμ = ∫(φ ∘ Prod.fst) dπ`, similarly for `ν`;
      (c) `∫φ dμ - ∫φ dν = ∫(φ(z.1) - φ(z.2)) dπ`;
      (d) `|φ(z.1) - φ(z.2)| ≤ dist(z.1, z.2)` by 1-Lipschitz;
      (e) integrability of each side via finite-first-moment of μ and ν,
          derivable from finite coupling cost.
This proof would need ~50-100 lines of measure-theoretic plumbing. -/
theorem wasserstein1_le_wasserstein1_coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_fm : Integrable (fun y => dist y x₀) μ)
    (hν_fm : Integrable (fun y => dist y x₀) ν) :
    wasserstein1 μ ν ≤ wasserstein1_coupling μ ν := by
  rw [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  refine le_iInf fun π => le_iInf fun hπ => ?_
  -- Goal: ENNReal.ofReal (∫φ dμ - ∫φ dν) ≤ ∫⁻ z, edist z.1 z.2 ∂π
  by_cases h_top : ∫⁻ z, edist z.1 z.2 ∂π = ⊤
  · rw [h_top]; exact le_top
  push_neg at h_top
  -- Step 1: π inherits IsProbabilityMeasure from its first marginal μ.
  haveI hπ_prob : IsProbabilityMeasure π := by
    refine ⟨?_⟩
    have h_eq : π Set.univ = μ Set.univ := by
      rw [← hπ.1, Measure.map_apply measurable_fst MeasurableSet.univ,
          Set.preimage_univ]
    rw [h_eq, measure_univ]
  -- Step 2: `dist z.1 z.2` is Integrable wrt π (from h_top, via edist = ofReal dist).
  have h_dist_meas : AEStronglyMeasurable (fun z : α × α => dist z.1 z.2) π :=
    (measurable_fst.dist measurable_snd).aestronglyMeasurable
  have h_enorm_eq : ∀ z : α × α, ‖dist z.1 z.2‖ₑ = edist z.1 z.2 := fun z => by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg dist_nonneg, edist_dist]
  have h_dist_int : Integrable (fun z : α × α => dist z.1 z.2) π := by
    refine ⟨h_dist_meas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [h_enorm_eq]
    exact h_top.lt_top
  -- Step 3: 1-Lipschitz φ is integrable wrt μ and wrt ν, via |φ y| ≤ |φ x₀| + dist y x₀
  -- and the finite-first-moment hypothesis on each marginal.
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_μ : AEStronglyMeasurable φ μ := hφ_cont.aestronglyMeasurable
  have hφ_meas_ν : AEStronglyMeasurable φ ν := hφ_cont.aestronglyMeasurable
  have h_pt_bound : ∀ y, |φ y| ≤ |φ x₀| + dist y x₀ := fun y => by
    calc |φ y|
        = |(φ y - φ x₀) + φ x₀|             := by ring_nf
      _ ≤ |φ y - φ x₀| + |φ x₀|              := abs_add_le _ _
      _ ≤ dist y x₀ + |φ x₀|                 := by
            have := hφ.dist_le_mul y x₀
            rw [Real.dist_eq, NNReal.coe_one, one_mul] at this
            linarith
      _ = |φ x₀| + dist y x₀                 := by ring
  have h_dom_μ : Integrable (fun y => |φ x₀| + dist y x₀) μ :=
    (integrable_const _).add hμ_fm
  have h_dom_ν : Integrable (fun y => |φ x₀| + dist y x₀) ν :=
    (integrable_const _).add hν_fm
  have hφ_int_μ : Integrable φ μ :=
    h_dom_μ.mono hφ_meas_μ (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) dist_nonneg)]
      exact h_pt_bound y)
  have hφ_int_ν : Integrable φ ν :=
    h_dom_ν.mono hφ_meas_ν (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) dist_nonneg)]
      exact h_pt_bound y)
  -- Step 4: φ ∘ Prod.fst integrable wrt π (since fst-marginal = μ).
  have hφ_fst_meas : AEStronglyMeasurable (fun z : α × α => φ z.1) π :=
    (hφ_cont.comp continuous_fst).aestronglyMeasurable
  have hφ_snd_meas : AEStronglyMeasurable (fun z : α × α => φ z.2) π :=
    (hφ_cont.comp continuous_snd).aestronglyMeasurable
  have h_diff_bound : ∀ z : α × α, |φ z.1 - φ z.2| ≤ dist z.1 z.2 := fun z => by
    have := hφ.dist_le_mul z.1 z.2
    rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this
  -- φ z.1 − φ z.2 is integrable wrt π (bounded by integrable dist).
  have h_diff_int : Integrable (fun z : α × α => φ z.1 - φ z.2) π :=
    h_dist_int.mono (hφ_fst_meas.sub hφ_snd_meas) (Filter.Eventually.of_forall fun z => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg dist_nonneg]
      exact h_diff_bound z)
  -- Step 5: change of variables via marginals.
  have hφ_meas_pf : AEStronglyMeasurable φ (Measure.map Prod.fst π) := by
    rw [hπ.1]; exact hφ_meas_μ
  have hφ_meas_ps : AEStronglyMeasurable φ (Measure.map Prod.snd π) := by
    rw [hπ.2]; exact hφ_meas_ν
  have h_cov_μ : ∫ y, φ y ∂μ = ∫ z, φ z.1 ∂π := by
    conv_lhs => rw [← hπ.1]
    exact integral_map measurable_fst.aemeasurable hφ_meas_pf
  have h_cov_ν : ∫ y, φ y ∂ν = ∫ z, φ z.2 ∂π := by
    conv_lhs => rw [← hπ.2]
    exact integral_map measurable_snd.aemeasurable hφ_meas_ps
  -- ∫(φ z.1) dπ and ∫(φ z.2) dπ are individually integrable.
  have hφ_fst_int : Integrable (fun z : α × α => φ z.1) π := by
    have h := hφ_int_μ
    rw [← hπ.1] at h
    exact (integrable_map_measure hφ_meas_pf measurable_fst.aemeasurable).mp h
  have hφ_snd_int : Integrable (fun z : α × α => φ z.2) π := by
    have h := hφ_int_ν
    rw [← hπ.2] at h
    exact (integrable_map_measure hφ_meas_ps measurable_snd.aemeasurable).mp h
  -- Step 6: ∫φ dμ − ∫φ dν = ∫(φ z.1 − φ z.2) dπ
  rw [h_cov_μ, h_cov_ν, ← integral_sub hφ_fst_int hφ_snd_int]
  -- Step 7: bound the integrand by dist (using 1-Lip), then integrate.
  have h_real_bound : ∫ z, (φ z.1 - φ z.2) ∂π ≤ ∫ z, dist z.1 z.2 ∂π := by
    apply integral_mono_ae h_diff_int h_dist_int
    exact Filter.Eventually.of_forall fun z => (le_abs_self _).trans (h_diff_bound z)
  -- Step 8: ofReal(∫(φ z.1 − φ z.2) dπ) ≤ ofReal(∫ dist dπ) = ∫⁻ edist dπ.
  refine (ENNReal.ofReal_le_ofReal h_real_bound).trans ?_
  -- ofReal(∫ dist dπ) = ∫⁻ ofReal(dist) dπ = ∫⁻ edist dπ
  rw [ofReal_integral_eq_lintegral_ofReal h_dist_int
        (Filter.Eventually.of_forall fun _ => dist_nonneg)]
  -- ∫⁻ ofReal(dist z.1 z.2) ∂π ≤ ∫⁻ edist z.1 z.2 ∂π  (equal pointwise via edist_dist)
  apply le_of_eq
  apply lintegral_congr
  intro z
  exact (edist_dist z.1 z.2).symm

/-! ## Foundation B — optimal coupling existence + hard Kantorovich–Rubinstein duality

This section states the project's single external optimal-transport theorem,
`foundationB_optimal_coupling_exists`, and derives the duality equality from it
(combined with the easy direction above).  Everything is stated
**cost-generically** over a continuous pseudometric cost `c`, so the deferred
cutoff cost `c = min (dist ·) 1` (the W̄ refactor) instantiates the same
statements verbatim.
-/

/-- Cost-generic coupling cost: the infimum over couplings `π` of `(μ, ν)` of
`∫⁻ ofReal (c z.1 z.2) ∂π`.  At `c = dist` this is `wasserstein1_coupling`
(`edist = ofReal ∘ dist`); see `wasserstein1_coupling_eq`. -/
noncomputable def wassersteinCost_coupling
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) : ENNReal :=
  ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
    ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π

/-- At `c = dist`, the cost-generic coupling cost reduces to `wasserstein1_coupling`
(since `edist x y = ofReal (dist x y)`). -/
lemma wasserstein1_coupling_eq
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] (μ ν : Measure α) :
    wasserstein1_coupling μ ν = wassersteinCost_coupling (fun x y => dist x y) μ ν := by
  unfold wasserstein1_coupling wassersteinCost_coupling
  refine iInf_congr fun π => iInf_congr fun _ => ?_
  exact lintegral_congr fun z => edist_dist z.1 z.2

/-! ### Kantorovich–Rubinstein duality (hard direction) — Route 1 skeleton

The helpers below decompose `foundationB_coupling_le_dual` (the hard KR direction)
via discrete approximation + limit (see `formalize/kr-duality-plan.md`).  All are
**general optimal-transport facts**, not Vlasov-specific — each is marked
`[General OT — reusable / Mathlib-upstreamable]` and stated cost-generically.
Bodies are `sorry` (P4 API-lock); closed in subsequent sessions.
-/

/-- **[General OT — reusable / Mathlib-upstreamable] Symmetry of the coupling cost.**
For a symmetric cost, `wassersteinCost_coupling c μ ν = wassersteinCost_coupling c ν μ`
(push a coupling forward under `Prod.swap`). -/
theorem wassersteinCost_coupling_comm
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (hc_symm : ∀ x y, c x y = c y x)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) :
    wassersteinCost_coupling c μ ν = wassersteinCost_coupling c ν μ := by
  -- One direction; the swap of a coupling of (a,b) is a coupling of (b,a) with equal cost.
  have key : ∀ (a b : Measure α),
      wassersteinCost_coupling c a b ≤ wassersteinCost_coupling c b a := by
    intro a b
    unfold wassersteinCost_coupling
    refine le_iInf fun π => le_iInf fun hπ => ?_
    -- π : IsCoupling π b a; `map swap π` couples (a, b).
    have hswap : IsCoupling (Measure.map Prod.swap π) a b := by
      refine ⟨?_, ?_⟩
      · rw [Measure.map_map measurable_fst measurable_swap]; exact hπ.2
      · rw [Measure.map_map measurable_snd measurable_swap]; exact hπ.1
    refine iInf_le_of_le (Measure.map Prod.swap π) (iInf_le_of_le hswap (le_of_eq ?_))
    calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(Measure.map Prod.swap π)
        = ∫⁻ z, ENNReal.ofReal (c (Prod.swap z).1 (Prod.swap z).2) ∂π :=
          lintegral_map (ENNReal.measurable_ofReal.comp hc_meas) measurable_swap
      _ = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π := by
          refine lintegral_congr fun z => ?_
          simp only [Prod.fst_swap, Prod.snd_swap]
          exact congrArg ENNReal.ofReal (hc_symm z.2 z.1)
  exact le_antisymm (key μ ν) (key ν μ)

/-- **[General OT — reusable / Mathlib-upstreamable] Gluing of couplings.**  Given a
coupling `π₁` of `(μ, ρ)` and a coupling `π₂` of `(ρ, ν)`, disintegrating `π₂` over
its `ρ`-marginal (`condKernel`) and re-binding along `π₁`'s `ρ`-marginal yields a
coupling `π₃` of `(μ, ν)` whose cost is at most the sum of the two costs (ground-cost
triangle `c x z ≤ c x y + c y z`).  The load-bearing facts are the two marginals
(`map fst π₃ = μ` via `fst_compProd`; `map snd π₃ = ν` via `snd_compProd` + the
`bind`/`map`/`comap` law). -/
theorem exists_coupling_glue
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ]
    (π₁ : Measure (α × α)) (h₁ : IsCoupling π₁ μ ρ)
    (π₂ : Measure (α × α)) (h₂ : IsCoupling π₂ ρ ν) :
    ∃ π₃ : Measure (α × α), IsCoupling π₃ μ ν ∧
      ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₃
        ≤ (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁)
          + (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) := by
  haveI : Nonempty α := nonempty_of_isProbabilityMeasure μ
  haveI hπ₁ : IsProbabilityMeasure π₁ := by
    constructor
    have h : π₁ Set.univ = μ Set.univ := by
      rw [← h₁.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [h, measure_univ]
  haveI hπ₂ : IsProbabilityMeasure π₂ := by
    constructor
    have h : π₂ Set.univ = ρ Set.univ := by
      rw [← h₂.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [h, measure_univ]
  set κ₂ : Kernel α α := π₂.condKernel with hκ₂
  haveI : IsMarkovKernel κ₂ := by rw [hκ₂]; infer_instance
  set κ₂' : Kernel (α × α) α := κ₂.comap Prod.snd measurable_snd with hκ₂'
  set glued : Measure ((α × α) × α) := π₁ ⊗ₘ κ₂' with hglued
  set proj : (α × α) × α → α × α := fun w => (w.1.1, w.2) with hproj
  have hproj_meas : Measurable proj :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hg : Measurable (fun z : α × α => ENNReal.ofReal (c z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp hc_meas
  have hdisint : π₂.fst ⊗ₘ κ₂ = π₂ := by
    rw [hκ₂]; exact Measure.disintegrate π₂ π₂.condKernel
  have hρπ₂ : ρ ⊗ₘ κ₂ = π₂ := by rw [show ρ = π₂.fst from h₂.1.symm]; exact hdisint
  refine ⟨glued.map proj, ⟨?_, ?_⟩, ?_⟩
  · -- fst marginal = μ
    rw [Measure.map_map measurable_fst hproj_meas]
    have hcomp : (Prod.fst ∘ proj) = (Prod.fst ∘ Prod.fst : (α × α) × α → α) := rfl
    rw [hcomp, ← Measure.map_map measurable_fst measurable_fst,
      show Measure.map Prod.fst glued = π₁ from Measure.fst_compProd π₁ κ₂']
    exact h₁.1
  · -- snd marginal = ν
    rw [Measure.map_map measurable_snd hproj_meas]
    have hcomp : (Prod.snd ∘ proj) = (Prod.snd : (α × α) × α → α) := rfl
    rw [hcomp, show Measure.map Prod.snd glued = κ₂' ∘ₘ π₁ from Measure.snd_compProd π₁ κ₂']
    have hLHS : κ₂' ∘ₘ π₁ = Measure.bind π₁ (fun p => κ₂ p.2) :=
      Measure.bind_congr_right
        (Filter.Eventually.of_forall fun p => Kernel.comap_apply κ₂ measurable_snd p)
    have hbindmap : κ₂ ∘ₘ (Measure.map Prod.snd π₁) = Measure.bind π₁ (fun p => κ₂ p.2) := by
      rw [show Measure.map Prod.snd π₁ = Measure.bind π₁ (fun p => Measure.dirac p.2) from
            (Measure.bind_dirac_eq_map π₁ measurable_snd).symm,
        show (κ₂ ∘ₘ Measure.bind π₁ (fun p => Measure.dirac p.2))
            = Measure.bind (Measure.bind π₁ (fun p => Measure.dirac p.2)) κ₂ from rfl,
        Measure.bind_bind
          (by fun_prop : Measurable (fun p : α × α => Measure.dirac p.2)).aemeasurable
          κ₂.aemeasurable]
      exact Measure.bind_congr_right
        (Filter.Eventually.of_forall fun p => Measure.dirac_bind κ₂.measurable p.2)
    have hRHS : ν = Measure.bind π₁ (fun p => κ₂ p.2) := by
      calc ν = π₂.snd := h₂.2.symm
        _ = (π₂.fst ⊗ₘ κ₂).snd := by rw [hdisint]
        _ = κ₂ ∘ₘ π₂.fst := Measure.snd_compProd π₂.fst κ₂
        _ = κ₂ ∘ₘ ρ := by rw [show π₂.fst = ρ from h₂.1]
        _ = κ₂ ∘ₘ (Measure.map Prod.snd π₁) := by rw [show ρ = Measure.map Prod.snd π₁ from h₁.2.symm]
        _ = Measure.bind π₁ (fun p => κ₂ p.2) := hbindmap
    rw [hLHS, hRHS]
  · -- cost bound: lintegral_compProd (Tonelli) + ground-cost triangle + Markov.
    have hF : Measurable (fun w : (α × α) × α => ENNReal.ofReal (c w.1.1 w.2)) :=
      hg.comp hproj_meas
    have hLcost : ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(glued.map proj)
        = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁ := by
      rw [hglued]
      calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂((π₁ ⊗ₘ κ₂').map proj)
          = ∫⁻ w, ENNReal.ofReal (c w.1.1 w.2) ∂(π₁ ⊗ₘ κ₂') := by
            rw [lintegral_map hg hproj_meas]
        _ = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂' p) ∂π₁ := Measure.lintegral_compProd hF
        _ = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁ := by
            simp only [hκ₂', Kernel.comap_apply]
    -- the c(y,z) leaf: the second piece reduces to the π₂-cost (sibling of snd-marginal).
    have hkey2 : ∫⁻ p, (∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁
        = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂ := by
      have hF_meas : Measurable (fun y : α => ∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) :=
        Measurable.lintegral_kernel_prod_right' hg
      calc ∫⁻ p, (∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁
          = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) ∂(Measure.map Prod.snd π₁) :=
            (lintegral_map hF_meas measurable_snd).symm
        _ = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) ∂ρ := by rw [h₁.2]
        _ = ∫⁻ w, ENNReal.ofReal (c w.1 w.2) ∂(ρ ⊗ₘ κ₂) := (Measure.lintegral_compProd hg).symm
        _ = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂ := by rw [hρπ₂]
    rw [hLcost]
    have hbound : ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁
        ≤ ∫⁻ p, (ENNReal.ofReal (c p.1 p.2)
            + ∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁ := by
      refine lintegral_mono fun p => ?_
      calc ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2)
          ≤ ∫⁻ z, (ENNReal.ofReal (c p.1 p.2) + ENNReal.ofReal (c p.2 z)) ∂(κ₂ p.2) := by
            refine lintegral_mono fun z => ?_
            exact (ENNReal.ofReal_le_ofReal (hc_triangle p.1 p.2 z)).trans ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (c p.1 p.2) + ∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2) := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    refine hbound.trans (le_of_eq ?_)
    rw [lintegral_add_left hg, hkey2]

/-- **[General OT — reusable / Mathlib-upstreamable] Triangle inequality for the
coupling cost.**  Gluing of couplings through a common middle measure
(`exists_coupling_glue`), then the `iInf` arithmetic. -/
theorem wassersteinCost_coupling_triangle
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] :
    wassersteinCost_coupling c μ ν
      ≤ wassersteinCost_coupling c μ ρ + wassersteinCost_coupling c ρ ν := by
  -- ε→0; the ⊤-case is the clean early-out (le_of_forall_pos_le_add supplies RHS < ⊤).
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hAB => ?_
  have hAfin : wassersteinCost_coupling c μ ρ < ⊤ := (ENNReal.add_lt_top.mp hAB).1
  have hBfin : wassersteinCost_coupling c ρ ν < ⊤ := (ENNReal.add_lt_top.mp hAB).2
  have hδ : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
    ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by norm_num)
  -- ε-optimal couplings (free from the iInf — no attainment needed).
  obtain ⟨π₁, h₁, hc₁⟩ : ∃ π₁, IsCoupling π₁ μ ρ ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁) < wassersteinCost_coupling c μ ρ + (ε : ℝ≥0∞) / 2 := by
    have hlt : wassersteinCost_coupling c μ ρ < wassersteinCost_coupling c μ ρ + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right hAfin.ne hδ.ne'
    unfold wassersteinCost_coupling at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨π, hπ⟩ := hlt
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hcost⟩ := hπ
    exact ⟨π, h, hcost⟩
  obtain ⟨π₂, h₂, hc₂⟩ : ∃ π₂, IsCoupling π₂ ρ ν ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) < wassersteinCost_coupling c ρ ν + (ε : ℝ≥0∞) / 2 := by
    have hlt : wassersteinCost_coupling c ρ ν < wassersteinCost_coupling c ρ ν + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right hBfin.ne hδ.ne'
    unfold wassersteinCost_coupling at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨π, hπ⟩ := hlt
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hcost⟩ := hπ
    exact ⟨π, h, hcost⟩
  obtain ⟨π₃, h₃, hcost⟩ :=
    exists_coupling_glue c hc_nonneg hc_triangle hc_meas μ ν ρ π₁ h₁ π₂ h₂
  calc wassersteinCost_coupling c μ ν
      ≤ ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₃ :=
        iInf_le_of_le π₃ (iInf_le_of_le h₃ le_rfl)
    _ ≤ (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁)
          + (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) := hcost
    _ ≤ (wassersteinCost_coupling c μ ρ + (ε : ℝ≥0∞) / 2)
          + (wassersteinCost_coupling c ρ ν + (ε : ℝ≥0∞) / 2) := add_le_add hc₁.le hc₂.le
    _ = wassersteinCost_coupling c μ ρ + wassersteinCost_coupling c ρ ν + (ε : ℝ≥0∞) := by
        rw [add_add_add_comm, ENNReal.add_halves]

/-- **[General OT — reusable / Mathlib-upstreamable] Graph-coupling bound.**  The
coupling cost between `μ` and a pushforward `Measure.map T μ` is at most the
integrated transport cost of `T`, witnessed by the graph coupling
`(id, T)_# μ`. -/
theorem wassersteinCost_coupling_map_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ : Measure α) [IsProbabilityMeasure μ]
    (T : α → α) (hT : Measurable T) :
    wassersteinCost_coupling c μ (Measure.map T μ)
      ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := by
  -- the graph coupling `(id, T)_# μ` couples `μ` and `T_# μ`; its cost is the integral.
  have hg : Measurable (fun x : α => (x, T x)) := measurable_id.prodMk hT
  have hγ : IsCoupling (Measure.map (fun x => (x, T x)) μ) μ (Measure.map T μ) := by
    refine ⟨?_, ?_⟩
    · rw [Measure.map_map measurable_fst hg]
      rw [show (Prod.fst ∘ fun x : α => (x, T x)) = id from rfl, Measure.map_id]
    · rw [Measure.map_map measurable_snd hg]; rfl
  unfold wassersteinCost_coupling
  refine iInf_le_of_le (Measure.map (fun x => (x, T x)) μ) (iInf_le_of_le hγ (le_of_eq ?_))
  calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(Measure.map (fun x => (x, T x)) μ)
      = ∫⁻ x, ENNReal.ofReal (c (x, T x).1 (x, T x).2) ∂μ :=
        lintegral_map (ENNReal.measurable_ofReal.comp hc_cont.measurable) hg
    _ = ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := rfl

/-! Decomposed by sorry-decomposer.
    See `formalize/plans/exists_finiteRange_map_cost_le.json`. -/

/-- **[General OT — reusable / Mathlib-upstreamable] Finite-range step map construction.**
Given a measurable pairwise-disjoint partition `As : ℕ → Set α` covering `univ` with
representatives `as : ℕ → α` and a fallback point `x₀`, the truncated step map
`T x = as n` when `x ∈ As n` for some `n < N`, `T x = x₀` otherwise, is measurable
and has finite range contained in `{as n | n < N} ∪ {x₀}`. -/
lemma finiteRange_approxMap_measurable
    {α : Type*} [MeasurableSpace α]
    (As : ℕ → Set α) (hAs_mble : ∀ n, MeasurableSet (As n))
    (_hAs_cover : ⋃ n, As n = Set.univ)
    (_hAs_disj : Pairwise fun n m => Disjoint (As n) (As m))
    (as : ℕ → α) (x₀ : α) (N : ℕ) :
    ∃ T : α → α,
      Measurable T ∧
      (Set.range T).Finite ∧
      (∀ n < N, ∀ x ∈ As n, T x = as n) ∧
      (∀ x ∈ (⋃ n ∈ Finset.range N, As n)ᶜ, T x = x₀) := by
  sorry

/-- **[General OT — reusable / Mathlib-upstreamable] Integrable nonneg → lintegral ofReal finite.**
If `f : α → ℝ` is integrable with respect to `μ` and a.e. nonneg, then
`∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞`.
Key tools: `hasFiniteIntegral_iff_ofReal` and `Integrable.hasFiniteIntegral`. -/
lemma lintegral_ofReal_ne_top_of_integrable_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) (hfnn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ := by
  sorry

/-- **[General OT — reusable / Mathlib-upstreamable] Tail cost control via absolute continuity.**
If `∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞` and `μ ((S n)ᶜ) → 0` as `n → ∞`, then the tail
costs `∫⁻ x in (S n)ᶜ, ENNReal.ofReal (f x) ∂μ → 0`.
Follows from `MeasureTheory.tendsto_setLIntegral_zero` (absolute continuity of the integral). -/
lemma lintegral_ofReal_tail_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hfint : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞)
    {S : ℕ → Set α}
    (hS_tendsto : Filter.Tendsto (fun n => μ ((S n)ᶜ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x in (S n)ᶜ, ENNReal.ofReal (f x) ∂μ)
      Filter.atTop (nhds 0) := by
  sorry

/-- **[General OT — reusable / Mathlib-upstreamable] Kept-cells cost bound.**
For a step map `T` with `T x = as n` on `As n` (for `n < N`), where we have a pointwise
bound `∀ n < N, ∀ x ∈ As n, c x (T x) ≤ δ` (established from the cell diameter), the
lintegral of `ENNReal.ofReal (c x (T x))` over the kept cells is at most `ENNReal.ofReal δ`
since `μ univ = 1`. -/
lemma lintegral_ofReal_kept_cells_le
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (As : ℕ → Set α) (hAs_mble : ∀ n, MeasurableSet (As n))
    (N : ℕ) (δ : ℝ) (_hδ : 0 < δ)
    (T : α → α)
    (hcT_le : ∀ n < N, ∀ x ∈ As n, c x (T x) ≤ δ) :
    ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ
      ≤ ENNReal.ofReal δ := by
  sorry

/-- **[General OT — reusable / Mathlib-upstreamable] Tail mass of a measurable cover → 0.**
For a finite measure and a measurable cover `⋃ n, As n = univ`, the mass of the complement
of the partial unions `⋃ j < n, As j` tends to `0` (continuity from above:
`⋂ n (⋃ j<n As j)ᶜ = ∅`). -/
lemma measure_compl_biUnion_range_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {As : ℕ → Set α} (hAs_mble : ∀ n, MeasurableSet (As n))
    (hAs_cover : ⋃ n, As n = Set.univ) :
    Filter.Tendsto (fun n => μ ((⋃ j ∈ Finset.range n, As j)ᶜ)) Filter.atTop (nhds 0) := by
  sorry

/-- **[General OT — reusable / Mathlib-upstreamable] Finite-range approximation.**
For a probability measure with finite first moment, the transport cost to a
finite-range pushforward can be made arbitrarily small (partition into
small-diameter cells + finite-moment tail control). -/
theorem exists_finiteRange_map_cost_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (_hc_nonneg : ∀ x y, 0 ≤ c x y) (_hc_self : ∀ x, c x x = 0)
    (_hc_symm : ∀ x y, c x y = c y x)
    (_hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (hc_le_dist : ∀ x y, c x y ≤ dist x y)
    (μ : Measure α) [IsProbabilityMeasure μ] (x₀ : α)
    (_hμ_cm : Integrable (fun y => c y x₀) μ)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ T : α → α, Measurable T ∧ (Set.range T).Finite ∧
      ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ ≤ ENNReal.ofReal ε := by
  -- Step 1: get a dist-diameter partition (cells of diam ≤ ε/2)
  haveI : TopologicalSpace.SeparableSpace α := inferInstance
  obtain ⟨As, hAs_mble, hAs_bdd, hAs_diam, hAs_cover, hAs_disj⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le α (half_pos _hε)
  -- per-cell representatives (x₀ on empty cells)
  classical
  set as : ℕ → α := fun n => if h : (As n).Nonempty then h.some else x₀ with has_def
  -- Step 2: lintegral ofReal (c · x₀) is finite
  have hfint : ∫⁻ x, ENNReal.ofReal (c x x₀) ∂μ ≠ ∞ :=
    lintegral_ofReal_ne_top_of_integrable_nonneg _hμ_cm
      (Filter.Eventually.of_forall (fun x => _hc_nonneg x x₀))
  -- Step 3: tail mass μ (⋃ j ∈ range n, As j)ᶜ → 0
  have htail_mass : Filter.Tendsto (fun n => μ ((⋃ j ∈ Finset.range n, As j)ᶜ))
      Filter.atTop (nhds 0) :=
    measure_compl_biUnion_range_tendsto_zero hAs_mble hAs_cover
  -- Step 4: tail costs → 0
  have htail_cost : Filter.Tendsto
      (fun n => ∫⁻ x in (⋃ j ∈ Finset.range n, As j)ᶜ, ENNReal.ofReal (c x x₀) ∂μ)
      Filter.atTop (nhds 0) :=
    lintegral_ofReal_tail_tendsto_zero hfint htail_mass
  -- Step 5: extract N with tail cost ≤ ε/2
  obtain ⟨N, hN⟩ : ∃ N, ∫⁻ x in (⋃ j ∈ Finset.range N, As j)ᶜ, ENNReal.ofReal (c x x₀) ∂μ ≤
      ENNReal.ofReal (ε / 2) := by
    rw [ENNReal.tendsto_nhds_zero] at htail_cost
    have hev := htail_cost (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos _hε))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    exact ⟨N, hN N le_rfl⟩
  -- Step 6: build finite-range step map T with representative x₀ on each cell
  -- (prover will later improve representatives to achieve kept-cell cost ≤ ε/2)
  obtain ⟨T, hT_mble, hT_fin, hT_kept, hT_tail⟩ :=
    finiteRange_approxMap_measurable As hAs_mble hAs_cover hAs_disj as x₀ N
  refine ⟨T, hT_mble, hT_fin, ?_⟩
  -- Step 7: decompose the total lintegral into kept + tail parts
  have hS_mble : MeasurableSet (⋃ n ∈ Finset.range N, As n) :=
    MeasurableSet.biUnion (Finset.countable_toSet _) (fun n _ => hAs_mble n)
  rw [show ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ =
      ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ +
      ∫⁻ x in (⋃ n ∈ Finset.range N, As n)ᶜ, ENNReal.ofReal (c x (T x)) ∂μ
    from (lintegral_add_compl _ hS_mble).symm]
  -- Step 8a: bound kept cells via the kept-cell lemma
  have hkept : ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ ≤
      ENNReal.ofReal (ε / 2) :=
    lintegral_ofReal_kept_cells_le c _hc_nonneg As hAs_mble N (ε / 2) (half_pos _hε) T
      (fun n hn x hx => by
        rw [hT_kept n hn x hx]
        have hxn : (As n).Nonempty := ⟨x, hx⟩
        have hasn : as n ∈ As n := by
          simp only [has_def, dif_pos hxn]; exact hxn.some_mem
        calc c x (as n) ≤ dist x (as n) := hc_le_dist x (as n)
          _ ≤ Metric.diam (As n) := Metric.dist_le_diam_of_mem (hAs_bdd n) hx hasn
          _ ≤ ε / 2 := hAs_diam n)
  -- Step 8b: bound tail by hN (T x = x₀ on tail, so cost = c x x₀ ≤ ε/2)
  have htail : ∫⁻ x in (⋃ n ∈ Finset.range N, As n)ᶜ, ENNReal.ofReal (c x (T x)) ∂μ ≤
      ENNReal.ofReal (ε / 2) := by
    have heq : Set.EqOn (fun x => ENNReal.ofReal (c x (T x))) (fun x => ENNReal.ofReal (c x x₀))
        (⋃ n ∈ Finset.range N, As n)ᶜ := by
      intro x hx
      simp only []
      congr 1
      rw [hT_tail x hx]
    rw [setLIntegral_congr_fun hS_mble.compl heq]
    exact hN
  -- Step 9: combine: ε/2 + ε/2 = ε
  have hε_split : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (le_of_lt (half_pos _hε)) (le_of_lt (half_pos _hε))]
    congr 1; ring
  calc ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ +
        ∫⁻ x in (⋃ n ∈ Finset.range N, As n)ᶜ, ENNReal.ofReal (c x (T x)) ∂μ
      ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by gcongr
    _ = ENNReal.ofReal ε := hε_split

/-- **[General OT — reusable / Mathlib-upstreamable] Finite Kantorovich–Rubinstein
duality.**  For finitely-supported (finite-range pushforward) probability measures,
the coupling-infimum is at most the dual-supremum — the finite LP duality core
(Birkhoff–von Neumann vertices + a finite dual-potential construction). -/
theorem wassersteinCost_coupling_le_dual_of_finiteRange
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    (c : α → α → ℝ) (_hc_nonneg : ∀ x y, 0 ≤ c x y) (_hc_self : ∀ x, c x x = 0)
    (_hc_symm : ∀ x y, c x y = c y x) (_hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (_hT : Measurable T) (_hS : Measurable S)
    (_hTfin : (Set.range T).Finite) (_hSfin : (Set.range S).Finite) :
    wassersteinCost_coupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) (Measure.map S ν) := by
  sorry

/-- **[General OT — reusable / Mathlib-upstreamable] Single-map dual bound.**  The
dual cost between a pushforward `Measure.map T μ` and `μ` is at most the integrated
transport cost of `T`.  Direct dual-side analogue of `wassersteinCost_coupling_map_le`:
for any `c`-admissible test `f` (oscillation `≤ c`, hence continuous), the change of
variables `∫ f d(T_# μ) = ∫ f∘T dμ` plus `|f(Tx) − f x| ≤ c x (Tx)` gives the bound;
the finite `c`-moment `hμ_cm` controls test-function integrability. -/
theorem wassersteinCost_dual_singleMap_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ : Measure α) [IsProbabilityMeasure μ] (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ)
    (T : α → α) (hT : Measurable T) :
    wassersteinCost c (Measure.map T μ) μ ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := by
  unfold wassersteinCost
  refine iSup_le fun f => iSup_le fun hf => ?_
  by_cases hItop : (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ) = ⊤
  · rw [hItop]; exact le_top
  -- f is continuous: oscillation `≤ c`, `c` continuous, `c a a = 0`.
  have hf_cont : Continuous f := by
    rw [Metric.continuous_iff]
    intro a ε hε
    have hca : Continuous (fun x => c x a) :=
      hc_cont.comp (continuous_id.prodMk continuous_const)
    have hca0 : Filter.Tendsto (fun x => c x a) (nhds a) (nhds 0) := by
      have h := hca.tendsto a
      rwa [hc_self a] at h
    obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhds_nhds.1 hca0 ε hε
    refine ⟨δ, hδ0, fun x hx => ?_⟩
    have hcxa : dist (c x a) 0 < ε := hδ hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hc_nonneg x a)] at hcxa
    calc dist (f x) (f a) = |f x - f a| := Real.dist_eq _ _
      _ ≤ c x a := hf x a
      _ < ε := hcxa
  have hf_meas : Measurable f := hf_cont.measurable
  -- `f` is `μ`-integrable: `|f x| ≤ |f x₀| + c x x₀`, with `c · x₀` integrable.
  have hf_int_mu : Integrable f μ := by
    have hbound : ∀ x, |f x| ≤ |f x₀| + c x x₀ := fun x => by
      calc |f x|
          = |(f x - f x₀) + f x₀| := by ring_nf
        _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
        _ ≤ c x x₀ + |f x₀| := by have := hf x x₀; linarith
        _ = |f x₀| + c x x₀ := by ring
    refine ((integrable_const |f x₀|).add hμ_cm).mono hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (add_nonneg (abs_nonneg (f x₀)) (hc_nonneg x x₀))]
    exact hbound x
  -- `c · (T ·)` is integrable (the `I < ⊤` case).
  have hcT_meas : Measurable (fun x => c x (T x)) :=
    hc_cont.measurable.comp (measurable_id.prodMk hT)
  have hcT_int : Integrable (fun x => c x (T x)) μ := by
    refine ⟨hcT_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have henorm : ∀ x, ‖c x (T x)‖ₑ = ENNReal.ofReal (c x (T x)) := fun x => by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hc_nonneg x (T x))]
    simp_rw [henorm]
    exact lt_top_iff_ne_top.mpr hItop
  -- `f ∘ T` is `μ`-integrable: `|f (T x)| ≤ |f x| + c x (T x)`.
  have hfT_int : Integrable (fun x => f (T x)) μ := by
    have hbound2 : ∀ x, |f (T x)| ≤ |f x| + c x (T x) := fun x => by
      have h1 := hf (T x) x
      rw [hc_symm (T x) x] at h1
      calc |f (T x)|
          = |(f (T x) - f x) + f x| := by ring_nf
        _ ≤ |f (T x) - f x| + |f x| := abs_add_le _ _
        _ ≤ c x (T x) + |f x| := by linarith
        _ = |f x| + c x (T x) := by ring
    refine (hf_int_mu.abs.add hcT_int).mono (hf_meas.comp hT).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (add_nonneg (abs_nonneg (f x)) (hc_nonneg x (T x)))]
    exact hbound2 x
  -- change of variables + integrand bound.
  have hcov : (∫ x, f x ∂(Measure.map T μ)) = ∫ x, f (T x) ∂μ :=
    integral_map hT.aemeasurable hf_cont.aestronglyMeasurable
  rw [hcov, ← integral_sub hfT_int hf_int_mu]
  have hmono : (∫ x, (f (T x) - f x) ∂μ) ≤ ∫ x, c x (T x) ∂μ := by
    refine integral_mono_ae (hfT_int.sub hf_int_mu) hcT_int
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := hf (T x) x
    rw [hc_symm (T x) x] at h1
    calc f (T x) - f x ≤ |f (T x) - f x| := le_abs_self _
      _ ≤ c x (T x) := h1
  refine (ENNReal.ofReal_le_ofReal hmono).trans (le_of_eq ?_)
  exact ofReal_integral_eq_lintegral_ofReal hcT_int
    (Filter.Eventually.of_forall fun x => hc_nonneg x (T x))

/-- **[General OT — reusable / Mathlib-upstreamable] Dual-side stability under
pushforward.**  A `c`-admissible test function changes value by at most the
transport cost, so the dual sup over `(T_# μ, S_# ν)` exceeds that over `(μ, ν)`
by at most the two transport costs.  Dual triangle (`wassersteinCost_triangle`)
through `μ` then `ν`, with each single-map leg bounded by
`wassersteinCost_dual_singleMap_le`. -/
theorem wassersteinCost_dual_le_add_map
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ) (hν_cm : Integrable (fun y => c y x₀) ν) :
    wassersteinCost c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c μ ν
        + (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
        + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν) := by
  have htri1 := wassersteinCost_triangle c (Measure.map T μ) μ (Measure.map S ν)
  have htri2 := wassersteinCost_triangle c μ ν (Measure.map S ν)
  have hT_bound : wassersteinCost c (Measure.map T μ) μ
      ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ :=
    wassersteinCost_dual_singleMap_le c hc_nonneg hc_self hc_symm hc_cont μ x₀ hμ_cm T hT
  have hS_bound : wassersteinCost c ν (Measure.map S ν)
      ≤ ∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν := by
    rw [wassersteinCost_comm c ν (Measure.map S ν)]
    exact wassersteinCost_dual_singleMap_le c hc_nonneg hc_self hc_symm hc_cont ν x₀ hν_cm S hS
  calc wassersteinCost c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) μ + wassersteinCost c μ (Measure.map S ν) := htri1
    _ ≤ wassersteinCost c (Measure.map T μ) μ
          + (wassersteinCost c μ ν + wassersteinCost c ν (Measure.map S ν)) :=
        add_le_add le_rfl htri2
    _ ≤ (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
          + (wassersteinCost c μ ν + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν)) :=
        add_le_add hT_bound (add_le_add le_rfl hS_bound)
    _ = wassersteinCost c μ ν
          + (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
          + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν) := by abel

/-- **Foundation B (the project's single external sorry): the hard direction of
Kantorovich–Rubinstein duality** — the primal coupling-formula is at most the
dual-formula.

For probability measures `μ, ν` with finite first moment on a Polish (here
second-countable Borel pseudometric) space and a continuous pseudometric cost
`c`:  `wassersteinCost_coupling c μ ν ≤ wassersteinCost c μ ν`.  The reverse
inequality (weak duality, `≥`) is the **easy** direction
`wasserstein1_le_wasserstein1_coupling` (already proved); together they give the
full KR equality `wasserstein1_eq_coupling`.

**Scope (post-Option-3 shrink, 2026-06-06).**  This inequality is ALL the project
trusts externally.  It is an *inf ≤ sup* statement (`inf over couplings ≤ sup over
1-Lipschitz`), so it needs neither the infimum **attained** (no optimal-coupling
existence / Prokhorov-tightness build) nor the full equality — only the duality
bound, approachable ε-optimally.  The earlier attainment-and-equality form
(`foundationB_optimal_coupling_exists`) was removed: its sole live consumer
(`dobrushin`, via `wasserstein1_eq_coupling`) needs only this inequality, which it
applies by monotonicity.  "Foundation A" (narrow ↔ W₁) was a phantom; existence,
uniqueness, the mean-field stability core, and the mean-field limit all stand
B-free — the axiom footprint pins B to this one line.

Stated cost-generically over a continuous pseudometric `c` so the deferred cutoff
cost `c = min (dist ·) 1` (the W̄ refactor) reuses it verbatim.

**Proof skeleton (Route 1 — discrete approximation + limit; helpers above, P4
API-lock — body pending).**  For `ε > 0` pick finite-range `T, S` with transport
cost `≤ ε/4` each (`exists_finiteRange_map_cost_le`).  With `μ' = Measure.map T μ`,
`ν' = Measure.map S ν`:
`W_c(μ,ν) ≤ W_c(μ,μ') + W_c(μ',ν') + W_c(ν',ν)`
(`wassersteinCost_coupling_triangle` ×2, `…_comm`); the outer terms `≤ ε/4`
(`wassersteinCost_coupling_map_le`); `W_c(μ',ν') ≤ dual(μ',ν')`
(`wassersteinCost_coupling_le_dual_of_finiteRange`); `dual(μ',ν') ≤ dual(μ,ν) +
ε/2` (`wassersteinCost_dual_le_add_map`).  Chain → `W_c(μ,ν) ≤ dual(μ,ν) + ε`;
`ε → 0` (`ENNReal.le_of_forall_pos_le_add`).  NOTE: the triangle needs
`StandardBorelSpace α` (disintegration); when wiring the body, thread that instance
here + through `wasserstein1_eq_coupling` (consumers instantiate at the Polish
`PhaseSpace d`, so it resolves).  See `formalize/kr-duality-plan.md`. -/
theorem foundationB_coupling_le_dual
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (hc_le_dist : ∀ x y, c x y ≤ dist x y)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ)
    (hν_cm : Integrable (fun y => c y x₀) ν) :
    wassersteinCost_coupling c μ ν ≤ wassersteinCost c μ ν := by
  -- ε→0; for each ε pick finite-range approximants T, S with transport cost ≤ ε/4.
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _hb => ?_
  have hε4 : (0 : ℝ) < (ε : ℝ) / 4 := by positivity
  obtain ⟨T, hT, hTfin, hTcost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_cont hc_le_dist μ x₀ hμ_cm
      ((ε : ℝ) / 4) hε4
  obtain ⟨S, hS, hSfin, hScost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_cont hc_le_dist ν x₀ hν_cm
      ((ε : ℝ) / 4) hε4
  haveI : IsProbabilityMeasure (Measure.map T μ) := Measure.isProbabilityMeasure_map hT.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map S ν) := Measure.isProbabilityMeasure_map hS.aemeasurable
  set q : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / 4) with hq
  -- triangle through the two approximants
  have htri1 := wassersteinCost_coupling_triangle c hc_nonneg hc_triangle hc_cont.measurable
    μ ν (Measure.map T μ)
  have htri2 := wassersteinCost_coupling_triangle c hc_nonneg hc_triangle hc_cont.measurable
    (Measure.map T μ) ν (Measure.map S ν)
  -- the two outer transport terms are ≤ q
  have hμμ' : wassersteinCost_coupling c μ (Measure.map T μ) ≤ q :=
    (wassersteinCost_coupling_map_le c hc_cont μ T hT).trans hTcost
  have hν'ν : wassersteinCost_coupling c (Measure.map S ν) ν ≤ q := by
    rw [wassersteinCost_coupling_comm c hc_symm hc_cont.measurable (Measure.map S ν) ν]
    exact (wassersteinCost_coupling_map_le c hc_cont ν S hS).trans hScost
  -- the middle: finite KR duality, then dual stability, then bound the two costs by q
  have hmid : wassersteinCost_coupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c μ ν + q + q :=
    (wassersteinCost_coupling_le_dual_of_finiteRange c hc_nonneg hc_self hc_symm hc_triangle
        μ ν T S hT hS hTfin hSfin).trans
      ((wassersteinCost_dual_le_add_map c hc_nonneg hc_self hc_symm hc_cont μ ν T S hT hS
          x₀ hμ_cm hν_cm).trans
        (add_le_add (add_le_add le_rfl hTcost) hScost))
  -- 4q = ofReal ε = ↑ε
  have hq4 : q + q + q + q = (ε : ℝ≥0∞) := by
    have h4 : q + q + q + q
        = ENNReal.ofReal ((ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4) := by
      rw [hq, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [h4, show (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 = (ε : ℝ) from by ring,
      ENNReal.ofReal_coe_nnreal]
  calc wassersteinCost_coupling c μ ν
      ≤ wassersteinCost_coupling c μ (Measure.map T μ)
          + wassersteinCost_coupling c (Measure.map T μ) ν := htri1
    _ ≤ q + (wassersteinCost_coupling c (Measure.map T μ) (Measure.map S ν)
          + wassersteinCost_coupling c (Measure.map S ν) ν) := add_le_add hμμ' htri2
    _ ≤ q + ((wassersteinCost c μ ν + q + q) + q) := add_le_add le_rfl (add_le_add hmid hν'ν)
    _ = wassersteinCost c μ ν + (q + q + q + q) := by ring
    _ = wassersteinCost c μ ν + (ε : ℝ≥0∞) := by rw [hq4]

/-- KR duality at `c = dist`: `wasserstein1 = wasserstein1_coupling`.  Sorry-free
corollary of Foundation B (the hard-direction inequality `foundationB_coupling_le_dual`)
+ the easy direction `wasserstein1_le_wasserstein1_coupling`. -/
theorem wasserstein1_eq_coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_fm : Integrable (fun y => dist y x₀) μ)
    (hν_fm : Integrable (fun y => dist y x₀) ν) :
    wasserstein1 μ ν = wasserstein1_coupling μ ν := by
  refine le_antisymm (wasserstein1_le_wasserstein1_coupling μ ν x₀ hμ_fm hν_fm) ?_
  rw [wasserstein1_coupling_eq]
  exact foundationB_coupling_le_dual (fun x y => dist x y) (fun _ _ => dist_nonneg)
    (fun x => dist_self x) (fun x y => dist_comm x y) (fun x y z => dist_triangle x y z)
    (continuous_fst.dist continuous_snd) (fun x y => le_refl (dist x y)) μ ν x₀ hμ_fm hν_fm

/-! ## Pushforward of couplings

The lemmas below are the "reusable pieces" needed for the dobrushin chain
once the easy direction of KR is available.  They build the bridge from
coupling-based bounds on initial measures (`μ`, `ν`) to coupling-based
bounds on pushed-forward measures (`Φ_# μ`, `Ψ_# ν`), which is how the
Dobrushin proof connects characteristic flows back to W₁ growth.
-/

/-- Pushforward of a coupling under a pair of measurable maps is a coupling
of the pushed-forward marginals.  Pure measure theory; no metric structure
needed.

This is the *generic α/β shape* — the codomain types `α'`, `β'` can be
arbitrary measurable spaces, not necessarily equal to the domain.  This
matters because the characteristic-flow application uses
`(Prod.map Φ Ψ)` with `Φ` and `Ψ` distinct maps; the diagonal
case `α' = α, Φ = Ψ` is a specialization. -/
lemma IsCoupling.map {α β α' β' : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β']
    {π : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (hπ : IsCoupling π μ ν)
    (Φ : α → α') (Ψ : β → β')
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    IsCoupling (Measure.map (Prod.map Φ Ψ) π) (Measure.map Φ μ) (Measure.map Ψ ν) := by
  refine ⟨?_, ?_⟩
  · -- fst marginal: Measure.map Prod.fst (Measure.map (Prod.map Φ Ψ) π) = Measure.map Φ μ
    have h_comp_fst : Prod.fst ∘ Prod.map Φ Ψ = Φ ∘ Prod.fst := by funext; rfl
    rw [Measure.map_map measurable_fst (hΦ.prodMap hΨ), h_comp_fst,
        ← Measure.map_map hΦ measurable_fst, hπ.1]
  · -- snd marginal: Measure.map Prod.snd (Measure.map (Prod.map Φ Ψ) π) = Measure.map Ψ ν
    have h_comp_snd : Prod.snd ∘ Prod.map Φ Ψ = Ψ ∘ Prod.snd := by funext; rfl
    rw [Measure.map_map measurable_snd (hΦ.prodMap hΨ), h_comp_snd,
        ← Measure.map_map hΨ measurable_snd, hπ.2]

/-- The dual-formula `wasserstein1` of the pushed-forward measures is bounded
above by the infimum over couplings of the original measures of the
pushed-forward cost.  This is the "iInf trick":

  wasserstein1 (Φ_# μ) (Ψ_# ν)
    ≤ wasserstein1_coupling (Φ_# μ) (Ψ_# ν)            (KR easy)
    = ⨅ π' (coupling of Φ_# μ, Ψ_# ν), ∫⁻ edist dπ'
    ≤ ⨅ π  (coupling of μ, ν), ∫⁻ edist (Φ z.1, Ψ z.2) dπ   (push couplings via IsCoupling.map)

Used in the dobrushin proof: applied with `Φ`, `Ψ` the characteristic
flows of `f`, `g` at time `t` (or the difference flow), this turns a
W₁-bound on `(f_t, g_t)` into a coupling-cost bound on `(f_0, g_0)`
that can be controlled by Gronwall. -/
lemma wasserstein1_pushforward_le_iInf
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (Φ Ψ : α → α) (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hΦμ_prob : IsProbabilityMeasure (Measure.map Φ μ))
    (hΨν_prob : IsProbabilityMeasure (Measure.map Ψ ν))
    (hΦμ_fm : Integrable (fun y => dist y x₀) (Measure.map Φ μ))
    (hΨν_fm : Integrable (fun y => dist y x₀) (Measure.map Ψ ν)) :
    wasserstein1 (Measure.map Φ μ) (Measure.map Ψ ν) ≤
      ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
        ∫⁻ z, edist (Φ z.1) (Ψ z.2) ∂π := by
  haveI := hΦμ_prob
  haveI := hΨν_prob
  -- Step 1: KR easy applied to (Φ_# μ, Ψ_# ν).
  have h_kr := wasserstein1_le_wasserstein1_coupling
    (Measure.map Φ μ) (Measure.map Ψ ν) x₀ hΦμ_fm hΨν_fm
  refine le_trans h_kr ?_
  -- Step 2: bound wasserstein1_coupling via a specific pushed-forward coupling.
  refine le_iInf fun π => le_iInf fun hπ => ?_
  -- The pushed-forward coupling IS a coupling of (Φ_# μ, Ψ_# ν) by IsCoupling.map.
  have hπ_pushed : IsCoupling (Measure.map (Prod.map Φ Ψ) π)
                              (Measure.map Φ μ) (Measure.map Ψ ν) :=
    hπ.map Φ Ψ hΦ hΨ
  -- So wasserstein1_coupling ≤ ∫⁻ edist d(pushed-forward π).
  have h_inf : wasserstein1_coupling (Measure.map Φ μ) (Measure.map Ψ ν) ≤
      ∫⁻ z, edist z.1 z.2 ∂(Measure.map (Prod.map Φ Ψ) π) := by
    refine iInf_le_of_le (Measure.map (Prod.map Φ Ψ) π) ?_
    exact iInf_le _ hπ_pushed
  refine le_trans h_inf ?_
  -- Step 3: pushforward of the lintegral.
  -- ∫⁻ z, edist z.1 z.2 ∂(Φ × Ψ)_# π = ∫⁻ z, edist (Φ z.1) (Ψ z.2) ∂π
  rw [lintegral_map (measurable_fst.edist measurable_snd) (hΦ.prodMap hΨ)]
  -- After rw: ∫⁻ z, edist (Prod.map Φ Ψ z).1 (Prod.map Φ Ψ z).2 ∂π ≤ ∫⁻ z, edist (Φ z.1) (Ψ z.2) ∂π
  -- (Prod.map Φ Ψ z).1 = Φ z.1 and .2 = Ψ z.2 by definition; the integrals are pointwise equal.
  rfl

end Vlasov
