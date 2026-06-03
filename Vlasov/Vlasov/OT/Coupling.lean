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

open MeasureTheory ENNReal

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
