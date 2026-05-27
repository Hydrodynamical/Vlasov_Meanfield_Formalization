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
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_fm : Integrable (fun y => dist y x₀) μ)
    (hν_fm : Integrable (fun y => dist y x₀) ν) :
    wasserstein1 μ ν ≤ wasserstein1_coupling μ ν := by
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  refine le_iInf fun π => le_iInf fun hπ => ?_
  -- Goal: ENNReal.ofReal (∫φ dμ - ∫φ dν) ≤ ∫⁻ z, edist z.1 z.2 ∂π
  -- Case 1: the cost is ⊤ → trivially bound by ⊤.
  by_cases h_top : ∫⁻ z, edist z.1 z.2 ∂π = ⊤
  · rw [h_top]; exact le_top
  -- Case 2: finite cost. Substantive proof.  The skeleton below maps each
  -- stage to a Mathlib API call but the integrability/measurability threading
  -- requires careful attention to instance synthesis and lemma-name churn.
  -- Initial draft attempted Stages 1+2 (π is probability measure; dist is
  -- integrable from h_top); both ran into Mathlib-API friction
  -- (AEStronglyMeasurable for continuous on PseudoMetric without
  -- SecondCountableTopology; HasFiniteIntegral.intro / hasFiniteIntegral_def
  -- naming).  Full proof deferred to a follow-up session.
  sorry

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
