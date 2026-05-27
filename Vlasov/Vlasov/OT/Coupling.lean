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

/-- The coupling-based Wasserstein-1 distance: infimum of `∫ dist(x,y) dπ(x,y)`
over all couplings `π` of `(μ, ν)`.  This is the Monge-Kantorovich definition,
to be compared with the dual definition `wasserstein1` (in `Vlasov/Basic.lean`)
via Kantorovich-Rubinstein duality.

Returns `⊤` if no coupling exists (a degenerate case for non-probability or
incompatible-mass measures). -/
noncomputable def wasserstein1_coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ENNReal :=
  ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
    ENNReal.ofReal (∫ z, dist z.1 z.2 ∂π)

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

(The finite-moment / probability hypotheses ensure all the integrals are
well-defined and the integral_map change-of-variables fires cleanly.) -/
theorem wasserstein1_le_wasserstein1_coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wasserstein1 μ ν ≤ wasserstein1_coupling μ ν := by
  sorry

end Vlasov
