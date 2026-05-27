/-
Characteristic flow for the Vlasov ODE + Lagrangian-Eulerian equivalence.

This file builds on `Vlasov/OT/Coupling.lean` and provides the flow-side
infrastructure needed to close the two flow-dependent placeholders in
`Vlasov/Basic.lean`:

  - `MathlibTODO_W1ContOn_uscNarrow`   (USC of W₁ along Vlasov flows)
  - `MathlibTODO_derivBound`           (right-derivative Gronwall condition)

Once these exports are in place, each placeholder becomes a ~20-line
composition: take an ε-optimal coupling at the base time, push forward
via the joint characteristic flows from `exists_vlasov_characteristicFlow`,
apply `wasserstein1_pushforward_le_iInf` from Coupling.lean to bound W₁
by the pushed-forward cost, then control the cost via Gronwall on the
pointwise ODE.  The LSC placeholder remains independent of this file
(it is the dual-formula + narrow-continuity approximation argument).

**Mathlib-upstream targeting note.**  Stages A (position-Lipschitz of
convolution against a probability measure) and B (Picard-Lindelöf
wrapper for a phase-space ODE) are domain-independent and Mathlib-
worthy.  When eventually contributed upstream, they live alongside
the OT chapter in `Mathlib/MeasureTheory/Wasserstein/CharacteristicFlow.lean`
or split between `Mathlib/Analysis/ODE/` and the OT chapter.  Stage C
(the Lagrangian → Eulerian equivalence: pushforward of `f₀` under the
characteristic flow satisfies the weak Vlasov equation) is the
genuine project responsibility — a Fubini + measure-map +
differentiation-under-integral check that is not in Mathlib.

See `formalize/DESIGN.md` for the overall design.
-/

import Vlasov.Basic
import Vlasov.OT.Coupling

namespace Vlasov

open MeasureTheory ENNReal

/-! ## Stage A — Vlasov velocity field and its Lipschitz lemma -/

/-- The Vlasov phase-space vector field:
`b_t(x, v) := (v, −(∇W ∗ ρ_t)(x))`.

Note that the first component is the identity in `v` (the position
ODE `ẋ = v`) and the second component is the mean-field force
`−∇W ∗ ρ_t` evaluated at `x` (the velocity ODE `v̇ = −(∇W ∗ ρ)(x)`).
-/
noncomputable def vlasovVectorField
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (t : ℝ) (z : PhaseSpace d) : PhaseSpace d :=
  (z.2, -(convolveFunctionMeasure gradW (ρ t) z.1))

/-- Position-side Lipschitz of the convolution `∇W ∗ ρ`.
For `gradW` L-Lipschitz and `ρ` a probability measure with finite
first moment (which guarantees integrability of the kernel), the map
`x ↦ (∇W ∗ ρ)(x)` is L-Lipschitz.

Proof sketch: by `LipschitzWith.dist_le_mul` applied pointwise to
`gradW`, then integration over the probability measure `ρ`:
  ‖∫ y, gradW(x−y) ∂ρ − ∫ y, gradW(x'−y) ∂ρ‖
    = ‖∫ y, (gradW(x−y) − gradW(x'−y)) ∂ρ‖
    ≤ ∫ y, ‖gradW(x−y) − gradW(x'−y)‖ ∂ρ
    ≤ ∫ y, L · ‖x − x'‖ ∂ρ
    = L · ‖x − x'‖ · ρ(univ)
    = L · ‖x − x'‖   (probability measure).

The integrability hypotheses on `gradW(x − ·)` for two distinct `x`s
are needed for `integral_sub` and `norm_integral_le_integral_norm`
to fire.  At the dobrushin call site these follow from finite first
moment of `ρ` + Lipschitz growth of `gradW`. -/
lemma convolveFunctionMeasure_lipschitz_in_x
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ) :
    LipschitzWith L (fun x => convolveFunctionMeasure gradW ρ x) := by
  refine LipschitzWith.of_dist_le_mul (fun x x' => ?_)
  unfold convolveFunctionMeasure
  rw [dist_eq_norm, ← integral_sub (h_int x) (h_int x')]
  -- Pointwise bound: ‖gradW(x − y) − gradW(x' − y)‖ ≤ L · ‖x − x'‖
  have h_pt : ∀ y, ‖gradW (x - y) - gradW (x' - y)‖ ≤ (L : ℝ) * ‖x - x'‖ := fun y => by
    have h_sub : (x - y) - (x' - y) = x - x' := by
      rw [sub_sub_sub_cancel_right]
    have := hL.dist_le_mul (x - y) (x' - y)
    rw [dist_eq_norm, dist_eq_norm, h_sub] at this
    exact this
  -- Integrability of the pointwise bound function (a constant).
  have h_bound_int : Integrable (fun _ : PhysSpace d => (L : ℝ) * ‖x - x'‖) ρ :=
    integrable_const _
  -- Integrability of the norm of the difference, via mono'.
  have h_norm_int : Integrable (fun y => ‖gradW (x - y) - gradW (x' - y)‖) ρ :=
    Integrable.mono' h_bound_int ((h_int x).sub (h_int x')).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact h_pt y)
  calc ‖∫ y, gradW (x - y) - gradW (x' - y) ∂ρ‖
      ≤ ∫ y, ‖gradW (x - y) - gradW (x' - y)‖ ∂ρ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _, (L : ℝ) * ‖x - x'‖ ∂ρ :=
        integral_mono_ae h_norm_int h_bound_int (Filter.Eventually.of_forall h_pt)
    _ = (L : ℝ) * ‖x - x'‖ := by
        simp [integral_const, measureReal_def, measure_univ]

/-! ## Stage B — Characteristic flow existence (Picard-Lindelöf wrapper)

This stage wraps Mathlib's parametric Picard-Lindelöf theorem to
extract a characteristic flow `(charX, charV)` for the Vlasov ODE.
The four `IsPicardLindelof` hypotheses (Lipschitz-on-ball,
continuous-in-time, norm bound, contraction) are derived from
Stage A's `convolveFunctionMeasure_lipschitz_in_x`, plus
narrow-continuity of the spatial-marginal curve `ρ`, plus a uniform
norm bound from the finite-mass assumption.

The contraction condition `L · max(tmax − t₀, t₀ − tmin) ≤ a − r`
pins down the local time-interval size relative to the ball radius.
For the dobrushin application we work on a finite interval `[0, T]`;
the existence theorem is parametrised by `T` and produces a flow
on `Set.Icc 0 T` (extending the local flow by stitching overlapping
windows; technically a separate iteration argument, deferred to
the proof body).

Status: the exact Mathlib invocation pattern of
`exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`
(constructing the `IsPicardLindelof` record from project hypotheses)
is intricate enough to warrant its own focused session.  The
theorem statement is committed here so downstream callers (the USC
and derivBound closures) can write against the right export shape;
the proof body is a documented sorry. -/

/-- Existence of a characteristic flow for the Vlasov ODE.

Given a fixed spatial-marginal curve `ρ : ℝ → Measure (PhysSpace d)`
that is continuous in time (the appropriate narrow / W₁-topology),
the position-velocity ODE
  `Ẋ(t, z) = V(t, z)`,
  `V̇(t, z) = −(∇W ∗ ρ_t)(X(t, z))`
admits a flow `(charX, charV) : ℝ → PhaseSpace d → PhysSpace d × PhysSpace d`
with the prescribed initial conditions.

This is the wrapper around Mathlib's parametric Picard-Lindelöf,
with the Lipschitz hypothesis on the velocity field supplied by
Stage A's `convolveFunctionMeasure_lipschitz_in_x`. -/
theorem exists_vlasov_characteristicFlow
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    -- Narrow / W₁-continuity of the spatial-marginal curve.  We state it
    -- abstractly as continuity of `t ↦ (∇W ∗ ρ_t)(x)` for each fixed `x`
    -- (this is what `IsPicardLindelof.continuousOn` requires).  At call
    -- sites this follows from the analogous `convolveLipschitz_inner_bound`
    -- + narrow continuity of `t ↦ ρ_t` in W₁.
    (hρ_cont : ∀ x : PhysSpace d, Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlow gradW ρ charX charV := by
  -- Construction sketch (deferred):
  --   1. For each compact sub-interval, build an IsPicardLindelof term
  --      with Lipschitz constant 1 + L (velocity-side identity has
  --      Lipschitz constant 1; position-side uses Stage A).
  --   2. Invoke Mathlib's exists_forall_mem_closedBall_..._hasDerivWithinAt
  --      to get a local flow.
  --   3. Extend by stitching overlapping windows of size ≤ a / (1 + L).
  --   4. Project to (charX, charV) via Prod.fst / Prod.snd of the flow.
  sorry

/-! ## Stage C — Lagrangian → Eulerian: pushforward solves weak Vlasov

This is the genuine project responsibility: showing that the pushforward
of `f_0` under a characteristic flow satisfies the distributional
Vlasov equation, i.e. matches `IsVlasovSolution`.

Proof strategy (deferred to a focused session):
1. Unfold `IsVlasovSolution`: for every smooth compactly-supported
   test function `φ`, the curve `t ↦ ∫ φ d(pushforward f₀)` satisfies
   the weak ODE shape from `WeakEvolutionEq`.
2. Change variables via `integral_map` (already used in Coupling.lean):
   `∫ φ d(map flow f₀) = ∫ (φ ∘ flow) df₀`.
3. Differentiate under the integral sign: `HasDerivAt` from the
   characteristic flow's ODE hypothesis (in `IsCharacteristicFlow`)
   plus the chain rule on `φ` gives the time-derivative formula.
4. The resulting expression matches `WeakEvolutionEq`'s RHS exactly
   because the flow's ODE was `(charV, −(∇W ∗ ρ)(charX))` and the
   dot-product chain rule on `φ(charX, charV)` produces precisely
   `⟨charV, ∇_x φ⟩ − ⟨(∇W ∗ ρ)(charX), ∇_v φ⟩`.

The differentiation-under-integral swap is the technical heart;
Mathlib's `hasDerivAt_integral_of_dominated_loc_of_lip` (or near-
equivalent) handles it, but the dominated-integrable hypothesis
threading is substantial. -/

/-- The Lagrangian → Eulerian equivalence: the pushforward of `f₀`
under a characteristic flow satisfies the weak Vlasov equation.

This connects the ODE side (`IsCharacteristicFlow`, with its
pointwise `HasDerivAt`) to the PDE side (`IsVlasovSolution`, with
its weak-evolution `WeakEvolutionEq` formulation), closing the
Lagrangian-Eulerian loop that Mathlib does not provide. -/
theorem vlasovSolutionViaPushforward_isVlasovSolution
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (hflow : IsCharacteristicFlow gradW
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              charX charV)
    (hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))) :
    IsVlasovSolution gradW (vlasovSolutionViaPushforward charX charV f₀) := by
  -- Unfold IsVlasovSolution; for each test function φ, prove WeakEvolutionEq.
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
  -- WeakEvolutionEq: ∀ t, HasDerivAt (fun s => ∫ φ d(pushforward f₀ at s)) (RHS) t.
  intro t
  -- Step 1: integral_map turns ∫ φ d(pushforward) into ∫ (φ ∘ flow) df₀.
  -- Step 2: differentiation under the integral, using HasDerivAt from hflow's ODE.
  -- Step 3: chain rule on φ produces the WeakEvolutionEq RHS.
  -- Step 4: handle the explicit-formula derivative match.
  sorry

/-! ## Integration smoke test (Stage D follow-up)

A small theorem demonstrating that the three OT files compose: given
two characteristic flows on the same initial probability measures
with finite first moment, the Wasserstein-1 distance between the
pushed-forward measures at time `t` is bounded by the infimum (over
couplings of the *initial* measures) of the pushed-forward edist
cost.

This is **exactly the shape** the USC and derivBound closures in
`Vlasov/Basic.lean` need: it turns a coupling at time 0 into a
W₁-upper-bound at time t.  The Gronwall-on-the-joint-ODE step (which
controls the cost growth) is the next piece — orthogonal to OT,
sits in the dynamics layer.

The theorem is a direct application of `wasserstein1_pushforward_le_iInf`
from `Coupling.lean`; the integration test confirms the type chain
composes correctly when the maps are characteristic flows. -/

theorem wasserstein1_lagrangian_pushforward_bound
    {d : ℕ} [NeZero d]
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ g₀ : Measure (PhaseSpace d))
    [IsProbabilityMeasure f₀] [IsProbabilityMeasure g₀]
    (t : ℝ)
    (h_meas_f : Measurable (fun z : PhaseSpace d => (charX_f t z, charV_f t z)))
    (h_meas_g : Measurable (fun z : PhaseSpace d => (charX_g t z, charV_g t z)))
    (h_fmpr_f : IsProbabilityMeasure
                (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀))
    (h_fmpr_g : IsProbabilityMeasure
                (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀))
    (x₀ : PhaseSpace d)
    (h_fm_f : Integrable (fun y : PhaseSpace d => dist y x₀)
              (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀))
    (h_fm_g : Integrable (fun y : PhaseSpace d => dist y x₀)
              (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀)) :
    wasserstein1
      (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀)
      (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀) ≤
      ⨅ (π : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π f₀ g₀),
        ∫⁻ z, edist (charX_f t z.1, charV_f t z.1)
                    (charX_g t z.2, charV_g t z.2) ∂π :=
  wasserstein1_pushforward_le_iInf
    (fun z => (charX_f t z, charV_f t z))
    (fun z => (charX_g t z, charV_g t z))
    h_meas_f h_meas_g f₀ g₀ x₀ h_fmpr_f h_fmpr_g h_fm_f h_fm_g

end Vlasov
