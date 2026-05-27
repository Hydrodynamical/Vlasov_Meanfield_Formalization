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

This sub-section first establishes the **global Lipschitz constant**
for `vlasovVectorField` (a direct composition of Stage A's
`convolveFunctionMeasure_lipschitz_in_x` with the 1-Lipschitz
identity on the velocity coordinate, combined via `LipschitzWith.prodMk`).
The global Lipschitz immediately restricts to any closed ball,
giving the first of the four `IsPicardLindelof` fields.

Status: the constructor `vlasovVectorField_lipschitzWith` is closed.
The full `exists_vlasov_characteristicFlow` still has a documented
sorry — the open work is (a) packaging the global norm bound
(`vlasovVectorField_norm_le`) into a `LipschitzOnWith`-restricted-
to-ball with a chosen radius, (b) extracting the in-time
continuity from `hρ_cont`, (c) selecting `(a, r, L, K)` so the
contraction condition `L · (tmax - t₀) ≤ a - r` holds on a small
window, (d) invoking
`exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`,
(e) bridging `HasDerivWithinAt` ↔ `HasDerivAt` for interior times,
and (f) stitching overlapping windows to cover `[0, T]`.

Each of (a)-(f) is intricate but routine.  Downstream callers can
already write against the export shape; closing (a)-(f) is the
follow-up session. -/

/-- Localized variant of `IsCharacteristicFlow` from `Basic.lean`:
the same initial condition + position/velocity ODEs, but quantified
over a chosen time set `s_t : Set ℝ` and initial-condition set
`s_z : Set (PhaseSpace d)`.

The global `IsCharacteristicFlow gradW ρ charX charV` is the
specialisation `IsCharacteristicFlowOn ... Set.univ Set.univ`
(modulo the unconditional init clause). -/
def IsCharacteristicFlowOn
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (s_t : Set ℝ) (s_z : Set (PhaseSpace d)) : Prop :=
  (∀ z ∈ s_z, charX 0 z = z.1 ∧ charV 0 z = z.2) ∧
  (∀ t ∈ s_t, ∀ z ∈ s_z, HasDerivAt (fun s => charX s z) (charV t z) t) ∧
  (∀ t ∈ s_t, ∀ z ∈ s_z, HasDerivAt (fun s => charV s z)
      (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)

/-- Monotonicity of `IsCharacteristicFlowOn` in both the time set and the
initial-condition set.  Used at the end of the global existence theorem
to restrict a flow produced on `Ioo 0 (N·δ)` (covering all of `[0, T]`)
down to `Ioo 0 T`. -/
lemma IsCharacteristicFlowOn.mono
    {d : ℕ} [NeZero d]
    {gradW : PhysSpace d → PhysSpace d}
    {ρ : ℝ → Measure (PhysSpace d)}
    {charX charV : ℝ → PhaseSpace d → PhysSpace d}
    {s_t s_t' : Set ℝ} {s_z s_z' : Set (PhaseSpace d)}
    (h : IsCharacteristicFlowOn gradW ρ charX charV s_t s_z)
    (hs_t : s_t' ⊆ s_t) (hs_z : s_z' ⊆ s_z) :
    IsCharacteristicFlowOn gradW ρ charX charV s_t' s_z' := by
  refine ⟨fun z hz => h.1 z (hs_z hz), fun t ht z hz => ?_, fun t ht z hz => ?_⟩
  · exact h.2.1 t (hs_t ht) z (hs_z hz)
  · exact h.2.2 t (hs_t ht) z (hs_z hz)

/-- Global Lipschitz constant for the Vlasov phase-space vector field.
`b_t(x, v) = (v, -(∇W ∗ ρ_t)(x))` is `max(1, L)`-Lipschitz when
`gradW` is `L`-Lipschitz: the velocity-side projection `(x, v) ↦ v`
is 1-Lipschitz (`LipschitzWith.prod_snd`), and the force-side map
`(x, v) ↦ -(∇W ∗ ρ_t)(x)` is `L`-Lipschitz (compose Stage A's
`convolveFunctionMeasure_lipschitz_in_x` with `Neg.neg` and
`Prod.fst`, both 1-Lipschitz).  Combining the two via
`LipschitzWith.prodMk` yields `max(1, L)` on the product. -/
lemma vlasovVectorField_lipschitzWith
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (t : ℝ) :
    LipschitzWith (max 1 L) (vlasovVectorField gradW ρ t) := by
  -- Force-side `x ↦ (∇W ∗ ρ_t)(x)` is `L`-Lipschitz (Stage A).
  have h_conv : LipschitzWith L
      (fun x : PhysSpace d => convolveFunctionMeasure gradW (ρ t) x) :=
    convolveFunctionMeasure_lipschitz_in_x gradW L hL (ρ t) (h_int t)
  -- Negate (`Neg.neg` is 1-Lipschitz): `x ↦ -(∇W ∗ ρ_t)(x)` is still `L`-Lipschitz.
  have h_neg_conv : LipschitzWith L
      (fun x : PhysSpace d => -convolveFunctionMeasure gradW (ρ t) x) := by
    simpa using LipschitzWith.id.neg.comp h_conv
  -- Compose with `Prod.fst` (1-Lipschitz): `z ↦ -(∇W ∗ ρ_t)(z.1)` is `L`-Lipschitz.
  have h_force : LipschitzWith L
      (fun z : PhaseSpace d => -convolveFunctionMeasure gradW (ρ t) z.1) := by
    simpa using h_neg_conv.comp
      (LipschitzWith.prod_fst (α := PhysSpace d) (β := PhysSpace d))
  -- Combine velocity-side projection (1-Lipschitz) with force-side (L-Lipschitz).
  exact (LipschitzWith.prod_snd (α := PhysSpace d) (β := PhysSpace d)).prodMk h_force

/-- Pointwise norm bound for the Vlasov phase-space vector field.
`‖b_t(x, v)‖ ≤ max(‖v‖, ‖(∇W ∗ ρ_t)(x)‖)` for the product `max`-norm
on `PhaseSpace d = PhysSpace d × PhysSpace d`.

This is the decomposition used to derive `IsPicardLindelof.norm_le`
once a uniform bound `M` for `‖(∇W ∗ ρ_t)(x)‖` on a closed ball is
known (e.g. from finite-first-moment + Lipschitz growth of `gradW`). -/
lemma vlasovVectorField_norm_le
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d)) (t : ℝ) (z : PhaseSpace d) :
    ‖vlasovVectorField gradW ρ t z‖ ≤
      max ‖z.2‖ ‖convolveFunctionMeasure gradW (ρ t) z.1‖ := by
  unfold vlasovVectorField
  -- Prod norm is the max of component norms; neg preserves norm.
  simp [Prod.norm_def, norm_neg]

/-- **Local-flow** existence for the Vlasov ODE.

Wraps Mathlib's parametric Picard-Lindelöf
(`IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`)
into a `HasDerivAt`-on-`Ioo`-shaped characteristic flow.  The result
holds for initial conditions inside `closedBall z₀ (a/2)` and for
times in `Ioo 0 δ` where `δ` is a Picard-derived constant.

The new hypothesis `hbound` (uniform norm bound on the convolution
force on a slightly larger ball, over `[0, 1]`) is the genuine input
the Picard wrapper needs: the contraction condition + the `norm_le`
field of `IsPicardLindelof` both require a global bound on `‖b_t‖`.

The global existence form `exists_vlasov_characteristicFlow` (below)
is the stitched version on `[0, T]`; it is currently sorry'd and
will iterate this local theorem on overlapping windows using
`ODE_solution_unique` to glue. -/
theorem exists_vlasov_characteristicFlow_local
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    -- Local-flow data: the basepoint `z₀`, the ball radius `a`, and a
    -- uniform force bound `M` on `closedBall z₀.1 (3a/2)` over `[0,1]`.
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
              ∀ x ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 δ) (Metric.closedBall z₀ ((a : ℝ) / 2)) := by
  classical
  -- IsPicardLindelof parameter choices.
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := ‖z₀.2‖₊ + a + M with hL_pl_def
  -- δ chosen to satisfy the contraction L_pl · δ ≤ a − r_pl = a/2.
  set δ : ℝ := min 1 ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min one_pos h_ratio_pos
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := min_le_right _ _
  -- t₀ ∈ Icc 0 δ.
  let t₀ : Set.Icc (0 : ℝ) δ := ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt hδ_pos⟩⟩
  -- Assemble IsPicardLindelof.
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ z₀ a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (a) lipschitzOnWith via Stage A's vlasovVectorField_lipschitzWith.
      intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · -- (b) continuousOn: velocity component constant in t, force continuous by hρ_cont.
      intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · -- (c) norm_le.
      intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x z₀ ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - z₀‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - z₀.2‖ ≤ ‖x - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖z₀.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - z₀.2) + z₀.2‖ ≤ ‖x.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 z₀.1 ≤ dist x z₀ := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2) := by
        have hx1d : dist x.1 z₀.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have : dist x.1 z₀.1 ≤ 3 * (a : ℝ) / 2 := by
          have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
          linarith
        exact this
      have h_t_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ht.1, le_trans ht.2 hδ_le_one⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = ‖z₀.2‖ + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add, coe_nnnorm]
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M]
            · linarith [norm_nonneg z₀.2, NNReal.coe_nonneg a]
    · -- (d) mul_max_le: L_pl · max(δ − 0, 0 − 0) = L_pl · δ ≤ a − a/2 = a/2.
      show (L_pl : ℝ) * max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = 0 := rfl
      simp only [ht₀_eq, sub_zero, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]
        ring
      rw [h_a_minus_r]
      -- L_pl * δ ≤ a/2 since δ ≤ (a/2)/(L_pl+1) and L_pl ≤ L_pl + 1.
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  -- Invoke headline Picard-Lindelöf.
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  -- α : PhaseSpace d → ℝ → PhaseSpace d.  Define charX, charV by projection.
  refine ⟨δ, hδ_pos, fun t z => (α z t).1, fun t z => (α z t).2, ?_, ?_, ?_⟩
  · -- Initial condition: α z 0 = z gives both component equalities.
    intro z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢
      rw [hreq]; exact hz
    have h_init : α z (t₀ : ℝ) = z := (hα z hz_in_r).1
    have ht₀_eq : (t₀ : ℝ) = 0 := rfl
    rw [ht₀_eq] at h_init
    refine ⟨?_, ?_⟩
    · change (α z 0).1 = z.1; rw [h_init]
    · change (α z 0).2 = z.2; rw [h_init]
  · -- Position ODE: HasDerivAt (charX · z) (charV t z) t.
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [this]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) δ ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).1)
        (vlasovVectorField gradW ρ t (α z t)).1 t :=
      (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj
  · -- Velocity ODE: HasDerivAt (charV · z) (−(∇W∗ρ)(charX t z)) t.
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [this]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) δ ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).2)
        (vlasovVectorField gradW ρ t (α z t)).2 t :=
      (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj

/-- **Global** characteristic-flow existence on `[0, T]`.

This is the eventual N-window stitching target: iterate the
two-window combine (`exists_vlasov_characteristicFlow_twoWindow`
below) on `⌈T/δ⌉` windows and glue via `ODE_solution_unique`
(`Mathlib/Analysis/ODE/Gronwall.lean:379`) at each interior join.

The conclusion is `IsCharacteristicFlowOn ... (Ioo 0 T) ...` rather
than the unconstrained `IsCharacteristicFlow` (which would require
`HasDerivAt` on all of `ℝ`, impossible to produce from local-on-`Icc`
Picard solutions).  The hypothesis `hR` enforces that the global
position-ball radius `R` covers the a-priori reachable set —
`(3a/2 + M·T)` is the loose bound; tighter forms work too.

Currently sorry'd; closing it is the next follow-up session. -/
theorem exists_vlasov_characteristicFlow
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal) (T : ℝ) (hT : 0 ≤ T)
    -- R is the global position-ball radius for `hbound`.  The quadratic-in-T
    -- form below accounts for the a priori position drift of a trajectory
    -- starting in `closedBall z₀ (a/2)`: at time `t ∈ [0, T]`, position is
    -- at distance `≤ a/2 + (‖z₀.2‖ + a/2)·t + M·t²/2` from `z₀.1`.  Adding
    -- the per-window safety margin `3a/2` (so each window's local
    -- `closedBall w.1 (3a/2)` is contained in `closedBall z₀.1 R`), the
    -- worst-case requirement is the quadratic form below.
    (R : NNReal)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 / 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 T) (Metric.closedBall z₀ ((a : ℝ) / 2)) := by
  classical
  -- ============================================================
  -- Parameter setup (uniform across all windows and initial z).
  -- ============================================================
  set V_max : NNReal :=
    ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T with hV_max_def
  set δ_uniform : ℝ :=
    min 1 ((a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < ((V_max + a + M : NNReal) : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1) := by
    positivity
  have hδ_pos : (0 : ℝ) < δ_uniform := lt_min one_pos h_ratio_pos
  -- N := number of windows of width δ_uniform needed to cover [0, T].
  set N : ℕ := ⌈T / δ_uniform⌉₊ with hN_def
  have hN_cover : T ≤ (N : ℝ) * δ_uniform := by
    rcases eq_or_lt_of_le hT with hT_eq | hT_pos
    · -- T = 0 case.
      rw [← hT_eq]; positivity
    · have : T / δ_uniform ≤ (N : ℝ) := Nat.le_ceil _
      have h_δ_ne : δ_uniform ≠ 0 := ne_of_gt hδ_pos
      calc T = T / δ_uniform * δ_uniform := by field_simp
        _ ≤ (N : ℝ) * δ_uniform := by
            exact mul_le_mul_of_nonneg_right this (le_of_lt hδ_pos)
  -- ============================================================
  -- Per-z induction: a curve solving the ODE on [0, N·δ_uniform].
  -- Inductive invariant (over n : ℕ):
  --   (a) the curve γ is defined and satisfies the ODE in within-
  --       derivative form on the closed interval [0, n·δ_uniform];
  --   (b) the velocity at the right endpoint is bounded by V_max
  --       (so the next `_extend_one_window` call has the V_max
  --       hypothesis satisfied);
  --   (c) the position at the right endpoint is at distance
  --       ≤ (a/2) + (‖z₀.2‖ + a/2)·(n·δ_uniform) + M·(n·δ_uniform)²/2
  --       from z₀.1, so the next window's local `closedBall w.1 (3a/2)`
  --       remains inside the global `closedBall z₀.1 R` by `hR`.
  -- ============================================================
  -- ============================================================
  -- Per-z curve existence on [0, N·δ_uniform], in HasDerivWithinAt form.
  -- This is the heart of the proof: a per-z Nat.rec construction that
  -- iterates `_extend_one_window` N times, gluing adjacent windows at
  -- their joins via `HasDerivWithinAt.union`.  The inductive invariant
  -- (within-derivative on Icc 0 (n·δ_uniform), velocity bound,
  -- position bound) is the load-bearing structure.  Body is the
  -- focused sub-sorry; the rest of the proof composes around it.
  -- ============================================================
  have h_perZ : ∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
      ∃ γ : ℝ → PhaseSpace d,
        γ 0 = z ∧
        ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform),
          HasDerivWithinAt (fun s => (γ s).1) (γ t).2
            (Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform)) t ∧
          HasDerivWithinAt (fun s => (γ s).2)
            (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
            (Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform)) t := by
    intro z hz
    -- ============================================================
    -- Strengthened inductive claim (per k ≤ N):
    --   ∃ γ_k, γ_k 0 = z ∧
    --        within-derivative ODE on Icc 0 (k·δ_uniform) ∧
    --        velocity bound ‖γ_k(k·δ).2‖ ≤ V_max ∧
    --        position bound ‖γ_k(k·δ).1 - z₀.1‖ ≤ a priori (quadratic in t).
    -- Specialise to k = N for the outer claim.
    -- ============================================================
    suffices h_strong : ∀ k : ℕ, ∃ γ : ℝ → PhaseSpace d,
        γ 0 = z ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform),
          HasDerivWithinAt (fun s => (γ s).1) (γ t).2
            (Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform)) t ∧
          HasDerivWithinAt (fun s => (γ s).2)
            (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
            (Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform)) t) ∧
        ‖(γ ((k : ℝ) * δ_uniform)).2‖ ≤ (V_max : ℝ) ∧
        ‖(γ ((k : ℝ) * δ_uniform)).1 - z₀.1‖ ≤
          (a : ℝ) / 2 + (‖z₀.2‖ + (a : ℝ) / 2) * ((k : ℝ) * δ_uniform) +
            (M : ℝ) * ((k : ℝ) * δ_uniform) ^ 2 / 2 by
      obtain ⟨γ, hγ0, hode, _, _⟩ := h_strong N
      exact ⟨γ, hγ0, hode⟩
    -- ============================================================
    -- Induction on k.
    -- ============================================================
    intro k
    induction k with
    | zero =>
      -- Base case: γ ≡ z is constant on the singleton [0, 0] = {0}.
      refine ⟨fun _ => z, rfl, ?_, ?_, ?_⟩
      · -- Within-derivative on Icc 0 0 = {0}: at t = 0 the only candidate,
        -- and HasDerivWithinAt on a singleton is vacuous for any derivative
        -- value (`HasFDerivWithinAt.of_not_accPt`).  The verbose Mathlib
        -- invocation pattern is left as a focused sub-sorry.
        intro t ht
        have ht_eq : t = 0 := le_antisymm (by simpa using ht.2) ht.1
        subst ht_eq
        refine ⟨?_, ?_⟩
        all_goals sorry
      · -- Velocity bound at t = 0: ‖z.2‖ ≤ V_max.
        have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
          rw [← dist_eq_norm]; exact hz
        have h_z2_proj : ‖z.2 - z₀.2‖ ≤ ‖z - z₀‖ := by
          rw [Prod.norm_def]; exact le_max_right _ _
        have h_z2_bound : ‖z.2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 := by
          have h1 : ‖z.2‖ = ‖(z.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
          have h2 : ‖(z.2 - z₀.2) + z₀.2‖ ≤ ‖z.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
          linarith [h_z2_proj, hdist]
        -- V_max := ‖z₀.2‖₊ + a/2 + M * T.toNNReal; coerce to ℝ and bound.
        have hMT_nn : (0 : ℝ) ≤ (M : ℝ) * (T.toNNReal : ℝ) := by positivity
        have h_V_max_coe : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T.toNNReal : ℝ) := by
          simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
        -- Goal: ‖((fun _ => z) (↑0 * δ_uniform)).2‖ ≤ (V_max : ℝ).
        show ‖z.2‖ ≤ (V_max : ℝ)
        rw [h_V_max_coe]; linarith
      · -- Position bound at t = 0: ‖z.1 - z₀.1‖ ≤ a/2.
        have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
          rw [← dist_eq_norm]; exact hz
        have h_z1_proj : ‖z.1 - z₀.1‖ ≤ ‖z - z₀‖ := by
          rw [Prod.norm_def]; exact le_max_left _ _
        -- Goal: ‖z.1 - z₀.1‖ ≤ a/2 + (‖z₀.2‖ + a/2) * (0·δ) + M * (0·δ)²/2
        --     = a/2 + 0 + 0 = a/2.
        show ‖((fun _ => z) ((0 : ℕ) * δ_uniform : ℝ)).1 - z₀.1‖ ≤ _
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
        linarith
    | succ k ih =>
      -- Inductive step: extend γ_k from [0, k·δ_uniform] to [0, (k+1)·δ_uniform]
      -- via `exists_vlasov_extend_one_window` at center γ_k (k·δ_uniform), then
      -- piecewise-glue at t = k·δ_uniform using `HasDerivWithinAt.union`.
      --
      -- Substeps:
      --   (1) Extract IH: γ_k, γ_k(0) = z, within-derivative on Icc 0 (k·δ),
      --       velocity bound, position bound.
      --   (2) Verify hbound on Icc (k·δ) ((k+1)·δ), closedBall (γ_k(k·δ)).1 (3a/2)
      --       using global hR + position bound from IH.
      --   (3) Invoke `exists_vlasov_extend_one_window` at center γ_k(k·δ),
      --       t_start := k·δ, V_max := V_max (with hV : ‖γ_k(k·δ).2‖ ≤ V_max from IH).
      --       Receive β on Ioo (k·δ) ((k+1)·δ) with β (k·δ) = γ_k(k·δ).
      --   (4) Define γ_{k+1} := Set.piecewise (Set.Iic (k·δ)) γ_k β.
      --   (5) Verify γ_{k+1}(0) = z (uses 0 ≤ k·δ).
      --   (6) Verify within-derivative on Icc 0 ((k+1)·δ) — case split on
      --       t ≤ k·δ vs t ≥ k·δ; at t = k·δ use HasDerivWithinAt.union.
      --   (7) Verify velocity + position bounds at (k+1)·δ using β's properties.
      sorry
  -- ============================================================
  -- Bundle per-z curves into a joint flow via Classical.choose.
  -- For z outside the initial-condition ball, value is arbitrary (the
  -- conclusion's `s_z` quantifies only over z in the ball).
  -- ============================================================
  let γ_func : PhaseSpace d → ℝ → PhaseSpace d := fun z =>
    if hz : z ∈ Metric.closedBall z₀ ((a : ℝ) / 2)
    then Classical.choose (h_perZ z hz)
    else (fun _ => z)
  refine ⟨fun t z => (γ_func z t).1, fun t z => (γ_func z t).2, ?_, ?_, ?_⟩
  · -- (i) Initial condition: γ_func z 0 = z for z in the ball.
    intro z hz
    have h_init : Classical.choose (h_perZ z hz) 0 = z :=
      (Classical.choose_spec (h_perZ z hz)).1
    have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
      simp only [γ_func, dif_pos hz]
    refine ⟨?_, ?_⟩
    · change (γ_func z 0).1 = z.1
      rw [h_func_eq, h_init]
    · change (γ_func z 0).2 = z.2
      rw [h_func_eq, h_init]
  · -- (ii) Position ODE on Ioo 0 T: extract HasDerivWithinAt from
    --     the per-z curve, promote to HasDerivAt via Icc_mem_nhds.
    intro t ht z hz
    have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
      simp only [γ_func, dif_pos hz]
    have h_ode := (Classical.choose_spec (h_perZ z hz)).2
    have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) := by
      refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) hN_cover⟩
    have h_dw := (h_ode t h_t_in).1
    have hT_lt_N : t < (N : ℝ) * δ_uniform := lt_of_lt_of_le ht.2 hN_cover
    have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) ∈ nhds t :=
      Icc_mem_nhds ht.1 hT_lt_N
    -- Goal: HasDerivAt (fun s => (γ_func z s).1) ((γ_func z t).2) t.
    -- Use h_func_eq to rewrite γ_func z to Classical.choose ... .
    have h_d_within :
        HasDerivWithinAt (fun s => (γ_func z s).1) (γ_func z t).2
          (Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform)) t := by
      have h_eq_fun : (fun s => (γ_func z s).1)
          = (fun s => ((Classical.choose (h_perZ z hz)) s).1) := by
        funext s; rw [h_func_eq]
      have h_eq_pt : (γ_func z t).2 = (Classical.choose (h_perZ z hz) t).2 := by
        rw [h_func_eq]
      rw [h_eq_fun, h_eq_pt]; exact h_dw
    exact h_d_within.hasDerivAt h_icc_nhds
  · -- (iii) Velocity ODE on Ioo 0 T: same pattern.
    intro t ht z hz
    have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
      simp only [γ_func, dif_pos hz]
    have h_ode := (Classical.choose_spec (h_perZ z hz)).2
    have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) := by
      refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) hN_cover⟩
    have h_dw := (h_ode t h_t_in).2
    have hT_lt_N : t < (N : ℝ) * δ_uniform := lt_of_lt_of_le ht.2 hN_cover
    have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) ∈ nhds t :=
      Icc_mem_nhds ht.1 hT_lt_N
    have h_d_within :
        HasDerivWithinAt (fun s => (γ_func z s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ_func z t).1))
          (Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform)) t := by
      have h_eq_fun : (fun s => (γ_func z s).2)
          = (fun s => ((Classical.choose (h_perZ z hz)) s).2) := by
        funext s; rw [h_func_eq]
      have h_eq_pt : (γ_func z t).1 = (Classical.choose (h_perZ z hz) t).1 := by
        rw [h_func_eq]
      rw [h_eq_fun, h_eq_pt]; exact h_dw
    exact h_d_within.hasDerivAt h_icc_nhds

/-- **Two-window** characteristic-flow existence.

A flow on `Ioo 0 (2δ)` for some `δ > 0` and initial conditions in
`closedBall z₀ (a/2)`.  Produces a strictly longer window than
`exists_vlasov_characteristicFlow_local` (which gave `Ioo 0 δ` with
the larger `δ := (a/2)/(L_pl + 1)`); here we tighten the contraction
constraint to `L_pl · (2δ) ≤ a/2`, yielding the smaller
`δ := (a/2)/(2·(L_pl + 1))` but covering a `2δ`-long interval.

**Implementation note.**  This is a single Mathlib Picard call with
`tmax = 2δ`, not a literal "two-window stitch" via uniqueness on
overlapping windows.  Mathematically the two are equivalent: a
single Picard with an extended `tmax` and tightened `δ` recovers the
same set of solutions that a two-window stitch would produce.  The
genuine two-window stitch (per-z second Picard at varying centers
glued via `ODE_solution_unique`) becomes essential only when the
single-Picard contraction cannot be satisfied — i.e., when the total
time window needed exceeds the asymptotic threshold `≈ 1/2` regardless
of `a`.  For the upcoming N-window induction follow-up, this single-
Picard extension is iterated, with each iteration using a per-z
center from the previous window's endpoint. -/
theorem exists_vlasov_characteristicFlow_twoWindow
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
              ∀ x ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 (2 * δ)) (Metric.closedBall z₀ ((a : ℝ) / 2)) := by
  classical
  -- IsPicardLindelof parameter choices.  Same K_pl, r_pl, L_pl as `_local`;
  -- only the time-step δ is halved to fit the 2δ contraction.
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := ‖z₀.2‖₊ + a + M with hL_pl_def
  -- δ chosen so the doubled window 2δ still satisfies L_pl · (2δ) ≤ a/2.
  set δ : ℝ := min (1 / 2) ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1))) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < 2 * ((L_pl : ℝ) + 1) := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min (by norm_num) h_ratio_pos
  have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)) := min_le_right _ _
  have h_2δ_pos : (0 : ℝ) < 2 * δ := by linarith
  have h_2δ_le_one : 2 * δ ≤ 1 := by linarith
  -- t₀ ∈ Icc 0 (2δ).
  let t₀ : Set.Icc (0 : ℝ) (2 * δ) :=
    ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt h_2δ_pos⟩⟩
  -- Assemble IsPicardLindelof on time window [0, 2δ].
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ z₀ a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · -- norm_le — verbatim from `_local` (uses hbound on Icc 0 1, ball 3a/2).
      intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x z₀ ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - z₀‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - z₀.2‖ ≤ ‖x - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖z₀.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - z₀.2) + z₀.2‖ ≤ ‖x.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 z₀.1 ≤ dist x z₀ := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2) := by
        have hx1d : dist x.1 z₀.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have : dist x.1 z₀.1 ≤ 3 * (a : ℝ) / 2 := by
          have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
          linarith
        exact this
      have h_t_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ht.1, le_trans ht.2 h_2δ_le_one⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = ‖z₀.2‖ + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add, coe_nnnorm]
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M]
            · linarith [norm_nonneg z₀.2, NNReal.coe_nonneg a]
    · -- mul_max_le: L_pl · (2δ) ≤ a − a/2 = a/2.  Tighter constraint than `_local`.
      show (L_pl : ℝ) * max (2 * δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = 0 := rfl
      simp only [ht₀_eq, sub_zero, sub_self, max_eq_left (le_of_lt h_2δ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * (2 * δ) ≤ (L_pl : ℝ) *
          (2 * ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)))) := by
        apply mul_le_mul_of_nonneg_left _ h_Lpl_nn
        linarith [hδ_le_ratio]
      have h_simp : (L_pl : ℝ) *
          (2 * ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1))))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by
        field_simp
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        have h_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by linarith
        rw [div_le_one h_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_simp ▸ h_step, h_bound]
  -- Invoke headline Picard-Lindelöf on the doubled window.
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  -- Define charX, charV by projection.
  refine ⟨δ, hδ_pos, fun t z => (α z t).1, fun t z => (α z t).2, ?_, ?_, ?_⟩
  · -- Initial condition.
    intro z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢
      rw [hreq]; exact hz
    have h_init : α z (t₀ : ℝ) = z := (hα z hz_in_r).1
    have ht₀_eq : (t₀ : ℝ) = 0 := rfl
    rw [ht₀_eq] at h_init
    refine ⟨?_, ?_⟩
    · change (α z 0).1 = z.1; rw [h_init]
    · change (α z 0).2 = z.2; rw [h_init]
  · -- Position ODE on Ioo 0 (2δ).
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [hreq]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) (2 * δ) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) (2 * δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).1)
        (vlasovVectorField gradW ρ t (α z t)).1 t :=
      (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj
  · -- Velocity ODE on Ioo 0 (2δ).
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [hreq]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) (2 * δ) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) (2 * δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).2)
        (vlasovVectorField gradW ρ t (α z t)).2 t :=
      (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj

/-- **Per-z, time-shifted single-trajectory Picard with a uniform velocity-bound parameter.**

Given a fixed phase-space point `w`, a starting time `t_start`, an a priori
velocity bound `V_max ≥ ‖w.2‖`, and a uniform force bound around `w` on the
time interval `[t_start, t_start + 1]`, this produces a single trajectory
`β : ℝ → PhaseSpace d` solving the Vlasov ODE on `Ioo t_start (t_start + δ)`
with `β t_start = w`.

**Why `V_max` as a separate parameter:** the Picard contraction time δ
depends on the norm-bound `L_pl := V_max + a + M` for the vector field on
the local ball.  Phrasing this via an explicit `V_max ≥ ‖w.2‖` rather than
the tight `‖w.2‖` makes δ uniform in `w` for any iteration centered at
points `w` whose velocity component is bounded by `V_max`.  This is the
input that lets the N-window iteration in
`exists_vlasov_characteristicFlow` pick a single δ valid across all
windows (by combining with the a priori bound
`‖w_n(z).2‖ ≤ ‖z₀.2‖ + a/2 + M·T` on a finite `[0, T]`-interval).

Implementation: build an IsPicardLindelof centered at `w` over `[t_start,
t_start + δ]` with `L_pl := V_max + a + M`.  Invoke Mathlib's headline
theorem.  Take the single trajectory `β t := α w t`. -/
lemma exists_vlasov_extend_one_window
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (w : PhaseSpace d) (a : NNReal) (ha : 0 < a) (M : NNReal)
    (V_max : NNReal) (hV : ‖w.2‖ ≤ (V_max : ℝ))
    (t_start : ℝ)
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (β : ℝ → PhaseSpace d),
      δ = min 1 ((a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1)) ∧
      β t_start = w ∧
      (∀ t ∈ Set.Ioo t_start (t_start + δ),
        HasDerivAt (fun s => (β s).1) (β t).2 t ∧
        HasDerivAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1)) t) ∧
      -- Within-derivative on the closed interval — useful for combining
      -- adjacent windows at the join via `HasDerivWithinAt.union`.
      (∀ t ∈ Set.Icc t_start (t_start + δ),
        HasDerivWithinAt (fun s => (β s).1) (β t).2
          (Set.Icc t_start (t_start + δ)) t ∧
        HasDerivWithinAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
          (Set.Icc t_start (t_start + δ)) t) := by
  classical
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  -- Uniform L_pl using V_max, NOT ‖w.2‖₊.
  set L_pl : NNReal := V_max + a + M with hL_pl_def
  set δ : ℝ := min 1 ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min one_pos h_ratio_pos
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := min_le_right _ _
  -- t₀ at the start of the time window.
  let t₀ : Set.Icc t_start (t_start + δ) :=
    ⟨t_start, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  -- Assemble IsPicardLindelof centered at w over [t_start, t_start + δ].
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ w a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (a) lipschitzOnWith.
      intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · -- (b) continuousOn.
      intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · -- (c) norm_le — same algebra as `_local` but ball is around w (not z₀).
      intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x w ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - w‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - w.2‖ ≤ ‖x - w‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖w.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - w.2) + w.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - w.2) + w.2‖ ≤ ‖x.2 - w.2‖ + ‖w.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 w.1 ≤ dist x w := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
        rw [Metric.mem_closedBall]
        have hx1d : dist x.1 w.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
        linarith
      have h_t_Icc : t ∈ Set.Icc t_start (t_start + 1) :=
        ⟨ht.1, le_trans ht.2 (by linarith [hδ_le_one])⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = (V_max : ℝ) + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add]
      -- Now bound `‖x.2‖ ≤ ‖w.2‖ + a ≤ V_max + a`, and the force by M.
      have h_x2_bound' : ‖x.2‖ ≤ (V_max : ℝ) + (a : ℝ) :=
        le_trans h_x2_bound (by linarith [hV])
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M, h_x2_bound']
            · linarith [norm_nonneg w.2, NNReal.coe_nonneg a, NNReal.coe_nonneg V_max]
    · -- (d) mul_max_le: L_pl · δ ≤ a/2, same arithmetic as `_local`.
      show (L_pl : ℝ) * max ((t_start + δ) - (t₀ : ℝ)) ((t₀ : ℝ) - t_start)
          ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = t_start := rfl
      simp only [ht₀_eq, add_sub_cancel_left, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  -- Invoke headline Picard-Lindelöf, then specialise to the single trajectory at w.
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  have hw_in_r : w ∈ Metric.closedBall w ((r_pl : ℝ)) := by
    rw [Metric.mem_closedBall, dist_self]
    exact r_pl.coe_nonneg
  -- Above: w is always in any closed ball around itself with radius ≥ 0.
  have hα_w := hα w hw_in_r
  refine ⟨δ, hδ_pos, fun t => α w t, ?_, ?_, ?_, ?_⟩
  · -- δ matches the declared formula.
    rfl
  · -- β t_start = α w t_start = w (initial condition).
    have h_init : α w (t₀ : ℝ) = w := hα_w.1
    have ht₀_eq : (t₀ : ℝ) = t_start := rfl
    rw [ht₀_eq] at h_init
    exact h_init
  · -- ODEs on Ioo t_start (t_start + δ) (HasDerivAt).
    intro t ht
    have h_t_Icc : t ∈ Set.Icc t_start (t_start + δ) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := hα_w.2 t h_t_Icc
    have h_icc_nhds : Set.Icc t_start (t_start + δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α w) (vlasovVectorField gradW ρ t (α w t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1 t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2 t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
  · -- HasDerivWithinAt on Icc t_start (t_start + δ) — same content, no `nhds` step.
    intro t ht
    have h_dw := hα_w.2 t ht
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivWithinAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivWithinAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj

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
