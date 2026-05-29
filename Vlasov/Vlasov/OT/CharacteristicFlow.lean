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
import Vlasov.Mathlib.ODE.PicardLindelof
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

/-! ## Stage A.2 — Flow distance growth bound (Gronwall on the characteristic ODE)

A standalone regularity theorem about `IsCharacteristicFlow`: solutions of
the characteristic ODE have at most linear growth in their initial condition,
with a constant depending on `T`, the Lipschitz constant of `gradW`, and a
uniform first-moment bound on the measure curve `ρ`.

**The common auxiliary** identified by the session's structural-failure
datapoints (SC.8 and H1_lag both reduce to this bound).  Math content:
Gronwall on the position-velocity pair, using
  `‖(∇W ∗ ρ_t)(x)‖ ≤ ‖gradW 0‖ + L · (‖x‖ + ∫‖y‖dρ_t)`
as the velocity-field bound. -/

/-- **Flow distance growth bound** (`L`-Lipschitz `gradW`, uniform first moment
on `ρ`).  Solutions of the characteristic ODE grow at most linearly in their
initial condition: `‖(charX t z, charV t z)‖ ≤ C_T · (‖z‖ + 1)` for some
`C_T` depending only on `T`, `L`, `‖gradW 0‖`, and the uniform first-moment
bound `M_ρ`. -/
theorem flow_distance_growth_bound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (T : ℝ) (hT : 0 ≤ T)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∃ C_T, 0 ≤ C_T ∧
      ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  -- Gronwall parameters: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Witness: C_T = gronwallBound 1 K ε₀ T
  use gronwallBound 1 K ε₀ T
  refine ⟨?_, ?_⟩
  · -- C_T ≥ 0: since gronwallBound 1 K ε₀ 0 = 1 and it's monotone
    have hmono := gronwallBound_mono (by norm_num : (0:ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  · intro t ht z
    -- Convolution bound: ‖(∇W ∗ ρ_t)(x)‖ ≤ ε₀ + L * ‖x‖
    have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
        ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
      intro s hs x
      unfold convolveFunctionMeasure
      -- Integrability of ‖x - y‖ via h_y_int and triangle
      have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
        Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
          ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
          (Filter.Eventually.of_forall fun y => by
            simp only [Real.norm_of_nonneg (norm_nonneg _)]
            exact norm_sub_le x y)
      -- Integrability of the bound function
      have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
        (integrable_const _).add (h_sub_int.const_mul _)
      -- Pointwise bound: ‖gradW(x-y)‖ ≤ ‖gradW 0‖ + L*‖x-y‖
      have h_pt : ∀ y : PhysSpace d, ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
        intro y
        have hd := hL.dist_le_mul (x - y) 0
        simp only [dist_eq_norm, sub_zero] at hd
        have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
          have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      -- ‖∫ y, gradW(x - y) dρ_s‖ ≤ ∫ ‖gradW(x - y)‖ dρ_s ≤ ...
      calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
          ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
        _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
            integral_mono (h_int s x).norm h_bnd_int (fun y => h_pt y)
        _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
            rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
            simp [integral_const, measureReal_def, measure_univ,
                  integral_const_mul]
        _ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
            have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
              calc ∫ y, ‖x - y‖ ∂(ρ s)
                  ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                    integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs))
                      (fun y => norm_sub_le x y)
                _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                    rw [integral_add (integrable_const _) (h_y_int s hs)]
                    simp [integral_const, measureReal_def, measure_univ]
                _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
            simp only [hε₀_def]
            linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
    -- Gronwall: apply norm_le_gronwallBound_of_norm_deriv_right_le
    -- f(s) = (charX s z, charV s z), f'(s) = (charV s z, -conv at charX s z)
    have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T) :=
      continuousOn_of_forall_continuousAt fun s _ =>
        (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
    have h_deriv : ∀ s ∈ Set.Ico 0 T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z)) (Set.Ici s) s :=
      fun s _ => ((hflow_x s z).prodMk (hflow_v s z)).hasDerivWithinAt
    have h_init : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by
      obtain ⟨hx0, hv0⟩ := hflow_init z
      simp [hx0, hv0, Prod.norm_def]
    have h_bound : ∀ s ∈ Set.Ico 0 T,
        ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
          K * ‖(charX s z, charV s z)‖ + ε₀ := by
      intro s hs
      have hs_mem : s ∈ Set.Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
      simp only [Prod.norm_def, norm_neg]
      have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
      have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
      have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
        le_max_iff.mpr (Or.inl (norm_nonneg _))
      -- ‖charV s z‖ ≤ K * ‖f s‖ + ε₀
      have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
              le_mul_of_one_le_left hM_nn (by linarith)
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := le_add_of_nonneg_right hε₀_nn
      -- ‖conv‖ ≤ K * ‖f s‖ + ε₀
      have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
            ≤ ε₀ + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
          _ ≤ ε₀ + K * max ‖charX s z‖ ‖charV s z‖ := by
              have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
              linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                        mul_le_mul_of_nonneg_right hLK hM_nn]
          _ = K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := by ring
      exact max_le h_v_le h_conv_le
    -- Apply Gronwall
    have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
      h_f_cont h_deriv h_init h_bound t ht
    simp only [sub_zero] at h_grw
    -- gronwallBound ‖z‖ K ε₀ t ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1)
    calc ‖(charX t z, charV t z)‖
        ≤ gronwallBound ‖z‖ K ε₀ t := h_grw
      _ ≤ gronwallBound ‖z‖ K ε₀ T :=
          gronwallBound_mono (norm_nonneg _) hε₀_nn hK_pos.le ht.2
      _ ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1) := by
          rw [gronwallBound_of_K_ne_0 hK_pos.ne', gronwallBound_of_K_ne_0 hK_pos.ne']
          simp only [one_mul]
          have he1 : 0 ≤ Real.exp (K * T) - 1 :=
            by linarith [Real.one_le_exp (mul_nonneg hK_pos.le hT)]
          have hεK := div_nonneg hε₀_nn hK_pos.le
          nlinarith [norm_nonneg z, Real.exp_nonneg (K * T),
            mul_nonneg hεK he1, mul_nonneg (norm_nonneg z) (mul_nonneg hεK he1)]

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
`‖w_n(z).2‖ ≤ ‖z₀.2‖ + a/2 + M·(T+1)` on a finite `[0, T]`-interval).

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
      (∀ t ∈ Set.Icc t_start (t_start + δ),
        HasDerivWithinAt (fun s => (β s).1) (β t).2
          (Set.Icc t_start (t_start + δ)) t ∧
        HasDerivWithinAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
          (Set.Icc t_start (t_start + δ)) t) ∧
      (∀ s ∈ Set.Icc t_start (t_start + δ), β s ∈ Metric.closedBall w (a : ℝ)) := by
  classical
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := V_max + a + M with hL_pl_def
  set δ : ℝ := min 1 ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min one_pos h_ratio_pos
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := min_le_right _ _
  let t₀ : Set.Icc t_start (t_start + δ) :=
    ⟨t_start, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ w a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · intro t ht x hx
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
      have h_x2_bound' : ‖x.2‖ ≤ (V_max : ℝ) + (a : ℝ) :=
        le_trans h_x2_bound (by linarith [hV])
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M, h_x2_bound']
            · linarith [norm_nonneg w.2, NNReal.coe_nonneg a, NNReal.coe_nonneg V_max]
    · show (L_pl : ℝ) * max ((t_start + δ) - (t₀ : ℝ)) ((t₀ : ℝ) - t_start)
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
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  have hw_in_r : w ∈ Metric.closedBall w ((r_pl : ℝ)) := by
    rw [Metric.mem_closedBall, dist_self]
    exact r_pl.coe_nonneg
  have hα_w := hα w hw_in_r
  refine ⟨δ, hδ_pos, fun t => α w t, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · have h_init : α w (t₀ : ℝ) = w := hα_w.1
    have ht₀_eq : (t₀ : ℝ) = t_start := rfl
    rw [ht₀_eq] at h_init
    exact h_init
  · intro t ht
    have h_t_Icc : t ∈ Set.Icc t_start (t_start + δ) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := hα_w.2.1 t h_t_Icc
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
  · intro t ht
    have h_dw := hα_w.2.1 t ht
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
  · -- confinement: β s ∈ closedBall w a (delivered by `_confined` variant)
    intro s hs
    exact hα_w.2.2 s hs

/-! ### Per-window helpers for the N-window induction in
    `exists_vlasov_characteristicFlow`.

    These three top-level lemmas are generic in `(β, ODE, confinement,
    field bound, IH bound, reference point)` with no mention of the
    N-window induction context (no `γ_k`, `k`, `N`, `z₀`).  This
    genericity gives each helper its own elaboration budget (closing
    the heartbeat-blocked inline carries) AND makes them composable
    for future call sites — Stage C's chain rule, well-posedness's
    Banach iteration, etc.

    Composition order: Helper 1 (confinement) → Helper 2 (window-wide
    velocity bound) → Helper 3 (endpoint position bound).
-/

/-- **Helper 1: Picard window confinement (projection from phase-space ball).**

For a trajectory β satisfying the Vlasov ODE on a Picard window
`[t_start, t_start + δ]` centered at `w`, the position component
stays within the local force-bound ball:
`(β s).1 ∈ closedBall w.1 (3a/2)` for `s` in the window.

**Argument.**  The strengthened Picard-Lindelöf theorem
`exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined`
(`Vlasov.Mathlib.ODE.PicardLindelof`) exposes
`FunSpace.compProj_mem_closedBall` at the public theorem level,
delivering `β s ∈ closedBall w a` (phase-space ball of radius `a` —
the outer Lipschitz radius) as a side product of the existence
guarantee.  We project this to the position component via
`Prod.dist_eq` + `le_max_left`, then loosen `a ≤ 3a/2` by arithmetic.
The result is a 3-5 line projection.

**Hypothesis `hβ_confined`** is supplied by Vlasov-side callers from
the widened `exists_vlasov_extend_one_window` output (Stage 4 of the
confinement-vendor refactor).  The other hypotheses (ODE, field
bound, contraction inequality) are retained for genericity / call
site compatibility; they are not consumed by the projection body but
remain available for future call sites that want to re-derive the
confinement directly (e.g. via supremum trick) without invoking
the vendored Mathlib API. -/
lemma vlasov_window_confinement
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
    (t_start δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδ_contract : δ ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (β : ℝ → PhaseSpace d) (hβ_init : β t_start = w)
    (hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).1) (β t).2
        (Set.Icc t_start (t_start + δ)) t ∧
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
        (Set.Icc t_start (t_start + δ)) t)
    (hβ_confined : ∀ s ∈ Set.Icc t_start (t_start + δ),
      β s ∈ Metric.closedBall w (a : ℝ)) :
    ∀ s ∈ Set.Icc t_start (t_start + δ),
      (β s).1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
  intro s hs
  have h_phase : β s ∈ Metric.closedBall w (a : ℝ) := hβ_confined s hs
  rw [Metric.mem_closedBall] at h_phase ⊢
  -- dist (β s).1 w.1 ≤ dist (β s) w ≤ a ≤ 3a/2
  have h_proj : dist (β s).1 w.1 ≤ dist (β s) w := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have h_a_nn : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
  linarith

/-- **Helper 2: Window-wide velocity bound.**

For a trajectory β with velocity-component ODE
`(β · ).2' = -(∇W ∗ ρ_·)((β ·).1)` on `[t_start, t_start + δ]` and
force bound M (made applicable by `h_β_in_ball`), the velocity at
every interior `s` is bounded by `h_vel_init + M · (s - t_start)`.

**Math sketch.**  One application of
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `(β · ).2`
over the convex window `Icc t_start (t_start + δ)`, with `y := s`
universally quantified:
  `‖(β s).2 - (β t_start).2‖ ≤ M · ‖s - t_start‖ = M · (s - t_start)`.
Triangle with `‖(β t_start).2‖ = ‖w.2‖ ≤ h_vel_init` (using `hβ_init`)
gives the conclusion.

The universal quantification over `y` in the mean-value lemma is what
makes this WINDOW-WIDE from ONE invocation — no per-s re-application. -/
lemma vlasov_window_velocity_bound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (w : PhaseSpace d) (a : NNReal) (M : NNReal)
    (t_start δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_vel_init : ℝ) (hβ_init_vel_bound : ‖w.2‖ ≤ h_vel_init)
    (β : ℝ → PhaseSpace d) (hβ_init : β t_start = w)
    (hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
        (Set.Icc t_start (t_start + δ)) t)
    (h_β_in_ball : ∀ s ∈ Set.Icc t_start (t_start + δ),
      (β s).1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2))
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∀ s ∈ Set.Icc t_start (t_start + δ),
      ‖(β s).2‖ ≤ h_vel_init + (M : ℝ) * (s - t_start) := by
  intro s hs
  -- Convexity of the window.
  have h_convex : Convex ℝ (Set.Icc t_start (t_start + δ)) := convex_Icc _ _
  have h_t_start_in : t_start ∈ Set.Icc t_start (t_start + δ) :=
    ⟨le_refl _, by linarith⟩
  -- Force bound on the window (via h_β_in_ball).
  have h_force_window : ∀ u ∈ Set.Icc t_start (t_start + δ),
      ‖-(convolveFunctionMeasure gradW (ρ u) (β u).1)‖ ≤ (M : ℝ) := by
    intro u hu
    rw [norm_neg]
    have hu_time : u ∈ Set.Icc t_start (t_start + 1) :=
      ⟨hu.1, le_trans hu.2 (by linarith [hδ_le_one])⟩
    exact hbound u hu_time (β u).1 (h_β_in_ball u hu)
  -- Velocity ODE on the window.
  have h_vel_ode : ∀ u ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun v => (β v).2)
        (-(convolveFunctionMeasure gradW (ρ u) (β u).1))
        (Set.Icc t_start (t_start + δ)) u :=
    fun u hu => hβ_ode_Icc u hu
  -- Apply Convex.norm_image_sub_le with x := t_start, y := s.
  have h_mv : ‖(β s).2 - (β t_start).2‖ ≤ (M : ℝ) * ‖s - t_start‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      h_vel_ode h_force_window h_t_start_in hs
  have h_diff_nn : 0 ≤ s - t_start := by linarith [hs.1]
  rw [Real.norm_of_nonneg h_diff_nn] at h_mv
  -- β t_start = w, so (β t_start).2 = w.2.
  have h_β_t_start_vel : (β t_start).2 = w.2 := by rw [hβ_init]
  -- Triangle: ‖(β s).2‖ ≤ ‖(β s).2 - (β t_start).2‖ + ‖(β t_start).2‖.
  have h_decomp : (β s).2 = ((β s).2 - (β t_start).2) + (β t_start).2 :=
    (sub_add_cancel _ _).symm
  have h_triangle : ‖(β s).2‖
      ≤ ‖(β s).2 - (β t_start).2‖ + ‖(β t_start).2‖ := by
    calc ‖(β s).2‖ = ‖((β s).2 - (β t_start).2) + (β t_start).2‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  -- Combine: ‖(β s).2‖ ≤ M·(s - t_start) + ‖w.2‖ ≤ h_vel_init + M·(s - t_start).
  rw [h_β_t_start_vel] at h_triangle
  -- h_mv has `(β t_start).2`; rewrite to `w.2` for compatibility.
  rw [h_β_t_start_vel] at h_mv
  linarith [h_mv, hβ_init_vel_bound]

/-- **Helper 3: Window endpoint position bound.**

For a trajectory β with position-component ODE
`(β · ).1' = (β · ).2` on `[t_start, t_start + δ]` and a uniform
velocity bound `V_bound` (typically Helper 2's output composed with
a worst-case substitution), the position at `t_start + δ` is bounded
relative to an explicit reference point `x_ref`:
  `‖(β (t_start + δ)).1 - x_ref‖ ≤ h_pos_init + V_bound · δ`
where `h_pos_init ≥ ‖w.1 - x_ref‖`.

**Math sketch.**  One application of
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `(β · ).1`
over the convex window with `x := t_start`, `y := t_start + δ`:
  `‖(β (t_start + δ)).1 - (β t_start).1‖ ≤ V_bound · δ` (using
  `hβ_init` for `(β t_start).1 = w.1`).
Triangle with `‖w.1 - x_ref‖ ≤ h_pos_init` gives the conclusion.

**Genericity.**  `x_ref : PhysSpace d` is an explicit parameter, NOT
hardcoded to the N-window induction's `z₀.1`.  This makes the helper
reusable for Stage C's chain rule (reference point: support of test
function φ), well-posedness's Banach iteration (reference point:
fixed-point candidate), etc. -/
lemma vlasov_window_position_bound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (w : PhaseSpace d)
    (t_start δ : ℝ) (hδ_pos : 0 < δ)
    (V_bound : ℝ)
    (x_ref : PhysSpace d)
    (h_pos_init : ℝ) (hβ_init_pos_bound : ‖w.1 - x_ref‖ ≤ h_pos_init)
    (β : ℝ → PhaseSpace d) (hβ_init : β t_start = w)
    (hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).1) (β t).2
        (Set.Icc t_start (t_start + δ)) t)
    (h_window_vel : ∀ s ∈ Set.Icc t_start (t_start + δ),
      ‖(β s).2‖ ≤ V_bound) :
    ‖(β (t_start + δ)).1 - x_ref‖ ≤ h_pos_init + V_bound * δ := by
  -- Convexity of the window.
  have h_convex : Convex ℝ (Set.Icc t_start (t_start + δ)) := convex_Icc _ _
  have h_t_start_in : t_start ∈ Set.Icc t_start (t_start + δ) :=
    ⟨le_refl _, by linarith⟩
  have h_t_end_in : t_start + δ ∈ Set.Icc t_start (t_start + δ) :=
    ⟨by linarith, le_refl _⟩
  -- Position ODE on the window.
  have h_pos_ode : ∀ u ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun v => (β v).1) (β u).2
        (Set.Icc t_start (t_start + δ)) u :=
    fun u hu => hβ_ode_Icc u hu
  -- Apply Convex.norm_image_sub_le with x := t_start, y := t_start + δ.
  have h_mv : ‖(β (t_start + δ)).1 - (β t_start).1‖
              ≤ V_bound * ‖(t_start + δ) - t_start‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      h_pos_ode h_window_vel h_t_start_in h_t_end_in
  have h_δ_eq : (t_start + δ) - t_start = δ := by ring
  rw [h_δ_eq, Real.norm_of_nonneg (le_of_lt hδ_pos)] at h_mv
  -- β t_start = w, so (β t_start).1 = w.1.
  have h_β_t_start_pos : (β t_start).1 = w.1 := by rw [hβ_init]
  rw [h_β_t_start_pos] at h_mv
  -- Triangle: ‖(β (t_start+δ)).1 - x_ref‖
  --        ≤ ‖(β (t_start+δ)).1 - w.1‖ + ‖w.1 - x_ref‖
  --        ≤ V_bound · δ + h_pos_init.
  have h_decomp : (β (t_start + δ)).1 - x_ref
                = ((β (t_start + δ)).1 - w.1) + (w.1 - x_ref) := by
    rw [sub_add_sub_cancel]
  have h_triangle : ‖(β (t_start + δ)).1 - x_ref‖
      ≤ ‖(β (t_start + δ)).1 - w.1‖ + ‖w.1 - x_ref‖ := by
    calc ‖(β (t_start + δ)).1 - x_ref‖
        = ‖((β (t_start + δ)).1 - w.1) + (w.1 - x_ref)‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  linarith [h_mv, hβ_init_pos_bound]

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
    -- Note: `hR`'s M coefficient is `(T + 1)²` (not `(T + 1)²/2`) because the
    -- proof uses the mean-value-with-sup approach for the position drift,
    -- which gives `V_max · δ` per window.  Total over the iteration is
    -- `V_max · (T + 1) = (‖z₀.2‖ + a/2 + M·(T+1)) · (T+1)`, expanding to a
    -- factor of `M·(T+1)²` (no halving).  An integral-based proof would
    -- recover the tighter `/2` form but at significant Lean-API cost.
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * (T + 1) + (M : ℝ) * (T + 1) ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (T + 1),
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
    ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal (T + 1) with hV_max_def
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
    suffices h_strong : ∀ k : ℕ, k ≤ N → ∃ γ : ℝ → PhaseSpace d,
        γ 0 = z ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform),
          HasDerivWithinAt (fun s => (γ s).1) (γ t).2
            (Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform)) t ∧
          HasDerivWithinAt (fun s => (γ s).2)
            (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
            (Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform)) t) ∧
        -- Velocity invariant: TIGHT.  Carries through mean-value (gain `+M·δ`
        -- per window matches the `M·(k·δ)` linear-in-time growth).
        ‖(γ ((k : ℝ) * δ_uniform)).2‖ ≤
          ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((k : ℝ) * δ_uniform) ∧
        -- Position invariant: LINEAR in time.  Carries through mean-value
        -- (gain `+V_max·δ` per window matches the `V_max·(k·δ)` growth).
        ‖(γ ((k : ℝ) * δ_uniform)).1 - z₀.1‖ ≤
          (a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ_uniform) by
      obtain ⟨γ, hγ0, hode, _, _⟩ := h_strong N (le_refl N)
      exact ⟨γ, hγ0, hode⟩
    -- ============================================================
    -- Bounded induction on k ≤ N — the `≤ N` constraint is needed so
    -- that the inductive step's `_extend_one_window` invocation at
    -- `t_start = k·δ_uniform` (for k = 0, ..., N-1) satisfies the
    -- widened hbound's `Icc 0 (T+1)` time range:
    -- `(N-1)·δ_uniform + 1 ≤ T + 1` since `(N-1)·δ_uniform ≤ T`.
    -- ============================================================
    intro k
    induction k with
    | zero =>
      -- Base case: γ ≡ z is constant on the singleton [0, 0] = {0}.
      intro _
      refine ⟨fun _ => z, rfl, ?_, ?_, ?_⟩
      · -- Within-derivative on Icc 0 0 = {0}: at t = 0, the only point in
        -- the set; HasDerivWithinAt at an isolated point holds for any
        -- derivative via `HasFDerivWithinAt.of_not_accPt`.  Pattern matches
        -- Mathlib's `hasFDerivWithinAt_singleton` proof.
        intro t ht
        have ht_eq : t = 0 := le_antisymm (by simpa using ht.2) ht.1
        subst ht_eq
        have h_notAccPt : ¬ AccPt (0 : ℝ)
            (Filter.principal (Set.Icc (0 : ℝ) ((0 : ℕ) * δ_uniform))) := by
          simp only [Nat.cast_zero, zero_mul, Set.Icc_self]
          rw [accPt_iff_clusterPt, Filter.inf_principal]
          simp [ClusterPt]
        refine ⟨?_, ?_⟩
        · rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
          exact HasFDerivWithinAt.of_not_accPt h_notAccPt
        · rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
          exact HasFDerivWithinAt.of_not_accPt h_notAccPt
      · -- Velocity bound at t = 0 (tight invariant): ‖z.2‖ ≤ ‖z₀.2‖ + a/2 + M·0.
        have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
          rw [← dist_eq_norm]; exact hz
        have h_z2_proj : ‖z.2 - z₀.2‖ ≤ ‖z - z₀‖ := by
          rw [Prod.norm_def]; exact le_max_right _ _
        have h_z2_bound : ‖z.2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 := by
          have h1 : ‖z.2‖ = ‖(z.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
          have h2 : ‖(z.2 - z₀.2) + z₀.2‖ ≤ ‖z.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
          linarith [h_z2_proj, hdist]
        show ‖((fun _ => z) ((0 : ℕ) * δ_uniform : ℝ)).2‖ ≤
          ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (((0 : ℕ) : ℝ) * δ_uniform)
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
        linarith
      · -- Position bound at t = 0 (linear invariant): ‖z.1 - z₀.1‖ ≤ a/2 + V_max·0.
        have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
          rw [← dist_eq_norm]; exact hz
        have h_z1_proj : ‖z.1 - z₀.1‖ ≤ ‖z - z₀‖ := by
          rw [Prod.norm_def]; exact le_max_left _ _
        show ‖((fun _ => z) ((0 : ℕ) * δ_uniform : ℝ)).1 - z₀.1‖ ≤
          (a : ℝ) / 2 + (V_max : ℝ) * (((0 : ℕ) : ℝ) * δ_uniform)
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
        linarith
    | succ k ih =>
      -- Inductive step: extend γ_k from [0, k·δ_uniform] to [0, (k+1)·δ_uniform]
      -- via `exists_vlasov_extend_one_window` at center γ_k (k·δ_uniform), then
      -- piecewise-glue at t = k·δ_uniform using `HasDerivWithinAt.union`.
      intro hk_succ_le_N
      -- (s.1) Extract IH for k.
      have hk_le_N : k ≤ N := Nat.le_of_succ_le hk_succ_le_N
      obtain ⟨γ_k, h_γ0, h_ode_k, h_vel_k, h_pos_k⟩ := ih hk_le_N
      -- Derived inequalities: k·δ ≤ T ≤ T+1, k·δ + 1 ≤ T+1, etc.
      have hk_lt_N : k < N := hk_succ_le_N
      have h_kδ_nn : (0 : ℝ) ≤ (k : ℝ) * δ_uniform := by positivity
      have hδ_le_one : δ_uniform ≤ 1 := min_le_left _ _
      -- (k+1)·δ ≤ N·δ ≤ T+1 (using N := ⌈T/δ⌉₊).
      have h_succ_kδ_le : ((k + 1 : ℕ) : ℝ) * δ_uniform ≤ T + 1 := by
        have h_kp1_le_N : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk_succ_le_N
        calc ((k + 1 : ℕ) : ℝ) * δ_uniform
            ≤ (N : ℝ) * δ_uniform :=
              mul_le_mul_of_nonneg_right h_kp1_le_N (le_of_lt hδ_pos)
          _ ≤ T + 1 := by
              -- N · δ_uniform ≤ (T/δ_uniform + 1) · δ_uniform = T + δ_uniform ≤ T + 1.
              have h_N_le : (N : ℝ) ≤ T / δ_uniform + 1 := by
                exact_mod_cast Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ T / δ_uniform) |>.le
              have h_δ_ne : δ_uniform ≠ 0 := ne_of_gt hδ_pos
              calc (N : ℝ) * δ_uniform
                  ≤ (T / δ_uniform + 1) * δ_uniform :=
                    mul_le_mul_of_nonneg_right h_N_le (le_of_lt hδ_pos)
                _ = T + δ_uniform := by field_simp
                _ ≤ T + 1 := by linarith [hδ_le_one]
      have h_kδ_le_T : (k : ℝ) * δ_uniform ≤ T := by
        -- From k + 1 ≤ N ≤ T/δ + 1, get k ≤ T/δ, hence k·δ ≤ T.
        have hk_real : (k : ℝ) ≤ T / δ_uniform := by
          have h1 : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk_succ_le_N
          have h_div_nn : (0 : ℝ) ≤ T / δ_uniform := by positivity
          have h2 : (N : ℝ) ≤ T / δ_uniform + 1 := by
            exact_mod_cast (Nat.ceil_lt_add_one h_div_nn).le
          push_cast at h1
          linarith
        calc (k : ℝ) * δ_uniform
            ≤ (T / δ_uniform) * δ_uniform :=
              mul_le_mul_of_nonneg_right hk_real (le_of_lt hδ_pos)
          _ = T := by field_simp
      have h_kδ_plus_1_le : (k : ℝ) * δ_uniform + 1 ≤ T + 1 := by linarith
      -- V_max bound on the IH velocity (loose), derived from the tight IH +
      -- the time bound `k·δ ≤ T+1`.  Required for `_extend_one_window`'s `hV`.
      have h_vel_Vmax : ‖(γ_k ((k : ℝ) * δ_uniform)).2‖ ≤ (V_max : ℝ) := by
        have h_V_coe : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((T + 1).toNNReal : ℝ) := by
          simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
        have h_toNNReal : ((T + 1).toNNReal : ℝ) = T + 1 := by
          rw [Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ T + 1)]
        have h_kδ_le_T1 : (k : ℝ) * δ_uniform ≤ T + 1 := by linarith
        have hM_nn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
        rw [h_V_coe, h_toNNReal]
        calc ‖(γ_k ((k : ℝ) * δ_uniform)).2‖
            ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((k : ℝ) * δ_uniform) := h_vel_k
          _ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T + 1) := by
              nlinarith [mul_le_mul_of_nonneg_left h_kδ_le_T1 hM_nn]
      -- (s.2) Verify hbound on Icc (k·δ) (k·δ + 1), closedBall (γ_k(k·δ)).1 (3a/2).
      have hbound_local : ∀ t ∈ Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + 1),
          ∀ x ∈ Metric.closedBall (γ_k ((k : ℝ) * δ_uniform)).1 (3 * (a : ℝ) / 2),
          ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M := by
        intro t ht x hx
        -- Time check: t ∈ Icc (k·δ) (k·δ + 1) ⊆ Icc 0 (T + 1).
        have h_t_in_global : t ∈ Set.Icc (0 : ℝ) (T + 1) :=
          ⟨le_trans h_kδ_nn ht.1, le_trans ht.2 h_kδ_plus_1_le⟩
        -- Position chain: dist x z₀.1 ≤ 3a/2 + (a/2 + V_max·(k·δ)) ≤ R.
        have h_x_local : dist x (γ_k ((k : ℝ) * δ_uniform)).1 ≤ 3 * (a : ℝ) / 2 := hx
        have h_pos_chain : dist x z₀.1
            ≤ 3 * (a : ℝ) / 2
              + ((a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ_uniform)) := by
          calc dist x z₀.1
              ≤ dist x (γ_k ((k : ℝ) * δ_uniform)).1
                + dist (γ_k ((k : ℝ) * δ_uniform)).1 z₀.1 := dist_triangle _ _ _
            _ ≤ 3 * (a : ℝ) / 2 + _ := by
                rw [dist_eq_norm]
                exact add_le_add h_x_local h_pos_k
        -- Bound `V_max · (k·δ)` by `V_max · (T+1)`, then expand to hR's form.
        have h_V_max_coe : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T + 1) := by
          have h_V_def : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((T + 1).toNNReal : ℝ) := by
            simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
          rw [h_V_def, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ T + 1)]
        have h_kδ_le_T1 : (k : ℝ) * δ_uniform ≤ T + 1 := by linarith
        have h_V_max_nn : (0 : ℝ) ≤ (V_max : ℝ) := V_max.coe_nonneg
        have h_M_nn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
        have h_T1_nn : (0 : ℝ) ≤ T + 1 := by linarith
        -- 2a + V_max · (T+1) = 2a + (‖z₀.2‖ + a/2)·(T+1) + M·(T+1)² ≤ R by hR.
        have h_R_expand : 2 * (a : ℝ) + (V_max : ℝ) * (T + 1) ≤ R := by
          rw [h_V_max_coe]; ring_nf; ring_nf at hR; linarith
        have h_x_in_R : dist x z₀.1 ≤ (R : ℝ) := by
          have h_pos_worst : (V_max : ℝ) * ((k : ℝ) * δ_uniform) ≤ (V_max : ℝ) * (T + 1) :=
            mul_le_mul_of_nonneg_left h_kδ_le_T1 h_V_max_nn
          linarith [h_pos_chain]
        exact hbound t h_t_in_global x h_x_in_R
      -- (s.3) Apply `exists_vlasov_extend_one_window` at center γ_k(k·δ).
      -- The widened output now includes `hβ_confined` (phase-space ball
      -- confinement), delivered by the strengthened Picard-Lindelöf in
      -- `Vlasov.Mathlib.ODE.PicardLindelof`.  Stage 5 will project this
      -- through `vlasov_window_confinement` to discharge `h_β_in_ball`.
      obtain ⟨δ', hδ'_pos, β, hδ'_eq, hβ_init, hβ_ode_Ioo, hβ_ode_Icc, hβ_confined⟩ :=
        exists_vlasov_extend_one_window gradW L hL ρ h_int hρ_cont
          (γ_k ((k : ℝ) * δ_uniform)) a ha M V_max h_vel_Vmax
          ((k : ℝ) * δ_uniform) hbound_local
      -- δ' coincides with δ_uniform by construction.
      have hδ'_eq_uniform : δ' = δ_uniform := hδ'_eq
      -- (s.4) Define γ_succ via Set.piecewise.
      let γ_succ : ℝ → PhaseSpace d :=
        Set.piecewise (Set.Iic ((k : ℝ) * δ_uniform)) γ_k β
      -- (s.5) γ_succ(0) = z.
      have h_γsucc_0 : γ_succ 0 = z := by
        have h0_mem : (0 : ℝ) ∈ Set.Iic ((k : ℝ) * δ_uniform) := h_kδ_nn
        simp only [γ_succ, Set.piecewise_eq_of_mem _ _ _ h0_mem]
        exact h_γ0
      -- Useful facts for substep (s.6) — interval shape + monotonicity.
      have h_kδ_succ_eq : (k : ℝ) * δ_uniform + δ_uniform = ((k + 1 : ℕ) : ℝ) * δ_uniform := by
        push_cast; ring
      have h_kδ_le_succ_kδ : (k : ℝ) * δ_uniform ≤ ((k + 1 : ℕ) : ℝ) * δ_uniform := by
        rw [← h_kδ_succ_eq]; linarith [hδ_pos]
      -- γ_succ agrees with γ_k on Iic (k·δ_uniform), with β on Ioi (k·δ_uniform).
      have h_γsucc_left : ∀ y ≤ (k : ℝ) * δ_uniform, γ_succ y = γ_k y := fun y hy =>
        Set.piecewise_eq_of_mem _ _ _ hy
      have h_γsucc_right : ∀ y, (k : ℝ) * δ_uniform < y → γ_succ y = β y := fun y hy =>
        Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hy)
      -- At the boundary t = k·δ, γ_succ = γ_k = β (using hβ_init).
      have h_γsucc_at_join : γ_succ ((k : ℝ) * δ_uniform) = γ_k ((k : ℝ) * δ_uniform) :=
        h_γsucc_left _ (le_refl _)
      have h_β_at_join : β ((k : ℝ) * δ_uniform) = γ_k ((k : ℝ) * δ_uniform) := hβ_init
      -- Also: γ_succ = β on Icc (k·δ) (...) (since at the join β = γ_k = γ_succ).
      have h_γsucc_on_right_Icc : ∀ y ∈ Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform),
          γ_succ y = β y := by
        intro y hy
        rcases eq_or_lt_of_le hy.1 with hy_eq | hy_lt
        · rw [← hy_eq, h_γsucc_at_join, h_β_at_join]
        · exact h_γsucc_right y hy_lt
      -- ============================================================
      -- SHARED FACT: β stays in `closedBall (γ_k(k·δ)).1 (3a/2)`
      -- throughout the window.  Delivered by the strengthened
      -- Picard-Lindelöf (`Vlasov.Mathlib.ODE.PicardLindelof`): the
      -- widened `_extend_one_window` returns `hβ_confined`
      -- (phase-space ball at radius `a`), which `vlasov_window_confinement`
      -- projects to the position component at radius `3a/2`.
      -- ============================================================
      -- The two interval forms `Icc (k·δ) ((k+1)·δ)` and `Icc (k·δ) (k·δ + δ)`
      -- are equal in ℝ but not syntactically; convert via `h_kδ_succ_eq`.
      have hδ_global_le_one : δ_uniform ≤ 1 := min_le_left _ _
      have hδ_global_le_ratio : δ_uniform ≤
          (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1) := min_le_right _ _
      -- Convert hβ_ode_Icc's interval from `Icc (k·δ) (k·δ + δ')` to
      -- `Icc (k·δ) (k·δ + δ_uniform)` via hδ'_eq_uniform.  Targeted
      -- rewrite — only the second δ occurrence (after the `+`).
      have h_sec_eq : (k : ℝ) * δ_uniform + δ' = (k : ℝ) * δ_uniform + δ_uniform := by
        rw [hδ'_eq_uniform]
      have hβ_ode_Icc_unified : ∀ t ∈ Set.Icc ((k : ℝ) * δ_uniform)
                                      ((k : ℝ) * δ_uniform + δ_uniform),
          HasDerivWithinAt (fun s => (β s).1) (β t).2
            (Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + δ_uniform)) t ∧
          HasDerivWithinAt (fun s => (β s).2)
            (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
            (Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + δ_uniform)) t := by
        rw [← h_sec_eq]; exact hβ_ode_Icc
      -- Same δ' → δ_uniform interval conversion for `hβ_confined` from Stage 4.
      have hβ_confined_unified : ∀ s ∈ Set.Icc ((k : ℝ) * δ_uniform)
                                      ((k : ℝ) * δ_uniform + δ_uniform),
          β s ∈ Metric.closedBall (γ_k ((k : ℝ) * δ_uniform)) (a : ℝ) := by
        rw [← h_sec_eq]; exact hβ_confined
      have h_β_in_ball_native : ∀ s ∈ Set.Icc ((k : ℝ) * δ_uniform)
                                    ((k : ℝ) * δ_uniform + δ_uniform),
          (β s).1 ∈ Metric.closedBall (γ_k ((k : ℝ) * δ_uniform)).1 (3 * (a : ℝ) / 2) :=
        vlasov_window_confinement gradW L hL ρ h_int hρ_cont
          (γ_k ((k : ℝ) * δ_uniform)) a ha M V_max h_vel_Vmax
          ((k : ℝ) * δ_uniform) δ_uniform hδ_pos hδ_global_le_one hδ_global_le_ratio
          hbound_local β hβ_init hβ_ode_Icc_unified hβ_confined_unified
      have h_β_in_ball : ∀ s ∈ Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform),
          (β s).1 ∈ Metric.closedBall (γ_k ((k : ℝ) * δ_uniform)).1 (3 * (a : ℝ) / 2) := by
        intro s hs
        apply h_β_in_ball_native s
        rw [show ((k : ℝ) * δ_uniform + δ_uniform) = ((k + 1 : ℕ) : ℝ) * δ_uniform
            from h_kδ_succ_eq]
        exact hs
      refine ⟨γ_succ, h_γsucc_0, ?_, ?_, ?_⟩
      · -- (s.6) Within-derivative on Icc 0 ((k+1)·δ_uniform).
        -- Use .union of two pieces (Icc 0 (k·δ_uniform) + Icc (k·δ_uniform) ((k+1)·δ_uniform)),
        -- each piece via .congr to γ_succ from γ_k or β, with the
        -- "outside-piece" handled vacuously via HasFDerivWithinAt.of_notMem_closure.
        intro t ht
        -- Convert the iterate ((k+1 : ℕ) : ℝ) * δ_uniform to a more workable form
        -- using h_kδ_succ_eq for arithmetic where needed.
        -- Build Piece A: on Icc 0 (k·δ_uniform).
        have hA_pos : HasDerivWithinAt (fun s => (γ_succ s).1) (γ_succ t).2
                        (Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform)) t := by
          by_cases ht_left : t ≤ (k : ℝ) * δ_uniform
          · -- t is in Icc 0 (k·δ); use h_ode_k via congr.
            have ht_in : t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform) := ⟨ht.1, ht_left⟩
            have h_γk_pos := (h_ode_k t ht_in).1
            -- h_γk_pos : HasDerivWithinAt (fun s => (γ_k s).1) (γ_k t).2 (Icc 0 (k·δ)) t
            have h_deriv_eq : (γ_succ t).2 = (γ_k t).2 := by
              rw [h_γsucc_left t ht_left]
            rw [h_deriv_eq]
            refine h_γk_pos.congr (fun y hy => ?_) ?_
            · rw [h_γsucc_left y hy.2]
            · rw [h_γsucc_left t ht_left]
          · -- t > k·δ: t is outside closure(Icc 0 (k·δ)) — vacuous.
            push_neg at ht_left
            rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
            apply HasFDerivWithinAt.of_notMem_closure
            rw [closure_Icc, Set.mem_Icc]
            push_neg
            intro _; linarith
        -- Build Piece B: on Icc (k·δ_uniform) ((k+1)·δ_uniform).
        have hB_pos : HasDerivWithinAt (fun s => (γ_succ s).1) (γ_succ t).2
                        (Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform)) t := by
          by_cases ht_right : (k : ℝ) * δ_uniform ≤ t
          · -- t is in Icc (k·δ) ((k+1)·δ); use hβ_ode_Icc via congr.
            have ht_in : t ∈ Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform) :=
              ⟨ht_right, ht.2⟩
            -- hβ_ode_Icc's domain is Icc t_start (t_start + δ'); rewrite to ((k+1)·δ).
            have ht_in' : t ∈ Set.Icc ((k : ℝ) * δ_uniform)
                            ((k : ℝ) * δ_uniform + δ') := by
              rw [hδ'_eq_uniform, h_kδ_succ_eq]; exact ht_in
            have h_β_pos := (hβ_ode_Icc t ht_in').1
            -- Convert the within-set's right endpoint: t_start + δ' = (k+1)·δ_uniform.
            have h_set_eq : Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + δ')
                          = Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform) := by
              rw [hδ'_eq_uniform, h_kδ_succ_eq]
            rw [h_set_eq] at h_β_pos
            -- (β t).2 = (γ_succ t).2 via h_γsucc_on_right_Icc.
            have h_deriv_eq : (γ_succ t).2 = (β t).2 := by
              rw [h_γsucc_on_right_Icc t ht_in]
            rw [h_deriv_eq]
            refine h_β_pos.congr (fun y hy => ?_) ?_
            · rw [h_γsucc_on_right_Icc y hy]
            · rw [h_γsucc_on_right_Icc t ht_in]
          · -- t < k·δ: t outside closure(Icc (k·δ) (...)) — vacuous.
            push_neg at ht_right
            rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
            apply HasFDerivWithinAt.of_notMem_closure
            rw [closure_Icc, Set.mem_Icc]
            push_neg
            intro h_le; exfalso; linarith
        -- Combine via .union and rewrite the set union.
        have h_union_pos := hA_pos.union hB_pos
        have h_set_union : Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform) ∪
                           Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform)
                         = Set.Icc (0 : ℝ) (((k + 1 : ℕ) : ℝ) * δ_uniform) := by
          rw [Set.Icc_union_Icc_eq_Icc h_kδ_nn h_kδ_le_succ_kδ]
        rw [h_set_union] at h_union_pos
        -- Now do the analogous velocity component.
        refine ⟨h_union_pos, ?_⟩
        -- Build velocity Piece A: on Icc 0 (k·δ).
        have hA_vel : HasDerivWithinAt (fun s => (γ_succ s).2)
                        (-(convolveFunctionMeasure gradW (ρ t) (γ_succ t).1))
                        (Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform)) t := by
          by_cases ht_left : t ≤ (k : ℝ) * δ_uniform
          · have ht_in : t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * δ_uniform) := ⟨ht.1, ht_left⟩
            have h_γk_vel := (h_ode_k t ht_in).2
            have h_pos_eq : (γ_succ t).1 = (γ_k t).1 := by
              rw [h_γsucc_left t ht_left]
            rw [h_pos_eq]
            refine h_γk_vel.congr (fun y hy => ?_) ?_
            · rw [h_γsucc_left y hy.2]
            · rw [h_γsucc_left t ht_left]
          · push_neg at ht_left
            rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
            apply HasFDerivWithinAt.of_notMem_closure
            rw [closure_Icc, Set.mem_Icc]
            push_neg
            intro _; linarith
        -- Build velocity Piece B: on Icc (k·δ) ((k+1)·δ).
        have hB_vel : HasDerivWithinAt (fun s => (γ_succ s).2)
                        (-(convolveFunctionMeasure gradW (ρ t) (γ_succ t).1))
                        (Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform)) t := by
          by_cases ht_right : (k : ℝ) * δ_uniform ≤ t
          · have ht_in : t ∈ Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform) :=
              ⟨ht_right, ht.2⟩
            have ht_in' : t ∈ Set.Icc ((k : ℝ) * δ_uniform)
                            ((k : ℝ) * δ_uniform + δ') := by
              rw [hδ'_eq_uniform, h_kδ_succ_eq]; exact ht_in
            have h_β_vel := (hβ_ode_Icc t ht_in').2
            have h_set_eq : Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + δ')
                          = Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform) := by
              rw [hδ'_eq_uniform, h_kδ_succ_eq]
            rw [h_set_eq] at h_β_vel
            have h_pos_eq : (γ_succ t).1 = (β t).1 := by
              rw [h_γsucc_on_right_Icc t ht_in]
            rw [h_pos_eq]
            refine h_β_vel.congr (fun y hy => ?_) ?_
            · rw [h_γsucc_on_right_Icc y hy]
            · rw [h_γsucc_on_right_Icc t ht_in]
          · push_neg at ht_right
            rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
            apply HasFDerivWithinAt.of_notMem_closure
            rw [closure_Icc, Set.mem_Icc]
            push_neg
            intro h_le; exfalso; linarith
        have h_union_vel := hA_vel.union hB_vel
        rw [h_set_union] at h_union_vel
        exact h_union_vel
      · -- (s.7) Velocity bound (TIGHT invariant):
        --   ‖γ_succ((k+1)·δ).2‖ ≤ ‖z₀.2‖ + a/2 + M·((k+1)·δ).
        -- Strategy: mean-value-on-β.2 over Icc (k·δ) ((k+1)·δ) gives
        --   ‖β((k+1)·δ).2 - β(k·δ).2‖ ≤ M·δ_uniform,
        -- then triangle + IH velocity bound at k·δ gives the (k+1)-th step.
        -- The window's velocity derivative is the (norm-≤-M) force from hβ_ode_Icc.
        have h_kδ_lt_succ_kδ : (k : ℝ) * δ_uniform < ((k + 1 : ℕ) : ℝ) * δ_uniform := by
          rw [← h_kδ_succ_eq]; linarith
        have h_succ_kδ_in : ((k + 1 : ℕ) : ℝ) * δ_uniform ∈
            Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform) :=
          ⟨le_of_lt h_kδ_lt_succ_kδ, le_refl _⟩
        have h_kδ_in : (k : ℝ) * δ_uniform ∈
            Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform) :=
          ⟨le_refl _, le_of_lt h_kδ_lt_succ_kδ⟩
        have h_convex_window :
            Convex ℝ (Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform)) :=
          convex_Icc _ _
        -- Extract the β-velocity HasDerivWithinAt on the window from hβ_ode_Icc.
        have h_set_eq_β : Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + δ')
                        = Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform) := by
          rw [hδ'_eq_uniform, h_kδ_succ_eq]
        have h_β_vel_window : ∀ s ∈ Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform),
            HasDerivWithinAt (fun u => (β u).2)
              (-(convolveFunctionMeasure gradW (ρ s) (β s).1))
              (Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform)) s := by
          intro s hs
          have hs' : s ∈ Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + δ') := by
            rw [h_set_eq_β]; exact hs
          have := (hβ_ode_Icc s hs').2
          rwa [h_set_eq_β] at this
        -- Force bound on the window — uses the lifted `h_β_in_ball` above.
        have h_force_window : ∀ s ∈ Set.Icc ((k : ℝ) * δ_uniform) (((k + 1 : ℕ) : ℝ) * δ_uniform),
            ‖-(convolveFunctionMeasure gradW (ρ s) (β s).1)‖ ≤ (M : ℝ) := by
          intro s hs
          rw [norm_neg]
          have hs_time : s ∈ Set.Icc ((k : ℝ) * δ_uniform) ((k : ℝ) * δ_uniform + 1) := by
            refine ⟨hs.1, ?_⟩
            calc s ≤ ((k + 1 : ℕ) : ℝ) * δ_uniform := hs.2
              _ = (k : ℝ) * δ_uniform + δ_uniform := by push_cast; ring
              _ ≤ (k : ℝ) * δ_uniform + 1 := by linarith [hδ_le_one]
          exact hbound_local s hs_time (β s).1 (h_β_in_ball s hs)
        -- Apply mean-value at endpoints (k+1)·δ and k·δ.
        have h_mv : ‖(β (((k + 1 : ℕ) : ℝ) * δ_uniform)).2 - (β ((k : ℝ) * δ_uniform)).2‖
                    ≤ (M : ℝ) * ‖((k + 1 : ℕ) : ℝ) * δ_uniform - (k : ℝ) * δ_uniform‖ :=
          h_convex_window.norm_image_sub_le_of_norm_hasDerivWithin_le
            h_β_vel_window h_force_window h_kδ_in h_succ_kδ_in
        have h_diff : ‖((k + 1 : ℕ) : ℝ) * δ_uniform - (k : ℝ) * δ_uniform‖ = δ_uniform := by
          have h_diff_eq : ((k + 1 : ℕ) : ℝ) * δ_uniform - (k : ℝ) * δ_uniform = δ_uniform := by
            push_cast; ring
          rw [h_diff_eq, Real.norm_of_nonneg (le_of_lt hδ_pos)]
        rw [h_diff] at h_mv
        -- γ_succ((k+1)·δ) = β((k+1)·δ) (since (k+1)·δ > k·δ).
        have h_succ_eq_β : γ_succ (((k + 1 : ℕ) : ℝ) * δ_uniform)
                         = β (((k + 1 : ℕ) : ℝ) * δ_uniform) :=
          h_γsucc_right _ h_kδ_lt_succ_kδ
        -- β(k·δ) = γ_k(k·δ) by hβ_init.
        have h_β_at_kδ : (β ((k : ℝ) * δ_uniform)).2 = (γ_k ((k : ℝ) * δ_uniform)).2 := by
          rw [hβ_init]
        -- Final triangle:
        --   ‖γ_succ((k+1)·δ).2‖ = ‖β((k+1)·δ).2‖
        --     ≤ ‖β((k+1)·δ).2 - β(k·δ).2‖ + ‖β(k·δ).2‖
        --     ≤ M·δ + ‖γ_k(k·δ).2‖
        --     ≤ M·δ + (‖z₀.2‖ + a/2 + M·(k·δ))   (IH h_vel_k)
        --     = ‖z₀.2‖ + a/2 + M·((k+1)·δ).
        show ‖(γ_succ (((k + 1 : ℕ) : ℝ) * δ_uniform)).2‖
              ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (((k + 1 : ℕ) : ℝ) * δ_uniform)
        rw [h_succ_eq_β]
        have h_succ_kδ_expand : ((k + 1 : ℕ) : ℝ) * δ_uniform
                              = (k : ℝ) * δ_uniform + δ_uniform := by push_cast; ring
        calc ‖(β (((k + 1 : ℕ) : ℝ) * δ_uniform)).2‖
            ≤ ‖(β (((k + 1 : ℕ) : ℝ) * δ_uniform)).2 - (β ((k : ℝ) * δ_uniform)).2‖
                + ‖(β ((k : ℝ) * δ_uniform)).2‖ := by
              have h_decomp : (β (((k + 1 : ℕ) : ℝ) * δ_uniform)).2
                = ((β (((k + 1 : ℕ) : ℝ) * δ_uniform)).2 - (β ((k : ℝ) * δ_uniform)).2)
                  + (β ((k : ℝ) * δ_uniform)).2 := (sub_add_cancel _ _).symm
              calc ‖(β (((k + 1 : ℕ) : ℝ) * δ_uniform)).2‖
                  = ‖((β (((k + 1 : ℕ) : ℝ) * δ_uniform)).2 - (β ((k : ℝ) * δ_uniform)).2)
                        + (β ((k : ℝ) * δ_uniform)).2‖ := by rw [← h_decomp]
                _ ≤ _ := norm_add_le _ _
          _ ≤ (M : ℝ) * δ_uniform + ‖(γ_k ((k : ℝ) * δ_uniform)).2‖ := by
              have h_norm_eq : ‖(β ((k : ℝ) * δ_uniform)).2‖
                             = ‖(γ_k ((k : ℝ) * δ_uniform)).2‖ := by rw [h_β_at_kδ]
              linarith [h_mv, h_norm_eq]
          _ ≤ (M : ℝ) * δ_uniform + (‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((k : ℝ) * δ_uniform)) := by
              linarith [h_vel_k]
          _ = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (((k + 1 : ℕ) : ℝ) * δ_uniform) := by
              rw [h_succ_kδ_expand]; ring
      · -- (s.7) Position bound (LINEAR invariant) via Helper 3.
        -- Compose: Helper 2 gives window-wide velocity bound ≤ V_max;
        -- Helper 3 then gives endpoint position bound `h_pos_init + V_max·δ`.
        -- Triangle / arithmetic to match the (k+1)-step invariant.
        -- The velocity-init bound for Helper 2: ‖γ_k(k·δ).2‖ (= ‖w.2‖)
        -- bounded by tight IH `‖z₀.2‖ + a/2 + M·(k·δ)`.
        have h_vel_init_w : ‖(γ_k ((k : ℝ) * δ_uniform)).2‖
                          ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((k : ℝ) * δ_uniform) :=
          h_vel_k
        -- Helper 2 output: pointwise velocity bound on the window.
        have h_vel_window_tight :=
          vlasov_window_velocity_bound gradW ρ
            (γ_k ((k : ℝ) * δ_uniform)) a M
            ((k : ℝ) * δ_uniform) δ_uniform hδ_pos hδ_global_le_one
            (‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((k : ℝ) * δ_uniform))
            h_vel_init_w β hβ_init
            (fun t ht => (hβ_ode_Icc_unified t ht).2)
            h_β_in_ball_native hbound_local
        -- Derive ‖(β s).2‖ ≤ V_max from the tight pointwise bound + (k+1)·δ ≤ T+1.
        have h_V_max_real : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T + 1) := by
          have h_V_def : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((T + 1).toNNReal : ℝ) := by
            simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
          rw [h_V_def, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ T + 1)]
        have h_window_vel_Vmax : ∀ s ∈ Set.Icc ((k : ℝ) * δ_uniform)
                                  ((k : ℝ) * δ_uniform + δ_uniform),
            ‖(β s).2‖ ≤ (V_max : ℝ) := by
          intro s hs
          have h_s_le_T1 : s ≤ T + 1 := by
            calc s ≤ (k : ℝ) * δ_uniform + δ_uniform := hs.2
              _ = ((k + 1 : ℕ) : ℝ) * δ_uniform := h_kδ_succ_eq
              _ ≤ T + 1 := h_succ_kδ_le
          have h_s_minus_nn : 0 ≤ s - (k : ℝ) * δ_uniform := by linarith [hs.1]
          have h_M_nn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
          have h_vel_at_s := h_vel_window_tight s hs
          -- h_vel_at_s : ‖(β s).2‖ ≤ ‖z₀.2‖ + a/2 + M·(k·δ) + M·(s - k·δ)
          --             = ‖z₀.2‖ + a/2 + M·s ≤ ‖z₀.2‖ + a/2 + M·(T+1) = V_max.
          rw [h_V_max_real]
          have h_sum : (M : ℝ) * ((k : ℝ) * δ_uniform) + (M : ℝ) * (s - (k : ℝ) * δ_uniform)
                     = (M : ℝ) * s := by ring
          have h_M_s_le : (M : ℝ) * s ≤ (M : ℝ) * (T + 1) :=
            mul_le_mul_of_nonneg_left h_s_le_T1 h_M_nn
          linarith [h_vel_at_s]
        -- Helper 3 application: position bound at endpoint.
        have h_pos_init_at_w : ‖(γ_k ((k : ℝ) * δ_uniform)).1 - z₀.1‖
                            ≤ (a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ_uniform) := h_pos_k
        have h_pos_carry :=
          vlasov_window_position_bound gradW ρ
            (γ_k ((k : ℝ) * δ_uniform)) ((k : ℝ) * δ_uniform) δ_uniform hδ_pos
            (V_max : ℝ) z₀.1
            ((a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ_uniform))
            h_pos_init_at_w β hβ_init
            (fun t ht => (hβ_ode_Icc_unified t ht).1)
            h_window_vel_Vmax
        -- h_pos_carry : ‖(β (k·δ + δ)).1 - z₀.1‖ ≤ a/2 + V_max·(k·δ) + V_max·δ.
        -- Goal: ‖(γ_succ ((k+1)·δ)).1 - z₀.1‖ ≤ a/2 + V_max·((k+1)·δ).
        -- Connect: γ_succ ((k+1)·δ) = β ((k+1)·δ) = β (k·δ + δ) (h_γsucc_right + h_kδ_succ_eq).
        have h_kδ_lt_succ_kδ : (k : ℝ) * δ_uniform < ((k + 1 : ℕ) : ℝ) * δ_uniform := by
          rw [← h_kδ_succ_eq]; linarith
        have h_γsucc_eq_β : (γ_succ (((k + 1 : ℕ) : ℝ) * δ_uniform)).1
                          = (β ((k : ℝ) * δ_uniform + δ_uniform)).1 := by
          rw [h_γsucc_right _ h_kδ_lt_succ_kδ, h_kδ_succ_eq]
        show ‖(γ_succ (((k + 1 : ℕ) : ℝ) * δ_uniform)).1 - z₀.1‖
              ≤ (a : ℝ) / 2 + (V_max : ℝ) * (((k + 1 : ℕ) : ℝ) * δ_uniform)
        rw [h_γsucc_eq_β]
        have h_succ_expand : ((k + 1 : ℕ) : ℝ) * δ_uniform
                           = (k : ℝ) * δ_uniform + δ_uniform := h_kδ_succ_eq.symm
        rw [h_succ_expand]
        calc ‖(β ((k : ℝ) * δ_uniform + δ_uniform)).1 - z₀.1‖
            ≤ (a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ_uniform) + (V_max : ℝ) * δ_uniform :=
              h_pos_carry
          _ = (a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ_uniform + δ_uniform) := by ring
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


/-! ## Stage C — Lagrangian → Eulerian: pushforward solves weak Vlasov

The pushforward `vlasovSolutionViaPushforward charX charV f₀` satisfies
`IsVlasovSolution`.  This connects the ODE side (`IsCharacteristicFlow`,
pointwise `HasDerivAt`) to the PDE side (`IsVlasovSolution`,
`WeakEvolutionEq` distributional formulation), closing the Lagrangian-
Eulerian loop that Mathlib does not provide.

**Decomposition (per the `clear-picture-now-the-starry-sparrow` plan).**

Four named helpers, used as black boxes by the wrapper:

  * **SC.1** `vlasov_pushforward_integral_eq_compose` — change of
    variables: `∫ φ d(map flow_s f₀) = ∫ (φ ∘ flow_s) df₀`.  Direct
    `integral_map`.  *(closed)*
  * **SC.2** `vlasov_traj_chain_rule` — pointwise chain rule:
    `HasDerivAt (s ↦ φ (charX s z, charV s z)) [formula] t`, using
    `hflow`'s ODE pointwise `HasDerivAt`s and the chain rule on `φ`.
    *(sorry'd — the product fderiv decomposition step needs API
    threading that is not wired up; see body comment.)*
  * **SC.3** `vlasov_pushforward_hasDerivAt_under_integral` —
    differentiation-under-integral via
    `hasDerivAt_integral_of_dominated_loc_of_lip`.  Requires a
    dominated-integrable Lipschitz bound on `s ↦ φ ∘ flow_s` uniform
    in `z`; this is the diff-under-integral technical heart.  *(sorry'd
    with detailed strategy — needs hypothesis enrichment.)*
  * **SC.4** `vlasov_rhs_pushforward_back` — push the chain-rule RHS
    back through `integral_map` to match `WeakEvolutionEq`'s shape.
    Symmetric to SC.1.  *(closed)*

The wrapper composes them: SC.1 (rewrite LHS) → SC.3 (diff-under-integral,
consuming SC.2 pointwise) → SC.4 (rewrite RHS).  Composition glue is
closed.  Remaining sorries: SC.2 body, SC.3 body, and one sub-sorry
inside the wrapper for AE-strong-measurability of the dot-product
integrand (continuity threading via smoothness of `φ` and Lipschitz
of `gradW`).  Sorry count for CharacteristicFlow.lean: 1 → 3, all on
targeted, narrow goals. -/

/-- **SC.1: integral change-of-variables for the Vlasov pushforward.**
Direct application of `integral_map`. -/
lemma vlasov_pushforward_integral_eq_compose
    {d : ℕ} [NeZero d]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (s : ℝ)
    (h_meas : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_aesm : AEStronglyMeasurable φ
                  (vlasovSolutionViaPushforward charX charV f₀ s)) :
    ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := by
  unfold vlasovSolutionViaPushforward
  exact integral_map h_meas hφ_aesm

/-- **SC.2: pointwise chain rule along the characteristic trajectory.**

For fixed `t` and fixed `z`, the curve `s ↦ φ (charX s z, charV s z)`
has derivative
`⟨charV t z, gradXφ (charX t z, charV t z)⟩
 − ⟨(∇W ∗ ρ_t)(charX t z), gradVφ (charX t z, charV t z)⟩`
at `t`.  Proof: chain rule on `φ ∘ (charX · z, charV · z)`, using
`hflow`'s pointwise `HasDerivAt`s and the gradient formula for `φ`'s
directional derivative. -/
lemma vlasov_traj_chain_rule
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (hX_deriv : ∀ t z, HasDerivAt (fun s => charX s z) (charV t z) t)
    (hV_deriv : ∀ t z, HasDerivAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)
    (t : ℝ) (z : PhaseSpace d) :
    HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
  -- Strategy: (a) Joint pair has HasDerivAt with derivative
  -- `(charV t z, -(∇W∗ρ_t)(charX t z))`.
  -- (b) `φ` is `ContDiff` so has an FDeriv at the image point.
  -- (c) Chain rule (`HasFDerivAt.comp_hasDerivAt`) gives HasDerivAt of
  -- the composite, with derivative `fderiv φ (flow_t z) (charV t z, -(∇W∗ρ_t)(charX t z))`.
  -- (d) The product fderiv splits via the gradient formula:
  --     `fderiv φ (x,v) (a,b) = ⟨gradXφ (x,v), a⟩ + ⟨gradVφ (x,v), b⟩`.
  -- (e) Substituting `(a,b) := (charV t z, -(∇W∗ρ_t)(charX t z))` and using
  --     bilinearity of inner product with the negation gives the claimed formula.
  --
  -- Step (a): joint pair HasDerivAt
  have hpair : HasDerivAt (fun s => (charX s z, charV s z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) t :=
    (hX_deriv t z).prodMk (hV_deriv t z)
  -- Step (b): φ has FDeriv at the image point
  have hFDeriv : HasFDerivAt φ (fderiv ℝ φ (charX t z, charV t z)) (charX t z, charV t z) :=
    (hφ_smooth.differentiable (by simp) _).hasFDerivAt
  -- Step (c): chain rule
  have hchain : HasDerivAt (fun s => φ (charX s z, charV s z))
      ((fderiv ℝ φ (charX t z, charV t z))
        (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z)))) t :=
    hFDeriv.comp_hasDerivAt t hpair
  -- Step (d): compute the value equality
  have hval : (fderiv ℝ φ (charX t z, charV t z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) =
      @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z)) := by
    -- Set up partial derivative identities (same pattern as h_integrand_aesm)
    set z₀ := (charX t z, charV t z)
    have hdiffφ : DifferentiableAt ℝ φ z₀ :=
      hφ_smooth.differentiable (by simp) z₀
    have hfderiv_X : fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z₀.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z₀.1 :=
        hasFDerivAt_prodMk_left z₀.1 z₀.2
      exact (h1.comp z₀.1 h2).fderiv
    have hfderiv_V : fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z₀.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z₀.2 :=
        hasFDerivAt_prodMk_right z₀.1 z₀.2
      exact (h1.comp z₀.2 h2).fderiv
    -- Decompose fderiv φ z₀ applied to (a, b) via inl/inr
    set F := fderiv ℝ φ z₀
    set a := charV t z
    set b := -(convolveFunctionMeasure gradW (ρ t) (charX t z))
    have hdecomp : F (a, b) = F (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) +
        F (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) := by
      rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      simp [← F.map_add]
    -- Differentiability of partial functions
    have hdiffX : DifferentiableAt ℝ (fun x => φ (x, z₀.2)) z₀.1 :=
      hdiffφ.comp z₀.1 (differentiableAt_id.prodMk (differentiableAt_const z₀.2))
    have hdiffV : DifferentiableAt ℝ (fun v => φ (z₀.1, v)) z₀.2 :=
      hdiffφ.comp z₀.2 ((differentiableAt_const z₀.1).prodMk differentiableAt_id)
    -- The two partial gradient inner products
    have hX_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
        @inner ℝ (PhysSpace d) _ a (gradXφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
          fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 a := by rw [hfderiv_X]; rfl
      rw [hstep, ← inner_gradient_left hdiffX, ← hgradXφ z₀, real_inner_comm]
    have hV_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
        @inner ℝ (PhysSpace d) _ b (gradVφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
          fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 b := by rw [hfderiv_V]; rfl
      rw [hstep, ← inner_gradient_left hdiffV, ← hgradVφ z₀, real_inner_comm]
    rw [hdecomp, hX_inner, hV_inner, show b = -(convolveFunctionMeasure gradW (ρ t) (charX t z))
        from rfl, inner_neg_left]
    ring
  rwa [hval] at hchain

/-- **Dominated-bundle data for SC.3.**

Packages the four ancillary hypotheses required by Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_lip` (excluding the pointwise
`HasDerivAt` which SC.2 already provides):
  * a neighborhood `nhd ∈ nhds t` on which the dominated Lipschitz bound holds;
  * eventual AE-strong-measurability of `(z ↦ φ ∘ flow_s)` for `s` near `t`;
  * integrability of the integrand at `s = t`;
  * AE-strong-measurability of the pointwise derivative as a function of `z`;
  * a `bound : PhaseSpace d → ℝ` with `Integrable bound f₀` such that, ae-z,
    the curve `s ↦ φ(charX s z, charV s z)` is `Real.nnabs (bound z)`-Lipschitz
    on `nhd`.

The dominated-bound clause is the technical heart: deriving it requires
a uniform-in-`z` bound on the flow speed `(charV s z, V̇(s,z))` on the
support of `φ`, which the eventual `vlasovWellPosedness` caller will
produce from Picard-Lindelof local-flow boundedness + `HasCompactSupport φ`. -/
def DiffUnderIntegralData
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ) : Prop :=
  ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
    nhd ∈ nhds t ∧
    (∀ᶠ s' in nhds t,
      AEStronglyMeasurable (fun z => φ (charX s' z, charV s' z)) f₀) ∧
    Integrable (fun z => φ (charX t z, charV t z)) f₀ ∧
    AEStronglyMeasurable
      (fun z => @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
                - @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW (ρ t) (charX t z))
                    (gradVφ (charX t z, charV t z))) f₀ ∧
    (∀ᵐ z ∂f₀,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
    Integrable bound f₀

/-- **SC.3: differentiation under the integral for the pushforward integral.**

`HasDerivAt (s ↦ ∫ z, φ (charX s z, charV s z) ∂f₀) (∫ z, [pointwise deriv] ∂f₀) t`,
where the pointwise derivative at `t` is the chain-rule formula from SC.2.

Proven by direct application of Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_lip`, given the
`DiffUnderIntegralData` bundle and the pointwise derivative from SC.2.

The signature widening (taking `h_data : DiffUnderIntegralData ...` as a
hypothesis) is the structural-close from the
`clear-picture-now-the-starry-sparrow` plan: SC.3's body becomes a one-line
Mathlib application; the burden of producing the dominated-bundle data
moves to the caller (currently sorry'd inside Stage C's wrapper as a
single bundled sub-sorry; eventually discharged by `vlasovWellPosedness`
from compact support of `φ` plus Picard regularity). -/
lemma vlasov_pushforward_hasDerivAt_under_integral
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ)
    (h_pointwise : ∀ z, HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t)
    (h_data : DiffUnderIntegralData gradW ρ charX charV f₀ φ gradXφ gradVφ t) :
    HasDerivAt (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀)
      (∫ z, @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
            - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (ρ t) (charX t z))
                (gradVφ (charX t z, charV t z))
          ∂f₀) t := by
  obtain ⟨nhd, bound, hnhd, hF_meas, hF_int, hF'_meas, h_lipsch, h_bound_int⟩ := h_data
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := f₀) (x₀ := t) (bound := bound) (s := nhd)
    (F := fun s' z => φ (charX s' z, charV s' z))
    hnhd hF_meas hF_int hF'_meas
    h_lipsch h_bound_int
    (Filter.Eventually.of_forall h_pointwise)).2

/-- **SC.4: push the chain-rule RHS back through `integral_map`.**

`∫ z, [formula(charX t z, charV t z)] df₀ = ∫ y, [formula(y)] d(map flow_t f₀)`.

Symmetric to SC.1; the same `integral_map` invocation, applied to the
dot-product integrand.  Closes by `integral_map` after establishing AE-
strong-measurability of the integrand. -/
lemma vlasov_rhs_pushforward_back
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (t : ℝ)
    (h_meas : AEMeasurable (fun z : PhaseSpace d => (charX t z, charV t z)) f₀)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) y.1)
            (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t)) :
    ∫ z, @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
         - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              (charX t z))
            (gradVφ (charX t z, charV t z))
        ∂f₀
      = ∫ y, @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW
                  (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) y.1)
                (gradVφ y)
            ∂(vlasovSolutionViaPushforward charX charV f₀ t) := by
  -- Direct application of integral_map in reverse direction, on the dot-product
  -- integrand.  The integrand at `(charX t z, charV t z)` is precisely the
  -- pre-image of the y-integrand under the pushforward map.
  unfold vlasovSolutionViaPushforward at h_integrand_aesm ⊢
  exact (integral_map h_meas h_integrand_aesm).symm

/-! ## Stage C bundle sub-helpers (SC.5 – SC.8)

Per the `clear-picture-now-the-starry-sparrow` plan, the
`DiffUnderIntegralData` bundle inside Stage C's wrapper is decomposed
into four named regularity sub-helpers:

  * **SC.5** `vlasov_compose_flow_aestronglymeas` — eventual
    AE-strong-measurability of `φ ∘ flow_s` near `t`.
  * **SC.6** `vlasov_compose_flow_integrable_at` — integrability of
    `φ ∘ flow_t` against `f₀` (uses `HasCompactSupport φ`).
  * **SC.7** `vlasov_pointwise_deriv_aestronglymeas` — AE-strong-
    measurability of the chain-rule pointwise derivative (same shape
    as the wrapper's `h_integrand_aesm` proof).
  * **SC.8** `vlasov_trajectory_lipschitz_bound` — the HARD one: the
    dominated Lipschitz bound on `s ↦ φ(charX s z, charV s z)` with an
    `f₀`-integrable Lipschitz coefficient.  Genuinely requires a
    uniform velocity bound on `nhd × (flow_t)⁻¹(supp φ)`.

SC.5/6/7 are intended to be closable by sorry-prover; SC.8 is the
single named regularity gap pending future work. -/

/-- **SC.5: AE-strong-measurability of `φ ∘ flow_s` for s near t.**

The composition `z ↦ φ (charX s' z, charV s' z)` is AE-strongly-
measurable wrt `f₀` for every `s'`, in particular for `s'` in any
neighborhood of `t`.  Uses continuity of `φ` plus
`h_flow_meas`'s AE-measurability of the flow pair. -/
lemma vlasov_compose_flow_aestronglymeas
    {d : ℕ} [NeZero d]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ) (hφ_cont : Continuous φ)
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (t : ℝ) :
    ∀ᶠ s' in nhds t, AEStronglyMeasurable
      (fun z => φ (charX s' z, charV s' z)) f₀ := by
  apply Filter.Eventually.of_forall
  intro s'
  exact hφ_cont.comp_aestronglyMeasurable (h_flow_meas s').aestronglyMeasurable

/-- **SC.6: Integrability of `φ ∘ flow_t` against `f₀`.**

`HasCompactSupport φ` + `Continuous φ` give boundedness; combined with
`[IsProbabilityMeasure f₀]` this yields integrability. -/
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

/-- **SC.7: AE-strong-measurability of the pointwise derivative.**

The chain-rule pointwise derivative integrand
`⟨charV t z, gradXφ(flow_t z)⟩ - ⟨convolve_t(charX t z), gradVφ(flow_t z)⟩`
is AE-strongly-measurable wrt `f₀`.  Same continuity argument as the
wrapper's `h_integrand_aesm` proof. -/
lemma vlasov_pointwise_deriv_aestronglymeas
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ)
    (h_flow_meas_t : AEMeasurable
      (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) :
    AEStronglyMeasurable
      (fun z => @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
                - @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW (ρ t) (charX t z))
                    (gradVφ (charX t z, charV t z))) f₀ := by
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


/-- **SC.8: Dominated Lipschitz bound (the hard sub-helper).**

The bundled existential: a neighborhood `nhd` of `t` plus a per-z
Lipschitz coefficient `bound z` such that
`s ↦ φ(charX s z, charV s z)` is `Real.nnabs (bound z)`-Lipschitz on
`nhd` for ae-z, with `bound` `f₀`-integrable.

**Status: sorry'd.**  Closing this helper requires a uniform-in-(s, z)
bound on the trajectory speed `(charV s z, V̇(s, z))` on
`nhd × (flow_t)⁻¹(supp φ)`.  Standard approach: compact image of flow
under continuous map + uniform-in-s bound on the convolution.  May
require widening with an `h_speed_bound` hypothesis at the wrapper
level (deferred per the plan).

In-project consumer: the Stage C wrapper's `h_diff_data` compose step. -/
lemma vlasov_trajectory_lipschitz_bound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_compact : HasCompactSupport φ)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  sorry

/-- **`_lag` variant of SC.8** — `vlasov_trajectory_lipschitz_bound` with the
flow-growth prerequisites supplied as explicit hypotheses, enabling the
dominated Lipschitz bound to be derived via Gronwall on the characteristic
ODE (see `flow_distance_growth_bound` above).  Used by future `_lag` variants
of the Stage C chain that route through `IsLagrangianVlasovSolution`. -/
lemma vlasov_trajectory_lipschitz_bound_lag
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_compact : HasCompactSupport φ)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) (ht_pos : 0 < t)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc 0 (t + 1), ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc 0 (t + 1),
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s)) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  -- Step 1: Get Gronwall growth bound C_T on [0, t+1]
  obtain ⟨C_T, hC_T_nn, hC_T⟩ := flow_distance_growth_bound gradW L hL ρ charX charV
      ⟨hflow_init, hflow_x, hflow_v⟩ (t + 1) (by linarith) M_ρ hM_ρ_nn hM_ρ h_y_int h_int
  -- Step 2: Bound ‖fderiv ℝ φ‖ uniformly (compact support + continuous fderiv)
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by norm_num)
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_smooth.continuous_fderiv (by norm_num)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
  obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  have hM_φ_nn : 0 ≤ M_φ :=
    le_trans (norm_nonneg (fderiv ℝ φ (0 : PhaseSpace d))) (hM_φ _)
  -- Gronwall constants: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ
  set K := 1 + (L : ℝ)
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Convolution bound (same derivation as flow_distance_growth_bound)
  have h_conv_bound : ∀ s ∈ Set.Icc 0 (t + 1), ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
    intro s hs x
    unfold convolveFunctionMeasure
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
      Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
        (Filter.Eventually.of_forall fun y => by
          simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
    have h_pt : ∀ y : PhysSpace d, ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
          integral_mono (h_int s x).norm h_bnd_int (fun y => h_pt y)
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
          have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(ρ s)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                  integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                  rw [integral_add (integrable_const _) (h_y_int s hs)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
          simp only [ε₀]; linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- Step 3: Choose neighborhood nhd = Ioo (t/2) (t + 1/2) ⊆ Icc 0 (t+1)
  refine ⟨Set.Ioo (t / 2) (t + 1 / 2),
    fun z => M_φ * (K * C_T + ε₀) * (‖z‖ + 1), ?_, ?_, ?_⟩
  · -- nhd ∈ nhds t
    exact Ioo_mem_nhds (by linarith) (by linarith)
  · -- LipschitzOnWith for ae-z
    apply Filter.Eventually.of_forall
    intro z
    -- For each z, apply MVT on convex nhd
    -- For each z, prove the derivative bound then apply MVT
    -- Define the derivative value as a function
    let deriv_val : ℝ → PhaseSpace d → ℝ := fun s z =>
      (fderiv ℝ φ (charX s z, charV s z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
    -- The derivative witness function f' for lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioo _ _)
      (f' := fun s => deriv_val s z)
    · -- HasDerivWithinAt for each s ∈ nhd
      intro s hs
      have h_flow_deriv : HasDerivAt (fun s' => (charX s' z, charV s' z))
          (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))) s :=
        (hflow_x s z).prodMk (hflow_v s z)
      have h_φ_fderiv : HasFDerivAt φ (fderiv ℝ φ (charX s z, charV s z))
          (charX s z, charV s z) :=
        hφ_diff (charX s z, charV s z) |>.hasFDerivAt
      exact (h_φ_fderiv.comp_hasDerivAt s h_flow_deriv).hasDerivWithinAt
    · -- Bound ‖deriv_val s z‖₊ ≤ Real.nnabs (M_φ * (K * C_T + ε₀) * (‖z‖ + 1))
      intro s hs
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm']
      have hs_mem : s ∈ Set.Icc 0 (t + 1) :=
        ⟨le_of_lt (by linarith [hs.1]),
         le_of_lt (by linarith [hs.2])⟩
      have h_flow_bnd : ‖(charX s z, charV s z)‖ ≤ C_T * (‖z‖ + 1) :=
        hC_T s hs_mem z
      have h_x_bnd : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_left ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_v_bnd2 : ‖charV s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_right ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_c_bnd : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          ε₀ + (L : ℝ) * C_T * (‖z‖ + 1) := by
        have := h_conv_bound s hs_mem (charX s z)
        linarith [mul_le_mul_of_nonneg_left h_x_bnd (NNReal.coe_nonneg L)]
      have h_vel_bnd : ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖
          ≤ K * C_T * (‖z‖ + 1) + ε₀ := by
        rw [Prod.norm_def]
        simp only [Prod.fst, Prod.snd, norm_neg]
        have hK1 : (1 : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
        have hz1 : (0 : ℝ) ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
        apply max_le
        · -- ‖charV s z‖ ≤ K * C_T * (‖z‖ + 1) + ε₀
          have h1 : C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hC_T_nn) hz1
            linarith
          linarith
        · -- ‖conv‖ ≤ K * C_T * (‖z‖ + 1) + ε₀
          have hLK : (L : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
          have h2 : (L : ℝ) * C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLK hC_T_nn) hz1
            linarith
          linarith
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
      calc ‖deriv_val s z‖
          ≤ ‖fderiv ℝ φ (charX s z, charV s z)‖ *
            ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M_φ * (K * C_T * (‖z‖ + 1) + ε₀) := by
            apply mul_le_mul (hM_φ _) h_vel_bnd (norm_nonneg _) hM_φ_nn
        _ ≤ M_φ * (K * C_T + ε₀) * (‖z‖ + 1) := by
            have hz1 : 1 ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
            nlinarith [mul_nonneg hM_φ_nn hε₀_nn,
                       mul_nonneg (mul_nonneg hM_φ_nn hε₀_nn) (by linarith [norm_nonneg z] : (0:ℝ) ≤ ‖z‖),
                       mul_nonneg hM_φ_nn hC_T_nn]
  · -- Integrable bound z
    have h_bound_eq : (fun z : PhaseSpace d => M_φ * (K * C_T + ε₀) * (‖z‖ + 1)) =
        fun z => M_φ * (K * C_T + ε₀) * ‖z‖ + M_φ * (K * C_T + ε₀) := by
      ext z; ring
    rw [h_bound_eq]
    exact (hf₀_fm.const_mul _).add (integrable_const _)

/-- The Lagrangian → Eulerian equivalence: the pushforward of `f₀`
under a characteristic flow satisfies the weak Vlasov equation.

This connects the ODE side (`IsCharacteristicFlow`, with its
pointwise `HasDerivAt`) to the PDE side (`IsVlasovSolution`, with
its weak-evolution `WeakEvolutionEq` formulation), closing the
Lagrangian-Eulerian loop that Mathlib does not provide.

**Hypothesis-widening (Stage C decomposition).**  Beyond `hflow` and
`hself`, the wrapper requires:
  * `h_flow_meas` — AE-measurability of the joint flow map
    `(charX s, charV s)` per `s`, used for `integral_map` change of
    variables in SC.1/SC.4.
  * `hgradW_cont` — continuity of the convolution kernel, used to
    establish continuity (hence AE-strong-measurability) of the
    convolution `x ↦ ∫ y, gradW (x - y) ∂(ρ t)` against the
    pushforward measure.
Eventual callers (e.g. `vlasovWellPosedness`) will derive these from
the regularity of Picard solutions and from `[AssW W]`'s smoothness
hypothesis on `W`. -/
theorem vlasovSolutionViaPushforward_isVlasovSolution
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hflow : IsCharacteristicFlow gradW
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              charX charV)
    (hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    /- Continuity of the spatial-marginal convolution in x, for each time s.
       Eventually derivable from hgradW_cont + integrability; added as a hypothesis
       to keep the proof of h_integrand_aesm tractable. -/
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsVlasovSolution gradW (vlasovSolutionViaPushforward charX charV f₀) := by
  -- Unfold IsVlasovSolution; for each test function φ, prove WeakEvolutionEq.
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t
  -- WeakEvolutionEq: HasDerivAt (fun s => ∫ φ d(pushforward s)) (RHS + 0) t.
  -- Notation aliases.
  set ρ : ℝ → Measure (PhysSpace d) :=
    fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) with hρ_def
  -- φ is continuous, hence AE-strongly-measurable wrt any measure.
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_aesm_general : ∀ μ : Measure (PhaseSpace d),
      AEStronglyMeasurable φ μ := fun μ => hφ_cont.aestronglyMeasurable
  -- SC.1 (used twice): unify ∫ φ d(vlasov s) with ∫ (φ ∘ flow_s) df₀.
  have h_compose : ∀ s, ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := fun s =>
    vlasov_pushforward_integral_eq_compose charX charV f₀ s
      (h_flow_meas s) φ (hφ_aesm_general _)
  -- SC.2: pointwise chain rule at every z.
  have h_pointwise := fun z =>
    vlasov_traj_chain_rule gradW ρ charX charV φ hφ_smooth
      gradXφ gradVφ hgradXφ hgradVφ hflow.2.1 hflow.2.2 t z
  -- SC.3: lift to differentiation-under-integral.  The `DiffUnderIntegralData`
  -- bundle is composed from the four named sub-helpers SC.5–SC.8 (defined
  -- just above the wrapper):
  --   * SC.5 supplies AE-strong-measurability of `φ ∘ flow_s` near t.
  --   * SC.6 supplies integrability of `φ ∘ flow_t` against f₀.
  --   * SC.7 supplies AE-strong-measurability of the pointwise derivative.
  --   * SC.8 supplies the dominated Lipschitz bound + integrable coefficient,
  --     plus the witness `nhd` and `bound` data.
  -- Only SC.8 remains as a named regularity gap pending future work.
  have h_diff_data : DiffUnderIntegralData gradW ρ charX charV f₀
      φ gradXφ gradVφ t := by
    -- Extract the hard sub-bundle from SC.8.
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasov_trajectory_lipschitz_bound gradW ρ charX charV f₀ φ
        hφ_smooth hφ_compact hflow hgradW_cont hconv_cont t
    -- Assemble: ⟨nhd, bound, hnhd, hF_meas, hF_int, hF'_meas, h_lipsch, h_bound_int⟩.
    refine ⟨nhd, bound, hnhd, ?_, ?_, ?_, h_lipsch, h_bound_int⟩
    · exact vlasov_compose_flow_aestronglymeas charX charV f₀ φ
        hφ_cont h_flow_meas t
    · exact vlasov_compose_flow_integrable_at charX charV f₀ φ
        hφ_cont hφ_compact t (h_flow_meas t)
    · exact vlasov_pointwise_deriv_aestronglymeas gradW ρ charX charV f₀
        φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ hconv_cont t (h_flow_meas t)
  have h_under_integral :=
    vlasov_pushforward_hasDerivAt_under_integral gradW ρ charX charV f₀
      φ gradXφ gradVφ t h_pointwise h_diff_data
  -- SC.4: push the inner integral's value back through the pushforward.
  -- We need AE-strong-measurability of the integrand wrt the pushforward.
  -- The integrand uses gradXφ, gradVφ (continuous because φ is C∞), the
  -- convolution (continuous in y.1 — Lipschitz of gradW + Continuous), and
  -- linear/bilinear inner products.  We package this as a single
  -- continuity-then-AEStronglyMeasurable step.
  have h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t) := by
    -- The integrand is a difference of two continuous functions, hence AEStronglyMeasurable.
    apply Continuous.aestronglyMeasurable
    apply Continuous.sub
    · -- First term: ⟨y.2, gradXφ y⟩. Continuous since gradXφ is continuous.
      apply Continuous.inner continuous_snd
      -- gradXφ z = (toDual ℝ _).symm ((fderiv ℝ φ z).comp inl). Continuous.
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
      simp_rw [heqX, gradient, hfderiv_X]
      exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        ((ContinuousLinearMap.isBoundedLinearMap_comp_right
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
          (hφ_smooth.continuous_fderiv (by simp)))
    · -- Second term: ⟨convolveFunctionMeasure gradW (ρ t) y.1, gradVφ y⟩. Continuous.
      apply Continuous.inner
      · -- convolveFunctionMeasure gradW (ρ t) ∘ Prod.fst is continuous via hconv_cont.
        -- ρ t = spatialMarginal (vlasovSolutionViaPushforward ...) by definition.
        exact (hconv_cont t).comp continuous_fst
      · -- gradVφ z = (toDual ℝ _).symm ((fderiv ℝ φ z).comp inr). Continuous.
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
        simp_rw [heqV, gradient, hfderiv_V]
        exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
          ((ContinuousLinearMap.isBoundedLinearMap_comp_right
            (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
            (hφ_smooth.continuous_fderiv (by simp)))
  have h_push_back :=
    vlasov_rhs_pushforward_back gradW charX charV f₀ t
      (h_flow_meas t) gradXφ gradVφ h_integrand_aesm
  -- Compose: rewrite LHS via h_compose into pushforward-integral form, apply
  -- h_under_integral, then rewrite the derivative's RHS via h_push_back.
  -- The target is `HasDerivAt (s ↦ ∫ φ d(vlasov s)) (∫ ... ∂(vlasov t) + 0) t`.
  -- Step A: `(fun s => ∫ φ d(vlasov s)) = (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀)`.
  have hLHS : (fun s => ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s)) =
              (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀) := funext h_compose
  rw [hLHS]
  -- Step B: rewrite the derivative value via h_push_back; the +0 is
  -- definitionally absorbed by the `WeakEvolutionEq` shape.
  rw [show (∫ z, @inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
              - @inner ℝ (PhysSpace d) _
                  (convolveFunctionMeasure gradW
                    (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) z.1)
                  (gradVφ z)
            ∂(vlasovSolutionViaPushforward charX charV f₀ t)
            + (fun _ => (0 : ℝ)) t)
          = ∫ z, @inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
                  - @inner ℝ (PhysSpace d) _
                      (convolveFunctionMeasure gradW
                        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) z.1)
                      (gradVφ z)
                ∂(vlasovSolutionViaPushforward charX charV f₀ t) from by ring]
  rw [← h_push_back]
  exact h_under_integral

/-- **Stage C producer for `IsLagrangianVlasovSolution`**: same hypothesis
package as `vlasovSolutionViaPushforward_isVlasovSolution`, but produces the
*strictly stronger* `IsLagrangianVlasovSolution` predicate by additionally
exposing the characteristic flow `(charX, charV)` and the pushforward
equation `f t = (charX t, charV t)_# (f 0)`.

The pushforward equation is essentially `rfl` once we know
`vlasovSolutionViaPushforward charX charV f₀ 0 = f₀` — which follows from
`IsCharacteristicFlow`'s initial-condition conjunct (`charX 0 z = z.1`,
`charV 0 z = z.2`, so the time-0 map is the identity and `Measure.map id`
acts trivially). -/
theorem vlasovSolutionViaPushforward_isLagrangianVlasovSolution
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hflow : IsCharacteristicFlow gradW
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              charX charV)
    (hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsLagrangianVlasovSolution gradW (vlasovSolutionViaPushforward charX charV f₀) := by
  -- The wrapper closes the IsVlasovSolution conjunct.
  refine ⟨vlasovSolutionViaPushforward_isVlasovSolution gradW charX charV f₀
            hflow hself h_flow_meas hgradW_cont hconv_cont,
          charX, charV, hflow, ?_, ?_⟩
  · -- Pushforward equation: f t = (flow_t)_# (f 0).
    -- Reduces to vlasovSolutionViaPushforward charX charV f₀ 0 = f₀, via
    -- (charX 0, charV 0) = id (from IsCharacteristicFlow's initial condition).
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow.1 z
      exact Prod.ext h.1 h.2
    have h0 : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      simp [vlasovSolutionViaPushforward, h_init, Measure.map_id]
    intro t
    -- vlasovSolutionViaPushforward charX charV f₀ t
    --   = Measure.map (charX t, charV t) f₀          (by defn)
    --   = Measure.map (charX t, charV t) (vlasov 0)  (h0)
    rw [h0]
    rfl
  · -- AEMeasurability wrt (f 0).  We have it wrt f₀, and (f 0) = f₀.
    intro s
    -- Goal: AEMeasurable (...) (vlasovSolutionViaPushforward charX charV f₀ 0)
    -- The map f₀ ↦ (vlasov 0) is the same as h0 above; same hypothesis works.
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow.1 z
      exact Prod.ext h.1 h.2
    have h0 : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      simp [vlasovSolutionViaPushforward, h_init, Measure.map_id]
    rw [h0]
    exact h_flow_meas s

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

-- ---------------------------------------------------------------------------
-- §9  Theorem (Existence and uniqueness for Vlasov)   (tex: thm:vlasov-wp)
-- ---------------------------------------------------------------------------
-- Relocated from `Vlasov/Basic.lean` (Stage 0 of the well-posedness plan) so
-- the proof can compose directly with the characteristic-flow infrastructure
-- developed in this file: `exists_vlasov_characteristicFlow`,
-- `flow_distance_growth_bound`, and
-- `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`.  The
-- `HasFiniteFirstMoment` predicate remains in `Basic.lean`.

/-- (tex: thm:vlasov-wp)
Existence and uniqueness for the Vlasov equation.

Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) be a probability measure with finite first moment.
Under Assumption ass:W, there exists a unique narrowly continuous curve
t ↦ f_t ∈ 𝒫_1(ℝ^d × ℝ^d) satisfying eq:vlasov in the distributional sense
with f_{t=0} = f_0.
-/
theorem vlasovWellPosedness
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) :
    ∃! f : ℝ → Measure (PhaseSpace d),
      -- initial condition
      f 0 = f₀ ∧
      -- each f_t has finite first moment
      (∀ t, HasFiniteFirstMoment (f t)) ∧
      -- f solves the Vlasov equation
      IsVlasovSolution gradW f ∧
      -- f is narrowly continuous: t ↦ ∫ g df_t is continuous for every bounded continuous g
      (∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        Continuous (fun t => ∫ z, g z ∂f t)) := by
  sorry

/-! ## Phase 1 callsite probe

A type-check probe to catch any partial-widening bug in the global theorem's
hypotheses.  If the `T → T + 1` widening is partial (one occurrence missed),
this `example` fails to elaborate, surfacing the error before Phase 2/3
work begins.  Concrete specialisation: `a = M = T = 1` so that `T + 1 = 2`
appears in `hbound` and in the quadratic-in-(T+1) `hR` form. -/
example {d : ℕ} [NeZero d] (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d)
    (R : NNReal)
    (hR : 2 * ((1 : NNReal) : ℝ) + (‖z₀.2‖ + ((1 : NNReal) : ℝ) / 2) * (1 + 1)
          + ((1 : NNReal) : ℝ) * (1 + 1) ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 + 1),
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ 1) :
    True := by
  have _ := exists_vlasov_characteristicFlow W gradW hgradW L hL ρ h_int hρ_cont
    z₀ 1 (by norm_num) 1 1 (by norm_num) R hR hbound
  trivial

end Vlasov
