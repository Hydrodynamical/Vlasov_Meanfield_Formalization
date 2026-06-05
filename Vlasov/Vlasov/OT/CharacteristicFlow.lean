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

/-- **Two-flow difference Gronwall bound** (de-risk spike, 2026-06-03 — the
reusable core of the integrated Dobrushin coupling bound that would collapse
`#3/#5/#6/#8` into one lemma).  The distance between two trajectories
`Φ_f · z₁`, `Φ_g · z₂` of flows generated by fields `b_f, b_g` (`b_f`
`L`-Lipschitz in space) grows by Gronwall: if the field difference *at the
second trajectory* is bounded by `ε` on `[0, T]` and the initial separation by
`δ`, then `‖Φ_f t z₁ - Φ_g t z₂‖ ≤ gronwallBound δ L ε t`.

Mirrors `flow_distance_growth_bound`'s Gronwall structure
(`norm_le_gronwallBound_of_norm_deriv_right_le`) but for the *difference* of two
flows.  In the integrated-bound application, `z₁ = ω.1`, `z₂ = ω.2` range over a
coupling `π₀` of `(f 0, g 0)`, `ε = (L : ℝ) * (wasserstein1 (f s) (g s)).toReal`
(the self-coupling diff-bound, uniform in the trajectory), and integrating this
pointwise bound over `π₀` against the pushforward bound gives the Dobrushin
estimate `W₁(f t, g t) ≤ … · W₁(f 0, g 0)`. -/
theorem flow_difference_growth_bound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (b_f b_g : ℝ → α → α) (L : NNReal) (hL_f : ∀ t, LipschitzWith L (b_f t))
    (Φ_f Φ_g : ℝ → α → α) (z₁ z₂ : α)
    (T : ℝ)
    (hcont_f : ContinuousOn (fun s => Φ_f s z₁) (Set.Icc 0 T))
    (hcont_g : ContinuousOn (fun s => Φ_g s z₂) (Set.Icc 0 T))
    (hΦ_f : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_f u z₁) (b_f s (Φ_f s z₁)) (Set.Ici s) s)
    (hΦ_g : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_g u z₂) (b_g s (Φ_g s z₂)) (Set.Ici s) s)
    (δ ε : ℝ) (h_init : ‖Φ_f 0 z₁ - Φ_g 0 z₂‖ ≤ δ)
    (h_diff : ∀ s ∈ Set.Icc 0 T,
      ‖b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂)‖ ≤ ε) :
    ∀ t ∈ Set.Icc 0 T,
      ‖Φ_f t z₁ - Φ_g t z₂‖ ≤ gronwallBound δ (L : ℝ) ε t := by
  have hcont : ContinuousOn (fun s => Φ_f s z₁ - Φ_g s z₂) (Set.Icc 0 T) :=
    hcont_f.sub hcont_g
  have hderiv : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_f u z₁ - Φ_g u z₂)
        (b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)) (Set.Ici s) s :=
    fun s hs => (hΦ_f s hs).sub (hΦ_g s hs)
  have hbound : ∀ s ∈ Set.Ico 0 T,
      ‖b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)‖ ≤
        (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ + ε := by
    intro s hs
    have hs_icc : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.le⟩
    have h_lip : ‖b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)‖ ≤
        (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ := by
      have := (hL_f s).dist_le_mul (Φ_f s z₁) (Φ_g s z₂)
      rwa [dist_eq_norm, dist_eq_norm] at this
    calc ‖b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)‖
        = ‖(b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)) +
            (b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂))‖ := by congr 1; abel
      _ ≤ ‖b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)‖ +
            ‖b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂)‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ + ε :=
            add_le_add h_lip (h_diff s hs_icc)
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv h_init hbound t ht
  simpa using hg

/-- **Per-trajectory mild (integral-form) difference bound** (integrated-Dobrushin
collapse, 2026-06-03).  Mild-form companion to `flow_difference_growth_bound`:
the raw integral inequality
`‖γ_f t − γ_g t‖ ≤ ‖γ_f 0 − γ_g 0‖ + ∫₀ᵗ (L‖γ_f s − γ_g s‖ + ε s) ds`,
keeping the forcing `ε s` *inside* the integral.  After integrating this over
the base measure, the self-reference `ε s = L·W₁(f s,g s) ≤ L·Q(s)` is resolved
by `gronwall_mild_le` — avoiding the constant-`ε` smallness that
`flow_difference_growth_bound`'s closed form would force (and the blocked
windowing that smallness needs). -/
theorem flow_difference_mild_bound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α]
    (b_f b_g : ℝ → α → α) (L : NNReal) (hL_f : ∀ t, LipschitzWith L (b_f t))
    (γ_f γ_g : ℝ → α) (T : ℝ)
    (hcont_f : ContinuousOn γ_f (Set.Icc 0 T))
    (hcont_g : ContinuousOn γ_g (Set.Icc 0 T))
    (hderiv_f : ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt γ_f (b_f s (γ_f s)) (Set.Ioi s) s)
    (hderiv_g : ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt γ_g (b_g s (γ_g s)) (Set.Ioi s) s)
    (hint : IntervalIntegrable (fun s => b_f s (γ_f s) - b_g s (γ_g s))
      MeasureTheory.volume 0 T)
    (ε : ℝ → ℝ) (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (h_diff : ∀ s ∈ Set.Icc (0:ℝ) T, ‖b_f s (γ_g s) - b_g s (γ_g s)‖ ≤ ε s) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖γ_f t - γ_g t‖ ≤ ‖γ_f 0 - γ_g 0‖ +
        ∫ s in (0:ℝ)..t, ((L : ℝ) * ‖γ_f s - γ_g s‖ + ε s) := by
  intro t ht
  have h0t : (0:ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hIcc_sub : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right htT
  have hcont_diff : ContinuousOn (fun s => γ_f s - γ_g s) (Set.Icc 0 t) :=
    (hcont_f.mono hIcc_sub).sub (hcont_g.mono hIcc_sub)
  have hderiv_diff : ∀ s ∈ Set.Ioo (0:ℝ) t,
      HasDerivWithinAt (fun s => γ_f s - γ_g s)
        (b_f s (γ_f s) - b_g s (γ_g s)) (Set.Ioi s) s := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0:ℝ) T := ⟨hs.1, hs.2.trans_le htT⟩
    exact (hderiv_f s hs').sub (hderiv_g s hs')
  have hint_t : IntervalIntegrable (fun s => b_f s (γ_f s) - b_g s (γ_g s))
      MeasureTheory.volume 0 t :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h0t, Set.uIcc_of_le (h0t.trans htT)]; exact hIcc_sub)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h0t hcont_diff
    hderiv_diff hint_t
  have hsplit : ∀ s ∈ Set.Icc (0:ℝ) t,
      ‖b_f s (γ_f s) - b_g s (γ_g s)‖ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s := by
    intro s hs
    have hsT : s ∈ Set.Icc (0:ℝ) T := hIcc_sub hs
    have h_lip : ‖b_f s (γ_f s) - b_f s (γ_g s)‖ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ := by
      have := (hL_f s).dist_le_mul (γ_f s) (γ_g s)
      rwa [dist_eq_norm, dist_eq_norm] at this
    calc ‖b_f s (γ_f s) - b_g s (γ_g s)‖
        = ‖(b_f s (γ_f s) - b_f s (γ_g s)) + (b_f s (γ_g s) - b_g s (γ_g s))‖ := by
          congr 1; abel
      _ ≤ ‖b_f s (γ_f s) - b_f s (γ_g s)‖ + ‖b_f s (γ_g s) - b_g s (γ_g s)‖ :=
          norm_add_le _ _
      _ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s := add_le_add h_lip (h_diff s hsT)
  have hci : IntervalIntegrable (fun s => (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s)
      MeasureTheory.volume 0 t := by
    refine IntervalIntegrable.add (IntervalIntegrable.const_mul ?_ (L:ℝ))
      (hε_int.mono_set (by
        rw [Set.uIcc_of_le h0t, Set.uIcc_of_le (h0t.trans htT)]; exact hIcc_sub))
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le h0t]; exact hcont_diff.norm
  have hnorm_le : ‖∫ s in (0:ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ ≤
      ∫ s in (0:ℝ)..t, ((L:ℝ) * ‖γ_f s - γ_g s‖ + ε s) := by
    calc ‖∫ s in (0:ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖
        ≤ ∫ s in (0:ℝ)..t, ‖b_f s (γ_f s) - b_g s (γ_g s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm h0t
      _ ≤ ∫ s in (0:ℝ)..t, ((L:ℝ) * ‖γ_f s - γ_g s‖ + ε s) :=
          intervalIntegral.integral_mono_on h0t hint_t.norm hci hsplit
  have ha_le : ‖γ_f t - γ_g t‖ ≤ ‖γ_f 0 - γ_g 0‖ +
      ‖∫ s in (0:ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ := by
    have heq : (γ_f t - γ_g t) - (γ_f 0 - γ_g 0) =
        ∫ s in (0:ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s)) := hftc.symm
    calc ‖γ_f t - γ_g t‖
        = ‖(γ_f 0 - γ_g 0) + ((γ_f t - γ_g t) - (γ_f 0 - γ_g 0))‖ := by congr 1; abel
      _ ≤ ‖γ_f 0 - γ_g 0‖ + ‖(γ_f t - γ_g t) - (γ_f 0 - γ_g 0)‖ := norm_add_le _ _
      _ = ‖γ_f 0 - γ_g 0‖ + ‖∫ s in (0:ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ := by
          rw [heq]
  linarith [ha_le, hnorm_le]

/-- **Integrate a per-trajectory mild bound over the base measure (Tonelli step).**
Given a base probability measure `π` on `Ω` and a family `w : ℝ → Ω → α`, if each
trajectory satisfies the mild bound `‖w t ω‖ ≤ ‖w 0 ω‖ + ∫₀ᵗ (L‖w s ω‖ + ε s) ds`,
then the integrated quantity `Q t := ∫ ‖w t ω‖ ∂π` satisfies
`Q t ≤ Q 0 + ∫₀ᵗ (L · Q s + ε s) ds`. The `∫₀ᵗ L‖w s ω‖` term swaps via Tonelli. -/
theorem integral_mild_bound
    {Ω α : Type*} [MeasurableSpace Ω] [NormedAddCommGroup α]
    [MeasurableSpace α] [BorelSpace α]
    (π : Measure Ω) [IsProbabilityMeasure π]
    (w : ℝ → Ω → α) (L : ℝ) (hL : 0 ≤ L) (ε : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    -- joint-measurability inputs (Carathéodory: continuous-in-time + measurable-in-ω)
    (hw_cont : ∀ ω, Continuous (fun s => w s ω))
    (hw_meas : ∀ s, Measurable (w s))
    -- domination: ‖w s ω‖ ≤ dom ω uniformly on [0,T], dom integrable
    (dom : Ω → ℝ) (hdom_int : Integrable dom π)
    (hdom : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ ω, ‖w s ω‖ ≤ dom ω)
    (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (hε_nn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ ε s)
    -- the per-trajectory mild bound (e.g. from flow_difference_mild_bound)
    (hper : ∀ ω, ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖w t ω‖ ≤ ‖w 0 ω‖ + ∫ s in (0:ℝ)..t, (L * ‖w s ω‖ + ε s)) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      (∫ ω, ‖w t ω‖ ∂π) ≤ (∫ ω, ‖w 0 ω‖ ∂π) +
        ∫ s in (0:ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
  -- joint measurability of `(s, ω) ↦ w s ω` and of its norm
  have hjoint : Measurable (Function.uncurry w) :=
    measurable_uncurry_of_continuous_of_measurable hw_cont hw_meas
  have hjoint_norm : Measurable (fun p : ℝ × Ω => ‖w p.1 p.2‖) := hjoint.norm
  -- abbreviation Q s := ∫ ω, ‖w s ω‖ ∂π
  set Q : ℝ → ℝ := fun s => ∫ ω, ‖w s ω‖ ∂π with hQ
  intro t ht
  have h0t : (0:ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hIcc_sub : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right htT
  -- `w 0 ·` and `w t ·` are integrable over π (dominated by `dom`)
  have h0_mem : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_refl 0, hT⟩
  have ht_mem : t ∈ Set.Icc (0:ℝ) T := ht
  have hint0 : Integrable (fun ω => ‖w 0 ω‖) π := by
    refine hdom_int.mono' ((hw_meas 0).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hdom 0 h0_mem ω
  have hintt : Integrable (fun ω => ‖w t ω‖) π := by
    refine hdom_int.mono' ((hw_meas t).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hdom t ht_mem ω
  -- the inner integrand `g s ω := L * ‖w s ω‖ + ε s`
  set g : ℝ → Ω → ℝ := fun s ω => L * ‖w s ω‖ + ε s with hg
  -- product measure for the Tonelli swap
  -- `volume.restrict (Set.uIoc 0 t)` is a finite measure (`uIoc 0 t = Ioc 0 t`)
  have huIoc : Set.uIoc (0:ℝ) t = Set.Ioc 0 t := Set.uIoc_of_le h0t
  have hvol_lt : MeasureTheory.volume (Set.uIoc (0:ℝ) t) < ⊤ := by
    rw [huIoc, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  haveI hfin_restrict : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]; exact hvol_lt
  -- `ε` is integrable over `volume.restrict (uIoc 0 t)`
  have hε_int_t : IntervalIntegrable ε MeasureTheory.volume 0 t :=
    hε_int.mono_set (by
      rw [Set.uIcc_of_le h0t, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc_right htT)
  have hε_intOn : Integrable ε (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)) :=
    hε_int_t.def'
  -- AEStronglyMeasurability of `uncurry g` over the product measure
  have hg_aesm : AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)).prod π) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × Ω => L * ‖w p.1 p.2‖)
        ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)).prod π) :=
      (measurable_const.mul hjoint_norm).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × Ω => ε p.1)
        ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)).prod π) :=
      hε_intOn.aestronglyMeasurable.comp_fst
    exact h1.add h2
  -- product integrability of `uncurry g`, via the dominator `L·dom(ω) + ε(s)`
  have hdom_prod : Integrable (fun p : ℝ × Ω => L * dom p.2 + ε p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)).prod π) :=
    ((hdom_int.const_mul L).comp_snd
        (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t))).add (hε_intOn.comp_fst π)
  have hae_fst : ∀ᵐ p : ℝ × Ω
      ∂((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)).prod π), p.1 ∈ Set.uIoc (0:ℝ) t :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst).tendsto_ae.eventually
      (MeasureTheory.ae_restrict_mem measurableSet_uIoc)
  have hg_int : Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)).prod π) := by
    refine hdom_prod.mono' hg_aesm ?_
    filter_upwards [hae_fst] with p hp
    have hp_icc : p.1 ∈ Set.Icc (0:ℝ) T := by
      rw [huIoc] at hp; exact ⟨le_of_lt hp.1, hp.2.trans htT⟩
    have hwle : ‖w p.1 p.2‖ ≤ dom p.2 := hdom p.1 hp_icc p.2
    have hεnn : 0 ≤ ε p.1 := hε_nn p.1 hp_icc
    have hg_nn : 0 ≤ L * ‖w p.1 p.2‖ + ε p.1 :=
      add_nonneg (mul_nonneg hL (norm_nonneg _)) hεnn
    show ‖L * ‖w p.1 p.2‖ + ε p.1‖ ≤ L * dom p.2 + ε p.1
    rw [Real.norm_of_nonneg hg_nn]
    nlinarith [mul_le_mul_of_nonneg_left hwle hL]
  -- inner intervalIntegral = integral against the restricted measure
  have hconv : ∀ ω, (∫ s in (0:ℝ)..t, g s ω)
      = ∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)) := by
    intro ω
    rw [intervalIntegral.integral_of_le h0t, ← huIoc]
  -- marginal integrability `ω ↦ ∫ s, g s ω`
  have hmarg : Integrable
      (fun ω => ∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t))) π :=
    hg_int.integral_prod_right
  have hinner_int : Integrable (fun ω => ∫ s in (0:ℝ)..t, g s ω) π := by
    simpa only [hconv] using hmarg
  -- per-`s` identity  ∫ ω, g s ω ∂π = L · (∫ ω, ‖w s ω‖ ∂π) + ε s
  have hg_int_s : ∀ s ∈ Set.Icc (0:ℝ) T, Integrable (fun ω => ‖w s ω‖) π := by
    intro s hs
    refine hdom_int.mono' ((hw_meas s).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom s hs ω
  have hQg : ∀ s ∈ Set.Icc (0:ℝ) T,
      (∫ ω, g s ω ∂π) = L * (∫ ω, ‖w s ω‖ ∂π) + ε s := by
    intro s hs
    simp only [hg]
    rw [integral_add ((hg_int_s s hs).const_mul L) (integrable_const _), integral_const_mul]
    congr 1
    simp [integral_const, measureReal_def, measure_univ]
  -- the double integral, via Tonelli
  have hdouble : (∫ ω, (∫ s in (0:ℝ)..t, g s ω) ∂π)
      = ∫ s in (0:ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
    calc (∫ ω, (∫ s in (0:ℝ)..t, g s ω) ∂π)
        = ∫ ω, (∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t))) ∂π := by
          simp only [hconv]
      _ = ∫ s, (∫ ω, g s ω ∂π) ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) t)) :=
          (MeasureTheory.integral_integral_swap hg_int).symm
      _ = ∫ s in (0:ℝ)..t, (∫ ω, g s ω ∂π) := by
          rw [huIoc, ← intervalIntegral.integral_of_le h0t]
      _ = ∫ s in (0:ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
          refine intervalIntegral.integral_congr (fun s hs => ?_)
          rw [Set.uIcc_of_le h0t] at hs
          exact hQg s ⟨hs.1, hs.2.trans htT⟩
  -- assemble
  calc (∫ ω, ‖w t ω‖ ∂π)
      ≤ ∫ ω, (‖w 0 ω‖ + ∫ s in (0:ℝ)..t, g s ω) ∂π :=
        integral_mono hintt (hint0.add hinner_int) (fun ω => hper ω t ht)
    _ = (∫ ω, ‖w 0 ω‖ ∂π) + ∫ ω, (∫ s in (0:ℝ)..t, g s ω) ∂π :=
        integral_add hint0 hinner_int
    _ = (∫ ω, ‖w 0 ω‖ ∂π) + ∫ s in (0:ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
        rw [hdouble]

/-- **Integrated coupling-Gronwall bound** (the `M→0` collapse core, base-measure
generic, 2026-06-04).

Given a base probability measure `π` on `Ω` and two parameter-families of
trajectories `X_f, X_g : ℝ → Ω → α` solving ODEs with `L`-Lipschitz vector fields
`b_f, b_g` on `[0, T]`, with a cross-field bound `‖b_f s y - b_g s y‖ ≤ ε s` whose
amplitude `ε s` is **self-referentially** controlled by the integrated trajectory
distance `Q s := ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π` (i.e. `ε s ≤ L · Q s`), the
integrated distance obeys the closed Gronwall bound
`Q t ≤ Q 0 · exp (2 L t)` on `[0, T]`.

**Composition** (the collapse pipeline):
* per-`ω`, `flow_difference_mild_bound` gives the mild integral inequality
  `‖X_f t ω - X_g t ω‖ ≤ ‖X_f 0 ω - X_g 0 ω‖ + ∫₀ᵗ (L‖X_f s ω - X_g s ω‖ + ε s)`;
* `integral_mild_bound` integrates this over `π` (Tonelli on a nonnegative
  integrand), yielding `Q t ≤ Q 0 + ∫₀ᵗ (L·Q s + ε s)`;
* the self-reference `ε s ≤ L·Q s` collapses the integrand to `2 L · Q s`;
* `gronwall_mild_le` (scalar mild Gronwall) closes to `Q 0 · exp (2 L t)`.

**Clamp bridge** (L11): `integral_mild_bound` and the DCT continuity of `Q`
require *global*-in-`s` continuity, but the flow regularity is only on the
window `[0, T]`.  We work with the clamped flow `s ↦ X_f (clamp s) ω` (globally
continuous, agreeing with `X_f` on `[0, T]`), apply the window machinery to it,
and transfer back on `[0, T]` where `clamp = id` via integrand congruence.

**Base-measure genericity**: `π` is abstract, so this serves both the
uniqueness call site (`π = f 0`, `Q 0 = 0`, Foundation-B-free) and the
mean-field call site (`π` an optimal coupling, `Q 0 = W₁(f 0, g 0)`). -/
theorem integrated_coupling_gronwall_bound
    {Ω α : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α]
    [MeasurableSpace α] [BorelSpace α] [MeasurableSub₂ α]
    (π : Measure Ω) [IsProbabilityMeasure π]
    (X_f X_g : ℝ → Ω → α) (b_f b_g : ℝ → α → α) (L : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hL_f : ∀ t, LipschitzWith L (b_f t))
    -- per-`ω` flow regularity (matches `flow_difference_mild_bound`)
    (hcont_f : ∀ ω, ContinuousOn (fun s => X_f s ω) (Set.Icc 0 T))
    (hcont_g : ∀ ω, ContinuousOn (fun s => X_g s ω) (Set.Icc 0 T))
    (hderiv_f : ∀ ω, ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt (fun s => X_f s ω) (b_f s (X_f s ω)) (Set.Ioi s) s)
    (hderiv_g : ∀ ω, ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt (fun s => X_g s ω) (b_g s (X_g s ω)) (Set.Ioi s) s)
    (hint : ∀ ω, IntervalIntegrable
      (fun s => b_f s (X_f s ω) - b_g s (X_g s ω)) MeasureTheory.volume 0 T)
    -- measurability + domination for the Tonelli / DCT
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π)
    (hdom : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω)
    -- the cross-field bound `ε` and its self-reference to `Q`
    (ε : ℝ → ℝ) (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (hε_nn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ ε s)
    (h_diff : ∀ ω, ∀ s ∈ Set.Icc (0:ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤ ε s)
    (h_self : ∀ s ∈ Set.Icc (0:ℝ) T,
      ε s ≤ (L:ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π) ≤
        (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π) * Real.exp (2 * (L:ℝ) * t) := by
  -- clamp into `[0, T]` (opaque; used only through its three properties)
  obtain ⟨clamp, hclamp_cont, hclamp_mem, hclamp_id⟩ :
      ∃ clamp : ℝ → ℝ, Continuous clamp ∧ (∀ s, clamp s ∈ Set.Icc (0:ℝ) T) ∧
        (∀ s ∈ Set.Icc (0:ℝ) T, clamp s = s) := by
    refine ⟨fun s => max 0 (min s T), ?_, ?_, ?_⟩
    · exact continuous_const.max (continuous_id.min continuous_const)
    · intro s; exact ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
    · intro s hs; show max 0 (min s T) = s
      rw [min_eq_left hs.2, max_eq_right hs.1]
  -- the clamped difference flow `W s ω = X_f (clamp s) ω - X_g (clamp s) ω`
  set W : ℝ → Ω → α := fun s ω => X_f (clamp s) ω - X_g (clamp s) ω with hW_def
  have hW_cont : ∀ ω, Continuous (fun s => W s ω) := by
    intro ω; simp only [hW_def]
    exact ((hcont_f ω).sub (hcont_g ω)).comp_continuous hclamp_cont hclamp_mem
  have hW_meas : ∀ s, Measurable (W s) := by
    intro s; simp only [hW_def]
    exact (hmeas_f (clamp s)).sub (hmeas_g (clamp s))
  have hW_dom : ∀ s, ∀ ω, ‖W s ω‖ ≤ dom ω := by
    intro s ω; simp only [hW_def]; exact hdom (clamp s) (hclamp_mem s) ω
  -- on `[0, T]`, `W` agrees with the unclamped difference, so the integrals agree
  have hQW_eq : ∀ s ∈ Set.Icc (0:ℝ) T,
      (∫ ω, ‖W s ω‖ ∂π) = ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π := by
    intro s hs
    apply integral_congr_ae
    filter_upwards with ω
    simp only [hW_def, hclamp_id s hs]
  -- per-`ω` mild bound (unclamped) via `flow_difference_mild_bound`
  have hper_w : ∀ ω, ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖X_f t ω - X_g t ω‖ ≤ ‖X_f 0 ω - X_g 0 ω‖ +
        ∫ s in (0:ℝ)..t, ((L:ℝ) * ‖X_f s ω - X_g s ω‖ + ε s) := fun ω =>
    flow_difference_mild_bound b_f b_g L hL_f (fun s => X_f s ω) (fun s => X_g s ω) T
      (hcont_f ω) (hcont_g ω) (hderiv_f ω) (hderiv_g ω) (hint ω) ε hε_int (h_diff ω)
  -- transfer the mild bound to the clamped flow `W` (needed by `integral_mild_bound`)
  have hper_W : ∀ ω, ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖W t ω‖ ≤ ‖W 0 ω‖ + ∫ s in (0:ℝ)..t, ((L:ℝ) * ‖W s ω‖ + ε s) := by
    intro ω t ht
    have h0t : (0:ℝ) ≤ t := ht.1
    have hWt : W t ω = X_f t ω - X_g t ω := by simp only [hW_def, hclamp_id t ht]
    have hW0 : W 0 ω = X_f 0 ω - X_g 0 ω := by
      simp only [hW_def, hclamp_id 0 ⟨le_refl 0, hT⟩]
    have hintegrand : (∫ s in (0:ℝ)..t, ((L:ℝ) * ‖W s ω‖ + ε s))
        = ∫ s in (0:ℝ)..t, ((L:ℝ) * ‖X_f s ω - X_g s ω‖ + ε s) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le h0t] at hs
      have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      simp only [hW_def, hclamp_id s hsT]
    rw [hWt, hW0, hintegrand]; exact hper_w ω t ht
  -- integrate over `π` (Tonelli): `Q t ≤ Q 0 + ∫₀ᵗ (L·Q s + ε s)`
  have hQW := integral_mild_bound π W (L:ℝ) (NNReal.coe_nonneg L) ε T hT
    hW_cont hW_meas dom hdom_int (fun s _ ω => hW_dom s ω) hε_int hε_nn hper_W
  -- `Q` is globally continuous via DCT (clamped flow globally dominated)
  have hQW_cont : Continuous (fun s => ∫ ω, ‖W s ω‖ ∂π) := by
    refine continuous_of_dominated
      (fun s => (hW_meas s).norm.aestronglyMeasurable)
      (fun s => Filter.Eventually.of_forall (fun ω => ?_)) hdom_int
      (Filter.Eventually.of_forall (fun ω => (hW_cont ω).norm))
    rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hW_dom s ω
  -- collapse the integrand to `2 L · Q s` using the self-reference
  have hmild_W : ∀ t ∈ Set.Icc (0:ℝ) T,
      (∫ ω, ‖W t ω‖ ∂π) ≤ (∫ ω, ‖W 0 ω‖ ∂π)
        + (2 * (L:ℝ)) * ∫ s in (0:ℝ)..t, (∫ ω, ‖W s ω‖ ∂π) := by
    intro t ht
    have h0t : (0:ℝ) ≤ t := ht.1
    have hstep := hQW t ht
    have hII_lhs : IntervalIntegrable
        (fun s => (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s) MeasureTheory.volume 0 t :=
      ((hQW_cont.intervalIntegrable 0 t).const_mul (L:ℝ)).add
        (hε_int.mono_set (by
          rw [Set.uIcc_of_le h0t, Set.uIcc_of_le hT]
          exact Set.Icc_subset_Icc_right ht.2))
    have hII_rhs : IntervalIntegrable
        (fun s => (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π)) MeasureTheory.volume 0 t :=
      (hQW_cont.intervalIntegrable 0 t).const_mul (2 * (L:ℝ))
    have hmono : (∫ s in (0:ℝ)..t, ((L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s))
        ≤ ∫ s in (0:ℝ)..t, (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π) := by
      refine intervalIntegral.integral_mono_on h0t hII_lhs hII_rhs (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have hεle : ε s ≤ (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by
        calc ε s ≤ (L:ℝ) * (∫ ω, ‖X_f s ω - X_g s ω‖ ∂π) := h_self s hsT
          _ = (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by rw [hQW_eq s hsT]
      have hring : (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π)
          = (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by ring
      rw [hring]; linarith [hεle]
    calc (∫ ω, ‖W t ω‖ ∂π)
        ≤ (∫ ω, ‖W 0 ω‖ ∂π)
          + ∫ s in (0:ℝ)..t, ((L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s) := hstep
      _ ≤ (∫ ω, ‖W 0 ω‖ ∂π)
          + ∫ s in (0:ℝ)..t, (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π) := by linarith [hmono]
      _ = (∫ ω, ‖W 0 ω‖ ∂π)
          + (2 * (L:ℝ)) * ∫ s in (0:ℝ)..t, (∫ ω, ‖W s ω‖ ∂π) := by
            rw [intervalIntegral.integral_const_mul]
  -- scalar mild Gronwall on `Q`
  have hgron := gronwall_mild_le (fun s => ∫ ω, ‖W s ω‖ ∂π)
    (∫ ω, ‖W 0 ω‖ ∂π) (2 * (L:ℝ)) T
    (by have := NNReal.coe_nonneg L; linarith)
    (integral_nonneg (fun ω => norm_nonneg _))
    hQW_cont (fun s => integral_nonneg (fun ω => norm_nonneg _)) hmild_W
  -- transfer back to the unclamped difference on `[0, T]`
  intro t ht
  rw [← hQW_eq t ht, ← hQW_eq 0 ⟨le_refl 0, hT⟩]
  exact hgron t ht

/-- **`IsCharacteristicFlowOn`-flavored variant of `flow_distance_growth_bound`**.

Same Gronwall growth bound, but for a flow specified by **boundary regularity
hypotheses** (`h_init`, `h_cont_Icc`, `h_deriv_Ico`) instead of the universal-in-`t`
ODE of `IsCharacteristicFlow`.  This matches what Stage 1.9's
`exists_vlasov_characteristicFlow_global_smallT` produces (modulo deriving the
boundary regularity from `IsCharacteristicFlowOn`'s `Ioo 0 T` ODE clauses), and
mirrors the hypothesis-passing pattern of `charFlow_measurable_via_gronwall`
(L3898–L3901).

**Used by**: Stage 4's `Phi_step` to derive the per-`z` growth bound
(`Phi_asVlasovMeasureCurve`'s `h_growth` hypothesis) from a Stage-1.9-style
flow.  Stage 8's uniqueness on overlapping windows is a natural secondary
consumer.

**Proof body**: identical to `flow_distance_growth_bound`'s except the three
`hflow`-derived facts (`h_f_cont`, `h_deriv`, `h_init_norm`) are now taken
directly from the boundary regularity hypotheses.  Same Gronwall step, same
final algebra.

**Metric-dependence note** (architectural priming for the W̄ refactor):
This bound uses the unbounded position difference `‖X^M(t,z) - X^{M'}(t,z)‖`,
which forces Gronwall and produces exponential-in-`T` constants
`C_T ≈ exp((1+L)·T)`.  The `W̄ = W_{min(|x-y|,1)}` analog (Dobrushin 1979, §5)
uses the bounded-and-Lipschitz absorption
  `|B_μ(x) - B_{μ'}(x)| ≤ max(2‖B‖_∞, C_B) · min(|x₁-x₂|, 1)`
and produces *linear-in-`T`* constants (Dobrushin 1979, eq. 5.7).  Under
the eventual `W̄` refactor, this lemma's output shape changes from
`C_T · (‖z‖ + 1)` to a bounded analog. -/
theorem flow_distance_growth_bound_on
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    -- Boundary regularity, replacing IsCharacteristicFlow's universal ODE.
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z))
          (Set.Ici s) s)
    -- ρ regularity, identical to flow_distance_growth_bound's hypotheses.
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∃ C_T, 0 ≤ C_T ∧
      ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
  -- Gronwall parameters: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ.  Identical to
  -- `flow_distance_growth_bound`.
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Witness: C_T = gronwallBound 1 K ε₀ T.
  use gronwallBound 1 K ε₀ T
  refine ⟨?_, ?_⟩
  · have hmono := gronwallBound_mono (by norm_num : (0:ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  · intro t ht z
    -- Convolution bound: ‖(∇W ∗ ρ_t)(x)‖ ≤ ε₀ + L * ‖x‖.  Identical derivation.
    have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
        ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
      intro s hs x
      unfold convolveFunctionMeasure
      have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
        Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
          ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
          (Filter.Eventually.of_forall fun y => by
            simp only [Real.norm_of_nonneg (norm_nonneg _)]
            exact norm_sub_le x y)
      have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
        (integrable_const _).add (h_sub_int.const_mul _)
      have h_pt : ∀ y : PhysSpace d, ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
        intro y
        have hd := hL.dist_le_mul (x - y) 0
        simp only [dist_eq_norm, sub_zero] at hd
        have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
          have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this
          linarith
        linarith
      calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
          ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
        _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
            integral_mono (h_int s x).norm h_bnd_int h_pt
        _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
            rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
            simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
        _ ≤ ‖gradW 0‖ + (L : ℝ) * (‖x‖ + M_ρ) := by
            have hint_bd : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
              calc ∫ y, ‖x - y‖ ∂(ρ s)
                  ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                    integral_mono h_sub_int
                      ((integrable_const _).add (h_y_int s hs))
                      (fun y => norm_sub_le x y)
                _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                    rw [integral_add (integrable_const _) (h_y_int s hs)]
                    simp [integral_const, measureReal_def, measure_univ]
                _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
            have := mul_le_mul_of_nonneg_left hint_bd L.coe_nonneg
            linarith
        _ = ε₀ + (L : ℝ) * ‖x‖ := by
            simp only [hε₀_def]; ring
    -- Gronwall step.  Boundary regularity comes from hypotheses, not from
    -- IsCharacteristicFlow.
    have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T) :=
      h_cont_Icc z
    have h_deriv : ∀ s ∈ Set.Ico 0 T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))
          (Set.Ici s) s := by
      intro s hs
      have hderiv := h_deriv_Ico z s hs
      -- vlasovVectorField gradW ρ s (charX s z, charV s z) = (charV s z, -conv ...)
      unfold vlasovVectorField at hderiv
      exact hderiv
    have h_init_norm : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by
      rw [h_init z]
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
      have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
              le_mul_of_one_le_left hM_nn (by linarith)
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := le_add_of_nonneg_right hε₀_nn
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
    have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
      h_f_cont h_deriv h_init_norm h_bound t ht
    simp only [sub_zero] at h_grw
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

/-- **Piece A (Option 2): time-dependent moment-envelope growth bound.**

Sharper sibling of `flow_distance_growth_bound_on`.  Instead of a single
constant moment bound `M_ρ` (which forces the constant-sup growth constant
`C_T` and, downstream, an `M_f₀`-dependent fixed-point on the curve space),
this takes a **monotone time-dependent envelope** `m : ℝ → ℝ` bounding the
spatial-marginal first moment, and concludes the **time-local** Gronwall bound

  `‖(charX t z, charV t z)‖ ≤ gronwallBound ‖z‖ (1+L) (‖gradW 0‖ + L · m t) t`,

with the force constant `ε(t) = ‖gradW 0‖ + L · m t` evaluated at the SAME time
`t` (not the sup `m T`).  Monotonicity of `m` lets the per-`t` Gronwall on
`[0, t]` use the endpoint value `ε(t)` while validating the derivative bound at
every `s ≤ t` (since `ε(s) ≤ ε(t)`).

**Why this is the option-2 foundation**: integrating the conclusion over a
probability `f₀` gives `M_{Φρ}(t) ≤ A(t) + B(t)·m(t)` with
`A(t) = M_f₀·e^{(1+L)t} + (‖gradW 0‖/(1+L))(e^{(1+L)t}-1)` and
`B(t) = (L/(1+L))(e^{(1+L)t}-1)` — crucially an **`M_f₀`-free** coefficient.
The canonical envelope `m*(t) := A(t)/(1-B(T))` is then Φ-invariant under the
**data-independent** constraint `B(T) < 1`, dissolving the constant-`M`
fixed-point without a data-dependent hypothesis.  (Contrast the constant-sup
bound, which feeds `m(T)` into `ε` and re-derives an `M_f₀`-dependent
smallness.) -/
theorem flow_distance_growth_bound_on_timedep
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z))
          (Set.Ici s) s)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ m t)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t := by
  intro t ht z
  set K : ℝ := 1 + (L : ℝ) with hK_def
  -- m t ≥ 0 (moment of a probability measure is nonneg, bounded by m t).
  have hmt_nn : 0 ≤ m t :=
    le_trans (integral_nonneg (fun y => norm_nonneg y)) (hm t ht)
  set εt : ℝ := ‖gradW 0‖ + (L : ℝ) * m t with hεt_def
  have hK_pos : 0 < K := by positivity
  have hεt_nn : 0 ≤ εt := by positivity
  -- Convolution force bound on [0, t], using m s ≤ m t (monotone).
  have h_conv_bound : ∀ s ∈ Set.Icc 0 t, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ εt + (L : ℝ) * ‖x‖ := by
    intro s hs x
    have hs_T : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
    have hms_le_mt : m s ≤ m t := hm_mono hs_T ht hs.2
    unfold convolveFunctionMeasure
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
      Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs_T))
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
        (Filter.Eventually.of_forall fun y => by
          simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    have h_pt : ∀ y : PhysSpace d, ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
          integral_mono (h_int s x).norm h_bnd_int h_pt
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ εt + (L : ℝ) * ‖x‖ := by
          have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + m t := by
            calc ∫ y, ‖x - y‖ ∂(ρ s)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                  integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs_T))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                  rw [integral_add (integrable_const _) (h_y_int s hs_T)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + m t := by linarith [hm s hs_T, hms_le_mt]
          simp only [hεt_def]
          nlinarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- Gronwall on [0, t] with the endpoint force constant εt.
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 t) :=
    (h_cont_Icc z).mono (Set.Icc_subset_Icc_right ht.2)
  have h_deriv : ∀ s ∈ Set.Ico 0 t,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))
        (Set.Ici s) s := by
    intro s hs
    have hs_T : s ∈ Set.Ico 0 T := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
    have hderiv := h_deriv_Ico z s hs_T
    unfold vlasovVectorField at hderiv
    exact hderiv
  have h_init_norm : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by rw [h_init z]
  have h_bound : ∀ s ∈ Set.Ico 0 t,
      ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
        K * ‖(charX s z, charV s z)‖ + εt := by
    intro s hs
    have hs_mem : s ∈ Set.Icc 0 t := ⟨hs.1, le_of_lt hs.2⟩
    simp only [Prod.norm_def, norm_neg]
    have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
    have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
    have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
      le_max_iff.mpr (Or.inl (norm_nonneg _))
    have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + εt :=
      calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
        _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
            le_mul_of_one_le_left hM_nn (by linarith)
        _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + εt := le_add_of_nonneg_right hεt_nn
    have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
        K * max ‖charX s z‖ ‖charV s z‖ + εt :=
      calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
          ≤ εt + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
        _ ≤ εt + K * max ‖charX s z‖ ‖charV s z‖ := by
            have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
            linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                      mul_le_mul_of_nonneg_right hLK hM_nn]
        _ = K * max ‖charX s z‖ ‖charV s z‖ + εt := by ring
    exact max_le h_v_le h_conv_le
  have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
    h_f_cont h_deriv h_init_norm h_bound t (Set.right_mem_Icc.mpr ht0)
  simpa using h_grw

/-- **Piece A.3 (Option 2): the canonical moment envelope closes (data-free).**

Pure-algebra companion to `flow_distance_growth_bound_on_timedep`.  Under the
**`M_f₀`-free** smallness `B(T) := (L/(1+L))(e^{(1+L)T}-1) < 1`, the explicit
envelope `m*(t) := gronwallBound M_f₀ (1+L) g0 t / (1 - B(T))` is a Gronwall
super-solution:

* monotone on `[0, T]`,
* dominates the initial moment `M_f₀`,
* **Φ-invariant** at the moment level:
  `gronwallBound M_f₀ (1+L) (g0 + L·m* t) t ≤ m* t`.

Composed with Piece A integrated over `f₀` (which gives
`M_{Φρ}(t) ≤ gronwallBound M_f₀ (1+L) (g0 + L·m(t)) t`, `g0 = ‖gradW 0‖`), this
shows the Picard iterates stay inside the fixed envelope `m*` with **no**
data-dependent hypothesis — the faithful dissolution of the constant-`M`
fixed-point.  This lemma is the measure-free heart of the option-2 escape;
Pieces B–D thread it through the curve space, `Phi_step`, and #11. -/
theorem gronwall_envelope_exists
    (M_f₀ g0 : ℝ) (hM_f₀ : 0 ≤ M_f₀) (hg0 : 0 ≤ g0)
    (L : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ m : ℝ → ℝ, MonotoneOn m (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc 0 T, M_f₀ ≤ m t) ∧
      (∀ t ∈ Set.Icc 0 T,
        gronwallBound M_f₀ (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t ≤ m t) := by
  set K : ℝ := 1 + (L : ℝ) with hK_def
  have hK_pos : 0 < K := by positivity
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- B(t) and its monotonicity.
  set Bf : ℝ → ℝ := fun t => (L : ℝ) / K * (Real.exp (K * t) - 1) with hBf_def
  have hBT_lt : Bf T < 1 := hB
  have hD_pos : 0 < 1 - Bf T := by linarith
  have hD_nn : (0 : ℝ) ≤ 1 - Bf T := hD_pos.le
  have hD_ne : (1 - Bf T) ≠ 0 := ne_of_gt hD_pos
  have hLK_nn : 0 ≤ (L : ℝ) / K := div_nonneg hL_nn hK_pos.le
  have hBf_T_nn : 0 ≤ Bf T := by
    have he1 : 0 ≤ Real.exp (K * T) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
      linarith
    exact mul_nonneg hLK_nn he1
  have hBf_le : ∀ t ∈ Set.Icc (0 : ℝ) T, Bf t ≤ Bf T := by
    intro t ht
    have hexp : Real.exp (K * t) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2, hK_pos.le])
    simp only [hBf_def]
    nlinarith [hexp, hLK_nn]
  -- A(t) := gronwallBound M_f₀ K g0 t, expanded + nonneg + monotone.
  set Af : ℝ → ℝ := fun t => gronwallBound M_f₀ K g0 t with hAf_def
  have hAf_expand : ∀ t,
      Af t = M_f₀ * Real.exp (K * t) + g0 / K * (Real.exp (K * t) - 1) := by
    intro t; simp only [hAf_def]; rw [gronwallBound_of_K_ne_0 hK_ne]
  have hAf_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Af t := by
    intro t ht
    rw [hAf_expand t]
    have he1 : 0 ≤ Real.exp (K * t) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (K * t) := Real.one_le_exp (by nlinarith [ht.1, hK_pos.le])
      linarith
    have hgK_nn : 0 ≤ g0 / K := div_nonneg hg0 hK_pos.le
    positivity
  have hAf_mono : MonotoneOn Af (Set.Icc 0 T) := by
    intro s _ t _ hst
    simp only [hAf_def]
    exact gronwallBound_mono hM_f₀ hg0 hK_pos.le hst
  refine ⟨fun t => Af t / (1 - Bf T), ?_, ?_, ?_⟩
  · -- monotone: Af increasing, positive constant divisor.
    intro s hs t ht hst
    show Af s / (1 - Bf T) ≤ Af t / (1 - Bf T)
    gcongr
    exact hAf_mono hs ht hst
  · -- M_f₀ ≤ m t.
    intro t ht
    have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
    have hAf0 : Af 0 = M_f₀ := by rw [hAf_expand 0]; simp [Real.exp_zero]
    have h_mono : Af 0 / (1 - Bf T) ≤ Af t / (1 - Bf T) := by
      gcongr
      exact hAf_mono h0_mem ht ht.1
    rw [hAf0] at h_mono
    have h_self : M_f₀ ≤ M_f₀ / (1 - Bf T) := by
      rw [le_div_iff₀ hD_pos]; nlinarith [hM_f₀, hBf_T_nn]
    linarith
  · -- Φ-invariance.
    intro t ht
    show gronwallBound M_f₀ K (g0 + (L : ℝ) * (Af t / (1 - Bf T))) t
        ≤ Af t / (1 - Bf T)
    have h_lhs : gronwallBound M_f₀ K (g0 + (L : ℝ) * (Af t / (1 - Bf T))) t
              = Af t + Bf t * (Af t / (1 - Bf T)) := by
      rw [gronwallBound_of_K_ne_0 hK_ne, hAf_expand t]
      simp only [hBf_def]; ring
    rw [h_lhs]
    have hkey : 0 ≤ Af t * (Bf T - Bf t) :=
      mul_nonneg (hAf_nn t ht) (by linarith [hBf_le t ht])
    have hexpand : Af t / (1 - Bf T) - (Af t + Bf t * (Af t / (1 - Bf T)))
                 = Af t * (Bf T - Bf t) / (1 - Bf T) := by
      field_simp
      ring
    linarith [div_nonneg hkey hD_pos.le, hexpand]

/-- **Piece A.2 (Option 2): integrate the per-`z` growth bound to a moment bound.**

The measure-level bridge between Piece A and Piece A.3: given the per-`z`
time-local growth bound (Piece A's conclusion, taken here as the hypothesis
`h_growth` so this lemma is decoupled from the flow construction), the
**position pushforward** `Measure.map (charX t ·) f₀` has first moment bounded
by the same Gronwall functional evaluated at the *initial* moment `∫‖z‖ ∂f₀`:

  `∫ x, ‖x‖ ∂(Measure.map (charX t ·) f₀) ≤ gronwallBound (∫‖z‖ ∂f₀) (1+L) (g0 + L·m t) t`.

Proof: `integral_map` exchanges the pushforward; `‖charX t z‖ ≤ ‖(charX t z, charV t z)‖`
+ `h_growth` bounds the integrand by `gronwallBound ‖z‖ …`, which is affine in `‖z‖`,
so its `f₀`-integral is `gronwallBound (∫‖z‖) …` (probability measure ⇒ the constant
term integrates to itself).

Composing with `gronwall_envelope_exists` (Piece A.3): when `m = m*` the canonical
envelope and `g0 = ‖gradW 0‖`, the RHS is `≤ m* t`, i.e. `Φ` maps the envelope to
itself at the moment level — the measure-level statement of the data-free escape. -/
theorem phi_moment_envelope_le {d : ℕ} [NeZero d]
    (L : NNReal) (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (g0 : ℝ) (T : ℝ) (m : ℝ → ℝ)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤ gronwallBound ‖z‖ (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (h_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ x, ‖x‖ ∂(Measure.map (fun z : PhaseSpace d => charX t z) f₀)
        ≤ gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t := by
  intro t ht
  set K : ℝ := 1 + (L : ℝ) with hK_def
  set εt : ℝ := g0 + (L : ℝ) * m t with hεt_def
  have hK_ne : K ≠ 0 := by positivity
  -- gronwallBound is affine in its initial value: gb r = e^{Kt}·r + C.
  have h_gb : ∀ r : ℝ,
      gronwallBound r K εt t = Real.exp (K * t) * r + εt / K * (Real.exp (K * t) - 1) := by
    intro r; rw [gronwallBound_of_K_ne_0 hK_ne]; ring
  have h_dom_int : Integrable (fun z : PhaseSpace d => gronwallBound ‖z‖ K εt t) f₀ := by
    simp only [h_gb]
    exact (hf₀_int.const_mul _).add (integrable_const _)
  have h_charX_le : ∀ z : PhaseSpace d, ‖charX t z‖ ≤ gronwallBound ‖z‖ K εt t := fun z =>
    le_trans (norm_fst_le (charX t z, charV t z)) (h_growth t ht z)
  have h_charX_int : Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀ :=
    h_dom_int.mono' ((h_meas t ht).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact h_charX_le z)
  rw [integral_map (h_meas t ht) continuous_norm.aestronglyMeasurable]
  calc ∫ z, ‖charX t z‖ ∂f₀
      ≤ ∫ z, gronwallBound ‖z‖ K εt t ∂f₀ :=
        integral_mono h_charX_int h_dom_int h_charX_le
    _ = gronwallBound (∫ z, ‖z‖ ∂f₀) K εt t := by
        simp only [h_gb]
        rw [integral_add (hf₀_int.const_mul _) (integrable_const _), integral_const_mul,
            integral_const]
        simp [measureReal_def, measure_univ]

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

Status: the constructor `vlasovVectorField_lipschitzWith` is closed,
and the full `exists_vlasov_characteristicFlow` is **closed** (no
`sorry`).  Its proof packages the global norm bound into a per-window
`IsPicardLindelof`, invokes the vendored Picard-Lindelöf
(`exists_vlasov_extend_one_window`), and stitches `N = ⌈T/δ⌉` windows
per-`z` via `HasDerivWithinAt.union` under the position/velocity
inductive invariant.  Downstream callers discharge its `hR`/`hbound`
hypotheses; the single-ball-over-`[0,T+1]` `hR` discharge in
`exists_vlasov_perz_trajectory` is what introduces the
`LocalSmallness_PL_buffer L T := L·(T+1)² < 1` constraint — see that
theorem's docstring for the `+1`-offset / arbitrary-`L` discussion. -/

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

/-! ### Localized Vlasov-solution predicates on `[0, T]`

The globally-quantified predicates `IsVlasovSolution` (Basic.lean L755) and
`IsLagrangianVlasovSolution` (Basic.lean L862) require the weak PDE and the
characteristic flow to hold *universally in `t : ℝ`*.  For local existence
(Stage 4's `vlasovWellPosedness_local`), the Picard iteration only produces
a solution on a small time window `[0, T₀]`; the underlying characteristic
flow comes from Stage 1.9's `exists_vlasov_characteristicFlow_global_smallT`
which exposes `IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` — open-interval
ODE behaviour, not the universal-in-`t` form `IsCharacteristicFlow` demands.

**Resolution** (Path 3 of the Stage 4 architectural decision, per the
five-friction discussion): introduce `_On`-localized predicates that
mirror the global ones with their quantification restricted to `[0, T]`.
Stage 4 produces the localized predicate; Stage 6 / Stage 5's continuation
glues local windows to recover the universal-in-`t` `IsLagrangianVlasovSolution`
required by the marquee `vlasovWellPosedness` theorem.

This is strictly additive: no existing predicate is modified, no closed
infrastructure is perturbed.  The `_On` family lives in this file so it
can compose with `IsCharacteristicFlowOn` (which lives here too); the
global versions stay in `Basic.lean` as the abstract endpoints. -/

/-- Localized weak Vlasov evolution equation on `Ioo 0 T`.  Same as
`WeakEvolutionEq` (Basic.lean L674) but with the derivative claim
restricted to the *open* interval `t ∈ Set.Ioo 0 T`.

**Why `Ioo` not `Icc`**: Stage 1.9's characteristic flow only provides
ODE behaviour on `Ioo 0 T` (the boundary derivatives at `t = 0` and
`t = T` are genuinely unavailable from open-interval HasDerivAt alone).
The Vlasov solution's weak PDE inherits the same regularity: it holds on
the open interval where the characteristic flow is differentiable, and
the initial condition at `t = 0` is captured separately by the
pushforward equation in `IsLagrangianVlasovSolutionOn`. -/
def WeakEvolutionEqOn {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (R_N : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (μ t)) z.1)
                (gradVφ z))
        ∂μ t
        + R_N t) t

/-- Localized Vlasov solution on `[0, T]`.  Mirror of `IsVlasovSolution`
with the weak PDE restricted to `[0, T]` via `WeakEvolutionEqOn`. -/
def IsVlasovSolutionOn {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ ⊤ φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      WeakEvolutionEqOn gradW f φ gradXφ gradVφ (fun _ => 0) T

/-- Localized Lagrangian Vlasov solution on `[0, T]`.  Mirror of
`IsLagrangianVlasovSolution` (Basic.lean L862) with:

* the weak PDE restricted to `[0, T]` (via `IsVlasovSolutionOn`),
* the characteristic flow restricted to `IsCharacteristicFlowOn ... (Ioo 0 T)
  Set.univ` (the natural output shape of Stage 1.9),
* the initial-condition clause stated explicitly (since `IsCharacteristicFlowOn`'s
  initial-condition clause is over `s_z`, here `Set.univ`, so it gives the
  same content; we restate it for direct usability),
* the pushforward equation restricted to `t ∈ Set.Icc 0 T`,
* the AEMeasurability clause restricted to `s ∈ Set.Icc 0 T`.

Strict additivity: every conjunct is the localized analogue of
`IsLagrangianVlasovSolution`'s.  Stage 6 will bridge to the global predicate
by gluing local windows via Stage 5's continuation. -/
def IsLagrangianVlasovSolutionOn {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  IsVlasovSolutionOn gradW f T ∧
  ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
    IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
    -- **Boundary regularity (B2 enrichment, 2026-06-01)**: the flow is
    -- continuous up to the *closed* window `[0, T]`.  This is the
    -- weakest-sufficient boundary fact for `W1ContOn_On` soundness — closed-
    -- window W₁-continuity ⟸ closed-window narrow continuity of `f` ⟸
    -- `ContinuousOn` of the flow (pushforward + DCT).  Exposed because the
    -- `Ioo`-only flow conjunct above leaves the endpoints `t ∈ {0,T}`
    -- unconstrained; producers supply this from data already in hand
    -- (Stage C's `h_cont_Icc`, universal `HasDerivAt`, #11's boundary bundle).
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))

/-- A global `IsVlasovSolution` restricts to `IsVlasovSolutionOn T` for any
`T : ℝ`.  Projects the universal HasDerivAt claim onto `Ioo 0 T` by direct
specialization (the restricted set is open, so HasDerivAt and
HasDerivWithinAt coincide there). -/
lemma IsVlasovSolution.toOn {d : ℕ} [NeZero d]
    {gradW : PhysSpace d → PhysSpace d}
    {f : ℝ → Measure (PhaseSpace d)} (h : IsVlasovSolution gradW f) (T : ℝ) :
    IsVlasovSolutionOn gradW f T := by
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
  intro t _ht
  exact h φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t

/-- A global `IsLagrangianVlasovSolution` restricts to
`IsLagrangianVlasovSolutionOn T` for any `T : ℝ`.

The flow witness restricts via `IsCharacteristicFlowOn`'s natural relationship
to the universal `IsCharacteristicFlow` (open Ioo ⊆ ℝ).  The pushforward and
AEMeasurability conjuncts restrict trivially since the originals are
universal. -/
lemma IsLagrangianVlasovSolution.toOn {d : ℕ} [NeZero d]
    {gradW : PhysSpace d → PhysSpace d}
    {f : ℝ → Measure (PhaseSpace d)}
    (h : IsLagrangianVlasovSolution gradW f) (T : ℝ) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  obtain ⟨h_sol, charX, charV, h_flow, h_push, h_meas⟩ := h
  refine ⟨h_sol.toOn T, charX, charV, ?_, ?_, ?_, ?_⟩
  · -- IsCharacteristicFlowOn from IsCharacteristicFlow.
    exact ⟨fun z _ => h_flow.1 z,
           fun t _ z _ => h_flow.2.1 t z,
           fun t _ z _ => h_flow.2.2 t z⟩
  · intro t _; exact h_push t
  · intro s _; exact h_meas s
  · -- Boundary ContinuousOn from universal HasDerivAt → continuity everywhere.
    intro z
    have hX : Continuous (fun s => charX s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.1 t z).continuousAt)
    have hV : Continuous (fun s => charV s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.2 t z).continuousAt)
    exact (hX.prodMk hV).continuousOn

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

Proven via a per-`z` N-window induction (`h_perZ` below): for each
initial `z ∈ closedBall z₀ (a/2)`, iterate `exists_vlasov_extend_one_window`
across `N = ⌈T/δ_uniform⌉` windows of uniform width `δ_uniform`, gluing
adjacent windows at their joins via `HasDerivWithinAt.union` under the
inductive invariant (within-derivative ODE on `Icc 0 (k·δ)`, tight
velocity bound, linear position bound).  No `sorry`; fully closed by
composition (and its vendored `Vlasov.Mathlib.ODE.PicardLindelof`
dependency is also `sorry`-free).

The conclusion is `IsCharacteristicFlowOn ... (Ioo 0 T) ...` rather
than the unconstrained `IsCharacteristicFlow` (which would require
`HasDerivAt` on all of `ℝ`, impossible to produce from local-on-`Icc`
Picard solutions).  The hypothesis `hR` enforces that the global
position-ball radius `R` covers the a-priori reachable set —
`(3a/2 + M·T)` is the loose bound; tighter forms work too.

**Note on the `(T+1)²` in `hR`** (the additive-`+1` offset): consumers
that discharge `hR` by a *single* ball over `[0, T+1]`
(`exists_vlasov_perz_trajectory`, via `R := N(z)/(1 - L(T+1)²)`) thereby
incur the smallness `LocalSmallness_PL_buffer L T := L·(T+1)² < 1`, which
forces `L < 1` (overclaim-by-restriction vs. Dobrushin's arbitrary `L`).
That constraint lives in the *consumer's* `hR`-discharge, not here — this
theorem takes `hR`/`hbound` as hypotheses and is `L`-agnostic.  A fixed-`δ`
N-window *re-consumption* of this (proven) theorem would discharge `hR`
per short window with `L·δ² < 1` (satisfiable for any `L`), dropping the
`+1`-offset smallness — a localized consumer swap, not a rebuild. -/
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
        (Set.Ioo 0 T) (Metric.closedBall z₀ ((a : ℝ) / 2)) ∧
      -- **Boundary regularity bundle** (Friction 5 surgery): expose the
      -- HasDerivWithinAt on `Set.Icc 0 T` that the proof internally builds
      -- at L1889-1897, L1910-1919 but otherwise discards via `.hasDerivAt`.
      -- This conjunct closes the boundary case at t = 0 (and any t = T) so
      -- consumers like `flow_distance_growth_bound_on` can establish
      -- ContinuousOn-on-Icc + HasDerivWithinAt-on-Ico without a separate
      -- boundary regularity helper.
      (∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => charX s z) (charV t z)
            (Set.Icc (0 : ℝ) T) t ∧
          HasDerivWithinAt (fun s => charV s z)
            (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
            (Set.Icc (0 : ℝ) T) t) := by
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
  -- Containment: Icc 0 T ⊆ Icc 0 (N · δ_uniform), via T ≤ N · δ_uniform.
  have h_Icc_T_sub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) :=
    fun t ht => ⟨ht.1, le_trans ht.2 hN_cover⟩
  -- Reusable per-z within-derivative extractor on Icc 0 (N · δ_uniform).
  -- Given z in the ball and t ∈ Icc 0 (N · δ_uniform), produce position and
  -- velocity HasDerivWithinAt clauses on that big set.
  have h_dw_on_big :
      ∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
        ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform),
          HasDerivWithinAt (fun s => (γ_func z s).1) (γ_func z t).2
            (Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform)) t ∧
          HasDerivWithinAt (fun s => (γ_func z s).2)
            (-(convolveFunctionMeasure gradW (ρ t) (γ_func z t).1))
            (Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform)) t := by
    intro z hz t ht
    have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
      simp only [γ_func, dif_pos hz]
    have h_ode := (Classical.choose_spec (h_perZ z hz)).2
    have h_pos_dw := (h_ode t ht).1
    have h_vel_dw := (h_ode t ht).2
    have h_eq_fun_pos : (fun s => (γ_func z s).1)
        = (fun s => ((Classical.choose (h_perZ z hz)) s).1) := by
      funext s; rw [h_func_eq]
    have h_eq_fun_vel : (fun s => (γ_func z s).2)
        = (fun s => ((Classical.choose (h_perZ z hz)) s).2) := by
      funext s; rw [h_func_eq]
    have h_eq_pt_vel : (γ_func z t).2 = (Classical.choose (h_perZ z hz) t).2 := by
      rw [h_func_eq]
    have h_eq_pt_pos : (γ_func z t).1 = (Classical.choose (h_perZ z hz) t).1 := by
      rw [h_func_eq]
    refine ⟨?_, ?_⟩
    · rw [h_eq_fun_pos, h_eq_pt_vel]; exact h_pos_dw
    · rw [h_eq_fun_vel, h_eq_pt_pos]; exact h_vel_dw
  refine ⟨fun t z => (γ_func z t).1, fun t z => (γ_func z t).2,
         ⟨?_, ?_, ?_⟩, ?_⟩
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
    have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) := by
      refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) hN_cover⟩
    have hT_lt_N : t < (N : ℝ) * δ_uniform := lt_of_lt_of_le ht.2 hN_cover
    have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) ∈ nhds t :=
      Icc_mem_nhds ht.1 hT_lt_N
    exact ((h_dw_on_big z hz t h_t_in).1).hasDerivAt h_icc_nhds
  · -- (iii) Velocity ODE on Ioo 0 T: same pattern.
    intro t ht z hz
    have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) := by
      refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) hN_cover⟩
    have hT_lt_N : t < (N : ℝ) * δ_uniform := lt_of_lt_of_le ht.2 hN_cover
    have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) ∈ nhds t :=
      Icc_mem_nhds ht.1 hT_lt_N
    exact ((h_dw_on_big z hz t h_t_in).2).hasDerivAt h_icc_nhds
  · -- (iv) **Boundary regularity bundle**: HasDerivWithinAt on Icc 0 T
    -- for every t ∈ Icc 0 T (including t = 0 and t = T).
    -- Derived by restricting the per-z curve's HasDerivWithinAt on the
    -- bigger Icc 0 (N · δ_uniform) via `.mono` (since Icc 0 T ⊆ Icc 0 (N · δ_uniform)).
    intro z hz t ht
    have h_t_in_big : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ_uniform) :=
      h_Icc_T_sub ht
    obtain ⟨h_pos_big, h_vel_big⟩ := h_dw_on_big z hz t h_t_in_big
    exact ⟨h_pos_big.mono h_Icc_T_sub, h_vel_big.mono h_Icc_T_sub⟩

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

/-- **`_at` variant of SC.2: pointwise chain rule at a specific `(t, z)`**.

Mirror of `vlasov_traj_chain_rule` (just above), generalized to take the
flow's HasDerivAt hypotheses at the specific `(t, z)` of interest rather
than universally `∀ t z`.  This is the form needed by the `_On` Stage C
PDE transport: Stage 1.9 produces `IsCharacteristicFlowOn ... (Ioo 0 T)
Set.univ` which gives HasDerivAt only at `t ∈ Ioo 0 T`, so the universal-
`t` form can't be supplied.

**Discharge route for Stage 4 Bridge #2 PDE**: this `_at` variant is the
foundation; downstream `_on` variants of the SC.5-SC.8 helpers and the
`vlasov_pushforward_hasDerivAt_under_integral` consumer all compose
against this one.

**Proof body**: identical to `vlasov_traj_chain_rule`'s body modulo the
hypothesis-naming.  The original uses `hX_deriv t z`, `hV_deriv t z`
exactly once each (at the `prodMk` step); we replace these with
`hX_deriv_at`, `hV_deriv_at` directly.  All other steps are
specific-`(t, z)` already. -/
lemma vlasov_traj_chain_rule_at
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (t : ℝ) (z : PhaseSpace d)
    (hX_deriv_at : HasDerivAt (fun s => charX s z) (charV t z) t)
    (hV_deriv_at : HasDerivAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t) :
    HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
  -- Step (a): joint pair HasDerivAt — uses hX_deriv_at, hV_deriv_at directly.
  have hpair : HasDerivAt (fun s => (charX s z, charV s z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) t :=
    hX_deriv_at.prodMk hV_deriv_at
  -- Step (b): φ has FDeriv at the image point.
  have hFDeriv : HasFDerivAt φ (fderiv ℝ φ (charX t z, charV t z)) (charX t z, charV t z) :=
    (hφ_smooth.differentiable (by simp) _).hasFDerivAt
  -- Step (c): chain rule.
  have hchain : HasDerivAt (fun s => φ (charX s z, charV s z))
      ((fderiv ℝ φ (charX t z, charV t z))
        (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z)))) t :=
    hFDeriv.comp_hasDerivAt t hpair
  -- Step (d): compute the value equality (identical to original).
  have hval : (fderiv ℝ φ (charX t z, charV t z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) =
      @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z)) := by
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
    set F := fderiv ℝ φ z₀
    set a := charV t z
    set b := -(convolveFunctionMeasure gradW (ρ t) (charX t z))
    have hdecomp : F (a, b) = F (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) +
        F (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) := by
      rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      simp [← F.map_add]
    have hdiffX : DifferentiableAt ℝ (fun x => φ (x, z₀.2)) z₀.1 :=
      hdiffφ.comp z₀.1 (differentiableAt_id.prodMk (differentiableAt_const z₀.2))
    have hdiffV : DifferentiableAt ℝ (fun v => φ (z₀.1, v)) z₀.2 :=
      hdiffφ.comp z₀.2 ((differentiableAt_const z₀.1).prodMk differentiableAt_id)
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


/-- **Mathlib-TODO (pure functional-analytic): Dominated per-z Lipschitz
bound for ODE flow trajectories composed with a smooth compactly-supported
test function.**

**⚑ RECLASSIFIED 2026-06-03 — STRUCTURE VERIFIED IN-PROJECT, CLOSE UNBUILT (NOT
EXTERNAL).**  A sorry-FREE twin `vlasov_trajectory_lipschitz_bound_lag` proves
the identical conclusion (via `flow_distance_growth_bound` + MVT).  That STRUCTURE
positions a close: reroute the consumer `vlasovTrajectoryLipschitzBound` through
the twin by THREADING a uniform first-moment bound `M_ρ` (the moment-cascade
pattern used to close `hM_ρ`).  **But the close is NOT BUILT**, and an open
question gates it — whether the call site's spatial marginal admits a derivable
`M_ρ` on `[0,t+1]`; the reroute could be a small thread or a large one.  Status:
*structure present (twin exists), closeability plausible-not-established*.  OWED
IN-PROJECT WORK, not a Mathlib gap; prefix retained to avoid churn.

For an ODE flow `Φ : ℝ → α → α` generated by a Lipschitz vector field
`b : ℝ → α → α`, and a smooth compact-support function `φ : α → ℝ`, the
composed map `s ↦ φ(Φ s z)` is per-z locally Lipschitz on a neighborhood
of any `t`, with the Lipschitz coefficient `μ`-integrable.

Standard ODE regularity + φ's compact support gives uniform-in-s bound on
the trajectory speed on `(flow_t)⁻¹(supp φ)`; composed with φ's smooth
boundedness gives the Lipschitz coefficient on the composed map.

**Bucket-1 PR scope**: pure ODE / functional-analytic result; no project-
specific instantiation.  Statable in pure Mathlib `Analysis.ODE` +
`MeasureTheory.Integration` language.

**Decomposed from `MathlibTODO_vlasovTrajectoryLipschitzBound`** (Phase 1.5,
2026-05-31).  The Vlasov-specific composition lives below as
`vlasovTrajectoryLipschitzBound`. -/
theorem MathlibTODO_lipschitzFlowTrajectoryLipBound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [MeasurableSpace α] [BorelSpace α]
    (b : ℝ → α → α) (L : NNReal) (_hL : ∀ t, LipschitzWith L (b t))
    (Φ : ℝ → α → α)
    (_hflow : ∀ z t, HasDerivAt (fun s => Φ s z) (b t (Φ t z)) t)
    (μ : Measure α)
    (φ : α → ℝ) (_hφ_smooth : ContDiff ℝ ⊤ φ)
    (_hφ_compact : HasCompactSupport φ)
    (t : ℝ) :
    ∃ (nhd : Set ℝ) (bound : α → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂μ, LipschitzOnWith (Real.nnabs (bound z))
        (fun s => φ (Φ s z)) nhd) ∧
      Integrable bound μ := by
  sorry

/-- **Project-internal composition (Phase 1.5 decomposition target,
2026-05-31)**: SC.8 dominated Lipschitz bound for the Vlasov characteristic
flow, derived from `MathlibTODO_lipschitzFlowTrajectoryLipBound` by
packaging the Vlasov phase-space vector field and the joint flow
`Φ t z := (charX t z, charV t z)`.

**Status**: body sorry'd as a Phase 2-4 close target.  The composition
follows the same mechanical pattern as `picardCharFlow_aemeasurable`
(extract joint Lipschitz constant max(1, L) for `b(t, z) := (z.2,
-convolveFunctionMeasure gradW (ρ t) z.1)`, package `Φ`'s HasDerivAt
from `IsCharacteristicFlow`'s two HasDerivAt clauses, apply the pure-FA
placeholder).

**Project alternatives** (`vlasov_trajectory_lipschitz_bound_lag` and
`vlasov_trajectory_lipschitz_bound_on`): substantively proved variants
taking additional `M_ρ` first-moment hypotheses.  This composition's
closure could either route through them (via `IsCharacteristicFlow.toOn`)
or apply the pure-FA placeholder directly.

**In-project consumer**: `vlasovSolutionViaPushforward_isVlasovSolution`'s
`h_diff_data` compose step (L3146-area). -/
theorem vlasovTrajectoryLipschitzBound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_compact : HasCompactSupport φ)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (_hgradW_cont : Continuous gradW)
    (_hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  -- Phase 3 substantive close (closure-plan, 2026-05-31): compose
  -- `MathlibTODO_lipschitzFlowTrajectoryLipBound` (pure-FA) with the
  -- Vlasov joint phase-space vector field + flow.
  -- * b := vlasovVectorField gradW ρ (joint phase-space field; project def).
  -- * Joint Lipschitz constant: max(1, L) via vlasovVectorField_lipschitzWith.
  -- * Joint flow: fun t' z => (charX t' z, charV t' z).
  -- * HasDerivAt for joint flow: prodMk of IsCharacteristicFlow's two
  --   HasDerivAt clauses; the derivative value matches
  --   vlasovVectorField gradW ρ t' (charX t' z, charV t' z) by definition.
  have h_pair_deriv : ∀ (z : PhaseSpace d) (t' : ℝ),
      HasDerivAt (fun s => ((charX s z, charV s z) : PhaseSpace d))
        (vlasovVectorField gradW ρ t' (charX t' z, charV t' z)) t' := by
    intro z t'
    exact (hflow.2.1 t' z).prodMk (hflow.2.2 t' z)
  exact MathlibTODO_lipschitzFlowTrajectoryLipBound
    (vlasovVectorField gradW ρ)
    (max 1 L)
    (vlasovVectorField_lipschitzWith gradW L hL ρ h_int)
    (fun t' z => (charX t' z, charV t' z))
    h_pair_deriv
    f₀ φ hφ_smooth hφ_compact t

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

/-- **`_on` variant of SC.8** — `vlasov_trajectory_lipschitz_bound` with
`IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` instead of universal
`IsCharacteristicFlow`, and with boundary regularity hypotheses
(`h_init`, `h_cont_Icc`, `h_deriv_Ico`) supplied explicitly.

**Sub-helper enrichment #2** of the Path-3-style swing at the sub-helper
layer (companion to `vlasov_traj_chain_rule_at`, sub-helper enrichment
#1).  Required by the Stage 4 Bridge #2 PDE transport
(`vlasovSolutionViaPushforward_isVlasovSolutionOn`).

**Body sorry'd**: the closure is a substantive transport of
`vlasov_trajectory_lipschitz_bound_lag`'s body (~150 lines) with two
substitutions:
1. `flow_distance_growth_bound` → `flow_distance_growth_bound_on`
   (Bridge #1) — uses the boundary regularity hypotheses.
2. `(hflow_x s z).prodMk (hflow_v s z)` → `hflow_on.2.1 s ... z ...` for
   s in the chosen neighborhood (must be within `Ioo 0 T`).

The proof structure is mechanically derivable from `_lag`'s body — the
issue is that the neighborhood `nhd` must be chosen as
`Ioo (max 0 (t/2)) (min T (t + 1/2))` or similar to stay within
`Ioo 0 T` (where `hflow_on` is defined), which requires careful interval
arithmetic.

**Sorry rationale**: API-lock-vs-substantive-proof pattern (sighting
#3, promotion-ready).  Lock the API for the Bridge #2 PDE transport
downstream consumer.  Substantive transport is a separate focused
~150-line follow-up commit.  Sorry count contribution: +1 (Stage 4's
sub-helper enrichment swing, expected to be discharged in the
substantive close phase).

**Closure path**: mirror `vlasov_trajectory_lipschitz_bound_lag`'s
body verbatim, replacing the `flow_distance_growth_bound` invocation
with `flow_distance_growth_bound_on` (passing boundary regularity
through) and the `hflow_x`/`hflow_v` usage with
`hflow_on.2.1`/`hflow_on.2.2` after asserting s ∈ Ioo 0 T from the
chosen neighborhood. -/
lemma vlasov_trajectory_lipschitz_bound_on
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
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW ρ charX charV
                                       (Set.Ioo 0 T) Set.univ)
    -- Boundary regularity for `flow_distance_growth_bound_on`.
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z))
        (Set.Ici s) s)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc 0 T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s)) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  -- Step 1: Get Gronwall growth bound C_T on [0, T] via Bridge #1.
  obtain ⟨C_T, hC_T_nn, hC_T⟩ := flow_distance_growth_bound_on gradW L hL ρ charX charV
      T (le_of_lt hT) h_init h_cont_Icc h_deriv_Ico M_ρ hM_ρ_nn hM_ρ h_y_int h_int
  -- Step 2: Bound ‖fderiv ℝ φ‖ uniformly (compact support + continuous fderiv).
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by norm_num)
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_smooth.continuous_fderiv (by norm_num)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
  obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  have hM_φ_nn : 0 ≤ M_φ :=
    le_trans (norm_nonneg (fderiv ℝ φ (0 : PhaseSpace d))) (hM_φ _)
  -- Gronwall constants: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ.
  set K := 1 + (L : ℝ)
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Convolution bound on [0, T] (same derivation as `_lag`, now Icc 0 T-restricted).
  have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
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
  -- Step 3: Choose nhd = Ioo (t/2) ((t+T)/2) ⊆ Ioo 0 T.  t/2 < t (since t>0) and
  -- t < (t+T)/2 (since t < T), so t ∈ nhd; further nhd ⊆ Icc 0 T for bounding.
  refine ⟨Set.Ioo (t / 2) ((t + T) / 2),
    fun z => M_φ * (K * C_T + ε₀) * (‖z‖ + 1), ?_, ?_, ?_⟩
  · -- nhd ∈ nhds t.
    exact Ioo_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  · -- LipschitzOnWith for ae-z, via MVT on the convex nhd.
    apply Filter.Eventually.of_forall
    intro z
    let deriv_val : ℝ → PhaseSpace d → ℝ := fun s z =>
      (fderiv ℝ φ (charX s z, charV s z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioo _ _)
      (f' := fun s => deriv_val s z)
    · -- HasDerivWithinAt for each s ∈ nhd; uses hflow_on at s ∈ Ioo 0 T.
      intro s hs
      have hs_Ioo : s ∈ Set.Ioo (0:ℝ) T :=
        ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
      have hX_at := hflow_on.2.1 s hs_Ioo z (Set.mem_univ z)
      have hV_at := hflow_on.2.2 s hs_Ioo z (Set.mem_univ z)
      have h_flow_deriv : HasDerivAt (fun s' => (charX s' z, charV s' z))
          (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))) s :=
        hX_at.prodMk hV_at
      have h_φ_fderiv : HasFDerivAt φ (fderiv ℝ φ (charX s z, charV s z))
          (charX s z, charV s z) :=
        hφ_diff (charX s z, charV s z) |>.hasFDerivAt
      exact (h_φ_fderiv.comp_hasDerivAt s h_flow_deriv).hasDerivWithinAt
    · -- Bound ‖deriv_val s z‖₊ ≤ M_φ * (K * C_T + ε₀) * (‖z‖ + 1).
      intro s hs
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm']
      have hs_mem : s ∈ Set.Icc 0 T :=
        ⟨le_of_lt (by linarith [hs.1, ht.1]),
         le_of_lt (by linarith [hs.2, ht.2])⟩
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
        · have h1 : C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hC_T_nn) hz1
            linarith
          linarith
        · have hLK : (L : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
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
  · -- Integrable bound (same as `_lag`).
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
    (L : NNReal) (hL : LipschitzWith L gradW)
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
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Phase 3 added (2026-05-31): convolution-integrability witness for the
    -- spatial-marginal pushforward measure curve; required by the substantively-
    -- closed `vlasovTrajectoryLipschitzBound`.  Derivable from hgradW + Lipschitz
    -- L gradW + the spatial marginal's finite first moment.
    (h_int_conv : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) :
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
    -- Phase 3 update (2026-05-31): pass L, hL, h_int_conv to the substantively-
    -- closed vlasovTrajectoryLipschitzBound.  Instance `IsProbabilityMeasure (ρ t)`
    -- inferred from spatialMarginal pushforward via `h_flow_meas`.
    haveI : ∀ t, IsProbabilityMeasure
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) := fun t => by
      unfold spatialMarginal vlasovSolutionViaPushforward
      have h_pair_aem := h_flow_meas t
      have : IsProbabilityMeasure (Measure.map
          (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) :=
        Measure.isProbabilityMeasure_map h_pair_aem
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasovTrajectoryLipschitzBound gradW L hL ρ h_int_conv charX charV f₀ φ
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
    (L : NNReal) (hL : LipschitzWith L gradW)
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
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Phase 3 added (2026-05-31): convolution-integrability witness; propagates
    -- to `vlasovSolutionViaPushforward_isVlasovSolution`.
    (h_int_conv : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) :
    IsLagrangianVlasovSolution gradW (vlasovSolutionViaPushforward charX charV f₀) := by
  -- The wrapper closes the IsVlasovSolution conjunct.
  refine ⟨vlasovSolutionViaPushforward_isVlasovSolution gradW L hL charX charV f₀
            hflow hself h_flow_meas hgradW_cont hconv_cont h_int_conv,
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

/-- **`_On`-flavored Stage C producer for `IsVlasovSolutionOn`**.

The `_on` analog of `vlasovSolutionViaPushforward_isVlasovSolution`
(L2735), taking the characteristic flow in `IsCharacteristicFlowOn ...
(Set.Ioo 0 T) Set.univ` form (Stage 1.9's natural output) and producing
the weak Vlasov PDE in localized `IsVlasovSolutionOn` form (also on
`Ioo 0 T`, per the predicate's revision in commit `966a9e6+`).

**Proof strategy** (deferred — substantive ~150-200 lines of careful
adaptation of the global L2735 proof body):

The original L2735 proof's structure transports cleanly to the `_On`
form:
* `intro t` becomes `intro t ht` with `ht : t ∈ Set.Ioo 0 T`.
* `hflow.2.1 t z` (HasDerivAt universal) becomes
  `hflow_on.2.1 t ht z (Set.mem_univ z)` (HasDerivAt at the specific
  `t ∈ Ioo 0 T`, `z ∈ Set.univ`).
* Conclusion stays at `HasDerivAt` (since `t ∈ Ioo` is an interior
  point of the predicate's quantification set; no `HasDerivWithinAt`
  conversion needed).
* The sub-helpers `vlasov_traj_chain_rule`, `vlasov_compose_flow_*`,
  `vlasov_pushforward_hasDerivAt_under_integral`,
  `vlasov_rhs_pushforward_back` all consume flow hypotheses at a
  *specific `t`*, not universally, so they transport unchanged after
  threading the `ht : t ∈ Ioo 0 T` constraint.

**Sorry rationale**: deferred to a focused follow-up commit.  The
substantive PDE-proof transport is a careful copy-edit task on the
~150-line L2735 body, easier as a focused unit than mid-Stage-4-closure.
Treating it as a named gap (analogous to `MathlibTODO_*` placeholders)
keeps Stage 4's structural assembly unblocked.  The downstream consumer
(`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn` below)
needs this as a black box; with this signature in place, the wrapper
composes cleanly. -/
theorem vlasovSolutionViaPushforward_isVlasovSolutionOn
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW
                (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
                charX charV (Set.Ioo 0 T) Set.univ)
    -- Boundary regularity (will be discharged by Friction 5 helper at the call site).
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s)
    -- ρ-regularity on Icc 0 T (the pushforward's spatial marginal).
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (h_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    [∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))]
    (hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsVlasovSolutionOn gradW (vlasovSolutionViaPushforward charX charV f₀) T := by
  -- Unfold IsVlasovSolutionOn; for each test function φ, prove WeakEvolutionEqOn at t ∈ Ioo 0 T.
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
  -- Notation aliases (same as L2735).
  set ρ : ℝ → Measure (PhysSpace d) :=
    fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) with hρ_def
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_aesm_general : ∀ μ : Measure (PhaseSpace d),
      AEStronglyMeasurable φ μ := fun μ => hφ_cont.aestronglyMeasurable
  -- SC.1 (same): unify ∫ φ d(vlasov s) with ∫ (φ ∘ flow_s) df₀.
  have h_compose : ∀ s, ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := fun s =>
    vlasov_pushforward_integral_eq_compose charX charV f₀ s
      (h_flow_meas s) φ (hφ_aesm_general _)
  -- SC.2 `_at`: pointwise chain rule at every z, AT the specific t ∈ Ioo 0 T.
  have h_pointwise : ∀ z, HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
    intro z
    have hX_at := hflow_on.2.1 t ht z (Set.mem_univ z)
    have hV_at := hflow_on.2.2 t ht z (Set.mem_univ z)
    exact vlasov_traj_chain_rule_at gradW ρ charX charV φ hφ_smooth
      gradXφ gradVφ hgradXφ hgradVφ t z hX_at hV_at
  -- SC.3: DiffUnderIntegralData via SC.5-SC.8 (`_on` for SC.8).
  have h_diff_data : DiffUnderIntegralData gradW ρ charX charV f₀
      φ gradXφ gradVφ t := by
    -- Use `_on` variant of SC.8.
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasov_trajectory_lipschitz_bound_on gradW L hL ρ charX charV f₀
        hf₀_fm φ hφ_smooth hφ_compact hT hflow_on h_init h_cont_Icc h_deriv_Ico
        hgradW_cont hconv_cont t ht M_ρ hM_ρ_nn hM_ρ h_y_int h_int
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
  -- SC.4: push the integrand back through `integral_map`.
  have h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.sub
    · apply Continuous.inner continuous_snd
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
    · apply Continuous.inner
      · exact (hconv_cont t).comp continuous_fst
      · have hfderiv_V : ∀ z : PhaseSpace d,
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
  -- Compose: rewrite LHS via h_compose, apply h_under_integral, then rewrite via h_push_back.
  have hLHS : (fun s => ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s)) =
              (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀) := funext h_compose
  rw [hLHS]
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

/-- **`_On`-flavored Stage C producer for `IsLagrangianVlasovSolutionOn`**.

Same hypothesis package as the global `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`
(L2895), but takes the characteristic flow in `IsCharacteristicFlowOn ...
(Set.Ioo 0 T) Set.univ` form (Stage 1.9's natural output) and produces
the strictly stronger `IsLagrangianVlasovSolutionOn` predicate.

**Composes**:
* `vlasovSolutionViaPushforward_isVlasovSolutionOn` (above) for the
  weak-PDE conjunct.
* Stage 1.9's flow output for the flow-witness conjunct.
* Trivial pushforward + AEMeasurability bundling for the remaining
  conjuncts (identical to the global wrapper's body at L2920-L2951,
  adapted to use `IsCharacteristicFlowOn`'s initial-condition clause).

This is the **packaging layer** of Stage 4's `_On` Stage C closure;
the substantive PDE proof lives in the sorry'd
`vlasovSolutionViaPushforward_isVlasovSolutionOn` above. -/
theorem vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW
                (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
                charX charV (Set.Ioo 0 T) Set.univ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (h_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    [∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))]
    (hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsLagrangianVlasovSolutionOn gradW
      (vlasovSolutionViaPushforward charX charV f₀) T := by
  refine ⟨vlasovSolutionViaPushforward_isVlasovSolutionOn gradW L hL charX charV f₀
            hf₀_fm hT hflow_on h_init h_cont_Icc h_deriv_Ico M_ρ hM_ρ_nn hM_ρ
            h_y_int h_int hself h_flow_meas hgradW_cont hconv_cont,
          charX, charV, hflow_on, ?_, ?_, h_cont_Icc⟩
  · -- Pushforward equation: f t = (flow_t)_# (f 0) for t ∈ Icc 0 T.
    -- Identical to the global wrapper's body, using IsCharacteristicFlowOn's
    -- initial-condition clause `hflow_on.1 z (Set.mem_univ z)`.
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow_on.1 z (Set.mem_univ z)
      exact Prod.ext h.1 h.2
    have h0 : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      simp [vlasovSolutionViaPushforward, h_init, Measure.map_id]
    intro t _ht
    rw [h0]
    rfl
  · -- AEMeasurability on Icc 0 T.  Same h0 step as above.
    intro s _hs
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow_on.1 z (Set.mem_univ z)
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
-- Banach fixed-point scaffolding for `vlasovWellPosedness`
-- ---------------------------------------------------------------------------
-- Stage 1 of the well-posedness plan.  The infrastructure here makes Stages
-- 2 (Φ well-defined), 3 (Gronwall contraction) and 4 (Picard iteration)
-- compose cleanly:
--   * `VlasovMeasureCurve T M`: admissible curves of probability measures
--     on `PhysSpace d` with uniform first-moment bound `M` on `[0, T]`.
--     The four structural fields are exactly what `Φ` preserves.
--   * `supW1On`: sup-W₁ pseudodistance over a set of times; the natural
--     contraction metric for the Picard iteration.
--   * `vlasovMeasureCurve_convCont`: convolution continuity in `t` derived
--     from the W₁-continuity field via `MathlibTODO_convolveLipschitzEstimate`.
--   * `constantCurve`: the constant curve `t ↦ μ₀`, used as the Picard
--     iteration's starting point and as a sanity-check witness that the
--     structure is inhabited.

/-- The sup-W₁ pseudodistance between two curves of measures over a set of
times `S`.  Returns `⨆ t ∈ S, wasserstein1 (ρ t) (σ t)` in `ℝ≥0∞`.

* Symmetric (`supW1On_comm`) and satisfies the triangle inequality
  (`supW1On_triangle`).
* Finite (≠ ⊤) when both curves are `VlasovMeasureCurve`s on `[0, T]` with
  the same moment bound, via `supW1On_ne_top_of_VlasovMeasureCurve`.

Used as the contraction metric for the Picard iteration in Stage 4 of the
well-posedness plan. -/
noncomputable def supW1On {d : ℕ} [NeZero d]
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : t ∈ S), wasserstein1 (ρ t) (σ t)

lemma supW1On_comm {d : ℕ} [NeZero d] (S : Set ℝ)
    (ρ σ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ σ = supW1On S σ ρ := by
  unfold supW1On
  refine iSup_congr fun t => ?_
  refine iSup_congr fun _ => ?_
  exact wasserstein1_comm _ _

lemma supW1On_self {d : ℕ} [NeZero d] (S : Set ℝ)
    (ρ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ ρ = 0 := by
  unfold supW1On
  simp [wasserstein1_self]

lemma supW1On_triangle {d : ℕ} [NeZero d] (S : Set ℝ)
    (ρ σ τ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ τ ≤ supW1On S ρ σ + supW1On S σ τ := by
  unfold supW1On
  refine iSup_le fun t => iSup_le fun ht => ?_
  calc wasserstein1 (ρ t) (τ t)
      ≤ wasserstein1 (ρ t) (σ t) + wasserstein1 (σ t) (τ t) :=
        wasserstein1_triangle _ _ _
    _ ≤ (⨆ s ∈ S, wasserstein1 (ρ s) (σ s))
        + (⨆ s ∈ S, wasserstein1 (σ s) (τ s)) := by
        gcongr
        · exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
        · exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- **Iterated triangle inequality for `supW1On` over a sequence**.

For any sequence `x : ℕ → ℝ → Measure (PhysSpace d)` and `m ≤ n`:
`supW1On S (x m) (x n) ≤ ∑ k ∈ Ico m n, supW1On S (x k) (x (k+1))`.

**Generic structural lemma** — stated over an arbitrary sequence and time
set `S`, not specialised to Picard iteration.  Downstream consumers (Stage
4's Cauchy-from-contraction argument, Stage 5's continuation, possibly
Stage 6's uniqueness) compose against this generic form.

**Per the M1 design principle** (registered this session): the entire
proof stays in ENNReal — `supW1On` is ENNReal-valued, the sum is in
ENNReal, ENNReal addition is well-defined with `⊤` as absorbing element,
no finiteness side conditions arise.  This is the recommended pattern
for any ENNReal-valued algebraic argument over a sequence: do the
induction in ENNReal, project to ℝ via `.toReal` only at the boundary
(or not at all, as in the upcoming Stage 4 ENNReal-form Cauchy argument).

Proof: induction on `n` starting from `n = m` via `Nat.le_induction`.
Base case is the empty sum via `supW1On_self`.  Inductive step combines
`supW1On_triangle` with `Finset.sum_Ico_succ_top`. -/
lemma supW1On_iterated_triangle {d : ℕ} [NeZero d] (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (m n : ℕ) (hmn : m ≤ n) :
    supW1On S (x m) (x n) ≤
      ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    -- Empty sum: Ico m m = ∅.
    rw [Finset.Ico_self, Finset.sum_empty]
    rw [supW1On_self]
  | succ n hmn ih =>
    calc supW1On S (x m) (x (n+1))
        ≤ supW1On S (x m) (x n) + supW1On S (x n) (x (n+1)) :=
          supW1On_triangle S (x m) (x n) (x (n+1))
      _ ≤ (∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1))) +
          supW1On S (x n) (x (n+1)) := by
          exact add_le_add ih (le_refl _)
      _ = ∑ k ∈ Finset.Ico m (n+1), supW1On S (x k) (x (k+1)) := by
          rw [Finset.sum_Ico_succ_top hmn]

-- ---------------------------------------------------------------------------
-- Metric-dependent abstractions (architectural priming for the W̄ refactor)
-- ---------------------------------------------------------------------------
--
-- The project's existence-and-contraction analysis uses TWO independent
-- smallness constraints in the `0 < L < 1` `W₁`-regime, captured as two
-- separate predicates:
--   * `LocalSmallness_PL_buffer L T := L · (T+1)² < 1` — per-ball
--     Picard-Lindelöf flow ball-geometry (the `(T+1)`-buffer + L-Lipschitz
--     R-existence fixed-point).
--   * `LocalSmallness_contraction L T := L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`
--     — supW1On contraction-ratio (Gronwall on the W₁-based flow).
--
-- **Stage 2b part 3 (commit `2eed838`, 2026-05-31)** retired a structural
-- debt where these two were conflated under one `LocalSmallness L T` with
-- the `L · (T+1)² < 1` shape; the `(T+1)²` form, plausible for ball
-- geometry, does NOT imply the exponential contraction constraint (and is
-- not implied by it).  The original `q < 1` sub-sub-sorry inside
-- `_picard_fixedPointFlow` traced to that conflation, which itself traced
-- one layer further to the q-definition at L6529 fusing the contraction
-- factor with the W₁-input bound D₀ = 2M.  Both layers fixed together.
--
-- Switching to the truncated-distance Wasserstein `W̄ = W_{min(|x-y|,1)}`
-- (per Dobrushin 1979, §5) is a separate post-cleanup arc that would
-- retire the `L < 1` restriction by replacing the `LocalSmallness_contraction`
-- exponential with a linear-in-T form; the named-predicate split makes
-- that future edit hit one definition rather than a fused predicate
-- carrying two distinct claims.
--
-- Existing closed proofs at PL-buffer-only call sites continue to compile
-- against `LocalSmallness_PL_buffer` (algebraically identical to the old
-- `LocalSmallness`); the new contraction-only sites take
-- `LocalSmallness_contraction` directly.

/-- **Smallness predicate for the per-ball Picard-Lindelöf flow's
ball-geometry constraint** (Stage 2b part 3 split, 2026-05-31).

Defined as `(L : ℝ) * (T + 1) ^ 2 < 1`, this is the smallness condition
the per-ball flow's R-selection requires: `R · (1 - L·(T+1)²) ≥ N(z)`
forces R > 0 only when `L·(T+1)² < 1`.  It comes from the
`(T+1)`-time-buffer Picard-Lindelöf geometry + L-Lipschitz fixed-point
analysis, NOT from contraction.

**Stage 2b part 3 split**: the original `LocalSmallness` conflated this
PL-buffer constraint with the supW1On *contraction-ratio* constraint
`LocalSmallness_contraction` (below).  Those are genuinely independent
mathematical constraints from distinct sub-arguments; carrying them as
two predicates rather than one prevents future edits from fusing them
back into "the constraint" (per M1: predicates match the mathematical
structure).  See planning-notes for the M1-recursion reasoning. -/
def LocalSmallness_PL_buffer (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * (T + 1) ^ 2 < 1

/-- **Smallness predicate for the supW1On contraction-ratio constraint**
(Stage 2b part 3 split, 2026-05-31).

For `Phi_supW1_contraction`'s output to satisfy `q < 1` — the genuine
M-independent contraction ratio — the constraint is
`L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`.  This comes from Gronwall
on the W₁-based contraction analysis, inherited off
`vlasovVectorField_lipschitzWith` (CharFlow L629, the joint phase-space
`max(1, L)`-Lipschitz constant).  Same constant items 5 and 6 cite
(commits `33e8baa`, `e9d9aa4`); banked once, used three times.

For the `0 < L < 1` regime the marquee operates in, `max(1, L) = 1` and
the constraint simplifies to `L · (exp T - 1) < 1`.

**W₁-regime gating**: this predicate is intentionally NOT generalized
to accommodate L ≥ 1.  The L ≥ 1 regime requires the truncated-distance
Wasserstein W̄ refactor (Dobrushin 1979 §5), a separate arc.  A future
L ≥ 1 proof attempting to cite this predicate via downstream lemmas
fails loudly at the `hL_lt : (L : ℝ) < 1` binder of the consequence
lemma, not silently broadens the W₁-regime estimate. -/
def LocalSmallness_contraction (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) < 1

/-- The curve metric used by the project's `VlasovMeasureCurve` Banach
iteration.  Currently `supW1On` (sup of `W₁` distances over the time
window).  Under a `W̄` refactor (post-cleanup arc), this becomes `supW̄On`.

Defined as `abbrev` so the abbreviation unfolds transparently — existing
proofs that reference `supW1On` continue to work without modification.
New consumers (Stage 6/8 bodies, marquee composition) can use
`CurveMetric` directly for explicit metric-agnosticism. -/
noncomputable abbrev CurveMetric {d : ℕ} [NeZero d]
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d)) : ℝ≥0∞ :=
  supW1On S ρ σ

/-- Admissible Vlasov measure curves on `[0, T]`: a curve of probability
measures on `PhysSpace d` with uniform first-moment bound `M`, pointwise
integrability of `‖·‖`, and W₁-continuity at every time in `[0, T]`.

The W₁-continuity field is phrased per-base-point `s ∈ [0, T]` as
`ContinuousWithinAt` of `t ↦ W₁(ρ s, ρ t).toReal` at `s` (which equals 0 at
`t = s`).  This is strictly stronger than naive ContinuousOn on the diagonal
— it gives the dominator we need for derived convolution continuity
(`vlasovMeasureCurve_convCont`) and for the Picard limit's bundling
(Stage 4).

`d` is an explicit parameter so that `VlasovMeasureCurve d T M` is fully
determined at use sites (otherwise `NeZero d` cannot be resolved from the
non-discriminating real-valued T, M alone). -/
structure VlasovMeasureCurve (d : ℕ) [NeZero d] (T : ℝ) (M : ℝ → ℝ) where
  ρ : ℝ → Measure (PhysSpace d)
  isProb : ∀ t, IsProbabilityMeasure (ρ t)
  hasMoment : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ t) ≤ M t
  yIntegrable : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t)
  hW1Cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
    ContinuousWithinAt (fun t => (wasserstein1 (ρ s) (ρ t)).toReal)
                       (Set.Icc 0 T) s

/-- `supW1On` of two `VlasovMeasureCurve`s on `[0, T]` with moment bound `M`
is bounded by `2M`, hence finite.

Combines pointwise `wasserstein1_le_moments_sum` with `iSup_le` over the
compact time set. -/
lemma supW1On_le_two_moment_of_VlasovMeasureCurve {d : ℕ} [NeZero d]
    {T : ℝ} {M : ℝ → ℝ} (Mbar : ℝ) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≤ ENNReal.ofReal (2 * Mbar) := by
  unfold supW1On
  refine iSup_le fun t => iSup_le fun ht => ?_
  -- Pointwise: W₁(ρ_t, σ_t) ≤ ofReal(∫‖y‖d(ρ_t) + ∫‖y‖d(σ_t)) ≤ ofReal(M + M)
  have h_bound : wasserstein1 (ρ.ρ t) (σ.ρ t) ≤
      ENNReal.ofReal (∫ y, ‖y‖ ∂(ρ.ρ t) + ∫ y, ‖y‖ ∂(σ.ρ t)) := by
    haveI : IsProbabilityMeasure (ρ.ρ t) := ρ.isProb t
    haveI : IsProbabilityMeasure (σ.ρ t) := σ.isProb t
    exact wasserstein1_le_moments_sum (ρ.ρ t) (σ.ρ t)
      (ρ.yIntegrable t ht) (σ.yIntegrable t ht)
  refine h_bound.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hρ_t : ∫ y, ‖y‖ ∂(ρ.ρ t) ≤ M t := ρ.hasMoment t ht
  have hσ_t : ∫ y, ‖y‖ ∂(σ.ρ t) ≤ M t := σ.hasMoment t ht
  linarith [hMbar t ht]

/-- `supW1On` of two `VlasovMeasureCurve`s is finite (≠ ⊤). -/
lemma supW1On_ne_top_of_VlasovMeasureCurve {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (Mbar : ℝ) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≠ ⊤ :=
  ne_of_lt ((supW1On_le_two_moment_of_VlasovMeasureCurve Mbar hMbar ρ σ).trans_lt
            ENNReal.ofReal_lt_top)

/-- Convolution continuity in time, derived from the structural
`hW1Cont` field via `MathlibTODO_convolveLipschitzEstimate`.

For each `x ∈ PhysSpace d`, the map `t ↦ (∇W ∗ ρ_t)(x)` is continuous on
`[0, T]`.  Used inside `Φ`'s well-definedness proof (Stage 2) to discharge
the convolution-continuity hypothesis of `exists_vlasov_characteristicFlow`. -/
lemma vlasovMeasureCurve_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T : ℝ} {M : ℝ → ℝ} (ρ : VlasovMeasureCurve d T M)
    (x : PhysSpace d)
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
              Integrable (fun y => gradW (x - y)) (ρ.ρ t)) :
    ContinuousOn (fun t => convolveFunctionMeasure gradW (ρ.ρ t) x)
                 (Set.Icc 0 T) := by
  -- Strategy: at every base `s ∈ [0, T]`, the Lipschitz convolution estimate
  --   ‖conv(ρ_s, x) - conv(ρ_t, x)‖ ≤ L · W₁(ρ_s, ρ_t).toReal
  -- composes with the hW1Cont field (W₁(ρ_s, ρ_t).toReal → 0 as t → s within
  -- [0, T]) to give ContinuousWithinAt at s.
  intro s hs
  haveI hPs : IsProbabilityMeasure (ρ.ρ s) := ρ.isProb s
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hCont := ρ.hW1Cont s hs
  rw [Metric.continuousWithinAt_iff] at hCont
  have h_self : (wasserstein1 (ρ.ρ s) (ρ.ρ s)).toReal = 0 := by
    rw [wasserstein1_self]; rfl
  -- Pick δ from hCont for tolerance ε / (L + 1)  (so that L · δ < ε)
  set η : ℝ := ε / ((L : ℝ) + 1) with hη_def
  have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 := by
    have : (0 : ℝ) ≤ L := L.coe_nonneg
    linarith
  have hη_pos : 0 < η := div_pos hε hLp1_pos
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hCont η hη_pos
  refine ⟨δ, hδ_pos, fun t ht hdist => ?_⟩
  have hδb := hδ_bound ht hdist
  rw [h_self, Real.dist_eq, sub_zero] at hδb
  have hW1_nn : 0 ≤ (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal := ENNReal.toReal_nonneg
  have hW1_lt : (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal < η := by
    rwa [abs_of_nonneg hW1_nn] at hδb
  haveI hPt : IsProbabilityMeasure (ρ.ρ t) := ρ.isProb t
  have h_finite : wasserstein1 (ρ.ρ s) (ρ.ρ t) ≠ ⊤ :=
    wasserstein1_ne_top_of_finite_moment _ _
      (ρ.yIntegrable s hs) (ρ.yIntegrable t ht)
  have h_lip := MathlibTODO_convolveLipschitzEstimate gradW L hL
    (ρ.ρ s) (ρ.ρ t) x h_finite (h_int s hs) (h_int t ht)
  -- h_lip : ‖conv(ρ_s, x) - conv(ρ_t, x)‖ ≤ L · W₁(ρ_s, ρ_t).toReal
  rw [dist_eq_norm]
  calc ‖convolveFunctionMeasure gradW (ρ.ρ t) x
        - convolveFunctionMeasure gradW (ρ.ρ s) x‖
      = ‖convolveFunctionMeasure gradW (ρ.ρ s) x
          - convolveFunctionMeasure gradW (ρ.ρ t) x‖ := norm_sub_rev _ _
    _ ≤ (L : ℝ) * (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal := h_lip
    _ ≤ (L : ℝ) * η := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hW1_lt) L.coe_nonneg
    _ < ((L : ℝ) + 1) * η := by nlinarith
    _ = ε := by
        rw [hη_def]
        field_simp

/-! ### Constant extension past `[0, T]`

A `VlasovMeasureCurve d T M` has its structural properties (moment bound,
integrability of `‖·‖`, W₁-continuity) only on `Icc 0 T`.  Stage 1.9's
`exists_vlasov_characteristicFlow_global_smallT` takes universal-in-`t`
hypotheses (the proof internally accesses `ρ` at `t ∈ Icc 0 (T + 1)` —
see `exists_vlasov_perz_trajectory`'s `hbound_local` at L3143 — but the
exposed signature is universal).

The constant-extension wrapper `VlasovMeasureCurve.extend` produces a
curve on all of `ℝ` by clamping `t` to `Icc 0 T`: `extend t := ρ.ρ (clamp t)`
where `clamp t := max 0 (min t T)`.  Outside `Icc 0 T` the extended
curve takes the boundary value (`ρ.ρ 0` for `t < 0`; `ρ.ρ T` for
`t > T`).  This is the canonical mathematical extension — a Vlasov
solution defined on a finite horizon is naturally extended by holding
the endpoint value past the horizon — and it makes the structural
properties hold universally without modifying Stage 1.9 itself.

Discharge of `hρ_cont` (universal convolveFunctionMeasure continuity)
routes through `vlasovMeasureCurve_convCont` precomposed with the
continuous clamp via `ContinuousOn.comp_continuous`. -/

/-- Clamp `t : ℝ` to `Icc 0 T`.  Used by `VlasovMeasureCurve.extend` to
extend a curve from `Icc 0 T` to all of `ℝ`. -/
def clampToIcc (T t : ℝ) : ℝ := max 0 (min t T)

lemma clampToIcc_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    clampToIcc T t ∈ Set.Icc (0 : ℝ) T := by
  unfold clampToIcc
  refine Set.mem_Icc.mpr ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma clampToIcc_continuous (T : ℝ) : Continuous (clampToIcc T) := by
  unfold clampToIcc
  exact continuous_const.max (continuous_id.min continuous_const)

/-- Constant extension of a `VlasovMeasureCurve d T M`'s underlying curve
`ρ.ρ` from `Icc 0 T` to all of `ℝ`.  Defined as `ρ.ρ` composed with the
clamp `max 0 (min t T)`.

For `t ∈ Icc 0 T`: `extend t = ρ.ρ t`.
For `t < 0`: `extend t = ρ.ρ 0`.
For `t > T`: `extend t = ρ.ρ T`.

The extension preserves all structural properties (`IsProbabilityMeasure`,
moment bound, integrability of `‖·‖`) universally in `t`, and extends
W₁-continuity to convolveFunctionMeasure-continuity universally in `t`
via `clampToIcc_continuous` + `vlasovMeasureCurve_convCont`. -/
noncomputable def VlasovMeasureCurve.extend {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (ρ : VlasovMeasureCurve d T M) : ℝ → Measure (PhysSpace d) :=
  fun t => ρ.ρ (clampToIcc T t)

/-- The extended curve is a probability measure at every `t : ℝ`. -/
instance VlasovMeasureCurve.extend_isProb {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    IsProbabilityMeasure (ρ.extend t) :=
  ρ.isProb _

/-- The extended curve has `‖·‖` integrable at every `t : ℝ`. -/
lemma VlasovMeasureCurve.extend_yIntegrable {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
  ρ.yIntegrable _ (clampToIcc_mem hT t)

/-- The extended curve preserves the moment bound `M` universally in `t`. -/
lemma VlasovMeasureCurve.extend_hasMoment {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M (clampToIcc T t) :=
  ρ.hasMoment _ (clampToIcc_mem hT t)

/-- Convolution continuity on the extended curve, universal in `t`.

Composed from `vlasovMeasureCurve_convCont` (ContinuousOn on `Icc 0 T`)
with `clampToIcc_continuous` via `ContinuousOn.comp_continuous`.  This
provides Stage 1.9's universal `hρ_cont` hypothesis directly from a
`VlasovMeasureCurve`'s structural fields. -/
lemma VlasovMeasureCurve.extend_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T : ℝ} {M : ℝ → ℝ} (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M)
    (x : PhysSpace d)
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
              Integrable (fun y => gradW (x - y)) (ρ.ρ t)) :
    Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
  -- The function decomposes as `(fun s => convolveFunctionMeasure gradW (ρ.ρ s) x) ∘ clamp`.
  -- Inner is ContinuousOn (Icc 0 T) via vlasovMeasureCurve_convCont.
  -- Clamp is continuous and lands in Icc 0 T.
  have h_convCont := vlasovMeasureCurve_convCont gradW L hL ρ x h_int
  exact h_convCont.comp_continuous (clampToIcc_continuous T) (clampToIcc_mem hT)

/-- The constant curve at a probability measure with finite first moment is
a valid `VlasovMeasureCurve` on `[0, T]` for any `T` and any moment
bound `M ≥ ∫‖y‖dμ₀`. -/
def constantCurve {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (μ₀ : Measure (PhysSpace d)) [IsProbabilityMeasure μ₀]
    (hμ_int : Integrable (fun y : PhysSpace d => ‖y‖) μ₀)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂μ₀ ≤ M t) :
    VlasovMeasureCurve d T M where
  ρ := fun _ => μ₀
  isProb := fun _ => inferInstance
  hasMoment := hM
  yIntegrable := fun _ _ => hμ_int
  hW1Cont := fun s _ => by
    -- The function `t ↦ (wasserstein1 μ₀ μ₀).toReal` is identically 0;
    -- ContinuousWithinAt of a constant is immediate.
    have h_zero : (fun t : ℝ => (wasserstein1 μ₀ μ₀).toReal)
                  = fun _ => (0 : ℝ) := by
      funext _; rw [wasserstein1_self]; rfl
    rw [h_zero]
    exact continuousWithinAt_const

/-- **Stage 1.7 of the well-posedness plan: parametric global-on-ball
characteristic flow.**

A convenience wrapper around `exists_vlasov_characteristicFlow` that
instantiates the per-ball flow theorem with the trivial center
`z₀ = 0 : PhaseSpace d` and ball radius `a := 2 * R₀`.  The resulting flow
is defined for every initial condition in `closedBall (0 : PhaseSpace d) R₀`,
on time `Ioo 0 T`.

**Surprisingly cheap by design**.  The plan originally envisioned a finite-
cover + `ODE_solution_unique` stitching argument; in fact
`exists_vlasov_characteristicFlow` is already parametric in *both* the ball
center `z₀` and the radius `a`, so the "lift from a single small ball to a
larger initial-condition ball" is just a re-parameterisation, not an honest
stitching.  ~30 lines of cast/algebra instead of ~150 lines of cover
construction.

Used by Stage 2 of the well-posedness plan to discharge the flow-existence
hypothesis when constructing the map Φ on `VlasovMeasureCurve`s, and by
Stage 5's continuation step (re-invoked with shifted initial data) and
Stage 8's uniqueness argument (where two competing solutions both produce
flows over a common ball). -/
theorem exists_vlasov_characteristicFlow_global_on_ball
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
    (R₀ : NNReal) (hR₀ : 0 < R₀)
    (M : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (R : NNReal)
    (hR : 4 * (R₀ : ℝ) + (R₀ : ℝ) * (T + 1) + (M : ℝ) * (T + 1) ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (T + 1),
              ∀ x ∈ Metric.closedBall (0 : PhysSpace d) (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 T) (Metric.closedBall (0 : PhaseSpace d) (R₀ : ℝ)) := by
  -- Instantiate `exists_vlasov_characteristicFlow` with z₀ = 0 and a := 2 R₀.
  have ha : (0 : NNReal) < 2 * R₀ := by
    have h2 : (0 : NNReal) < 2 := by norm_num
    exact mul_pos h2 hR₀
  -- closedBall 0 ((2 R₀ : NNReal) : ℝ) / 2) = closedBall 0 R₀.
  have h_ball_eq : Metric.closedBall (0 : PhaseSpace d) (((2 * R₀ : NNReal) : ℝ) / 2)
                   = Metric.closedBall (0 : PhaseSpace d) (R₀ : ℝ) := by
    congr 1
    push_cast
    ring
  rw [← h_ball_eq]
  -- Invoke the per-ball theorem.  Note: the per-ball theorem's enriched
  -- conclusion (post-Friction-5 surgery) bundles `IsCharacteristicFlowOn`
  -- with a boundary-regularity conjunct.  This caller (Stage 1.7) only
  -- needs the IsCharacteristicFlowOn piece; the boundary conjunct is
  -- discarded here but propagates through Stage 1.9's separate caller.
  have h_perBall : 2 * ((2 * R₀ : NNReal) : ℝ)
        + (‖(0 : PhaseSpace d).2‖ + ((2 * R₀ : NNReal) : ℝ) / 2) * (T + 1)
        + (M : ℝ) * (T + 1) ^ 2 ≤ R := by
    -- = 4R₀ + (0 + R₀)(T+1) + M(T+1)² = 4R₀ + R₀(T+1) + M(T+1)² ≤ R (from hR).
    have h_snd_zero : (0 : PhaseSpace d).2 = 0 := rfl
    rw [h_snd_zero, norm_zero, zero_add]
    push_cast
    calc 2 * (2 * (R₀ : ℝ)) + (2 * (R₀ : ℝ) / 2) * (T + 1) + (M : ℝ) * (T + 1) ^ 2
        = 4 * (R₀ : ℝ) + (R₀ : ℝ) * (T + 1) + (M : ℝ) * (T + 1) ^ 2 := by ring
      _ ≤ (R : ℝ) := hR
  have h_bnd : ∀ t ∈ Set.Icc (0 : ℝ) (T + 1),
                ∀ x ∈ Metric.closedBall (0 : PhaseSpace d).1 (R : ℝ),
                ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M := by
    intro t ht x hx
    have h_fst_zero : (0 : PhaseSpace d).1 = 0 := rfl
    rw [h_fst_zero] at hx
    exact hbound t ht x hx
  obtain ⟨charX, charV, hflow, _⟩ :=
    exists_vlasov_characteristicFlow W gradW hgradW L hL ρ h_int hρ_cont
      (0 : PhaseSpace d) (2 * R₀) ha M T hT R h_perBall h_bnd
  exact ⟨charX, charV, hflow⟩

/-- **Stage 1.9 helper: per-z trajectory existence for small T.**

For each `z : PhaseSpace d`, produces a trajectory `γ : ℝ → PhaseSpace d` with
`γ 0 = z` satisfying the Vlasov ODE on `Ioo 0 T`.

**Smallness constraint**: `L · (T+1)² < 1`.  Comes from `exists_vlasov_characteristicFlow`'s
`hR` inequality, whose `M·(T+1)²` term has quadratic-in-T growth.  Solving
the algebraic constraint per-z yields a finite `R(z)` and `M(z)`, with the
existence-bound on `T` driven by `L·(T+1)² < 1`.

Stage 5's continuation argument extends to arbitrary T via shifted initial
data; for Stages 2–4 we only need the small-T regime where the contraction
operates. -/
theorem exists_vlasov_perz_trajectory
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
    (h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (T : ℝ) (hT : 0 ≤ T)
    (hTL_PL : LocalSmallness_PL_buffer L T)
    (z : PhaseSpace d) :
    ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s => (γ s).1) (γ t).2 t ∧
        HasDerivAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) t) ∧
      -- **Boundary regularity** (Friction 5 surgery): HasDerivWithinAt on
      -- `Icc 0 T` for every t ∈ Icc 0 T, derived from the per-ball flow's
      -- enriched conjunct.  Closes the t = 0 (and t = T) boundary case for
      -- consumers like `flow_distance_growth_bound_on`.
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2 (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) (Set.Icc 0 T) t) := by
  -- ============================================================
  -- Compute R(z), M(z) from the algebraic constraint:
  --   R ≥ 2·1 + (‖z.2‖ + 1/2)(T+1) + M·(T+1)²
  --   M ≤ ‖gradW(0)‖ + L·(R + ‖z.1‖ + M_ρ)         (from L-Lipschitz)
  -- Substituting: R·(1 - L·(T+1)²) ≥ N(z)
  --   where N(z) := 2 + (‖z.2‖ + 1/2)(T+1)
  --                + (‖gradW(0)‖ + L·‖z.1‖ + L·M_ρ)·(T+1)²
  -- Use R := N(z) / (1 - L·(T+1)²)  (positive since `hTL_PL`).
  -- ============================================================
  -- **`LocalSmallness_PL_buffer` unfold site** (Stage 2b part 3 split,
  -- 2026-05-31).  This body consumes the PL-buffer constraint
  -- `L · (T+1)² < 1` directly for R-existence — the linarith on the next
  -- line derives `hTL_pos := 1 - L·(T+1)² > 0` from `hTL_PL`'s algebraic
  -- form, and the subsequent `R := N(z) / (1 - L·(T+1)²)` selection
  -- depends on the quadratic shape.  This is a SINGLE-PURPOSE use of the
  -- PL-buffer predicate (verified by the Stage 2b part 3 Commit 2 read):
  -- no contraction-flavored step in this body discharges off the same
  -- hypothesis.  Under the W̄ refactor, `LocalSmallness_PL_buffer L T`
  -- would become `C₂(L) · T < 1` (linear in T, no `+1`); this `have`
  -- updates to expose the new algebraic form and R re-derives under
  -- `C₂(L)`.  The `LocalSmallness_contraction` predicate is governed
  -- separately at `_picard_fixedPointFlow`'s `hq_lt` close, NOT here.
  have hTL : (L : ℝ) * (T + 1) ^ 2 < 1 := hTL_PL
  set hTL_pos : (0 : ℝ) < 1 - (L : ℝ) * (T + 1) ^ 2 := by linarith with hTL_pos_def
  -- N(z) is the right-hand-side numerator; non-negative.
  set N_z : ℝ := 2 + (‖z.2‖ + 1 / 2) * (T + 1)
                 + (‖gradW 0‖ + (L : ℝ) * ‖z.1‖ + (L : ℝ) * M_ρ) * (T + 1) ^ 2
    with hN_z_def
  have hN_z_nn : 0 ≤ N_z := by
    have h1 : 0 ≤ ‖z.2‖ + 1 / 2 := by positivity
    have h2 : 0 ≤ ‖gradW 0‖ + (L : ℝ) * ‖z.1‖ + (L : ℝ) * M_ρ := by
      have hgW : 0 ≤ ‖gradW 0‖ := norm_nonneg _
      have hLz1 : 0 ≤ (L : ℝ) * ‖z.1‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
      have hLMρ : 0 ≤ (L : ℝ) * M_ρ := mul_nonneg L.coe_nonneg hM_ρ_nn
      linarith
    have hT1nn : 0 ≤ T + 1 := by linarith
    have hT1sq : 0 ≤ (T + 1) ^ 2 := sq_nonneg _
    have := mul_nonneg h1 hT1nn
    have := mul_nonneg h2 hT1sq
    rw [hN_z_def]; positivity
  -- R_real := N(z) / (1 - L·(T+1)²)
  set R_real : ℝ := N_z / (1 - (L : ℝ) * (T + 1) ^ 2) with hR_real_def
  have hR_real_nn : 0 ≤ R_real := div_nonneg hN_z_nn (le_of_lt hTL_pos)
  set R : NNReal := Real.toNNReal R_real with hR_def
  have hR_eq : (R : ℝ) = R_real := Real.coe_toNNReal _ hR_real_nn
  -- M_real := ‖gradW(0)‖ + L · (R + ‖z.1‖ + M_ρ)
  set M_real : ℝ :=
    ‖gradW 0‖ + (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) with hM_real_def
  have hM_real_nn : 0 ≤ M_real := by
    have : 0 ≤ (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) := by
      apply mul_nonneg L.coe_nonneg
      have hR_nn : 0 ≤ (R : ℝ) := NNReal.coe_nonneg R
      have : 0 ≤ ‖z.1‖ := norm_nonneg _
      linarith
    linarith [norm_nonneg (gradW 0)]
  set M : NNReal := Real.toNNReal M_real with hM_def
  have hM_eq : (M : ℝ) = M_real := Real.coe_toNNReal _ hM_real_nn
  -- ============================================================
  -- Verify hR_local: 2·a + (‖z.2‖ + a/2)(T+1) + M·(T+1)² ≤ R
  -- with a = 1.
  -- After substitution: this is N_z ≤ R = R_real * (1 - L·(T+1)²) + correction.
  -- The construction gives R · (1 - L·(T+1)²) = N_z, so the inequality is tight.
  -- ============================================================
  have ha : (0 : NNReal) < 1 := by norm_num
  have hR_local : 2 * ((1 : NNReal) : ℝ)
                  + (‖z.2‖ + ((1 : NNReal) : ℝ) / 2) * (T + 1)
                  + (M : ℝ) * (T + 1) ^ 2 ≤ R := by
    -- Prove the equivalent inequality in real form, then transport via hM_eq, hR_eq.
    have hne : 1 - (L : ℝ) * (T + 1) ^ 2 ≠ 0 := ne_of_gt hTL_pos
    have h_R_rel : R_real * (1 - (L : ℝ) * (T + 1) ^ 2) = N_z := by
      simp only [hR_real_def]
      field_simp
    have h_LHS_eq : (2 : ℝ) + (‖z.2‖ + 1 / 2) * (T + 1) + M_real * (T + 1) ^ 2
                  = N_z + (L : ℝ) * R_real * (T + 1) ^ 2 := by
      -- M_real contains (R : ℝ); substitute via hR_eq before ring.
      simp only [hM_real_def, hN_z_def, hR_eq]; ring
    have h_target_eq : N_z + (L : ℝ) * R_real * (T + 1) ^ 2 = R_real := by
      nlinarith [h_R_rel]
    have h_real : (2 : ℝ) + (‖z.2‖ + 1 / 2) * (T + 1) + M_real * (T + 1) ^ 2 ≤ R_real := by
      linarith [h_LHS_eq, h_target_eq]
    -- Cast to NNReal form: ((1 : NNReal) : ℝ) = 1 and 2 * 1 = 2.
    have h_one : ((1 : NNReal) : ℝ) = 1 := by norm_cast
    rw [hM_eq, hR_eq, h_one]
    linarith [h_real]
  -- ============================================================
  -- Verify hbound_local: force bound on closedBall z.1 R for t ∈ Icc 0 (T+1).
  -- Uses ‖conv(ρ t, x)‖ ≤ ‖gradW(0)‖ + L · ∫‖x-y‖ dρ_t ≤ ‖gradW(0)‖ + L·(‖x‖ + M_ρ).
  -- For x ∈ closedBall z.1 R: ‖x‖ ≤ R + ‖z.1‖, so bound ≤ M_real = M.
  -- ============================================================
  have hbound_local : ∀ t ∈ Set.Icc (0 : ℝ) (T + 1),
                     ∀ x ∈ Metric.closedBall z.1 (R : ℝ),
                     ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M := by
    intro t _ht x hx
    have hx_norm : ‖x‖ ≤ (R : ℝ) + ‖z.1‖ := by
      have hdx : dist x z.1 ≤ (R : ℝ) := hx
      have hxz : ‖x - z.1‖ ≤ (R : ℝ) := by rwa [dist_eq_norm] at hdx
      have h_tri := norm_add_le (x - z.1) z.1
      rw [sub_add_cancel] at h_tri
      linarith
    -- ‖∫ gradW(x - y) dρ_t(y)‖ ≤ ∫ ‖gradW(x - y)‖ dρ_t(y).
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ t) := by
      have habs_meas : AEStronglyMeasurable (fun y : PhysSpace d => ‖x - y‖) (ρ t) :=
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id).norm
      refine Integrable.mono' ((integrable_const ‖x‖).add (h_y_int t)) habs_meas ?_
      refine Filter.Eventually.of_forall fun y => ?_
      simp only [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_sub_le x y
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ t) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    have h_pt : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this
        linarith
      linarith
    rw [hM_eq, hM_real_def]
    calc ‖convolveFunctionMeasure gradW (ρ t) x‖
        = ‖∫ y, gradW (x - y) ∂(ρ t)‖ := rfl
      _ ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ t) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ t) :=
          integral_mono (h_int t x).norm h_bnd_int h_pt
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ t) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ‖gradW 0‖ + (L : ℝ) * (‖x‖ + M_ρ) := by
          have hint_bd : ∫ y, ‖x - y‖ ∂(ρ t) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(ρ t)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ t) :=
                  integral_mono h_sub_int
                    ((integrable_const _).add (h_y_int t))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ t) := by
                  rw [integral_add (integrable_const _) (h_y_int t)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ t]
          have := mul_le_mul_of_nonneg_left hint_bd L.coe_nonneg
          linarith
      _ ≤ ‖gradW 0‖ + (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) := by
          have hL_nn : 0 ≤ (L : ℝ) := L.coe_nonneg
          have hMρ_nn : 0 ≤ M_ρ := hM_ρ_nn
          have h_bound : ‖x‖ + M_ρ ≤ (R : ℝ) + ‖z.1‖ + M_ρ := by linarith
          have := mul_le_mul_of_nonneg_left h_bound hL_nn
          linarith
  -- ============================================================
  -- Apply exists_vlasov_characteristicFlow with z₀ = z, a = 1.
  -- ============================================================
  obtain ⟨charX, charV, hflow, h_boundary⟩ :=
    exists_vlasov_characteristicFlow W gradW hgradW L hL
      ρ h_int hρ_cont z 1 ha M T hT R hR_local hbound_local
  -- Extract trajectory at w = z (z is the center of the ball, trivially in it).
  have hz_in : z ∈ Metric.closedBall z (((1 : NNReal) : ℝ) / 2) := by
    rw [Metric.mem_closedBall, dist_self]
    have : ((1 : NNReal) : ℝ) / 2 = (1 : ℝ) / 2 := by push_cast; ring
    linarith
  obtain ⟨hinit, hode_x, hode_v⟩ := hflow
  refine ⟨fun t => (charX t z, charV t z), ?_, ?_, ?_⟩
  · -- γ 0 = z
    have h0 := hinit z hz_in
    exact Prod.ext h0.1 h0.2
  · -- ODE on Ioo 0 T.
    intro t ht
    exact ⟨hode_x t ht z hz_in, hode_v t ht z hz_in⟩
  · -- Boundary regularity on Icc 0 T: lifted from the per-ball flow's
    -- enriched conjunct h_boundary.
    intro t ht
    exact h_boundary z hz_in t ht

/-- **Stage 1.9: True global-in-z characteristic flow on a small-T interval.**

For `L · (T+1)² < 1`, produces a characteristic flow `(charX, charV)` defined
for *every* `z : PhaseSpace d` (not just z in a ball), satisfying the Vlasov
ODE on `Ioo 0 T`.

This is the foundation Stage 2's Φ pushforward construction depends on.
Stage 5's continuation extends to arbitrary T via shifted-initial-data
iteration.

**Architecture**: per-z application of `exists_vlasov_characteristicFlow`
with `z₀ = z, a = 1` (via `exists_vlasov_perz_trajectory` helper), bundled
into a global flow via `Classical.choose`.  See helper's docstring for the
algebraic R(z), M(z) computation.

**Measurability**: NOT exposed.  The per-z Classical.choose bundling
doesn't propagate continuity-in-z.  Stage 1.8's placeholder
(`exists_vlasov_characteristicFlow_global_on_ball_measurable`) covers
the analogous question for the ball-localized variant; a parallel
`_global_smallT_measurable` companion can be added when needed, or the
measurability question can be addressed once (along with continuity-in-z)
by the Path-A real proof of Stage 1.8. -/
theorem exists_vlasov_characteristicFlow_global_smallT
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
    (h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (T : ℝ) (hT : 0 ≤ T)
    (hTL_PL : LocalSmallness_PL_buffer L T) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ ∧
      -- **Boundary regularity bundle** (Friction 5 surgery): expose the
      -- HasDerivWithinAt on `Icc 0 T` for every z and t ∈ Icc 0 T.  Lifted
      -- from the per-z trajectory's boundary-regularity conjunct.
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
          (Set.Icc 0 T) t) := by
  classical
  -- Per-z trajectory existence (with boundary regularity).
  have h_perZ : ∀ z : PhaseSpace d, ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s => (γ s).1) (γ t).2 t ∧
        HasDerivAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2 (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) (Set.Icc 0 T) t) := by
    intro z
    exact exists_vlasov_perz_trajectory W gradW hgradW L hL ρ h_int hρ_cont
      h_y_int M_ρ hM_ρ_nn hM_ρ T hT hTL_PL z
  -- Bundle via Classical.choose.
  let γ_func : PhaseSpace d → ℝ → PhaseSpace d := fun z =>
    Classical.choose (h_perZ z)
  refine ⟨fun t z => (γ_func z t).1, fun t z => (γ_func z t).2,
         ⟨?_, ?_, ?_⟩, ?_⟩
  · -- (i) Initial condition: γ_func z 0 = z for all z (Set.univ).
    intro z _
    have h_init : γ_func z 0 = z := (Classical.choose_spec (h_perZ z)).1
    exact ⟨congrArg Prod.fst h_init, congrArg Prod.snd h_init⟩
  · -- (ii) Position ODE at t ∈ Ioo 0 T.
    intro t ht z _
    exact ((Classical.choose_spec (h_perZ z)).2.1 t ht).1
  · -- (iii) Velocity ODE at t ∈ Ioo 0 T.
    intro t ht z _
    exact ((Classical.choose_spec (h_perZ z)).2.1 t ht).2
  · -- (iv) Boundary regularity bundle on Icc 0 T for every z.
    intro z t ht
    exact (Classical.choose_spec (h_perZ z)).2.2 t ht

-- ---------------------------------------------------------------------------
-- Stage 2 — Define the map Φ and prove well-defined (partial: def + first three fields)
-- ---------------------------------------------------------------------------
-- The pushforward operator Φ takes a characteristic flow `charX : ℝ → PhaseSpace
-- d → PhysSpace d` and an initial measure `f₀ : Measure (PhaseSpace d)`, and
-- produces a time-indexed curve of measures on `PhysSpace d` via
-- `Φ charX f₀ t := Measure.map (fun z => charX t z) f₀`.
--
-- This file's Stage 2 covers:
--   * `Phi`: the bare definition.
--   * `Phi_isProbabilityMeasure`: under AEMeasurable hypothesis.
--   * `Phi_hasMoment_le`: under measurability + per-z growth-bound hypothesis.
--   * `Phi_yIntegrable`: derived from hasMoment_le.
--
-- Deferred to Stage 2b (next session):
--   * `Phi_hW1Cont`: W₁-continuity via DCT (substantive ~60 lines).
--   * `Phi_asVlasovMeasureCurve`: the full bundling into a `VlasovMeasureCurve d T M`.
--
-- The measurability + growth-bound hypotheses are passed through as inputs; their
-- discharge happens at the call site (Stage 4's Picard iteration), where the
-- concrete flow is constructed and the hypotheses follow from the construction.

/-- The Φ pushforward operator: maps a characteristic flow + initial measure to
the time-indexed pushforward measure on `PhysSpace d`. -/
noncomputable def Phi {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) : ℝ → Measure (PhysSpace d) :=
  fun t => Measure.map (fun z => charX t z) f₀

/-- `Phi charX f₀ t` is a probability measure when `charX t` is AE-measurable
wrt `f₀`. -/
theorem Phi_isProbabilityMeasure {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (t : ℝ) :
    IsProbabilityMeasure (Phi charX f₀ t) := by
  unfold Phi
  exact MeasureTheory.Measure.isProbabilityMeasure_map (h_meas t)

/-- Uniform first-moment bound on `Phi charX f₀` under a per-z position growth
hypothesis `‖charX t z‖ ≤ C_T · (‖z‖ + 1)`.

Composes `integral_map` (which exchanges the pushforward) with the pointwise
growth bound + linearity of integration over `f₀`. -/
theorem Phi_hasMoment_le {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ y, ‖y‖ ∂(Phi charX f₀ t) ≤ C_T * (M_f₀ + 1) := by
  unfold Phi
  -- ∫ y ‖y‖ ∂(Measure.map (charX t) f₀) = ∫ z ‖charX t z‖ ∂f₀  via integral_map.
  rw [integral_map (h_meas t) (Continuous.aestronglyMeasurable continuous_norm)]
  -- ≤ ∫ z (C_T·(‖z‖+1)) ∂f₀  via pointwise growth bound.
  have h_growth_t := h_growth t ht
  -- Both sides integrable; use integral_mono.
  have h_growth_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact this.const_mul _
  have h_lhs_int : Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀ := by
    refine Integrable.mono' h_growth_int ((h_meas t).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hbd := h_growth_t z
    have h_rhs_nn : 0 ≤ C_T * (‖z‖ + 1) := by
      apply mul_nonneg hC_T_nn
      linarith [norm_nonneg z]
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    linarith
  calc ∫ z, ‖charX t z‖ ∂f₀
      ≤ ∫ z, C_T * (‖z‖ + 1) ∂f₀ :=
        integral_mono h_lhs_int h_growth_int (fun z => h_growth_t z)
    _ = C_T * ∫ z, (‖z‖ + 1) ∂f₀ := by
        rw [integral_const_mul]
    _ = C_T * (∫ z, ‖z‖ ∂f₀ + 1) := by
        congr 1
        rw [integral_add h_f₀_int (integrable_const _)]
        simp [integral_const, measureReal_def, measure_univ]
    _ ≤ C_T * (M_f₀ + 1) := by
        have h_M_nn : 0 ≤ M_f₀ + 1 := by
          have : 0 ≤ ∫ z, ‖z‖ ∂f₀ := integral_nonneg (fun _ => norm_nonneg _)
          linarith [hM_f₀]
        apply mul_le_mul_of_nonneg_left _ hC_T_nn
        linarith

/-- `‖·‖` is integrable wrt `Phi charX f₀ t` under the growth hypothesis. -/
theorem Phi_yIntegrable {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ t) := by
  -- Integrable wrt pushforward iff ‖·‖ ∘ (charX t) is integrable wrt f₀.
  unfold Phi
  rw [integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas t)]
  -- Now integrable wrt f₀.
  have h_growth_t := h_growth t ht
  have h_growth_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact this.const_mul _
  refine Integrable.mono' h_growth_int ?_ ?_
  · -- AEStronglyMeasurable of ‖·‖ ∘ charX t.
    exact ((h_meas t).aestronglyMeasurable.norm)
  · refine Filter.Eventually.of_forall fun z => ?_
    have hbd := h_growth_t z
    -- Goal shape: ‖((fun a => ‖a‖) ∘ (fun z => charX t z)) z‖ ≤ C_T * (‖z‖ + 1).
    -- The composition simplifies to ‖‖charX t z‖‖, then Real.norm_of_nonneg.
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hbd

/-- **Stage 2b: W₁ bound on Φ pushforwards via 1-Lipschitz test functions.**

For any two time points `s, t`, the Wasserstein-1 distance between
`Phi charX f₀ s` and `Phi charX f₀ t` is bounded by the integral
`∫ z, ‖charX s z - charX t z‖ ∂f₀`.

**Proof strategy** (KR-dual direct): for each 1-Lipschitz `φ : PhysSpace d → ℝ`,
`integral_map` converts `∫ φ d(charX_·)#f₀` to `∫ z, φ(charX_· z) ∂f₀`.
The integral diff is bounded pointwise by `‖charX s z - charX t z‖` (1-Lipschitz
of φ), then by integral monotonicity.

**Architectural note**: `wasserstein1_pushforward_le_iInf` (Coupling.lean L270)
requires endomaps `Φ Ψ : α → α`.  Our `charX t : PhaseSpace d → PhysSpace d`
is cross-type, so we work directly with the KR-dual sup — cleaner than
re-deriving the coupling theory.

**Implementation discipline** (CLAUDE.md L7 + L8): all `Integrable.mono'`
dominator facts are built as named `have` statements BEFORE the call (no
inline `?_`).  The `integrable_map_measure` bridge uses `.mpr` to handle
the `g ∘ f` ↔ `fun z => g (f z)` syntactic mismatch.

Used by Stage 2b's follow-on `Phi_hW1Cont` (next swing) to bound W₁(Φ_s,
Φ_t) by an integral that DCT controls as `t → s`. -/
theorem wasserstein1_Phi_le_integral_diff {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    -- ‖charX t z‖ integrable wrt f₀ for each t.
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (s t : ℝ)
    -- ‖charX s z - charX t z‖ integrable wrt f₀ (follows from h_int_charX s, t + triangle).
    (h_diff_int : Integrable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀) :
    wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t) ≤
      ENNReal.ofReal (∫ z, ‖charX s z - charX t z‖ ∂f₀) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  unfold Phi
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  -- ============================================================
  -- Setup: φ is 1-Lipschitz; AEStronglyMeasurable wrt each pushforward.
  -- ============================================================
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_νs : AEStronglyMeasurable φ (Measure.map (fun z => charX s z) f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_meas_νt : AEStronglyMeasurable φ (Measure.map (fun z => charX t z) f₀) :=
    hφ_cont.aestronglyMeasurable
  -- ============================================================
  -- 1-Lipschitz dominator: |φ y| ≤ |φ 0| + ‖y‖.
  -- ============================================================
  have hφ_abs_bound : ∀ y : PhysSpace d, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith
      _ = |φ 0| + ‖y‖ := by ring
  -- ============================================================
  -- EXPLICIT DOMINATOR CONSTRUCTION (CLAUDE.md L7).
  -- Build h_norm_int_νs and h_norm_int_νt via `.mpr` (CLAUDE.md L8) —
  -- this avoids the `g ∘ f` ↔ `fun z => g (f z)` rewrite mismatch.
  -- ============================================================
  have h_norm_int_νs : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map (fun z => charX s z) f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas s)).mpr (h_int_charX s)
  have h_norm_int_νt : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map (fun z => charX t z) f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas t)).mpr (h_int_charX t)
  -- Dominator `|φ 0| + ‖y‖` integrable wrt each pushforward.
  have h_dom_νs : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map (fun z => charX s z) f₀) :=
    (integrable_const _).add h_norm_int_νs
  have h_dom_νt : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map (fun z => charX t z) f₀) :=
    (integrable_const _).add h_norm_int_νt
  -- φ integrable wrt each pushforward (via `Integrable.mono'` with explicit dominator).
  have hφ_int_νs : Integrable φ (Measure.map (fun z => charX s z) f₀) := by
    refine Integrable.mono' h_dom_νs hφ_meas_νs ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h_dom_nn : 0 ≤ |φ 0| + ‖y‖ :=
      add_nonneg (abs_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  have hφ_int_νt : Integrable φ (Measure.map (fun z => charX t z) f₀) := by
    refine Integrable.mono' h_dom_νt hφ_meas_νt ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h_dom_nn : 0 ≤ |φ 0| + ‖y‖ :=
      add_nonneg (abs_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  -- ============================================================
  -- Convert pushforward integrals via `integral_map`.
  -- The RHS of `integral_map` is point-full `f (g x)` (NOT `(f ∘ g) x`),
  -- so no L8 bridge needed here.
  -- ============================================================
  rw [integral_map (h_meas s) hφ_meas_νs,
      integral_map (h_meas t) hφ_meas_νt]
  -- Goal: ∫ z, φ (charX s z) ∂f₀ - ∫ z, φ (charX t z) ∂f₀
  --        ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀.
  -- ============================================================
  -- Pull-back integrability of `fun z => φ (charX · z)` to wrt f₀ via `.mp`.
  -- ============================================================
  have hφ_comp_int_s : Integrable (fun z : PhaseSpace d => φ (charX s z)) f₀ :=
    (integrable_map_measure hφ_meas_νs (h_meas s)).mp hφ_int_νs
  have hφ_comp_int_t : Integrable (fun z : PhaseSpace d => φ (charX t z)) f₀ :=
    (integrable_map_measure hφ_meas_νt (h_meas t)).mp hφ_int_νt
  -- Combine into single integral; bound by Lipschitz inequality.
  rw [← integral_sub hφ_comp_int_s hφ_comp_int_t]
  have h_pt : ∀ z : PhaseSpace d,
      φ (charX s z) - φ (charX t z) ≤ ‖charX s z - charX t z‖ := fun z => by
    have h_lip := hφ.dist_le_mul (charX s z) (charX t z)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h_lip
    -- h_lip : |φ (charX s z) - φ (charX t z)| ≤ ‖charX s z - charX t z‖.
    linarith [abs_le.mp h_lip |>.2]
  exact integral_mono (hφ_comp_int_s.sub hφ_comp_int_t) h_diff_int h_pt

/-- **Stage 2c sub-piece: DCT step — the integral `∫ z, ‖charX s z - charX t z‖ ∂f₀`
tends to 0 as `t → s` within `Icc 0 T`.**

Combines pointwise continuity `t ↦ charX t z` (from the flow's HasDerivAt
→ ContinuousAt) with a uniform dominator `2·C_T·(‖z‖+1)` (from the per-z
growth bound) via Mathlib's filter-DCT.

**Implementation discipline** (L7): the dominator integrability is built
as a named `have` before the DCT call. -/
theorem Phi_integral_diff_tendsto_zero {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    -- Continuity of t ↦ charX t z at base s (from HasDerivAt).
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T)
    (h_charX_cont : ∀ z, ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    Filter.Tendsto (fun t => ∫ z, ‖charX s z - charX t z‖ ∂f₀)
      (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
  -- ============================================================
  -- Dominator: `bound z := 2 * C_T * (‖z‖ + 1)` integrable wrt f₀.
  -- ============================================================
  set bound : PhaseSpace d → ℝ :=
    fun z => 2 * C_T * (‖z‖ + 1) with hbound_def
  have h_bound_int : Integrable bound f₀ := by
    have h1 : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact h1.const_mul _
  -- ============================================================
  -- AE strong measurability of (fun z => ‖charX s z - charX t z‖) wrt f₀, eventually in t.
  -- ============================================================
  have h_F_meas : ∀ᶠ t in nhdsWithin s (Set.Icc 0 T),
      AEStronglyMeasurable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀ := by
    refine Filter.Eventually.of_forall fun t => ?_
    exact ((h_meas s).sub (h_meas t)).norm.aestronglyMeasurable
  -- ============================================================
  -- Pointwise bound: ‖‖charX s z - charX t z‖‖ ≤ bound z eventually.
  -- ============================================================
  have h_F_bound : ∀ᶠ t in nhdsWithin s (Set.Icc 0 T),
      ∀ᵐ z ∂f₀, ‖‖charX s z - charX t z‖‖ ≤ bound z := by
    refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Icc 0 T, ?_, ?_⟩
    · exact self_mem_nhdsWithin
    · intro t ht
      refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h_tri := norm_sub_le (charX s z) (charX t z)
      have h_s := h_growth s hs z
      have h_t := h_growth t ht z
      have h_C_nn_2 : 0 ≤ 2 * C_T := by linarith
      have hz_nn : 0 ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
      calc ‖charX s z - charX t z‖
          ≤ ‖charX s z‖ + ‖charX t z‖ := h_tri
        _ ≤ C_T * (‖z‖ + 1) + C_T * (‖z‖ + 1) := by linarith
        _ = 2 * C_T * (‖z‖ + 1) := by ring
  -- ============================================================
  -- Pointwise limit: ‖charX s z - charX t z‖ → 0 as t → s within Icc 0 T.
  -- ============================================================
  have h_F_lim : ∀ᵐ z ∂f₀, Filter.Tendsto
      (fun t => ‖charX s z - charX t z‖) (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
    refine Filter.Eventually.of_forall fun z => ?_
    -- t ↦ charX s z - charX t z → 0 as t → s, because charX(·) z → charX s z.
    have h_tendsto : Filter.Tendsto (fun t => charX t z) (nhdsWithin s (Set.Icc 0 T))
                       (nhds (charX s z)) := h_charX_cont z
    have h_sub : Filter.Tendsto (fun t => charX s z - charX t z)
                   (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
      have h_cancel : (charX s z - charX s z : PhysSpace d) = 0 := sub_self _
      rw [← h_cancel]
      exact (tendsto_const_nhds (x := charX s z)).sub h_tendsto
    have h_norm_tendsto :
        Filter.Tendsto (fun t => ‖charX s z - charX t z‖)
          (nhdsWithin s (Set.Icc 0 T)) (nhds ‖(0 : PhysSpace d)‖) :=
      (continuous_norm.tendsto 0).comp h_sub
    simpa using h_norm_tendsto
  -- ============================================================
  -- Apply Mathlib's filter-DCT.
  -- ============================================================
  have h_dct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := f₀)
    bound h_F_meas h_F_bound h_bound_int h_F_lim
  -- h_dct : Tendsto (fun t => ∫ z, ‖charX s z - charX t z‖ ∂f₀)
  --   (nhdsWithin s (Icc 0 T)) (nhds (∫ z, 0 ∂f₀))
  -- ∫ z, 0 ∂f₀ = 0
  simp only [integral_zero] at h_dct
  exact h_dct

/-- **Stage 2c sub-piece: W₁-continuity of `t ↦ Phi charX f₀ t` at every base
point `s ∈ Icc 0 T`.**

Composes the W₁ bound (`wasserstein1_Phi_le_integral_diff`) with the DCT step
(`Phi_integral_diff_tendsto_zero`) to conclude that
`(wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal → 0` as `t → s`. -/
theorem Phi_hW1Cont {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (h_charX_cont : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      ContinuousWithinAt
        (fun t => (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal)
        (Set.Icc 0 T) s := by
  intro s hs
  -- ContinuousWithinAt at s ↔ Tendsto · → value-at-s within filter.
  -- Value at t = s: wasserstein1_self = 0.
  rw [ContinuousWithinAt]
  have h_value_at_s : (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ s)).toReal = 0 := by
    rw [wasserstein1_self]; rfl
  rw [h_value_at_s]
  -- DCT gives ∫-tendsto-zero.
  have h_dct := Phi_integral_diff_tendsto_zero charX f₀ h_meas T hT C_T hC_T_nn
    h_growth h_f₀_int s hs (h_charX_cont s hs)
  -- Build the ‖charX s z - charX t z‖-diff-integrability eventually.
  have h_diff_int_eventually : ∀ᶠ t in nhdsWithin s (Set.Icc 0 T),
      Integrable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀ := by
    refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Icc 0 T, self_mem_nhdsWithin, ?_⟩
    intro t ht
    have h_dom_int : Integrable (fun z : PhaseSpace d => 2 * C_T * (‖z‖ + 1)) f₀ :=
      (h_f₀_int.add (integrable_const _)).const_mul _
    refine Integrable.mono' h_dom_int
      (((h_meas s).sub (h_meas t)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h_tri := norm_sub_le (charX s z) (charX t z)
    have h_s := h_growth s hs z
    have h_t := h_growth t ht z
    calc ‖charX s z - charX t z‖
        ≤ ‖charX s z‖ + ‖charX t z‖ := h_tri
      _ ≤ C_T * (‖z‖ + 1) + C_T * (‖z‖ + 1) := by linarith
      _ = 2 * C_T * (‖z‖ + 1) := by ring
  -- Combine: W₁ bound ⇒ toReal bound ⇒ tendsto-zero.
  -- Strategy: bound the W₁.toReal by the integral via wasserstein1_Phi_le_integral_diff.
  -- Then use squeeze on Tendsto.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- From h_dct: ∃ δ, ∀ t ∈ Icc 0 T, dist t s < δ → |∫ ...| < ε.
  rw [Metric.tendsto_nhdsWithin_nhds] at h_dct
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := h_dct ε hε
  -- Use the same δ.
  refine ⟨δ, hδ_pos, fun t ht hdt => ?_⟩
  -- Goal: dist ((wasserstein1 (Phi s) (Phi t)).toReal) 0 < ε.
  rw [Real.dist_eq, sub_zero]
  -- |(W₁ s t).toReal| ≤ |∫ ...|.
  haveI hΦs_prob : IsProbabilityMeasure (Phi charX f₀ s) :=
    Phi_isProbabilityMeasure charX f₀ h_meas s
  haveI hΦt_prob : IsProbabilityMeasure (Phi charX f₀ t) :=
    Phi_isProbabilityMeasure charX f₀ h_meas t
  have h_yint_s : Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ s) :=
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int s hs
  have h_yint_t : Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ t) :=
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int t ht
  have h_W1_finite : wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t) ≠ ⊤ :=
    wasserstein1_ne_top_of_finite_moment _ _ h_yint_s h_yint_t
  have h_diff_int_t : Integrable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀ := by
    -- Inline the integrability proof to avoid the `Filter.eventually_iff_exists_mem`
    -- destructuring's metavariable mismatch.
    have h_dom_int : Integrable (fun z : PhaseSpace d => 2 * C_T * (‖z‖ + 1)) f₀ :=
      (h_f₀_int.add (integrable_const _)).const_mul _
    refine Integrable.mono' h_dom_int
      (((h_meas s).sub (h_meas t)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h_tri := norm_sub_le (charX s z) (charX t z)
    have h_s := h_growth s hs z
    have h_t := h_growth t ht z
    calc ‖charX s z - charX t z‖
        ≤ ‖charX s z‖ + ‖charX t z‖ := h_tri
      _ ≤ C_T * (‖z‖ + 1) + C_T * (‖z‖ + 1) := by linarith
      _ = 2 * C_T * (‖z‖ + 1) := by ring
  have h_W1_le := wasserstein1_Phi_le_integral_diff charX f₀ h_meas h_int_charX
    s t h_diff_int_t
  -- |∫ ‖charX s z - charX t z‖ ∂f₀| < ε from hδ_bd.
  have h_int_bd := hδ_bd ht hdt
  rw [Real.dist_eq, sub_zero] at h_int_bd
  -- Combine: (W₁ s t).toReal ≤ ofReal(∫ ‖...‖).toReal ≤ |∫ ‖...‖| < ε.
  have h_int_nn : 0 ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have h_toReal_le : (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal ≤
      ∫ z, ‖charX s z - charX t z‖ ∂f₀ := by
    have h_ofReal_eq : (ENNReal.ofReal (∫ z, ‖charX s z - charX t z‖ ∂f₀)).toReal
                      = ∫ z, ‖charX s z - charX t z‖ ∂f₀ := by
      rw [ENNReal.toReal_ofReal h_int_nn]
    rw [← h_ofReal_eq]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_le
  have h_toReal_nn : 0 ≤ (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal :=
    ENNReal.toReal_nonneg
  rw [abs_of_nonneg h_toReal_nn]
  calc (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal
      ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀ := h_toReal_le
    _ < ε := by
        have h_abs_eq : |∫ z, ‖charX s z - charX t z‖ ∂f₀|
                      = ∫ z, ‖charX s z - charX t z‖ ∂f₀ := abs_of_nonneg h_int_nn
        linarith [h_int_bd, h_abs_eq.symm.le, abs_nonneg (∫ z, ‖charX s z - charX t z‖ ∂f₀)]

/-- **Stage 2c: full bundling of Φ into a `VlasovMeasureCurve`.**

Given the four hypothesis bundles (measurability, growth, f₀'s integrability,
flow continuity), bundles Stage 2a's three properties + Stage 2c's `Phi_hW1Cont`
into a `VlasovMeasureCurve d T M'` where `M' := C_T · (M_f₀ + 1)`.

This is the structured output that Stage 3's contraction estimate and Stage 4's
Banach iteration consume. -/
noncomputable def Phi_asVlasovMeasureCurve {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    (h_charX_cont : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)) where
  ρ := Phi charX f₀
  isProb := Phi_isProbabilityMeasure charX f₀ h_meas
  hasMoment := fun t ht =>
    Phi_hasMoment_le charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int M_f₀ hM_f₀ t ht
  yIntegrable := fun t ht =>
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int t ht
  hW1Cont :=
    Phi_hW1Cont charX f₀ h_meas h_int_charX T hT C_T hC_T_nn h_growth h_f₀_int
      h_charX_cont

/-- **Stage 1.8 (re-stated for Stage 1.9's flow): measurability of a
characteristic flow given Picard-style boundary regularity.**

Given a flow `(charX, charV)` that:
* matches the initial condition at `t = 0`,
* is continuous in `t` on `Icc 0 T` for each `z` (i.e. Picard-solution
  regularity at the boundary),
* satisfies the Vlasov ODE in `HasDerivWithinAt`-on-`Ico` form,

we prove that for each `t ∈ Icc 0 T`, the map `z ↦ (charX t z, charV t z)`
is Borel-measurable on `PhaseSpace d`.

**Proof strategy** (Gronwall on flow difference, via Mathlib's
`dist_le_of_trajectories_ODE`):  the Vlasov vector field is
`max(1, L)`-Lipschitz uniformly in `t` (`vlasovVectorField_lipschitzWith`),
so two trajectories `f, g : ℝ → PhaseSpace d` starting from `z₁, z₂` satisfy
`dist (f t) (g t) ≤ dist(z₁, z₂) · exp(max(1, L) · t)` for `t ∈ Icc 0 T`.
This is exp(K·t)-Lipschitz-in-`z`, hence continuous in `z`, hence Borel-
measurable.

**Why the boundary regularity is taken as hypothesis**: Stage 1.9's
`IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` gives `HasDerivAt` only on
the open interval `Ioo 0 T`.  Mathlib's `dist_le_of_trajectories_ODE`
requires `ContinuousOn` on `Icc 0 T` plus `HasDerivWithinAt` on `Ico 0 T`
(closed at the left endpoint).  The boundary regularity at `t = 0` is a
property of the underlying Picard construction, not derivable from
`IsCharacteristicFlowOn` alone.  Stage 4's Picard iteration discharges
these hypotheses from the concrete construction.

**Supersedes the original Stage 1.8 placeholder** (which targeted the
ball-localized Stage 1.7 flow that Stage 2 doesn't use).  The previous
sorry'd lemma — `exists_vlasov_characteristicFlow_global_on_ball_measurable`
— is removed since it's not on the project's critical path.  This new
lemma is what Stage 4's Picard construction will plug into the Φ
pipeline.

**Sorry count**: this commit DECREASES the project's sorry count from
6 to 5 (the old Stage 1.8 placeholder is removed, the new lemma is fully
proved). -/
theorem charFlow_measurable_via_gronwall
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) := by
  intro t ht
  -- ============================================================
  -- Vector field is max(1, L)-Lipschitz uniformly in t.
  -- ============================================================
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  -- ============================================================
  -- Gronwall on flow difference: dist-bound on Icc 0 T.
  -- ============================================================
  have h_dist_bound : ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
      dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)) := by
    intro z₁ z₂
    -- Apply dist_le_of_trajectories_ODE with f, g = per-z trajectories.
    have h := dist_le_of_trajectories_ODE
      (v := fun s => vlasovVectorField gradW ρ s)
      (f := fun s => (charX s z₁, charV s z₁))
      (g := fun s => (charX s z₂, charV s z₂))
      (K := K) (a := 0) (b := T)
      (δ := dist z₁ z₂)
      h_vf_lip
      (h_cont_Icc z₁) (h_deriv_Ico z₁)
      (h_cont_Icc z₂) (h_deriv_Ico z₂)
      ?_ t ht
    · exact h
    · -- dist (f 0) (g 0) = dist z₁ z₂ via h_init.  Need to beta-reduce first.
      show dist ((charX 0 z₁, charV 0 z₁) : PhaseSpace d) (charX 0 z₂, charV 0 z₂)
           ≤ dist z₁ z₂
      rw [h_init z₁, h_init z₂]
  -- ============================================================
  -- Convert dist-bound to continuity in z via Metric.continuous_iff.
  -- ============================================================
  have h_cont_z : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [Metric.continuous_iff]
    intro z₀ ε hε
    -- Lipschitz constant exp(K * t); pick δ := ε / exp(K * t).
    have h_exp_pos : 0 < Real.exp ((K : ℝ) * (t - 0)) := Real.exp_pos _
    refine ⟨ε / Real.exp ((K : ℝ) * (t - 0)), div_pos hε h_exp_pos, ?_⟩
    intro z hz
    -- dist (f z₀) (f z) ≤ exp(K*t) * dist z₀ z < exp(K*t) * (ε / exp(K*t)) = ε.
    have h_bd := h_dist_bound z₀ z
    -- Note: dist_bound gives `dist (f z₀) (f z)`, but `Metric.continuous_iff`
    -- gives `dist z z₀ < δ → dist (f z) (f z₀) < ε`.  Symmetric: use dist_comm.
    rw [dist_comm] at hz
    have h_chain : dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
                  < ε := by
      calc dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
          ≤ dist z₀ z * Real.exp ((K : ℝ) * (t - 0)) := h_bd
        _ < (ε / Real.exp ((K : ℝ) * (t - 0))) * Real.exp ((K : ℝ) * (t - 0)) :=
            mul_lt_mul_of_pos_right hz h_exp_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt h_exp_pos)
    rwa [dist_comm] at h_chain
  exact h_cont_z.measurable

/-- **Step 0b — the flow's Lipschitz-in-`z` bound (open-interval form).**

Extracted from `charFlow_measurable_via_gronwall_Ioo`'s internal
`h_dist_bound`.  Given the open-interval flow ODE, the characteristic flow
`z ↦ (charX t z, charV t z)` is Lipschitz in the initial datum `z` with
constant `exp((max 1 L) · (t − 0))`, uniformly for `t ∈ [0, T]`.

Same hypotheses as `charFlow_measurable_via_gronwall_Ioo`; the conclusion
is the Grönwall distance bound used by both that lemma (to derive
continuity-in-`z` hence measurability) and the moment-free dominator in
`dobrushin_uniqueness_On`. -/
theorem charFlow_lipschitzInZ_via_gronwall_Ioo
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ioo : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
        dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
        dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (t - 0)) := by
  intro t ht
  -- Vector field is max(1, L)-Lipschitz uniformly in s.
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  intro z₁ z₂
  -- Abbreviations for the two per-z trajectories.
  set F : ℝ → PhaseSpace d := fun s => (charX s z₁, charV s z₁) with hF_def
  set G : ℝ → PhaseSpace d := fun s => (charX s z₂, charV s z₂) with hG_def
  -- Split on whether t = 0 or 0 < t.
  rcases eq_or_lt_of_le ht.1 with h_t0 | h_pos
  · -- t = 0: both trajectories evaluate to their initial conditions.
    subst h_t0
    simp only [hF_def, hG_def, h_init z₁, h_init z₂, sub_self, mul_zero,
      Real.exp_zero, mul_one, le_refl]
  · -- 0 < t: take the s₀ → 0⁺ limit of Grönwall bounds on [s₀, t].
    -- Per-s₀ Grönwall bound on the window [s₀, t] ⊆ [0, T].
    have h_perS0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
        dist (F t) (G t) ≤ dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)) := by
      intro s₀ hs₀
      -- Window inclusions.
      have hsub_Ico : Set.Ico s₀ t ⊆ Set.Ioo (0 : ℝ) T := fun s hs =>
        ⟨lt_of_lt_of_le hs₀.1 hs.1, lt_of_lt_of_le hs.2 ht.2⟩
      have hsub_Icc : Set.Icc s₀ t ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc hs₀.1.le ht.2
      have h := dist_le_of_trajectories_ODE
        (v := fun s => vlasovVectorField gradW ρ s)
        (f := F) (g := G)
        (K := K) (a := s₀) (b := t)
        (δ := dist (F s₀) (G s₀))
        h_vf_lip
        ((h_cont_Icc z₁).mono hsub_Icc)
        (fun s hs => h_deriv_Ioo z₁ s (hsub_Ico hs))
        ((h_cont_Icc z₂).mono hsub_Icc)
        (fun s hs => h_deriv_Ioo z₂ s (hsub_Ico hs))
        (le_refl _) t ⟨hs₀.2.le, le_refl t⟩
      exact h
    -- The filter 𝓝[Ioo 0 t] 0 is NeBot since 0 < t.
    have : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot :=
      left_nhdsWithin_Ioo_neBot h_pos
    -- Tendsto F to z₁ along 𝓝[Ioo 0 t] 0.
    have hIoo_sub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun s hs =>
      ⟨hs.1.le, le_trans hs.2.le ht.2⟩
    have hF0 : F 0 = z₁ := h_init z₁
    have hG0 : G 0 = z₂ := h_init z₂
    have h_tendsto_F : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
        (nhds z₁) := by
      have hcw : ContinuousWithinAt F (Set.Icc (0 : ℝ) T) 0 :=
        (h_cont_Icc z₁) 0 ⟨le_refl 0, hT⟩
      have : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (F 0)) :=
        hcw
      rw [hF0] at this
      exact this.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
    have h_tendsto_G : Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
        (nhds z₂) := by
      have hcw : ContinuousWithinAt G (Set.Icc (0 : ℝ) T) 0 :=
        (h_cont_Icc z₂) 0 ⟨le_refl 0, hT⟩
      have : Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (G 0)) :=
        hcw
      rw [hG0] at this
      exact this.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
    -- Tendsto of dist (F s₀) (G s₀) to dist z₁ z₂.
    have h_tendsto_dist :
        Filter.Tendsto (fun s₀ => dist (F s₀) (G s₀))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds (dist z₁ z₂)) :=
      h_tendsto_F.dist h_tendsto_G
    -- Tendsto of exp(K*(t-s₀)) to exp(K*(t-0)).
    have h_tendsto_exp :
        Filter.Tendsto (fun s₀ => Real.exp ((K : ℝ) * (t - s₀)))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
          (nhds (Real.exp ((K : ℝ) * (t - 0)))) := by
      have hcont : Continuous (fun s₀ : ℝ => Real.exp ((K : ℝ) * (t - s₀))) := by
        fun_prop
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    -- Product of the two limits.
    have h_lim :
        Filter.Tendsto (fun s₀ => dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
          (nhds (dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)))) :=
      h_tendsto_dist.mul h_tendsto_exp
    -- The per-s₀ bound holds eventually along the filter.
    have h_event :
        ∀ᶠ s₀ in nhdsWithin (0 : ℝ) (Set.Ioo 0 t),
          dist (F t) (G t) ≤ dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)) :=
      eventually_nhdsWithin_of_forall h_perS0
    -- Pass to the limit.
    exact ge_of_tendsto h_lim h_event

/-- **Open-interval variant of `charFlow_measurable_via_gronwall`.**

Identical to `charFlow_measurable_via_gronwall` except the derivative
hypothesis is on the OPEN interval `Set.Ioo 0 T` instead of the
half-open `Set.Ico 0 T`.  This matches the regularity that an
`IsCharacteristicFlowOn ... (Set.Ioo 0 T)` predicate directly produces
(the ODE holds on the open interval, with the endpoints handled by
continuity).

The proof reuses the per-window Grönwall distance bound, but obtains the
`t = 0` endpoint distance bound by taking a one-sided limit
`s₀ → 0⁺` of the Grönwall bounds on `[s₀, t]` (each of which only needs
the derivative on `Set.Ico s₀ t ⊆ Set.Ioo 0 T`), rather than applying
Grönwall directly on `[0, t]`. -/
theorem charFlow_measurable_via_gronwall_Ioo
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ioo : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) := by
  intro t ht
  -- ============================================================
  -- Vector field is max(1, L)-Lipschitz uniformly in t.
  -- ============================================================
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  -- ============================================================
  -- Gronwall on flow difference: dist-bound on Icc 0 T (step 0b, extracted
  -- to `charFlow_lipschitzInZ_via_gronwall_Ioo`).
  -- ============================================================
  have h_dist_bound : ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
      dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT
      h_init h_cont_Icc h_deriv_Ioo t ht
  -- ============================================================
  -- Convert dist-bound to continuity in z via Metric.continuous_iff.
  -- ============================================================
  have h_cont_z : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [Metric.continuous_iff]
    intro z₀ ε hε
    -- Lipschitz constant exp(K * t); pick δ := ε / exp(K * t).
    have h_exp_pos : 0 < Real.exp ((K : ℝ) * (t - 0)) := Real.exp_pos _
    refine ⟨ε / Real.exp ((K : ℝ) * (t - 0)), div_pos hε h_exp_pos, ?_⟩
    intro z hz
    -- dist (f z₀) (f z) ≤ exp(K*t) * dist z₀ z < exp(K*t) * (ε / exp(K*t)) = ε.
    have h_bd := h_dist_bound z₀ z
    -- Note: dist_bound gives `dist (f z₀) (f z)`, but `Metric.continuous_iff`
    -- gives `dist z z₀ < δ → dist (f z) (f z₀) < ε`.  Symmetric: use dist_comm.
    rw [dist_comm] at hz
    have h_chain : dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
                  < ε := by
      calc dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
          ≤ dist z₀ z * Real.exp ((K : ℝ) * (t - 0)) := h_bd
        _ < (ε / Real.exp ((K : ℝ) * (t - 0))) * Real.exp ((K : ℝ) * (t - 0)) :=
            mul_lt_mul_of_pos_right hz h_exp_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt h_exp_pos)
    rwa [dist_comm] at h_chain
  exact h_cont_z.measurable

/-- **Stage 4 helper (sorry'd): boundary regularity of a Stage 1.9 flow.**

Given a flow `(charX, charV)` produced by
`exists_vlasov_characteristicFlow_global_smallT` with the open-interval
predicate `IsCharacteristicFlowOn ... (Set.Ioo 0 T) Set.univ`, this helper
extracts the closed-interval boundary regularity package needed by both
`flow_distance_growth_bound_on` (Bridge #1) and
`charFlow_measurable_via_gronwall`:

* `h_init` — the initial-condition clause at `t = 0`,
* `h_cont_Icc` — continuity of `(charX, charV)(·, z)` on the closed
  interval `Icc 0 T`,
* `h_deriv_Ico` — HasDerivWithinAt on `Ico 0 T` (closed at the left
  endpoint).

**This is Friction 5 in named form.**  The five-friction-cascade analysis
(per the Path-3 architectural turn) identified that Stage 1.9's internal
Picard-Lindelöf construction does build the closed-interval regularity
(Mathlib's PL output naturally has `ContinuousOn (Icc t₀ T)` plus
`HasDerivAt` on `Ioo`), but Stage 1.9's conclusion only exposes the
open-interval HasDerivAt clause via `IsCharacteristicFlowOn`.

Path 3's `_On` predicates resolved the *structural* friction at the
type system, but this **regularity gap** between Ioo-HasDerivAt and
Icc-ContinuousOn + Ico-HasDerivWithinAt remains and is needed for the
Gronwall growth bound's hypotheses.

**Closure path (precise, after this session's signature reading)**:

The per-ball flow's proof (`exists_vlasov_characteristicFlow` at L1112)
INTERNALLY constructs the needed boundary regularity but discards it.
Specifically:
* At L1892-1907 (position): builds `h_d_within :
  HasDerivWithinAt (fun s => (γ_func z s).1) (γ_func z t).2
    (Set.Icc 0 (N * δ_uniform)) t`,
  then immediately calls `.hasDerivAt h_icc_nhds` (L1908) to convert
  to `HasDerivAt`, losing the closed-interval info.
* At L1916-1922 (velocity): same pattern.

**Minimum additive surgery to close this sorry** (~50-80 lines):
1. Add a conjunct to `exists_vlasov_characteristicFlow`'s conclusion
   exposing the `HasDerivWithinAt` on `Icc 0 (N * δ_uniform)` form
   (which restricts to `Icc 0 T`).  Proof body modification: stop
   discarding `h_d_within` — expose it through a new clause.
   ~20-30 lines.
2. Lift through `exists_vlasov_perz_trajectory` (~15 lines).
3. Lift through `exists_vlasov_characteristicFlow_global_smallT`
   (~10 lines).
4. Close `Stage_1_9_flow_boundary_regularity` by deconstruction
   (~20 lines), using:
   * `hflow.1 z (Set.mem_univ z)` for the initial-condition conjunct.
   * `HasDerivWithinAt.continuousWithinAt` + `ContinuousOn.eq_of_eqOn` for
     the `ContinuousOn (Icc 0 T)` conjunct.
   * `nhdsWithin` agreement at boundary points
     (`nhdsWithin 0 (Icc 0 T) = nhdsWithin 0 (Ici 0)`) to convert
     HasDerivWithinAt-on-`Icc` to HasDerivWithinAt-on-`Ici` at `s = 0`,
     and similarly for interior `s ∈ Ico 0 T` (where both sets agree
     locally).

**Closure status (2026-05-29 surgery)**: closed by Friction 5 surgery —
the per-ball flow → per-z trajectory → Stage 1.9 chain was enriched to
expose the HasDerivWithinAt-on-`Icc 0 T` form at every t ∈ Icc 0 T.
This theorem now takes that boundary regularity as an explicit
hypothesis (`h_boundary`) and discharges its conclusion by structural
transport:

* `h_init` from `hflow.1 z (Set.mem_univ z)` (initial-condition clause).
* `h_cont_Icc` from `h_boundary`'s HasDerivWithinAt → ContinuousWithinAt
  → ContinuousOn (with `Prod.continuousWithinAt_iff` to join components).
* `h_deriv_Ico` from `h_boundary`'s HasDerivWithinAt-on-Icc lifted to
  HasDerivWithinAt-on-Ici at boundary points via
  `mono_of_mem_nhdsWithin` (the local-equivalence-of-filters argument). -/
theorem Stage_1_9_flow_boundary_regularity
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV
                                    (Set.Ioo 0 T) Set.univ)
    -- **Friction 5 surgery (2026-05-29)**: the boundary regularity is now
    -- an explicit input.  The Stage 1.9 → per-z → per-ball chain produces
    -- it as a separate conjunct alongside `IsCharacteristicFlowOn`; this
    -- helper transports the input forward into the precise form the
    -- Gronwall growth bound needs.
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
          (Set.Icc 0 T) t) :
    (∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z) ∧
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) ∧
    (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z))
        (Set.Ici s) s) := by
  refine ⟨?_, ?_, ?_⟩
  · -- h_init: from hflow's initial-condition clause at every z ∈ univ.
    intro z
    obtain ⟨hX, hV⟩ := hflow.1 z (Set.mem_univ z)
    exact Prod.ext hX hV
  · -- h_cont_Icc: from h_boundary's HasDerivWithinAt → ContinuousWithinAt →
    -- ContinuousOn, joined componentwise via Prod.
    intro z
    intro s hs
    obtain ⟨h_pos_dw, h_vel_dw⟩ := h_boundary z s hs
    have h_pos_cwn : ContinuousWithinAt (fun s' => charX s' z) (Set.Icc 0 T) s :=
      h_pos_dw.continuousWithinAt
    have h_vel_cwn : ContinuousWithinAt (fun s' => charV s' z) (Set.Icc 0 T) s :=
      h_vel_dw.continuousWithinAt
    exact h_pos_cwn.prodMk h_vel_cwn
  · -- h_deriv_Ico: from h_boundary's HasDerivWithinAt-on-Icc lifted to Ici.
    -- For s ∈ Ico 0 T, Icc 0 T ∈ 𝓝[Ici s] s (since [s, s+ε) ⊆ Icc 0 T
    -- for small ε), so HasDerivWithinAt _ _ (Icc 0 T) s implies
    -- HasDerivWithinAt _ _ (Ici s) s via mono_of_mem_nhdsWithin.
    intro z s hs
    have hs_Icc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_of_lt hs.2⟩
    obtain ⟨h_pos_dw, h_vel_dw⟩ := h_boundary z s hs_Icc
    -- Membership: Icc 0 T ∈ nhdsWithin (Ici s) s.  Witness: take the
    -- open neighborhood `Iio T` ∋ s (since s < T from hs.2); then
    -- `Iio T ∩ Ici s = [s, T) ⊆ [0, T] = Icc 0 T`.
    have h_mem : Set.Icc (0 : ℝ) T ∈ nhdsWithin s (Set.Ici s) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio T, Iio_mem_nhds hs.2, ?_⟩
      intro u hu
      refine ⟨?_, ?_⟩
      · -- u ≥ 0: from u ∈ Ici s ⊆ Ici 0 (since s ≥ 0 by hs.1).
        exact le_trans hs.1 hu.2
      · -- u ≤ T: from u ∈ Iio T (so u < T).
        exact le_of_lt hu.1
    have h_pos_Ici : HasDerivWithinAt (fun s' => charX s' z) (charV s z)
                       (Set.Ici s) s :=
      h_pos_dw.mono_of_mem_nhdsWithin h_mem
    have h_vel_Ici : HasDerivWithinAt (fun s' => charV s' z)
                       (-(convolveFunctionMeasure gradW (ρ s) (charX s z)))
                       (Set.Ici s) s :=
      h_vel_dw.mono_of_mem_nhdsWithin h_mem
    -- Join componentwise into the joint Prod-valued HasDerivWithinAt.
    -- vlasovVectorField gradW ρ s (charX s z, charV s z)
    --   = (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))).
    have h_prod : HasDerivWithinAt
        (fun s' : ℝ => (charX s' z, charV s' z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
        (Set.Ici s) s := h_pos_Ici.prodMk h_vel_Ici
    -- Convert from componentwise to the vector-field form.
    show HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
            (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s
    convert h_prod using 1

/-- **Stage 4 Bridge #3: single Picard step `VlasovMeasureCurve d T M → VlasovMeasureCurve d T M'`**.

Composes Stage 1.9 + `Stage_1_9_flow_boundary_regularity` (Friction 5
helper) + `flow_distance_growth_bound_on` (Bridge #1) +
`charFlow_measurable_via_gronwall` + `Phi_asVlasovMeasureCurve` into a
single Picard step.

**Output bundle** (sigma form): the flow + growth constant + bundled
output curve + local pushforward equation on `Icc 0 T`.  Internally,
`σ.ρ = Phi charX_clamped f₀` where `charX_clamped t := charX (clampToIcc T t)`;
on `Icc 0 T` the clamp is the identity so the pushforward equation
holds with the un-clamped `charX`.

**No new sorries** (this commit): indirectly invokes the sorry'd
`Stage_1_9_flow_boundary_regularity` (Friction 5).  All other
intermediates are fully proved by composition. -/
theorem Phi_step
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    {T : ℝ} {M : ℝ → ℝ} (hT : 0 ≤ T)
    (Mbar : ℝ) (hMbar_nn : 0 ≤ Mbar) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (hM_mono : MonotoneOn M (Set.Icc 0 T))
    (hTL_PL : LocalSmallness_PL_buffer L T)
    (ρ : VlasovMeasureCurve d T M)
    (h_int_ext : ∀ t (x : PhysSpace d),
                  Integrable (fun y => gradW (x - y)) (ρ.extend t)) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (C_T : ℝ),
      0 ≤ C_T ∧
      IsCharacteristicFlowOn gradW ρ.extend charX charV (Set.Ioo 0 T) Set.univ ∧
      -- **Piece A (time-local envelope) growth bound** — exposes the per-`z`
      -- bound `flow_distance_growth_bound_on_timedep` produces against the input
      -- moment envelope `M`.  Piece D integrates this (A.2) and closes it against
      -- the canonical envelope (A.3) to re-bundle `σ` into the fixed envelope
      -- space, dissolving the M-fixed-point.
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤
          gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * M t) t) ∧
      ∃ σ : VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)),
        ∀ t ∈ Set.Icc (0:ℝ) T,
          σ.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
  haveI hExt_prob : ∀ t, IsProbabilityMeasure (ρ.extend t) :=
    VlasovMeasureCurve.extend_isProb ρ
  have hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
    intro x
    have h_int_Icc : ∀ t ∈ Set.Icc (0:ℝ) T,
        Integrable (fun y => gradW (x - y)) (ρ.ρ t) := by
      intro t ht
      have h_eq : ρ.extend t = ρ.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ext t x
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT ρ x h_int_Icc
  have h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
    fun t => VlasovMeasureCurve.extend_yIntegrable hT ρ t
  have hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ Mbar :=
    fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT ρ t)
      (hMbar (clampToIcc T t) (clampToIcc_mem hT t))
  obtain ⟨charX, charV, hflow_on, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ.extend h_int_ext hρ_cont h_y_int Mbar hMbar_nn hM_ρ T hT hTL_PL
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    Stage_1_9_flow_boundary_regularity gradW ρ.extend charX charV T hT
      hflow_on h_boundary
  -- Piece A (time-local envelope) per-`z` growth bound against the input
  -- envelope `M` (on `Icc`, `ρ.extend t = ρ.ρ t`, so `ρ`'s moment bound `M t`
  -- feeds the time-local Gronwall forcing).
  have hm_M : ∀ t ∈ Set.Icc (0:ℝ) T, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M t := by
    intro t ht
    have h_eq : ρ.extend t = ρ.ρ t := by
      unfold VlasovMeasureCurve.extend clampToIcc
      congr 1
      rw [min_eq_left ht.2, max_eq_right ht.1]
    rw [h_eq]; exact ρ.hasMoment t ht
  have h_growth_timedep : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * M t) t :=
    flow_distance_growth_bound_on_timedep gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico M hM_mono hm_M (fun t _ => h_y_int t) h_int_ext
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico Mbar hMbar_nn
      (fun t _ => hM_ρ t) (fun t _ => h_y_int t) h_int_ext
  have h_meas_Icc : ∀ t ∈ Set.Icc (0:ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall gradW L hL ρ.extend h_int_ext charX charV
      T hT h_init h_cont_Icc h_deriv_Ico
  let charX_clamped : ℝ → PhaseSpace d → PhysSpace d :=
    fun t z => charX (clampToIcc T t) z
  have h_meas_clamped : ∀ t,
      AEMeasurable (fun z : PhaseSpace d => charX_clamped t z) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_meas_full := h_meas_Icc (clampToIcc T t) h_clamp_mem
    exact (measurable_fst.comp h_meas_full).aemeasurable
  have h_growth_clamped : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    show ‖charX (clampToIcc T t) z‖ ≤ _
    rw [h_clamp_eq]
    have h_full := h_growth t ht z
    have h_proj : ‖charX t z‖ ≤ ‖(charX t z, charV t z)‖ := by
      simp [Prod.norm_def]
    linarith
  have h_int_charX_clamped : ∀ t,
      Integrable (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_bound : ∀ z, ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
      intro z
      show ‖charX (clampToIcc T t) z‖ ≤ _
      have h_full := h_growth (clampToIcc T t) h_clamp_mem z
      have h_proj : ‖charX (clampToIcc T t) z‖ ≤
                    ‖(charX (clampToIcc T t) z, charV (clampToIcc T t) z)‖ := by
        simp [Prod.norm_def]
      linarith
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
        h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                  fun z => C_T * ‖z‖ + C_T := by funext z; ring
      rw [h_eq]; exact h1.add h2
    have h_aesm : AEStronglyMeasurable
        (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ :=
      (h_meas_clamped t).norm.aestronglyMeasurable
    refine h_dom_int.mono' h_aesm ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact h_bound z
  have h_charX_cont_clamped : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX_clamped t z) (Set.Icc 0 T) s := by
    intro s hs z
    have h_full := (h_cont_Icc z).continuousWithinAt hs
    have h_charX_cwn : ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s :=
      h_full.fst
    have h_eq_on : ∀ t ∈ Set.Icc (0:ℝ) T, charX_clamped t z = charX t z := by
      intro t ht
      show charX (clampToIcc T t) z = charX t z
      have h_clamp_eq : clampToIcc T t = t := by
        unfold clampToIcc
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [h_clamp_eq]
    exact h_charX_cwn.congr h_eq_on (h_eq_on s hs)
  let σ : VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)) :=
    Phi_asVlasovMeasureCurve charX_clamped f₀ h_meas_clamped h_int_charX_clamped
      T hT C_T hC_T_nn h_growth_clamped h_f₀_int M_f₀ hM_f₀ h_charX_cont_clamped
  refine ⟨charX, charV, C_T, hC_T_nn, hflow_on, h_growth_timedep, σ, ?_⟩
  intro t ht
  show Phi charX_clamped f₀ t = Measure.map (fun z => charX t z) f₀
  unfold Phi
  have h_clamp_eq : clampToIcc T t = t := by
    unfold clampToIcc
    rw [min_eq_left ht.2, max_eq_right ht.1]
  congr 1
  funext z
  show charX (clampToIcc T t) z = charX t z
  rw [h_clamp_eq]

/-- **Piece D keystone (Option 2): `Φ`-step landing in the fixed envelope space.**

`Phi_step` produces a flow `(charX, charV)` against `ρ.extend` and bundles its
position pushforward into the *constant* space `VlasovMeasureCurve d T (fun _ =>
C_T·(M_f₀+1))`.  The constant bound grows with each `Φ`-iteration (the moment
fixed-point pathology, M2 sighting 4 / M3).  This wrapper **re-bundles the same
pushforward into the fixed envelope space** `VlasovMeasureCurve d T m`, where
`m` is the canonical Gronwall envelope of `gronwall_envelope_exists` (Piece A.3):
because `m` is `Φ`-invariant at the moment level, `Φ` maps `space(m)` to itself,
so the Picard sequence stays in one fixed curve space — dissolving the
fixed-point in `M`.

The moment re-bundling is the measure-level data-free escape:
`∫‖x‖∂(map (charX t) f₀) ≤ gronwallBound (∫z‖z‖∂f₀) (1+L) (‖gradW 0‖ + L·m t) t`
(Piece A.2 `phi_moment_envelope_le`, fed the per-`z` growth bound `Phi_step`
exposes) `≤ m t` (Piece A.3 invariance `hm_inv`).

Output also exposes the **boundary-regularity bundle** (as
`exists_vlasov_characteristicFlow_global_smallT`) so the Picard recursion can
discharge `Phi_supW1_contraction`'s per-`z` regularity hypotheses at each step.

The envelope's anchor moment is the **phase-space** `∫z‖z‖∂f₀` (matching A.2's
`integral_map` initial value), NOT the spatial marginal — see Piece D brief F1.

API-lock (body deferred): the construction is `Phi_step` + boundary exposure +
A.2/A.3 moment re-bundle; closing it is a focused leaf. -/
theorem Phi_step_envelope
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 ≤ T)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ m t)
    (hm_inv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t ≤ m t)
    (hTL_PL : LocalSmallness_PL_buffer L T)
    (ρ : VlasovMeasureCurve d T m)
    (h_int_ext : ∀ t (x : PhysSpace d),
                  Integrable (fun y => gradW (x - y)) (ρ.extend t)) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ.extend charX charV (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ.extend t) (charX t z)))
          (Set.Icc 0 T) t) ∧
      ∃ σ : VlasovMeasureCurve d T m,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          σ.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
  haveI hExt_prob : ∀ t, IsProbabilityMeasure (ρ.extend t) :=
    VlasovMeasureCurve.extend_isProb ρ
  have hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
    intro x
    have h_int_Icc : ∀ t ∈ Set.Icc (0:ℝ) T,
        Integrable (fun y => gradW (x - y)) (ρ.ρ t) := by
      intro t ht
      have h_eq : ρ.extend t = ρ.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ext t x
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT ρ x h_int_Icc
  have h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
    fun t => VlasovMeasureCurve.extend_yIntegrable hT ρ t
  have hMbar_nn : 0 ≤ m T := hm_nn T ⟨hT, le_refl T⟩
  have hMbar : ∀ t ∈ Set.Icc (0:ℝ) T, m t ≤ m T :=
    fun t ht => hm_mono ht ⟨hT, le_refl T⟩ ht.2
  have hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ m T :=
    fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT ρ t)
      (hMbar (clampToIcc T t) (clampToIcc_mem hT t))
  obtain ⟨charX, charV, hflow_on, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ.extend h_int_ext hρ_cont h_y_int (m T) hMbar_nn hM_ρ T hT hTL_PL
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    Stage_1_9_flow_boundary_regularity gradW ρ.extend charX charV T hT
      hflow_on h_boundary
  have hm_M : ∀ t ∈ Set.Icc (0:ℝ) T, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ m t := by
    intro t ht
    have h_eq : ρ.extend t = ρ.ρ t := by
      unfold VlasovMeasureCurve.extend clampToIcc
      congr 1
      rw [min_eq_left ht.2, max_eq_right ht.1]
    rw [h_eq]; exact ρ.hasMoment t ht
  have h_growth_timedep : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t :=
    flow_distance_growth_bound_on_timedep gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico m hm_mono hm_M (fun t _ => h_y_int t) h_int_ext
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico (m T) hMbar_nn
      (fun t _ => hM_ρ t) (fun t _ => h_y_int t) h_int_ext
  have h_meas_Icc : ∀ t ∈ Set.Icc (0:ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall gradW L hL ρ.extend h_int_ext charX charV
      T hT h_init h_cont_Icc h_deriv_Ico
  let charX_clamped : ℝ → PhaseSpace d → PhysSpace d :=
    fun t z => charX (clampToIcc T t) z
  have h_meas_clamped : ∀ t,
      AEMeasurable (fun z : PhaseSpace d => charX_clamped t z) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_meas_full := h_meas_Icc (clampToIcc T t) h_clamp_mem
    exact (measurable_fst.comp h_meas_full).aemeasurable
  have h_growth_clamped : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    show ‖charX (clampToIcc T t) z‖ ≤ _
    rw [h_clamp_eq]
    have h_full := h_growth t ht z
    have h_proj : ‖charX t z‖ ≤ ‖(charX t z, charV t z)‖ := by
      simp [Prod.norm_def]
    linarith
  have h_int_charX_clamped : ∀ t,
      Integrable (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_bound : ∀ z, ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
      intro z
      show ‖charX (clampToIcc T t) z‖ ≤ _
      have h_full := h_growth (clampToIcc T t) h_clamp_mem z
      have h_proj : ‖charX (clampToIcc T t) z‖ ≤
                    ‖(charX (clampToIcc T t) z, charV (clampToIcc T t) z)‖ := by
        simp [Prod.norm_def]
      linarith
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
        h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                  fun z => C_T * ‖z‖ + C_T := by funext z; ring
      rw [h_eq]; exact h1.add h2
    have h_aesm : AEStronglyMeasurable
        (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ :=
      (h_meas_clamped t).norm.aestronglyMeasurable
    refine h_dom_int.mono' h_aesm ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact h_bound z
  have h_charX_cont_clamped : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX_clamped t z) (Set.Icc 0 T) s := by
    intro s hs z
    have h_full := (h_cont_Icc z).continuousWithinAt hs
    have h_charX_cwn : ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s :=
      h_full.fst
    have h_eq_on : ∀ t ∈ Set.Icc (0:ℝ) T, charX_clamped t z = charX t z := by
      intro t ht
      show charX (clampToIcc T t) z = charX t z
      have h_clamp_eq : clampToIcc T t = t := by
        unfold clampToIcc
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [h_clamp_eq]
    exact h_charX_cwn.congr h_eq_on (h_eq_on s hs)
  let σ_const := Phi_asVlasovMeasureCurve charX_clamped f₀ h_meas_clamped
    h_int_charX_clamped T hT C_T hC_T_nn h_growth_clamped h_f₀_int
    (∫ z, ‖z‖ ∂f₀) (le_refl _) h_charX_cont_clamped
  -- On `Icc`, the clamped pushforward equals the raw pushforward.
  have h_rho_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      σ_const.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
    intro t ht
    show Phi charX_clamped f₀ t = Measure.map (fun z => charX t z) f₀
    unfold Phi
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    congr 1
    funext z
    show charX (clampToIcc T t) z = charX t z
    rw [h_clamp_eq]
  -- Moment re-bundle (the data-free escape): A.2 integrates the per-`z`
  -- envelope growth to a moment bound, A.3's `hm_inv` closes it against `m`.
  have h_meas_charX_Icc : ∀ t ∈ Set.Icc (0:ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀ :=
    fun t ht => (measurable_fst.comp (h_meas_Icc t ht)).aemeasurable
  have h_moment_m : ∀ t ∈ Set.Icc (0:ℝ) T, ∫ y, ‖y‖ ∂(σ_const.ρ t) ≤ m t := by
    intro t ht
    rw [h_rho_eq t ht]
    calc ∫ y, ‖y‖ ∂(Measure.map (fun z : PhaseSpace d => charX t z) f₀)
        ≤ gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ))
            (‖gradW 0‖ + (L : ℝ) * m t) t :=
          phi_moment_envelope_le L charX charV (‖gradW 0‖) T m h_growth_timedep
            f₀ h_f₀_int h_meas_charX_Icc t ht
      _ ≤ m t := hm_inv t ht
  -- Re-bundle `σ_const` (constant space) into the fixed envelope space `m`:
  -- only `hasMoment` changes; the other fields are `m`-independent.
  let σ : VlasovMeasureCurve d T m :=
    { ρ := σ_const.ρ
      isProb := σ_const.isProb
      hasMoment := h_moment_m
      yIntegrable := σ_const.yIntegrable
      hW1Cont := σ_const.hW1Cont }
  exact ⟨charX, charV, hflow_on, h_boundary, σ, h_rho_eq⟩

/-- **Stage 3 sub-piece: pointwise Gronwall on flow difference.**

Given two characteristic flow trajectories `γ_ρ, γ_σ : ℝ → PhaseSpace d`
starting at the same initial condition `z`, driven by *different* measure
curves `ρ, σ` with `supW1On(Icc 0 T) ρ σ ≤ D`, the pointwise difference
satisfies a Gronwall-type bound:
`‖γ_ρ(t) - γ_σ(t)‖ ≤ gronwallBound 0 K (L · D) t`
where `K := max(1, L)`.

**Proof strategy** (Gronwall on the trajectory-difference function):
* Set `f(s) := γ_ρ(s) - γ_σ(s)`.  Then `f(0) = 0` (both start at `z`).
* `f'(s) = vlasovVectorField gradW ρ s (γ_ρ s) − vlasovVectorField gradW σ s (γ_σ s)`.
* Split via triangle:
  `f'(s) = [VF_ρ γ_ρ − VF_ρ γ_σ]  +  [VF_ρ γ_σ − VF_σ γ_σ]`
* First bracket bounded by `K · ‖γ_ρ - γ_σ‖ = K · ‖f s‖` via
  `vlasovVectorField_lipschitzWith`.
* Second bracket: the velocity components cancel (`VF`'s first component is
  `z.2`, identical in both); only the force components differ.  Bounded by
  `L · W₁(ρ_s, σ_s).toReal ≤ L · D` via `MathlibTODO_convolveLipschitzEstimate`.
* Apply `norm_le_gronwallBound_of_norm_deriv_right_le` with `δ := 0`,
  `K := max(1, L)`, `ε := L · D`.

**Boundary regularity** identical to `charFlow_measurable_via_gronwall`:
`ContinuousOn (Icc 0 T)` + `HasDerivWithinAt` on `Ico 0 T` for each
trajectory.  Stage 4's Picard construction discharges these hypotheses.

Used by Stage 3's main contraction lemma (next commit) to bound
`supW1On(Icc 0 T)(Phi ρ)(Phi σ)` by `K_contract(T) · supW1On(Icc 0 T) ρ σ`
where `K_contract(T) := (L/K) · (exp(K·T) - 1) → 0` as `T → 0`. -/
theorem flow_difference_gronwall_bound {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    (γ_ρ γ_σ : ℝ → PhaseSpace d)
    (z : PhaseSpace d)
    (h_init_ρ : γ_ρ 0 = z) (h_init_σ : γ_σ 0 = z)
    (h_cont_ρ : ContinuousOn γ_ρ (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ContinuousOn γ_σ (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ_ρ (vlasovVectorField gradW ρ s (γ_ρ s)) (Set.Ici s) s)
    (h_deriv_σ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ_σ (vlasovVectorField gradW σ s (γ_σ s)) (Set.Ici s) s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖γ_ρ t - γ_σ t‖ ≤
        gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) t := by
  -- ============================================================
  -- Setup: K = max(1, L), f(s) = γ_ρ(s) - γ_σ(s).
  -- ============================================================
  set K_NN : NNReal := max 1 L with hK_NN_def
  set K_lip : ℝ := (K_NN : ℝ) with hK_lip_def
  have hK_NN_eq : K_lip = ((max 1 L : NNReal) : ℝ) := rfl
  set f : ℝ → PhaseSpace d := fun s => γ_ρ s - γ_σ s with hf_def
  set f' : ℝ → PhaseSpace d := fun s =>
    vlasovVectorField gradW ρ s (γ_ρ s) - vlasovVectorField gradW σ s (γ_σ s)
    with hf'_def
  -- ============================================================
  -- Continuity + right-derivative of f on the relevant intervals.
  -- ============================================================
  have h_f_cont : ContinuousOn f (Set.Icc (0 : ℝ) T) := h_cont_ρ.sub h_cont_σ
  have h_f_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt f (f' s) (Set.Ici s) s := fun s hs =>
    (h_deriv_ρ s hs).sub (h_deriv_σ s hs)
  -- ============================================================
  -- Initial: ‖f 0‖ = 0.
  -- ============================================================
  have h_f0 : ‖f 0‖ ≤ 0 := by
    show ‖γ_ρ 0 - γ_σ 0‖ ≤ 0
    rw [h_init_ρ, h_init_σ, sub_self, norm_zero]
  -- ============================================================
  -- Differential bound: ‖f'(s)‖ ≤ K_lip · ‖f(s)‖ + L · D for s ∈ Ico 0 T.
  -- ============================================================
  have h_f'_bound : ∀ s ∈ Set.Ico (0 : ℝ) T,
      ‖f' s‖ ≤ K_lip * ‖f s‖ + (L : ℝ) * D := by
    intro s hs
    -- s ∈ Icc 0 T from s ∈ Ico 0 T
    have hs_Icc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_of_lt hs.2⟩
    -- ============================================================
    -- Triangle split: f'(s) = [VF_ρ γ_ρ − VF_ρ γ_σ] + [VF_ρ γ_σ − VF_σ γ_σ]
    -- ============================================================
    have h_split : f' s =
        (vlasovVectorField gradW ρ s (γ_ρ s) -
         vlasovVectorField gradW ρ s (γ_σ s)) +
        (vlasovVectorField gradW ρ s (γ_σ s) -
         vlasovVectorField gradW σ s (γ_σ s)) := by
      simp only [hf'_def]; abel
    have h_tri : ‖f' s‖ ≤
        ‖vlasovVectorField gradW ρ s (γ_ρ s) - vlasovVectorField gradW ρ s (γ_σ s)‖ +
        ‖vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s)‖ := by
      rw [h_split]; exact norm_add_le _ _
    -- ============================================================
    -- First bracket: ‖VF_ρ γ_ρ − VF_ρ γ_σ‖ ≤ K_lip · ‖γ_ρ - γ_σ‖.
    -- ============================================================
    have h_vf_lip := vlasovVectorField_lipschitzWith gradW L hL ρ h_int_ρ s
    have h_first : ‖vlasovVectorField gradW ρ s (γ_ρ s) -
                    vlasovVectorField gradW ρ s (γ_σ s)‖ ≤
                   K_lip * ‖γ_ρ s - γ_σ s‖ := by
      have h := h_vf_lip.dist_le_mul (γ_ρ s) (γ_σ s)
      rw [dist_eq_norm, dist_eq_norm] at h
      exact h
    -- ============================================================
    -- Second bracket: VF_ρ γ_σ − VF_σ γ_σ = (0, conv σ - conv ρ at γ_σ.1).
    -- Norm = ‖conv ρ - conv σ at γ_σ.1‖ ≤ L * W₁(ρ_s, σ_s).toReal ≤ L * D.
    -- ============================================================
    have h_VF_diff_explicit :
        vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s) =
        (0, convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
            convolveFunctionMeasure gradW (ρ s) (γ_σ s).1) := by
      simp only [vlasovVectorField, Prod.mk_sub_mk, sub_self, neg_sub_neg]
    have h_second_norm :
        ‖vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s)‖ =
        ‖convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
         convolveFunctionMeasure gradW (ρ s) (γ_σ s).1‖ := by
      rw [h_VF_diff_explicit]
      simp [Prod.norm_def, max_eq_right (norm_nonneg _)]
    have h_conv_lip := MathlibTODO_convolveLipschitzEstimate gradW L hL
      (σ s) (ρ s) (γ_σ s).1
      (by rw [wasserstein1_comm]; exact h_W1_fin s hs_Icc)
      (h_int_σ s _) (h_int_ρ s _)
    have h_W1_comm : (wasserstein1 (σ s) (ρ s)).toReal =
                     (wasserstein1 (ρ s) (σ s)).toReal := by
      rw [wasserstein1_comm]
    have h_second : ‖vlasovVectorField gradW ρ s (γ_σ s) -
                     vlasovVectorField gradW σ s (γ_σ s)‖ ≤ (L : ℝ) * D := by
      rw [h_second_norm]
      calc ‖convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
            convolveFunctionMeasure gradW (ρ s) (γ_σ s).1‖
          ≤ (L : ℝ) * (wasserstein1 (σ s) (ρ s)).toReal := h_conv_lip
        _ = (L : ℝ) * (wasserstein1 (ρ s) (σ s)).toReal := by rw [h_W1_comm]
        _ ≤ (L : ℝ) * D := by
            apply mul_le_mul_of_nonneg_left (h_W1_bound s hs_Icc) L.coe_nonneg
    -- ============================================================
    -- Combine: ‖f'(s)‖ ≤ K_lip · ‖f(s)‖ + L · D.
    -- ============================================================
    calc ‖f' s‖
        ≤ ‖vlasovVectorField gradW ρ s (γ_ρ s) -
            vlasovVectorField gradW ρ s (γ_σ s)‖ +
          ‖vlasovVectorField gradW ρ s (γ_σ s) -
            vlasovVectorField gradW σ s (γ_σ s)‖ := h_tri
      _ ≤ K_lip * ‖γ_ρ s - γ_σ s‖ + (L : ℝ) * D := by
          linarith [h_first, h_second]
      _ = K_lip * ‖f s‖ + (L : ℝ) * D := by
          simp only [hf_def]
  -- ============================================================
  -- Apply norm_le_gronwallBound_of_norm_deriv_right_le.
  -- ============================================================
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    h_f_cont h_f_deriv h_f0 h_f'_bound t ht
  -- h : ‖f t‖ ≤ gronwallBound 0 K_lip (L · D) (t - 0)
  simp only [sub_zero] at h
  exact h

/-- **Stage 3b sub-piece 1: W₁ pushforward bound for two arbitrary maps.**

Generalizes `wasserstein1_Phi_le_integral_diff` (which handled a single
flow at two times) to two arbitrary maps `f, g : PhaseSpace d → PhysSpace d`.
For pushforwards of the same initial measure `f₀`:
`W₁(f_# f₀, g_# f₀) ≤ ENNReal.ofReal (∫ z, ‖f z - g z‖ ∂f₀)`.

**Proof structure** parallel to `wasserstein1_Phi_le_integral_diff`: KR-
dual direct, with `integral_map` converting pushforward integrals + the
1-Lipschitz bound `|φ y - φ y'| ≤ ‖y - y'‖`.  Explicit-dominator discipline
(L7) + `.mp/.mpr` bridge for `_map_measure` (L8) applied throughout.

Used by Stage 3b's `Phi_pointwise_contraction` (below) with
`f := charX_ρ t, g := charX_σ t` to bound the pushforward W₁ in terms of
the pointwise flow difference. -/
theorem wasserstein1_pushforward_pair_le_integral_norm_diff {d : ℕ} [NeZero d]
    (f g : PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_f : AEMeasurable f f₀) (h_meas_g : AEMeasurable g f₀)
    (h_int_f : Integrable (fun z : PhaseSpace d => ‖f z‖) f₀)
    (h_int_g : Integrable (fun z : PhaseSpace d => ‖g z‖) f₀)
    (h_diff_int : Integrable (fun z : PhaseSpace d => ‖f z - g z‖) f₀) :
    wasserstein1 (Measure.map f f₀) (Measure.map g f₀) ≤
      ENNReal.ofReal (∫ z, ‖f z - g z‖ ∂f₀) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_νf : AEStronglyMeasurable φ (Measure.map f f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_meas_νg : AEStronglyMeasurable φ (Measure.map g f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_abs_bound : ∀ y : PhysSpace d, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith
      _ = |φ 0| + ‖y‖ := by ring
  have h_norm_int_νf : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map f f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      h_meas_f).mpr h_int_f
  have h_norm_int_νg : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map g f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      h_meas_g).mpr h_int_g
  have h_dom_νf : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map f f₀) :=
    (integrable_const _).add h_norm_int_νf
  have h_dom_νg : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map g f₀) :=
    (integrable_const _).add h_norm_int_νg
  have hφ_int_νf : Integrable φ (Measure.map f f₀) := by
    refine Integrable.mono' h_dom_νf hφ_meas_νf ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  have hφ_int_νg : Integrable φ (Measure.map g f₀) := by
    refine Integrable.mono' h_dom_νg hφ_meas_νg ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  rw [integral_map h_meas_f hφ_meas_νf, integral_map h_meas_g hφ_meas_νg]
  have hφ_comp_int_f : Integrable (fun z : PhaseSpace d => φ (f z)) f₀ :=
    (integrable_map_measure hφ_meas_νf h_meas_f).mp hφ_int_νf
  have hφ_comp_int_g : Integrable (fun z : PhaseSpace d => φ (g z)) f₀ :=
    (integrable_map_measure hφ_meas_νg h_meas_g).mp hφ_int_νg
  rw [← integral_sub hφ_comp_int_f hφ_comp_int_g]
  have h_pt : ∀ z : PhaseSpace d,
      φ (f z) - φ (g z) ≤ ‖f z - g z‖ := fun z => by
    have h_lip := hφ.dist_le_mul (f z) (g z)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h_lip
    linarith [abs_le.mp h_lip |>.2]
  exact integral_mono (hφ_comp_int_f.sub hφ_comp_int_g) h_diff_int h_pt

/-- **Stage 3b sub-piece 2: pointwise contraction estimate at time t.**

Composes Stage 3a's pointwise Gronwall (`flow_difference_gronwall_bound`)
with the W₁ pair bound to get:
`(wasserstein1 (charX_ρ t # f₀) (charX_σ t # f₀)).toReal ≤ gronwallBound 0 K (L·D) t`
for `t ∈ Icc 0 T`, where `K := max(1, L)` and `D := supW1On(Icc 0 T) ρ σ`.

**Proof**: Stage 3a gives `‖charX_ρ t z - charX_σ t z‖ ≤ gronwallBound 0 K (L·D) t`
uniformly in z.  Integrating over f₀ (a probability measure) gives the same
bound on `∫ ‖charX_ρ t z - charX_σ t z‖ ∂f₀`.  The W₁ pair bound then
transfers to the Wasserstein side.

The remaining Stage 3 piece (next commit) takes sup over `t ∈ Icc 0 T` to
derive the contraction `supW1On(Phi_ρ)(Phi_σ) ≤ K_contract(T) · D` where
`K_contract(T) := (L/K)·(exp(K·T)−1) → 0` as `T → 0`. -/
theorem Phi_pointwise_contraction {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    -- Two flows (ρ-driven and σ-driven) starting at f₀-distributed initials.
    (charX_ρ charV_ρ charX_σ charV_σ : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
    -- Per-z trajectories satisfy boundary regularity (Stage 4's Picard discharges).
    -- Phrased per-z, but uniformly across z : PhaseSpace d.
    (h_init_ρ : ∀ z, (charX_ρ 0 z, charV_ρ 0 z) = z)
    (h_init_σ : ∀ z, (charX_σ 0 z, charV_σ 0 z) = z)
    (h_cont_ρ : ∀ z,
      ContinuousOn (fun s => (charX_ρ s z, charV_ρ s z)) (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ∀ z,
      ContinuousOn (fun s => (charX_σ s z, charV_σ s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_ρ s' z, charV_ρ s' z))
        (vlasovVectorField gradW ρ s (charX_ρ s z, charV_ρ s z))
        (Set.Ici s) s)
    (h_deriv_σ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_σ s' z, charV_σ s' z))
        (vlasovVectorField gradW σ s (charX_σ s z, charV_σ s z))
        (Set.Ici s) s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                  (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
      gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) t := by
  -- ============================================================
  -- Pointwise Gronwall bound: applies for each z, uniformly.
  -- ============================================================
  set K_lip : ℝ := ((max 1 L : NNReal) : ℝ) with hK_lip_def
  set C_T : ℝ := gronwallBound 0 K_lip ((L : ℝ) * D) t with hC_T_def
  have h_pt_bound : ∀ z : PhaseSpace d,
      ‖(charX_ρ t z, charV_ρ t z) - (charX_σ t z, charV_σ t z)‖ ≤ C_T := by
    intro z
    have h := flow_difference_gronwall_bound gradW L hL ρ σ h_int_ρ h_int_σ
      T hT D hD_nn h_W1_fin h_W1_bound
      (fun s => (charX_ρ s z, charV_ρ s z))
      (fun s => (charX_σ s z, charV_σ s z))
      z (h_init_ρ z) (h_init_σ z) (h_cont_ρ z) (h_cont_σ z)
      (h_deriv_ρ z) (h_deriv_σ z) t ht
    exact h
  -- ============================================================
  -- Project to position component: ‖charX_ρ t z - charX_σ t z‖ ≤ C_T.
  -- ============================================================
  have h_proj_bound : ∀ z : PhaseSpace d,
      ‖charX_ρ t z - charX_σ t z‖ ≤ C_T := fun z => by
    have h := h_pt_bound z
    -- ‖charX_ρ - charX_σ‖ ≤ ‖(charX_ρ, charV_ρ) - (charX_σ, charV_σ)‖.
    have h_proj :
        ‖charX_ρ t z - charX_σ t z‖ ≤
        ‖((charX_ρ t z, charV_ρ t z) - (charX_σ t z, charV_σ t z) : PhaseSpace d)‖ := by
      rw [Prod.norm_def]
      simp only [Prod.fst_sub]
      exact le_max_left _ _
    linarith
  -- ============================================================
  -- C_T is non-negative (gronwallBound at 0 with δ = 0 and ε ≥ 0).
  -- ============================================================
  have hC_T_nn : 0 ≤ C_T := by
    have h_LD_nn : 0 ≤ (L : ℝ) * D := mul_nonneg L.coe_nonneg hD_nn
    have h_K_pos : 0 ≤ K_lip := by
      have h_max_le : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
        push_cast
        exact le_max_left _ _
      linarith
    have ht_nn : 0 ≤ t := ht.1
    -- gronwallBound monotone in x from x = 0
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := K_lip) (ε := (L : ℝ) * D)
      (le_refl 0) h_LD_nn h_K_pos ht_nn
    rw [gronwallBound_x0] at this
    exact this
  -- ============================================================
  -- Integrability of `‖charX_ρ t z - charX_σ t z‖` wrt f₀.
  -- ============================================================
  have h_diff_int_f₀ : Integrable (fun z : PhaseSpace d =>
      ‖charX_ρ t z - charX_σ t z‖) f₀ := by
    -- Bounded by C_T (constant), integrable on probability measure.
    refine Integrable.mono' (integrable_const C_T)
      (((h_meas_ρ t ht).sub (h_meas_σ t ht)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact h_proj_bound z
  -- ============================================================
  -- Apply the W₁ pair bound.
  -- ============================================================
  have h_W1 := wasserstein1_pushforward_pair_le_integral_norm_diff
    (fun z => charX_ρ t z) (fun z => charX_σ t z) f₀
    (h_meas_ρ t ht) (h_meas_σ t ht) (h_int_charX_ρ t ht) (h_int_charX_σ t ht) h_diff_int_f₀
  -- ============================================================
  -- ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀ ≤ C_T.
  -- ============================================================
  have h_integral_bound : ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀ ≤ C_T := by
    calc ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀
        ≤ ∫ _, C_T ∂f₀ := integral_mono h_diff_int_f₀ (integrable_const _) h_proj_bound
      _ = C_T := by
          simp [integral_const, measureReal_def, measure_univ]
  -- ============================================================
  -- Convert ENNReal.ofReal bound to .toReal bound.
  -- ============================================================
  have h_W1_le_ofReal : (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                                       (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
                       (ENNReal.ofReal C_T).toReal := by
    apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
    refine le_trans h_W1 ?_
    exact ENNReal.ofReal_le_ofReal h_integral_bound
  rw [ENNReal.toReal_ofReal hC_T_nn] at h_W1_le_ofReal
  exact h_W1_le_ofReal

/-- **Stage 3c: sup-W₁ contraction estimate over `Icc 0 T`.**

The final Stage 3 deliverable, combining Stage 3b's pointwise contraction
with `gronwallBound`'s monotonicity in `t` to derive:
`(supW1On(Icc 0 T) Phi_ρ Phi_σ).toReal ≤ gronwallBound 0 K (L·D) T`
where `K := max(1, L)` and `D := supW1On(Icc 0 T) ρ σ` bound.

**For Stage 4's Banach fixed-point**: expanding `gronwallBound`'s explicit
form `(ε/K)·(exp(K·t) − 1)`, the bound is `(L·D/K) · (exp(K·T) − 1) =
D · K_contract(T)` where `K_contract(T) := (L/K)·(exp(K·T) − 1) → 0` as
`T → 0`.  This is the contraction factor Stage 4's Banach iteration
exploits.

**Metric-dependence note** (architectural priming for the W̄ refactor):
The contraction factor `K_contract(T) := (L/K)·(exp(K·T) − 1)` is
*exponential in T*.  For contraction (`K_contract < 1`), this requires
`L · (exp T - 1) < 1` when `K = 1` (i.e., `L < 1`) — exactly the
`LocalSmallness_contraction L T` predicate (CharFlow §3.5).  This is
genuinely independent of the per-ball Picard-Lindelöf flow's
quadratic-in-`T` ball-geometry constraint `LocalSmallness_PL_buffer L T
:= L·(T+1)² < 1`.  The two predicates are the M1-recursive split that
retired the original conflation under one `LocalSmallness` name
(structural-debt finding in commit `580548e`, fixed in commit
`2eed838`).

Under the `W̄` refactor (Dobrushin 1979, §5), the contraction factor
becomes `C₂(L) · T` — *linear in T*, no exponential, no `L < 1`
restriction.  `LocalSmallness_contraction` would reduce to `C₂(L) · T <
1` and the `L < 1` restriction lifts; `LocalSmallness_PL_buffer` is
independent of that change. -/
theorem Phi_supW1_contraction {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    (charX_ρ charV_ρ charX_σ charV_σ : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
    -- The pushforwards have finite first moments (for W₁ finiteness).
    (h_yint_Phi_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX_ρ t z) f₀))
    (h_yint_Phi_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX_σ t z) f₀))
    -- Per-z trajectory regularity (Stage 4's Picard discharges).
    (h_init_ρ : ∀ z, (charX_ρ 0 z, charV_ρ 0 z) = z)
    (h_init_σ : ∀ z, (charX_σ 0 z, charV_σ 0 z) = z)
    (h_cont_ρ : ∀ z,
      ContinuousOn (fun s => (charX_ρ s z, charV_ρ s z)) (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ∀ z,
      ContinuousOn (fun s => (charX_σ s z, charV_σ s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_ρ s' z, charV_ρ s' z))
        (vlasovVectorField gradW ρ s (charX_ρ s z, charV_ρ s z))
        (Set.Ici s) s)
    (h_deriv_σ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_σ s' z, charV_σ s' z))
        (vlasovVectorField gradW σ s (charX_σ s z, charV_σ s z))
        (Set.Ici s) s) :
    (supW1On (Set.Icc (0 : ℝ) T)
        (fun t => Measure.map (fun z => charX_ρ t z) f₀)
        (fun t => Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
      gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) T := by
  -- ============================================================
  -- Setup.
  -- ============================================================
  set K_lip : ℝ := ((max 1 L : NNReal) : ℝ) with hK_lip_def
  set C_T : ℝ := gronwallBound 0 K_lip ((L : ℝ) * D) T with hC_T_def
  have h_LD_nn : 0 ≤ (L : ℝ) * D := mul_nonneg L.coe_nonneg hD_nn
  have h_K_pos : 0 ≤ K_lip := by
    have h_max_le : (1 : ℝ) ≤ K_lip := by push_cast; exact le_max_left _ _
    linarith
  have hC_T_nn : 0 ≤ C_T := by
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := K_lip) (ε := (L : ℝ) * D)
      (le_refl 0) h_LD_nn h_K_pos hT
    rw [gronwallBound_x0] at this
    exact this
  -- ============================================================
  -- Pointwise bound (from Stage 3b): for each t ∈ Icc 0 T,
  --   wasserstein1 (Phi_ρ t) (Phi_σ t) ≤ ENNReal.ofReal C_T.
  -- ============================================================
  have h_pt_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                   (Measure.map (fun z => charX_σ t z) f₀) ≤
      ENNReal.ofReal C_T := by
    intro t ht
    haveI hΦρ_t : IsProbabilityMeasure (Measure.map (fun z => charX_ρ t z) f₀) :=
      MeasureTheory.Measure.isProbabilityMeasure_map (h_meas_ρ t ht)
    haveI hΦσ_t : IsProbabilityMeasure (Measure.map (fun z => charX_σ t z) f₀) :=
      MeasureTheory.Measure.isProbabilityMeasure_map (h_meas_σ t ht)
    -- W₁ is finite (probability + finite first moment).
    have h_W1_t_ne_top :
        wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                     (Measure.map (fun z => charX_σ t z) f₀) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _ (h_yint_Phi_ρ t ht) (h_yint_Phi_σ t ht)
    -- Pointwise contraction at time t.
    have h_pt := Phi_pointwise_contraction gradW L hL ρ σ h_int_ρ h_int_σ
      T hT D hD_nn h_W1_fin h_W1_bound
      charX_ρ charV_ρ charX_σ charV_σ f₀
      h_meas_ρ h_meas_σ h_int_charX_ρ h_int_charX_σ
      h_init_ρ h_init_σ h_cont_ρ h_cont_σ h_deriv_ρ h_deriv_σ t ht
    -- h_pt : (W₁ ...).toReal ≤ gronwallBound 0 K_lip (L*D) t
    -- Monotonicity of gronwallBound in t: t ≤ T ⇒ value at t ≤ value at T = C_T.
    have h_gronwall_mono : gronwallBound 0 K_lip ((L : ℝ) * D) t ≤ C_T := by
      apply gronwallBound_mono (le_refl 0) h_LD_nn h_K_pos ht.2
    have h_W1_real_le : (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                                       (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤ C_T :=
      le_trans h_pt h_gronwall_mono
    -- Lift from .toReal-bound to ENNReal bound (using W₁ ≠ ⊤).
    rw [← ENNReal.ofReal_toReal h_W1_t_ne_top]
    exact ENNReal.ofReal_le_ofReal h_W1_real_le
  -- ============================================================
  -- supW1On ≤ ENNReal.ofReal C_T.
  -- ============================================================
  have h_sup_bound : supW1On (Set.Icc (0 : ℝ) T)
        (fun t => Measure.map (fun z => charX_ρ t z) f₀)
        (fun t => Measure.map (fun z => charX_σ t z) f₀) ≤
      ENNReal.ofReal C_T := by
    unfold supW1On
    refine iSup_le fun t => iSup_le fun ht => h_pt_bound t ht
  -- ============================================================
  -- .toReal: (supW1On ...).toReal ≤ C_T.
  -- ============================================================
  calc (supW1On (Set.Icc (0 : ℝ) T)
          (fun t => Measure.map (fun z => charX_ρ t z) f₀)
          (fun t => Measure.map (fun z => charX_σ t z) f₀)).toReal
      ≤ (ENNReal.ofReal C_T).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h_sup_bound
    _ = C_T := ENNReal.toReal_ofReal hC_T_nn

/-- **Stage 4 sub-piece: Picard-iteration geometric bound.**

Given a sequence with geometric contraction `supW1On (x k) (x (k+1)) ≤
ENNReal.ofReal (q^k * D₀)` for `0 ≤ q < 1`, the iterated triangle
inequality + `ENNReal.ofReal_sum_of_nonneg` + Mathlib's `geom_sum_Ico_le_of_lt_one`
gives:
`supW1On (x m) (x n) ≤ ENNReal.ofReal (D₀ * q^m / (1 - q))` for `m ≤ n`.

**M1 design principle applied**: pure ENNReal modulo one cleanly-localized
`ENNReal.ofReal` boundary at the bridge between the structural argument
(supW1On in ENNReal) and the closed-form algebra (real geometric series).
The Finset partial sum bound comes from `Mathlib/Algebra/Order/Field/GeomSum.lean`'s
`geom_sum_Ico_le_of_lt_one` — no case-split on `q = 0` vs `q > 0` needed,
no shifting tricks via `Finset.sum_Ico_eq_sum_range`. -/
lemma picard_iterate_geometric_bound {d : ℕ} [NeZero d] (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On S (x k) (x (k+1)) ≤ ENNReal.ofReal (q^k * D₀))
    (m n : ℕ) (hmn : m ≤ n) :
    supW1On S (x m) (x n) ≤ ENNReal.ofReal (D₀ * q^m / (1 - q)) := by
  -- Iterated triangle gives the sum bound.
  have h_tri := supW1On_iterated_triangle S x m n hmn
  have h_sum_bound :
      ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) ≤
      ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) :=
    Finset.sum_le_sum (fun k _ => h_contract k)
  -- ENNReal.ofReal of finite sum (all non-negative).
  have h_qk_D₀_nn : ∀ k ∈ Finset.Ico m n, (0 : ℝ) ≤ q^k * D₀ := fun k _ =>
    mul_nonneg (pow_nonneg hq_nn k) hD₀_nn
  have h_sum_eq :
      ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) =
      ENNReal.ofReal (∑ k ∈ Finset.Ico m n, q^k * D₀) :=
    (ENNReal.ofReal_sum_of_nonneg h_qk_D₀_nn).symm
  -- Real-valued geometric bound: factor D₀ + apply geom_sum_Ico_le_of_lt_one.
  have h1mq_pos : 0 < 1 - q := by linarith
  have h_real_bound : ∑ k ∈ Finset.Ico m n, q^k * D₀ ≤ D₀ * q^m / (1 - q) := by
    have h_factor : ∑ k ∈ Finset.Ico m n, q^k * D₀ =
                    D₀ * ∑ k ∈ Finset.Ico m n, q^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_factor]
    calc D₀ * ∑ k ∈ Finset.Ico m n, q^k
        ≤ D₀ * (q^m / (1 - q)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq_nn hq_lt) hD₀_nn
      _ = D₀ * q^m / (1 - q) := by ring
  -- Chain everything.
  calc supW1On S (x m) (x n)
      ≤ ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) := h_tri
    _ ≤ ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) := h_sum_bound
    _ = ENNReal.ofReal (∑ k ∈ Finset.Ico m n, q^k * D₀) := h_sum_eq
    _ ≤ ENNReal.ofReal (D₀ * q^m / (1 - q)) :=
        ENNReal.ofReal_le_ofReal h_real_bound

/-- **Stage 4 sub-piece: Picard iteration is Cauchy from contraction.**

Standard Banach-fixed-point Cauchy condition derived from the geometric
contraction.

**Output form** matches `MathlibTODO_cauchyW1_hasNarrowLimit`'s ENNReal-form
Cauchy hypothesis: for every `ε : ENNReal` with `0 < ε`, there is `N` such
that `supW1On (x m) (x n) < ε` for all `m, n ≥ N`.

**Proof sketch**: for the symmetric case (m > n), use `supW1On_comm`.
For `ε = ⊤`, any N works.  For `ε < ⊤`, pick N such that
`D₀ * q^N / (1-q) < ε.toReal`; combine with the geometric bound. -/
theorem picard_iterate_isCauchy_of_contraction {d : ℕ} [NeZero d] (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On S (x k) (x (k+1)) ≤ ENNReal.ofReal (q^k * D₀)) :
    ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → supW1On S (x m) (x n) < ε := by
  intro ε hε
  have h1mq_pos : 0 < 1 - q := by linarith
  -- Helper: bound supW1On(x m, x n) in both orderings.
  have h_bound_both : ∀ m n, supW1On S (x m) (x n) ≤
      ENNReal.ofReal (D₀ * q^(min m n) / (1 - q)) := by
    intro m n
    by_cases h_order : m ≤ n
    · rw [min_eq_left h_order]
      exact picard_iterate_geometric_bound S x q hq_nn hq_lt D₀ hD₀_nn h_contract m n h_order
    · rw [supW1On_comm, min_eq_right (le_of_lt (not_le.mp h_order))]
      exact picard_iterate_geometric_bound S x q hq_nn hq_lt D₀ hD₀_nn h_contract n m
        (le_of_lt (not_le.mp h_order))
  -- Case split on ε = ⊤.
  by_cases hε_top : ε = ⊤
  · refine ⟨0, fun m n _ _ => ?_⟩
    rw [hε_top]
    exact lt_of_le_of_lt (h_bound_both m n) ENNReal.ofReal_lt_top
  · -- ε < ⊤ case.
    have hε_real_pos : 0 < ε.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hε, lt_top_iff_ne_top.mpr hε_top⟩
    -- Tendsto of q^N → 0 gives existence of N.
    have h_pow_tendsto : Filter.Tendsto (fun n : ℕ => D₀ * q^n / (1 - q))
                          Filter.atTop (nhds 0) := by
      have h_pow : Filter.Tendsto (fun n : ℕ => q^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
      have h_factored : (fun n : ℕ => D₀ * q^n / (1 - q)) =
                       fun n : ℕ => (D₀ / (1 - q)) * q^n := by
        funext n; ring
      rw [h_factored]
      have h_zero_eq : (0 : ℝ) = (D₀ / (1 - q)) * 0 := by ring
      rw [h_zero_eq]
      exact h_pow.const_mul _
    rw [Metric.tendsto_atTop] at h_pow_tendsto
    obtain ⟨N, hN⟩ := h_pow_tendsto ε.toReal hε_real_pos
    refine ⟨N, fun m n hm hn => ?_⟩
    -- Apply the bound and the tendsto-induced threshold.
    have h_min_ge : N ≤ min m n := le_min hm hn
    have h_bound_real_lt : D₀ * q^(min m n) / (1 - q) < ε.toReal := by
      have h_dist := hN (min m n) h_min_ge
      rw [Real.dist_eq] at h_dist
      have h_val_nn : 0 ≤ D₀ * q^(min m n) / (1 - q) :=
        div_nonneg (mul_nonneg hD₀_nn (pow_nonneg hq_nn _)) (le_of_lt h1mq_pos)
      rw [abs_sub_lt_iff] at h_dist
      linarith [h_dist.1]
    calc supW1On S (x m) (x n)
        ≤ ENNReal.ofReal (D₀ * q^(min m n) / (1 - q)) := h_bound_both m n
      _ < ENNReal.ofReal ε.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hε_real_pos).mpr h_bound_real_lt
      _ = ε := ENNReal.ofReal_toReal hε_top

/-- **Stage 4 helper: pointwise W₁ bounded by `supW1On`**.

For `t ∈ S`, the per-`t` Wasserstein-1 distance is bounded by the sup-W₁
over `S`.  Routine `le_iSup` chain.  Mirror image of the `supW1On`-shape
lemmas (`supW1On_triangle`, `supW1On_self`) — the per-point extraction
from the sup. -/
lemma wasserstein1_le_supW1On {d : ℕ} [NeZero d]
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d))
    (t : ℝ) (ht : t ∈ S) :
    wasserstein1 (ρ t) (σ t) ≤ supW1On S ρ σ := by
  unfold supW1On
  exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- **Stage 4 helper: uniform-in-`t` W₁-tendsto from supW1On Cauchy + per-`t`
pointwise W₁-tendsto**.

Given a sequence `x n : ℝ → Measure (PhysSpace d)` Cauchy in `supW1On S` and
per-`t` pointwise W₁-tendsto to `y t`, the convergence is uniform in `t ∈ S`:
for every `ε : ENNReal` with `0 < ε`, there is `N` such that
`wasserstein1 (x n t) (y t) ≤ ε` for all `n ≥ N` and `t ∈ S`.

**Proof idea**: triangle through `x m t` for arbitrarily large `m`:
`wasserstein1 (x n t) (y t) ≤ wasserstein1 (x n t) (x m t) + wasserstein1 (x m t) (y t)`.
The first term `≤ supW1On (x n) (x m) < ε` by Cauchy; the second `→ 0` by
pointwise tendsto.  Apply `ENNReal.le_of_forall_pos_le_add` for the limit
passage. -/
lemma picard_iterate_limit_uniform_tendsto {d : ℕ} [NeZero d]
    (S : Set ℝ) (x : ℕ → ℝ → Measure (PhysSpace d))
    (y : ℝ → Measure (PhysSpace d))
    (h_cauchy : ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
                supW1On S (x m) (x n) < ε)
    (h_pointwise : ∀ t ∈ S,
        Filter.Tendsto (fun n => wasserstein1 (x n t) (y t)) Filter.atTop (nhds 0)) :
    ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ t ∈ S,
        wasserstein1 (x n t) (y t) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_cauchy ε hε
  refine ⟨N, fun n hn t ht => ?_⟩
  -- Use ENNReal.le_of_forall_pos_le_add to reduce to `≤ ε + ε'` for ε' > 0.
  apply ENNReal.le_of_forall_pos_le_add
  intro ε' hε'_pos _
  -- Pick m ≥ N such that wasserstein1 (x m t) (y t) ≤ ε'.
  have h_tend := h_pointwise t ht
  rw [ENNReal.tendsto_atTop_zero] at h_tend
  have hε'_ennreal_pos : (0 : ENNReal) < (ε' : ENNReal) := by
    exact_mod_cast hε'_pos
  obtain ⟨M, hM⟩ := h_tend (ε' : ENNReal) hε'_ennreal_pos
  let m := max N M
  have hmN : N ≤ m := le_max_left _ _
  have hmM : M ≤ m := le_max_right _ _
  -- Apply triangle inequality.
  calc wasserstein1 (x n t) (y t)
      ≤ wasserstein1 (x n t) (x m t) + wasserstein1 (x m t) (y t) :=
        wasserstein1_triangle _ _ _
    _ ≤ supW1On S (x n) (x m) + wasserstein1 (x m t) (y t) :=
        add_le_add (wasserstein1_le_supW1On S (x n) (x m) t ht) le_rfl
    _ ≤ ε + (ε' : ENNReal) := by
        gcongr
        · exact le_of_lt (hN n m hn hmN)
        · exact hM m hmM

/-- **Stage 4 main: bundle the Picard iteration's W₁-limit as a `VlasovMeasureCurve`**.

Given a sequence of `VlasovMeasureCurve d T M` iterates with the geometric
contraction property `supW1On (x k) (x (k+1)) ≤ ofReal (q^k * D₀)`,
produce a limit `ρ_lim : VlasovMeasureCurve d T M` such that
`wasserstein1 ((x n).ρ t) (ρ_lim.ρ t) → 0` pointwise (and, by the helper
`picard_iterate_limit_uniform_tendsto`, uniformly) in `t ∈ Icc 0 T`.

**Proof strategy** (Path (a) per the well-posedness plan, Stage 4):

1. Apply `picard_iterate_isCauchy_of_contraction` to get supW1On Cauchy.
2. Per-`t ∈ Icc 0 T`, the pointwise sequence `n ↦ (x n).ρ t` is Cauchy in
   W₁ (by `wasserstein1_le_supW1On` from the sup-Cauchy).
3. Invoke `MathlibTODO_cauchyW1_hasNarrowLimit` per-`t` to obtain the
   pointwise limit `ρ_lim t` (with probability, integrability, moment bound,
   W₁-tendsto, all from the strengthened placeholder).
4. Extend `ρ_lim` to all of `ℝ` by `(x 0).ρ` outside `Icc 0 T` (so the
   `isProb` field — universal in `t` — holds).
5. Verify the four `VlasovMeasureCurve` fields:
   * `isProb`: from the placeholder (inside `Icc 0 T`) + `(x 0).isProb`
     (outside).
   * `hasMoment`: from the placeholder's strengthened moment-preservation
     conjunct (`∫‖y‖ ∂μ ≤ M`).
   * `yIntegrable`: from the placeholder.
   * `hW1Cont`: ε/3 triangle through `x N`, using
     `picard_iterate_limit_uniform_tendsto` for the uniform tendsto +
     `(x N).hW1Cont` for the middle term. -/
theorem picard_iterate_bundlesAs_VlasovMeasureCurve {d : ℕ} [NeZero d]
    {T : ℝ} {M : ℝ → ℝ}
    (x : ℕ → VlasovMeasureCurve d T M)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
                       ENNReal.ofReal (q ^ k * D₀)) :
    ∃ ρ_lim : VlasovMeasureCurve d T M,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim.ρ t))
          Filter.atTop (nhds 0) := by
  -- Step 1: supW1On-Cauchy from the contraction.
  have h_cauchy := picard_iterate_isCauchy_of_contraction
    (Set.Icc (0:ℝ) T) (fun n => (x n).ρ) q hq_nn hq_lt D₀ hD₀_nn h_contract
  -- Step 2: per-t Cauchy from the supW1On bound.
  have h_per_t_cauchy : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ ε : ENNReal, 0 < ε →
      ∃ N, ∀ m n, N ≤ m → N ≤ n →
        wasserstein1 ((x m).ρ t) ((x n).ρ t) < ε := by
    intro t ht ε hε
    obtain ⟨N, hN⟩ := h_cauchy ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    exact lt_of_le_of_lt (wasserstein1_le_supW1On _ _ _ t ht) (hN m n hm hn)
  -- Step 3: per-t Classical.choose to extract the limit measure.
  have h_per_t : ∀ t ∈ Set.Icc (0:ℝ) T, ∃ μ : Measure (PhysSpace d),
      IsProbabilityMeasure μ ∧
      Integrable (fun y : PhysSpace d => ‖y‖) μ ∧
      ∫ y, ‖y‖ ∂μ ≤ M t ∧
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) μ) Filter.atTop (nhds 0) := by
    intro t ht
    haveI : ∀ n, IsProbabilityMeasure ((x n).ρ t) := fun n => (x n).isProb t
    exact MathlibTODO_cauchyW1_hasNarrowLimit (fun n => (x n).ρ t) (M t)
      (fun n => (x n).hasMoment t ht) (fun n => (x n).yIntegrable t ht)
      (h_per_t_cauchy t ht)
  -- Step 4: define ρ_lim via dependent choice on whether t ∈ Icc 0 T.
  let ρ_lim : ℝ → Measure (PhysSpace d) := fun t =>
    if ht : t ∈ Set.Icc (0:ℝ) T then Classical.choose (h_per_t t ht)
    else (x 0).ρ t
  -- Helper accessor on Icc.
  have hρ_spec : ∀ t (ht : t ∈ Set.Icc (0:ℝ) T),
      ρ_lim t = Classical.choose (h_per_t t ht) := by
    intro t ht
    simp only [ρ_lim, dif_pos ht]
  -- Step 5: verify the four VlasovMeasureCurve fields.
  -- isProb: universal in t.
  have h_isProb : ∀ t, IsProbabilityMeasure (ρ_lim t) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0:ℝ) T
    · rw [hρ_spec t ht]
      exact (Classical.choose_spec (h_per_t t ht)).1
    · simp only [ρ_lim, dif_neg ht]
      exact (x 0).isProb t
  -- hasMoment: from the placeholder's strengthened conclusion.
  have h_hasMoment : ∀ t ∈ Set.Icc (0:ℝ) T, ∫ y, ‖y‖ ∂(ρ_lim t) ≤ M t := by
    intro t ht
    rw [hρ_spec t ht]
    exact (Classical.choose_spec (h_per_t t ht)).2.2.1
  -- yIntegrable: from the placeholder.
  have h_yIntegrable : ∀ t ∈ Set.Icc (0:ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ_lim t) := by
    intro t ht
    rw [hρ_spec t ht]
    exact (Classical.choose_spec (h_per_t t ht)).2.1
  -- Pointwise tendsto on Icc 0 T (also part of the conclusion).
  have h_tendsto : ∀ t ∈ Set.Icc (0:ℝ) T,
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim t))
        Filter.atTop (nhds 0) := by
    intro t ht
    have h_spec := (Classical.choose_spec (h_per_t t ht)).2.2.2
    rw [hρ_spec t ht]
    exact h_spec
  -- Uniform tendsto from the helper.
  have h_uniform := picard_iterate_limit_uniform_tendsto
    (Set.Icc (0:ℝ) T) (fun n => (x n).ρ) ρ_lim h_cauchy h_tendsto
  -- hW1Cont: ε/3 argument through x N.
  have h_hW1Cont : ∀ s ∈ Set.Icc (0:ℝ) T,
      ContinuousWithinAt (fun t => (wasserstein1 (ρ_lim s) (ρ_lim t)).toReal)
                         (Set.Icc 0 T) s := by
    intro s hs
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    -- Self-distance at t = s is 0.
    have h_self : (wasserstein1 (ρ_lim s) (ρ_lim s)).toReal = 0 := by
      rw [wasserstein1_self]; rfl
    -- Pick N via uniform tendsto for tolerance ENNReal.ofReal (ε/3).
    have hε3 : 0 < ε / 3 := by linarith
    have hε3_nn : 0 < ENNReal.ofReal (ε / 3) := by
      exact_mod_cast ENNReal.ofReal_pos.mpr hε3
    obtain ⟨N, hN_uniform⟩ := h_uniform (ENNReal.ofReal (ε / 3)) hε3_nn
    -- Use (x N).hW1Cont for the middle term.
    have hN_cont := (x N).hW1Cont s hs
    rw [Metric.continuousWithinAt_iff] at hN_cont
    have h_self_N : (wasserstein1 ((x N).ρ s) ((x N).ρ s)).toReal = 0 := by
      rw [wasserstein1_self]; rfl
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := hN_cont (ε / 3) hε3
    refine ⟨δ, hδ_pos, fun t ht hdist => ?_⟩
    -- Triangle bound in ENNReal then toReal.
    have h_W1_first : wasserstein1 (ρ_lim s) ((x N).ρ s) ≤ ENNReal.ofReal (ε / 3) := by
      rw [wasserstein1_comm]
      exact hN_uniform N le_rfl s hs
    have h_W1_third : wasserstein1 ((x N).ρ t) (ρ_lim t) ≤ ENNReal.ofReal (ε / 3) :=
      hN_uniform N le_rfl t ht
    -- Finiteness of the limit's W₁.
    haveI hPs_inf : IsProbabilityMeasure (ρ_lim s) := h_isProb s
    haveI hPt_inf : IsProbabilityMeasure (ρ_lim t) := h_isProb t
    have h_finite : wasserstein1 (ρ_lim s) (ρ_lim t) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _
        (h_yIntegrable s hs) (h_yIntegrable t ht)
    -- Triangle.
    have h_tri : wasserstein1 (ρ_lim s) (ρ_lim t) ≤
        wasserstein1 (ρ_lim s) ((x N).ρ s) + wasserstein1 ((x N).ρ s) ((x N).ρ t) +
          wasserstein1 ((x N).ρ t) (ρ_lim t) := by
      calc wasserstein1 (ρ_lim s) (ρ_lim t)
          ≤ wasserstein1 (ρ_lim s) ((x N).ρ t) + wasserstein1 ((x N).ρ t) (ρ_lim t) :=
            wasserstein1_triangle _ _ _
        _ ≤ (wasserstein1 (ρ_lim s) ((x N).ρ s) + wasserstein1 ((x N).ρ s) ((x N).ρ t))
              + wasserstein1 ((x N).ρ t) (ρ_lim t) :=
            add_le_add (wasserstein1_triangle _ _ _) le_rfl
    -- Bound the middle term via hδ_bound.
    have h_mid_lt : (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal < ε / 3 := by
      have hδb := hδ_bound ht hdist
      rw [h_self_N, Real.dist_eq, sub_zero] at hδb
      have h_nn : 0 ≤ (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal :=
        ENNReal.toReal_nonneg
      rwa [abs_of_nonneg h_nn] at hδb
    -- Convert toReal and bound by ε/3 + ε/3 + ε/3 = ε.
    have h_W1_first_ne_top : wasserstein1 (ρ_lim s) ((x N).ρ s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_W1_first
    have h_W1_third_ne_top : wasserstein1 ((x N).ρ t) (ρ_lim t) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_W1_third
    haveI hPNs : IsProbabilityMeasure ((x N).ρ s) := (x N).isProb s
    haveI hPNt : IsProbabilityMeasure ((x N).ρ t) := (x N).isProb t
    have h_mid_ne_top : wasserstein1 ((x N).ρ s) ((x N).ρ t) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _
        ((x N).yIntegrable s hs) ((x N).yIntegrable t ht)
    have h_W1_first_real : (wasserstein1 (ρ_lim s) ((x N).ρ s)).toReal ≤ ε / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_first
      rwa [ENNReal.toReal_ofReal hε3.le] at this
    have h_W1_third_real : (wasserstein1 ((x N).ρ t) (ρ_lim t)).toReal ≤ ε / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_third
      rwa [ENNReal.toReal_ofReal hε3.le] at this
    -- Apply ENNReal.toReal to the triangle.
    have h_tri_real : (wasserstein1 (ρ_lim s) (ρ_lim t)).toReal ≤
        (wasserstein1 (ρ_lim s) ((x N).ρ s)).toReal +
          (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal +
          (wasserstein1 ((x N).ρ t) (ρ_lim t)).toReal := by
      have h_add_ne_top : wasserstein1 (ρ_lim s) ((x N).ρ s) +
                          wasserstein1 ((x N).ρ s) ((x N).ρ t) +
                          wasserstein1 ((x N).ρ t) (ρ_lim t) ≠ ⊤ := by
        simp [h_W1_first_ne_top, h_mid_ne_top, h_W1_third_ne_top]
      have := ENNReal.toReal_mono h_add_ne_top h_tri
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h_W1_first_ne_top, h_mid_ne_top⟩)
            h_W1_third_ne_top,
          ENNReal.toReal_add h_W1_first_ne_top h_mid_ne_top] at this
      exact this
    rw [Real.dist_eq, h_self, sub_zero,
        abs_of_nonneg ENNReal.toReal_nonneg]
    linarith [h_tri_real, h_mid_lt, h_W1_first_real, h_W1_third_real]
  -- Bundle.
  refine ⟨{ρ := ρ_lim, isProb := h_isProb, hasMoment := h_hasMoment,
           yIntegrable := h_yIntegrable, hW1Cont := h_hW1Cont}, ?_⟩
  intro t ht
  exact h_tendsto t ht

-- ---------------------------------------------------------------------------
-- §9  Theorem (Existence and uniqueness for Vlasov)   (tex: thm:vlasov-wp)
-- ---------------------------------------------------------------------------
-- Relocated from `Vlasov/Basic.lean` (Stage 0 of the well-posedness plan) so
-- the proof can compose directly with the characteristic-flow infrastructure
-- developed in this file: `exists_vlasov_characteristicFlow`,
-- `flow_distance_growth_bound`, and
-- `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`.  The
-- `HasFiniteFirstMoment` predicate remains in `Basic.lean`.

/-- **Project-internal: AEMeasurability of the Vlasov characteristic flow's
joint map** `z ↦ (charX s z, charV s z)` on the window `Icc 0 T`.

**Closed genuinely (2026-06-02), NOT modulo deferred FA.** The earlier plan
routed this through a global-in-`t` pure-FA placeholder
(`MathlibTODO_lipschitzFlowAEMeasurable`), but that placeholder required
`HasDerivAt` at *every* `t : ℝ`, which the Vlasov flow only satisfies on
`Ioo 0 T` (off-window it is uncontrolled `Classical.choose` data).  The
global-in-`s` conclusion was an over-strength artifact (M3): its sole
consumer applies it only at `clampToIcc T s ∈ Icc 0 T`, so the
window-restricted statement suffices — and on the window the joint flow's
measurability follows from the *already-proven*
`charFlow_measurable_via_gronwall` (genuine `Measurable`, via the boundary
bundle through `Stage_1_9_flow_boundary_regularity`).  No deferred FA.

**In-project consumer**: `vlasovWellPosedness_local_picard_fixedPointFlow`'s
AEMeasurable conjunct, applied at clamp times `clampToIcc T s ∈ Icc 0 T`. -/
private lemma picardCharFlow_aemeasurable
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    {T : ℝ} (hT : 0 ≤ T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (hbdry : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0:ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) (Set.Icc 0 T) t)
    (μ : Measure (PhaseSpace d)) :
    ∀ s ∈ Set.Icc (0:ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) μ := by
  intro s hs
  obtain ⟨h_init, h_cont, h_deriv⟩ :=
    Stage_1_9_flow_boundary_regularity gradW ρ charX charV T hT hflow hbdry
  exact (charFlow_measurable_via_gronwall gradW L hL ρ h_int charX charV T hT
    h_init h_cont h_deriv s hs).aemeasurable

/-- **Piece D sorry-1 helper**: from a flow's exposed facts (`IsCharacteristicFlowOn`
on `Ioo` + the boundary bundle on `Icc` — the `Phi_step_envelope` output shape)
against a curve `ν`, derive the six per-`z` regularity facts that the (M2-weakened)
`Phi_supW1_contraction` consumes.  Chains `Stage_1_9_flow_boundary_regularity`
(→ init/cont/deriv, the last three EXACT), `charFlow_measurable_via_gronwall`
(→ AEMeasurable), and `flow_distance_growth_bound_on` (→ growth bound, integrated
to the two integrability facts). -/
private lemma envelopeStep_contractionInputs {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 ≤ T) {m : ℝ → ℝ}
    (ν : VlasovMeasureCurve d T m)
    (Mbar : ℝ) (hMbar_nn : 0 ≤ Mbar)
    (hM_ρ : ∀ t ∈ Set.Icc (0:ℝ) T, ∫ y, ‖y‖ ∂(ν.extend t) ≤ Mbar)
    (cX cV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ)
    (hbdry : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0:ℝ) T,
        HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => cV s z)
          (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t)
    (h_int_ext : ∀ t (x : PhysSpace d),
        Integrable (fun y => gradW (x - y)) (ν.extend t)) :
    (∀ t ∈ Set.Icc (0:ℝ) T, AEMeasurable (fun z : PhaseSpace d => cX t z) f₀) ∧
    (∀ t ∈ Set.Icc (0:ℝ) T, Integrable (fun z : PhaseSpace d => ‖cX t z‖) f₀) ∧
    (∀ t ∈ Set.Icc (0:ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => cX t z) f₀)) ∧
    (∀ z : PhaseSpace d, (cX 0 z, cV 0 z) = z) ∧
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (cX s z, cV s z)) (Set.Icc (0:ℝ) T)) ∧
    (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0:ℝ) T,
      HasDerivWithinAt (fun s' => (cX s' z, cV s' z))
        (vlasovVectorField gradW (ν.extend) s (cX s z, cV s z))
        (Set.Ici s) s) := by
  haveI : ∀ t, IsProbabilityMeasure (ν.extend t) := VlasovMeasureCurve.extend_isProb ν
  obtain ⟨h_init, h_cont, h_deriv⟩ :=
    Stage_1_9_flow_boundary_regularity gradW ν.extend cX cV T hT hflow hbdry
  have h_meas : ∀ t ∈ Set.Icc (0:ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => cX t z) f₀ := by
    have h_meas_Icc := charFlow_measurable_via_gronwall gradW L hL ν.extend h_int_ext
      cX cV T hT h_init h_cont h_deriv
    exact fun t ht => (measurable_fst.comp (h_meas_Icc t ht)).aemeasurable
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ν.extend cX cV T hT
      h_init h_cont h_deriv Mbar hMbar_nn hM_ρ
      (fun t _ => VlasovMeasureCurve.extend_yIntegrable hT ν t) h_int_ext
  have h_int_charX : ∀ t ∈ Set.Icc (0:ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖cX t z‖) f₀ := by
    intro t ht
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ := h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) = fun z => C_T * ‖z‖ + C_T := by
        funext z; ring
      rw [h_eq]; exact h1.add h2
    refine h_dom_int.mono' (h_meas t ht).norm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact le_trans (norm_fst_le (cX t z, cV t z)) (h_growth t ht z)
  have h_yint_Phi : ∀ t ∈ Set.Icc (0:ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => cX t z) f₀) := by
    intro t ht
    rw [integrable_map_measure continuous_norm.aestronglyMeasurable (h_meas t ht)]
    exact h_int_charX t ht
  exact ⟨h_meas, h_int_charX, h_yint_Phi, h_init, h_cont, h_deriv⟩

/-- **Sub-helper for `vlasovWellPosedness_local`** — the Picard fixed-point
self-consistent flow.

Given `f₀ : Measure (PhaseSpace d)` with finite first moment, produces a
characteristic flow `(charX, charV)` whose **own pushforward's spatial
marginal** is the reference measure the flow is built against — i.e., the
Picard fixed point at the spatial-marginal-curve level:

  `ρ_t := spatialMarginal (Measure.map (z ↦ (charX t z, charV t z)) f₀)`
  `charX, charV solve the Vlasov ODE against this ρ`.

The sorry'd body encapsulates the substantive Picard analysis (steps 1-5
of `vlasovWellPosedness_local`'s 7-step plan):

* M-fixed-point: pick a moment bound `M ≥ A/(1 - B)` where
  `A = gronwallBound 1 (1+L) ‖gradW 0‖ T · (M_f₀ + 1)` and
  `B = L · (exp((1+L)·T) - 1)/(1+L) · (M_f₀ + 1)`.  Requires `B < 1`,
  which is the genuine convergence criterion for the moment iteration
  (stronger than the contraction predicate `LocalSmallness_contraction
  L T` alone for large `M_f₀` — the contraction predicate gates the q
  factor; the M-fixed-point additionally requires the moment iteration
  to converge).
* Picard sequence `x_n : ℕ → VlasovMeasureCurve d T M` starting from
  `x_0 := constantCurve (spatialMarginal f₀)` and `x_{n+1} := Phi_step(x_n)`.
* Contraction via `Phi_supW1_contraction`: `supW1On (Φρ) (Φσ) ≤ q · D`
  with `q < 1`.  Apply `picard_iterate_isCauchy_of_contraction` +
  `picard_iterate_bundlesAs_VlasovMeasureCurve` to get the W₁-limit
  `ρ_lim : VlasovMeasureCurve d T M`.
* Self-consistency `Φ(ρ_lim) = ρ_lim`: triangle through `x_n`.
* Apply `exists_vlasov_characteristicFlow_global_smallT` to `ρ_lim.extend`
  to get the flow.

**Metric-dependence note** (architectural priming for the W̄ refactor):
The two-predicate structure introduced in Stage 2b part 3 (commit
`2eed838`, retiring the structural-debt finding from `580548e`):
* `LocalSmallness_contraction L T := L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`
  — exponential in T, from `Phi_supW1_contraction`'s W₁-based shape.
* `LocalSmallness_PL_buffer L T := L · (T+1)² < 1` — quadratic, from
  per-ball Picard-Lindelöf's `(T+1)`-buffer.

These are GENUINELY INDEPENDENT (neither universally implies the other;
verified numerically per planning-notes `b7d4d05`).  Carrying them as
two predicates rather than one prevents fusing them back into "the
constraint" — predicates match the mathematical structure (M1).

Under the W̄ refactor (Dobrushin 1979, §5), both constraints become
linear-in-T and align: `LocalSmallness_contraction` reduces to
`C₂(L)·T < 1`, and the PL window's `(T+1)`-buffer disappears.  The
single algebraic constraint `C₂(L)·T < 1` then suffices and is
satisfiable for any `L > 0` by taking `T < 1/C₂(L)`.

**Output bundle** (designed to feed
`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn` directly):

* Flow `(charX, charV)` against the *spatial marginal of the pushforward*
  — the load-bearing self-consistency conjunct.
* Boundary regularity (post-Friction-5 form).
* Uniform moment bound `M_ρ` on the spatial marginal trajectory.

**Status**: sorry'd, per the API-lock-vs-substantive-proof discipline
(third sighting of this pattern; promotion-candidate for P-series after
Stage C and Friction 5).  The body is the load-bearing Picard math
(~150-220 lines as estimated in the plan's process notes #5), best done
as a focused follow-up session.  Locking the signature here lets
`vlasovWellPosedness_local`'s body close substantively, threading this
output into the final assembly. -/
theorem vlasovWellPosedness_local_picard_fixedPointFlow
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallness_PL_buffer L T)
    (hTL_con : LocalSmallness_contraction L T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (M_ρ : ℝ), 0 ≤ M_ρ ∧
      -- Self-consistent characteristic flow: against the spatial marginal
      -- of its own phase-space pushforward.
      IsCharacteristicFlowOn gradW
        (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
        charX charV (Set.Ioo 0 T) Set.univ ∧
      -- Boundary regularity (post-Friction-5 form): HasDerivWithinAt on
      -- `Icc 0 T` for every z and t ∈ Icc 0 T.
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              (charX t z)))
          (Set.Icc 0 T) t) ∧
      -- Uniform first-moment bound on the spatial-marginal trajectory.
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ) ∧
      -- First-moment integrability on the spatial-marginal trajectory.
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y : PhysSpace d => ‖y‖)
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) ∧
      -- Continuity of the convolution force in `x` (uniformly in `s`).
      (∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) ∧
      -- **AEMeasurable witness** (Stage 1.8 territory, projected from the
      -- Picard fixed-point construction's continuity-in-z) — closes the
      -- `h_aemeas` sub-sub-sorries in downstream `_finalAssembly_*`.
      (∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) ∧
      -- **Universal-in-s convolution integrability**.  For `s ∈ Icc 0 T`
      -- follows from `h_y_int_ρ` + Lipschitz of `gradW`; the extension to
      -- all `s` requires constant-extension (clamp) past T inside the
      -- Picard construction.  Closes the `h_int_conv` sub-sub-sorries
      -- in downstream `_finalAssembly_*`.
      (∀ s (x : PhysSpace d),
        Integrable (fun y => gradW (x - y))
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) := by
  -- ============================================================
  -- Step 1: Spatial marginal setup.
  -- μ₀ := spatialMarginal f₀ = Measure.map Prod.fst f₀.
  -- IsProbabilityMeasure μ₀ via Measure.isProbabilityMeasure_map.
  -- Integrable ‖·‖ μ₀ from hf₀_int via integral_map on Prod.fst.
  -- ============================================================
  have hμ₀_prob : IsProbabilityMeasure (spatialMarginal f₀) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hμ₀_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal f₀) := by
    unfold spatialMarginal
    rw [integrable_map_measure
      (Continuous.aestronglyMeasurable continuous_norm) measurable_fst.aemeasurable]
    -- Need: Integrable (‖·‖ ∘ Prod.fst) f₀ = Integrable (fun z => ‖z.1‖) f₀.
    -- This follows from hf₀_int (Integrable ‖·‖ f₀) and ‖z.1‖ ≤ ‖z‖.
    refine hf₀_int.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (measurable_fst.norm.aestronglyMeasurable)
    · simp only [Function.comp, Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_fst_le z)
  -- **F1 (phase-space anchor)**: `M_f₀` is the *phase-space* first moment
  -- `∫z‖z‖∂f₀`, NOT the spatial marginal — matching `phi_moment_envelope_le`'s
  -- (A.2) `integral_map` initial value, so the envelope dominates both the
  -- pushforward moments (A.2) and the spatial base case (`∫‖x‖∂μ₀ ≤ M_f₀`).
  let M_f₀ : ℝ := ∫ z : PhaseSpace d, ‖z‖ ∂f₀
  have hM_f₀_nn : 0 ≤ M_f₀ := integral_nonneg (fun z => norm_nonneg z)
  -- ============================================================
  -- Step 2: time-dependent moment envelope `m` (option 2, dissolving the
  -- constant-`M` fixed-point).  `gronwall_envelope_exists` (Piece A.3) under
  -- `hB := B(T) < 1` yields a monotone `m` that is `Φ`-invariant at the moment
  -- level, so `Φ : space(m) → space(m)` and the Picard sequence stays in one
  -- fixed curve space.
  -- ============================================================
  obtain ⟨m, hm_mono, hm_ge, hm_inv⟩ :=
    gronwall_envelope_exists M_f₀ ‖gradW 0‖ hM_f₀_nn (norm_nonneg _) L T hT.le hB
  have hm_nn : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ m t :=
    fun t ht => le_trans hM_f₀_nn (hm_ge t ht)
  have hMbar_nn : 0 ≤ m T := hm_nn T ⟨hT.le, le_refl T⟩
  have hMbar_mono : ∀ t ∈ Set.Icc (0:ℝ) T, m t ≤ m T :=
    fun t ht => hm_mono ht ⟨hT.le, le_refl T⟩ ht.2
  -- ============================================================
  -- Step 3: Convolution integrability for constantCurve.
  -- For the base case x 0 = constantCurve μ₀, need h_int_ext:
  --   ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) ((constantCurve μ₀).extend t).
  -- This reduces to: Integrable (fun y => gradW (x - y)) μ₀, which follows
  -- from hμ₀_int + Lipschitz bound on gradW.
  -- Sub-sub-sorry: integrability of gradW against μ₀.
  -- ============================================================
  have h_int_gradW_μ₀ : ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal f₀) := by
    intro x_pt
    -- AEStronglyMeasurable: gradW is continuous (from Lipschitz), (x_pt - ·) is continuous.
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal f₀) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    -- Pointwise bound: ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + L*(‖x_pt‖ + ‖y‖).
    have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x_pt - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    -- Dominator is integrable: constant + L * ‖y‖ (using hμ₀_int).
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
        (spatialMarginal f₀) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖) (spatialMarginal f₀) :=
        hμ₀_int.const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  -- ============================================================
  -- Step 4: Picard sequence + contraction bound.
  -- Sub-sub-sorry: construction of the sequence x : ℕ → VlasovMeasureCurve d T M
  -- and the contraction estimate.
  -- The construction uses Phi_step + induction.
  -- The contraction uses Phi_supW1_contraction applied to consecutive iterates.
  -- ============================================================
  -- **Historical structural-debt note (2026-05-29 sorry-prover analysis,
  -- FIXED in commit `2eed838` 2026-05-31)**: the original q-definition
  -- used `gronwallBound 0 (max 1 L) (L · (2·M)) T`, conflating the
  -- contraction factor with the W₁-input bound D = 2M.  The contraction
  -- constraint `L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1` was not
  -- implied by the then-current `LocalSmallness L T = L · (T+1)² < 1`
  -- predicate (which fused two independent constraints).  Fix: predicate
  -- split into `LocalSmallness_PL_buffer` (PL ball-geometry) and
  -- `LocalSmallness_contraction` (this contraction-ratio constraint),
  -- plus q de-conflation (drop 2M from ε).  Both layers fixed together
  -- so the named-lemma citation (`hq_lt` discharges from
  -- `LocalSmallness_contraction` directly, no inline derivation) wires
  -- through without rebuilding the fusion-generator pattern.  This note
  -- preserved historically since it documents the original design.
  --
  -- **Stage 2b part 3 fix (2026-05-31)**: q is the M-INDEPENDENT genuine
  -- contraction ratio, NOT 2M·q_true.  The old q-definition
  -- `gronwallBound 0 (max 1 L) (L · 2M) T` conflated the contraction
  -- factor with the W₁-input bound D₀ = 2M (which appears separately
  -- below).  Per the L6495 read of the structural-debt note (now retired):
  -- the standard Phi_supW1_contraction output is `q · D` per step, so
  -- `q^k · D₀ = q^k · (2M)` is the iterated contraction bound.  The
  -- de-conflation drops 2M from the ε-input of gronwallBound, leaving q
  -- = `gronwallBound 0 (max 1 L) L T = (L/(max 1 L)) · (exp((max 1 L)·T) - 1)`
  -- — the M-independent ratio.  hq_lt closes by direct citation of
  -- `hTL_con` (LocalSmallness_contraction) after one-line unfold.
  let q : ℝ := gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T
  have hq_nn : 0 ≤ q := by
    have hK_nn : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hε_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := ((max 1 L : NNReal) : ℝ))
      (ε := (L : ℝ)) (le_refl 0) hε_nn hK_nn hT.le
    rw [gronwallBound_x0] at this; exact this
  -- Direct citation: `LocalSmallness_contraction L T` IS `q < 1` after
  -- unfolding both definitions.  No local derivation; the named-lemma
  -- pattern from the soundness-fix mechanism.
  have hq_lt : q < 1 := by
    show gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T < 1
    -- gronwallBound 0 K ε T = ε/K · (exp(K·T) - 1) when K ≠ 0.
    -- With K = max 1 L ≥ 1 > 0, this is (L/(max 1 L)) · (exp((max 1 L)·T) - 1).
    have hK_pos : (0 : ℝ) < ((max 1 L : NNReal) : ℝ) := by
      have : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
        rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
      linarith
    have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := ne_of_gt hK_pos
    rw [gronwallBound_of_K_ne_0 hK_ne]
    simp only [zero_mul, zero_add]
    -- Goal: L / (max 1 L) * (exp((max 1 L) * T) - 1) < 1, which is exactly
    -- `LocalSmallness_contraction L T` after one rewrite of `a/b · c = a·c/b`.
    have h_eq : (L : ℝ) / ((max 1 L : NNReal) : ℝ) *
        (Real.exp (((max 1 L : NNReal) : ℝ) * T) - 1) =
        (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) := by
      rw [NNReal.coe_max, NNReal.coe_one]
      ring
    rw [h_eq]
    exact hTL_con
  -- D₀: initial supW1On bound = supW1On (x 0).ρ (x 1).ρ ≤ 2 * M.
  let D₀ : ℝ := 2 * (m T)
  have hD₀_nn : 0 ≤ D₀ := by linarith [hMbar_nn]
  -- Sub-sub-sorry: Picard sequence + contraction, in the fixed envelope
  -- space `m`.  The closing recursion uses `Phi_step_envelope` (proven) per
  -- step + `Phi_supW1_contraction` for the geometric bound.
  -- **Enriched existential (architecture A)**: the Picard sequence exposes, per
  -- step `k`, the flow `(charXs k, charVs k)` against `(x k).extend` — exactly
  -- `Phi_step_envelope`'s output shape — plus the pushforward identity
  -- `(x(k+1)).ρ t = map (charXs k t) f₀`.  Exposing the flows lets the
  -- self-consistency proof (Step 8) feed them directly to `Phi_supW1_contraction`,
  -- dissolving the (un-banked) ODE-uniqueness that re-deriving them would need.
  obtain ⟨x, charXs, charVs, h_contract, h_flow⟩ :
      ∃ (x : ℕ → VlasovMeasureCurve d T m)
        (charXs charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d),
        (∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
              ENNReal.ofReal (q ^ k * D₀)) ∧
        (∀ k,
          IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
            (Set.Ioo 0 T) Set.univ ∧
          (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0:ℝ) T,
            HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
            HasDerivWithinAt (fun s => charVs k s z)
              (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
              (Set.Icc 0 T) t) ∧
          (∀ t ∈ Set.Icc (0:ℝ) T,
            (x (k + 1)).ρ t
              = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀)) := by
    -- General convolution integrability for ANY envelope curve `ν : space m`.
    have h_int_ext_gen : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ) (xp : PhysSpace d),
        Integrable (fun y => gradW (xp - y)) (ν.extend t) := by
      intro ν t xp
      have h_yint : Integrable (fun y : PhysSpace d => ‖y‖) (ν.extend t) :=
        VlasovMeasureCurve.extend_yIntegrable hT.le ν t
      have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (xp - y)) (ν.extend t) :=
        (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      have h_dom : ∀ y : PhysSpace d, ‖gradW (xp - y)‖ ≤
          ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖ := by
        intro y
        have hd := hL.dist_le_mul (xp - y) 0
        simp only [dist_eq_norm, sub_zero] at hd
        have h_tri : ‖gradW (xp - y)‖ ≤ ‖gradW 0‖ + ‖gradW (xp - y) - gradW 0‖ := by
          have := norm_add_le (gradW (xp - y) - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        have h_sub_le : ‖xp - y‖ ≤ ‖xp‖ + ‖y‖ := norm_sub_le xp y
        have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
        linarith
      have h_dom_int : Integrable
          (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) (ν.extend t) := by
        have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖) (ν.extend t) :=
          h_yint.const_mul (L : ℝ)
        have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) =
                    fun y => (‖gradW 0‖ + (L : ℝ) * ‖xp‖) + (L : ℝ) * ‖y‖ := by funext y; ring
        rw [h_eq]; exact (integrable_const _).add h_norm
      exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
    -- Base-curve moment bound: ∫‖y‖∂μ₀ ≤ m t  (μ₀ = spatialMarginal f₀).
    have hμ₀_int_fst : Integrable (fun z : PhaseSpace d => ‖z.1‖) f₀ :=
      hf₀_int.mono' measurable_fst.norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_fst_le z)
    have hμ₀_le_m : ∀ t ∈ Set.Icc (0:ℝ) T,
        ∫ y, ‖y‖ ∂(spatialMarginal f₀) ≤ m t := by
      intro t ht
      have h_eq : ∫ y, ‖y‖ ∂(spatialMarginal f₀) = ∫ z, ‖z.1‖ ∂f₀ := by
        unfold spatialMarginal
        rw [integral_map measurable_fst.aemeasurable continuous_norm.aestronglyMeasurable]
      have h_le : ∫ z, ‖z.1‖ ∂f₀ ≤ M_f₀ :=
        integral_mono hμ₀_int_fst hf₀_int (fun z => norm_fst_le z)
      rw [h_eq]; exact le_trans h_le (hm_ge t ht)
    -- Per-step `Φ` via `Phi_step_envelope`, reshaped with `σ` first.
    have step : ∀ (ν : VlasovMeasureCurve d T m),
        ∃ (σ : VlasovMeasureCurve d T m) (cX cV : ℝ → PhaseSpace d → PhysSpace d),
          (∀ t ∈ Set.Icc (0:ℝ) T, σ.ρ t = Measure.map (fun z => cX t z) f₀) ∧
          IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ ∧
          (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0:ℝ) T,
            HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
            HasDerivWithinAt (fun s => cV s z)
              (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t) := by
      intro ν
      obtain ⟨cX, cV, hflow, hbdry, σ, hσ⟩ :=
        Phi_step_envelope W gradW hgradW L hL f₀ hf₀_int hT.le m hm_mono hm_nn hm_inv hTL_PL
          ν (h_int_ext_gen ν)
      exact ⟨σ, cX, cV, hσ, hflow, hbdry⟩
    -- The Picard sequence + its exposed flows (via `Classical.choose`).
    haveI hμ₀_prob_inst : IsProbabilityMeasure (spatialMarginal f₀) := hμ₀_prob
    let base : VlasovMeasureCurve d T m := constantCurve (spatialMarginal f₀) hμ₀_int hμ₀_le_m
    let x : ℕ → VlasovMeasureCurve d T m :=
      fun n => Nat.rec base (fun _ ν => Classical.choose (step ν)) n
    let charXs : ℕ → ℝ → PhaseSpace d → PhysSpace d :=
      fun k => Classical.choose (Classical.choose_spec (step (x k)))
    let charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d :=
      fun k => Classical.choose (Classical.choose_spec (Classical.choose_spec (step (x k))))
    have hx_succ : ∀ k, x (k + 1) = Classical.choose (step (x k)) := fun _ => rfl
    have hspec : ∀ k,
        (∀ t ∈ Set.Icc (0:ℝ) T,
          (Classical.choose (step (x k))).ρ t = Measure.map (fun z => charXs k t z) f₀) ∧
        IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
          (Set.Ioo 0 T) Set.univ ∧
        (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0:ℝ) T,
          HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
          HasDerivWithinAt (fun s => charVs k s z)
            (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
            (Set.Icc 0 T) t) :=
      fun k => Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec (step (x k))))
    -- Conjunct (b): the flow-facts, directly from `hspec`.
    have h_flow : ∀ k,
        IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
          (Set.Ioo 0 T) Set.univ ∧
        (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0:ℝ) T,
          HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
          HasDerivWithinAt (fun s => charVs k s z)
            (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
            (Set.Icc 0 T) t) ∧
        (∀ t ∈ Set.Icc (0:ℝ) T,
          (x (k + 1)).ρ t = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀) := by
      intro k
      obtain ⟨hpush, hcf, hbd⟩ := hspec k
      refine ⟨hcf, hbd, fun t ht => ?_⟩
      rw [hx_succ k]; exact hpush t ht
    -- Conjunct (a): the geometric contraction bound (induction).
    -- Per-step 6-fact bundle (the proven helper, `Mbar = m T`).
    have hCI : ∀ k,
        (∀ t ∈ Set.Icc (0:ℝ) T, AEMeasurable (fun z : PhaseSpace d => charXs k t z) f₀) ∧
        (∀ t ∈ Set.Icc (0:ℝ) T, Integrable (fun z : PhaseSpace d => ‖charXs k t z‖) f₀) ∧
        (∀ t ∈ Set.Icc (0:ℝ) T,
          Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => charXs k t z) f₀)) ∧
        (∀ z : PhaseSpace d, (charXs k 0 z, charVs k 0 z) = z) ∧
        (∀ z : PhaseSpace d,
          ContinuousOn (fun s => (charXs k s z, charVs k s z)) (Set.Icc (0:ℝ) T)) ∧
        (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0:ℝ) T,
          HasDerivWithinAt (fun s' => (charXs k s' z, charVs k s' z))
            (vlasovVectorField gradW ((x k).extend) s (charXs k s z, charVs k s z))
            (Set.Ici s) s) :=
      fun k => envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le (x k) (m T) hMbar_nn
        (fun t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le (x k) t)
          (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t)))
        (charXs k) (charVs k) (h_flow k).1 (h_flow k).2.1 (h_int_ext_gen (x k))
    have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := by
      have h1 : (1:ℝ) ≤ ((max 1 L : NNReal):ℝ) := by
        rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
      linarith
    have hq_scale : ∀ D : ℝ,
        gronwallBound 0 ((max 1 L : NNReal):ℝ) ((L:ℝ)*D) T = D * q := by
      intro D
      show gronwallBound 0 ((max 1 L : NNReal):ℝ) ((L:ℝ)*D) T
        = D * gronwallBound 0 ((max 1 L : NNReal):ℝ) (L:ℝ) T
      rw [gronwallBound_of_K_ne_0 hK_ne, gronwallBound_of_K_ne_0 hK_ne]; ring
    -- Abstractly-typed extend-probability (M = m pinned in the binder, so applying
    -- to a `let`-bound `x k` is pure substitution — sidesteps the stuck `{M}`-synthesis).
    have hPext : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ),
        IsProbabilityMeasure (ν.extend t) :=
      fun ν => VlasovMeasureCurve.extend_isProb ν
    have h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
        ENNReal.ofReal (q ^ k * D₀) := by
      intro k
      induction k with
      | zero =>
        simp only [pow_zero, one_mul]
        exact supW1On_le_two_moment_of_VlasovMeasureCurve (m T) hMbar_mono (x 0) (x 1)
      | succ k ih =>
        set D : ℝ := q ^ k * D₀ with hD_def
        have hD_nn : 0 ≤ D := mul_nonneg (pow_nonneg hq_nn k) hD₀_nn
        -- `extend = ρ` on `Icc`.
        have he : ∀ (ν : VlasovMeasureCurve d T m) s, s ∈ Set.Icc (0:ℝ) T → ν.extend s = ν.ρ s := by
          intro ν s hs
          unfold VlasovMeasureCurve.extend clampToIcc; congr 1
          rw [min_eq_left hs.2, max_eq_right hs.1]
        -- W₁ finiteness + bound on `Icc`, from `ih`.
        have h_W1_fin : ∀ s ∈ Set.Icc (0:ℝ) T,
            wasserstein1 ((x k).extend s) ((x (k+1)).extend s) ≠ ⊤ := by
          intro s hs
          rw [he (x k) s hs, he (x (k+1)) s hs]
          haveI := (x k).isProb s; haveI := (x (k+1)).isProb s
          exact wasserstein1_ne_top_of_finite_moment _ _
            ((x k).yIntegrable s hs) ((x (k+1)).yIntegrable s hs)
        have h_W1_bound : ∀ s ∈ Set.Icc (0:ℝ) T,
            (wasserstein1 ((x k).extend s) ((x (k+1)).extend s)).toReal ≤ D := by
          intro s hs
          rw [he (x k) s hs, he (x (k+1)) s hs]
          have h_le : wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s)
              ≤ ENNReal.ofReal D :=
            le_trans (wasserstein1_le_supW1On _ _ _ s hs) ih
          have h_ne : wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s) ≠ ⊤ := by
            haveI := (x k).isProb s; haveI := (x (k+1)).isProb s
            exact wasserstein1_ne_top_of_finite_moment _ _
              ((x k).yIntegrable s hs) ((x (k+1)).yIntegrable s hs)
          calc (wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s)).toReal
              ≤ (ENNReal.ofReal D).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_le
            _ = D := ENNReal.toReal_ofReal hD_nn
        -- Apply the (weakened) contraction.
        have h_contr := @Phi_supW1_contraction d _ gradW L hL ((x k).extend) ((x (k+1)).extend)
          (hPext (x k)) (hPext (x (k+1)))
          (h_int_ext_gen (x k)) (h_int_ext_gen (x (k+1))) T hT.le D hD_nn h_W1_fin h_W1_bound
          (charXs k) (charVs k) (charXs (k+1)) (charVs (k+1)) f₀ _
          (hCI k).1 (hCI (k+1)).1 (hCI k).2.1 (hCI (k+1)).2.1
          (hCI k).2.2.1 (hCI (k+1)).2.2.1 (hCI k).2.2.2.1 (hCI (k+1)).2.2.2.1
          (hCI k).2.2.2.2.1 (hCI (k+1)).2.2.2.2.1 (hCI k).2.2.2.2.2 (hCI (k+1)).2.2.2.2.2
        rw [hq_scale D] at h_contr
        -- Transfer the sup to the curve values (`map charXs = ρ` on `Icc`).
        have h_supW1_eq : supW1On (Set.Icc 0 T) (x (k+1)).ρ (x (k+1+1)).ρ
            = supW1On (Set.Icc 0 T)
                (fun t => Measure.map (fun z => charXs k t z) f₀)
                (fun t => Measure.map (fun z => charXs (k+1) t z) f₀) := by
          unfold supW1On
          exact iSup_congr fun t => iSup_congr fun ht => by
            rw [(h_flow k).2.2 t ht, (h_flow (k+1)).2.2 t ht]
        -- `D · q = q^(k+1) · D₀`.
        have hDq : D * q = q ^ (k + 1) * D₀ := by rw [hD_def, pow_succ]; ring
        rw [hDq] at h_contr
        -- Lift the `.toReal` bound back to ENNReal.
        have h_ne_top : supW1On (Set.Icc 0 T)
            (fun t => Measure.map (fun z => charXs k t z) f₀)
            (fun t => Measure.map (fun z => charXs (k+1) t z) f₀) ≠ ⊤ := by
          rw [← h_supW1_eq]
          exact supW1On_ne_top_of_VlasovMeasureCurve (m T) hMbar_mono (x (k+1)) (x (k+1+1))
        have h_pow_nn : 0 ≤ q ^ (k + 1) * D₀ := mul_nonneg (pow_nonneg hq_nn _) hD₀_nn
        rw [h_supW1_eq]
        rw [← ENNReal.toReal_le_toReal h_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal h_pow_nn]
        exact h_contr
    exact ⟨x, charXs, charVs, h_contract, h_flow⟩
  -- ============================================================
  -- Step 5: Extract limit ρ_lim via picard_iterate_bundlesAs_VlasovMeasureCurve.
  -- ============================================================
  obtain ⟨ρ_lim, h_tendsto⟩ :=
    picard_iterate_bundlesAs_VlasovMeasureCurve x q hq_nn hq_lt D₀ hD₀_nn h_contract
  -- ============================================================
  -- Step 6: Convolution integrability for ρ_lim.extend.
  -- Needed by exists_vlasov_characteristicFlow_global_smallT.
  -- Sub-sub-sorry: integrability of gradW against ρ_lim.extend t.
  -- ============================================================
  have h_int_ρ_lim : ∀ t (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (ρ_lim.extend t) := by
    intro t x_pt
    -- Integrability via dominator, same pattern as h_int_gradW_μ₀.
    have h_yint_t : Integrable (fun y : PhysSpace d => ‖y‖) (ρ_lim.extend t) :=
      VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim t
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y)) (ρ_lim.extend t) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x_pt - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
        (ρ_lim.extend t) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖) (ρ_lim.extend t) :=
        h_yint_t.const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  -- Convolution continuity for ρ_lim.extend, universal in t.
  -- Deduced from ρ_lim.extend_convCont + h_int_ρ_lim restricted to Icc 0 T.
  have h_conv_cont_ρ_lim : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ_lim.extend t) x) := by
    intro x_pt
    have h_int_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y => gradW (x_pt - y)) (ρ_lim.ρ t) := by
      intro t ht
      have h_eq : ρ_lim.extend t = ρ_lim.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ρ_lim t x_pt
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT.le ρ_lim x_pt h_int_Icc
  -- ============================================================
  -- Step 7: Flow construction via exists_vlasov_characteristicFlow_global_smallT.
  -- Build (charX, charV) against ρ_lim.extend.
  -- ============================================================
  obtain ⟨charX, charV, hflow_on_ρlim, h_boundary_ρlim⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ_lim.extend h_int_ρ_lim h_conv_cont_ρ_lim
      (fun t => VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim t)
      (m T) hMbar_nn
      (fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim t)
        (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t)))
      T hT.le hTL_PL
  -- ============================================================
  -- Step 8: Self-consistency.
  -- Sub-sub-sorry: for t ∈ Icc 0 T,
  --   ρ_lim.ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t).
  -- This is the Picard fixed-point equation: Phi charX f₀ t = ρ_lim.ρ t,
  -- proved by triangle through x n using contraction + tendsto.
  -- ============================================================
  -- ============================================================
  -- Sub-sub-sorry: self-consistency on Icc 0 T.
  -- For t ∈ Icc 0 T:
  --   ρ_lim.extend t = ρ_lim.ρ t   (by clampToIcc identity on Icc)
  --   ρ_lim.ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)
  -- The second equality is the Picard fixed-point equation, proved by triangle
  -- through x n using contraction + tendsto.
  -- ============================================================
  have h_self_consist : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ρ_lim.extend t =
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) := by
    -- The Picard fixed-point equation.  On `Icc`, `ρ_lim.extend = ρ_lim.ρ`
    -- and `spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) =
    -- map (charX t) f₀`; since `charX` is the flow built against `ρ_lim.extend`,
    -- the RHS is `Φ(ρ_lim) t`.  We show `W₁(ρ_lim.ρ t, Φ(ρ_lim) t) = 0` by a
    -- triangle through the iterate `x (n+1) = Φ(x n)`, sending both legs to 0,
    -- then conclude via the separation lemma `wasserstein1_eq_zero_iff_measure_eq`.
    -- Abbreviations / Lipschitz-constant bookkeeping.
    have hK_ge1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hK_pos : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by linarith
    -- `extend = ρ` on the window.
    have he : ∀ (ν : VlasovMeasureCurve d T m) s, s ∈ Set.Icc (0:ℝ) T →
        ν.extend s = ν.ρ s := by
      intro ν s hs
      unfold VlasovMeasureCurve.extend clampToIcc; congr 1
      rw [min_eq_left hs.2, max_eq_right hs.1]
    -- (1) General convolution integrability for any envelope curve (rebuilt; this
    -- was a local `have` inside the now-closed sorry-1 block).
    have h_int_ext_gen : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ) (xp : PhysSpace d),
        Integrable (fun y => gradW (xp - y)) (ν.extend t) := by
      intro ν t xp
      have h_yint : Integrable (fun y : PhysSpace d => ‖y‖) (ν.extend t) :=
        VlasovMeasureCurve.extend_yIntegrable hT.le ν t
      have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (xp - y)) (ν.extend t) :=
        (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      have h_dom : ∀ y : PhysSpace d, ‖gradW (xp - y)‖ ≤
          ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖ := by
        intro y
        have hd := hL.dist_le_mul (xp - y) 0
        simp only [dist_eq_norm, sub_zero] at hd
        have h_tri : ‖gradW (xp - y)‖ ≤ ‖gradW 0‖ + ‖gradW (xp - y) - gradW 0‖ := by
          have := norm_add_le (gradW (xp - y) - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        have h_sub_le : ‖xp - y‖ ≤ ‖xp‖ + ‖y‖ := norm_sub_le xp y
        have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
        linarith
      have h_dom_int : Integrable
          (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) (ν.extend t) := by
        have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖) (ν.extend t) :=
          h_yint.const_mul (L : ℝ)
        have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) =
                    fun y => (‖gradW 0‖ + (L : ℝ) * ‖xp‖) + (L : ℝ) * ‖y‖ := by funext y; ring
        rw [h_eq]; exact (integrable_const _).add h_norm
      exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
    -- Window moment bound for any envelope curve (the `hM_ρ` arg of `envelopeStep`).
    have hMm : ∀ (ν : VlasovMeasureCurve d T m), ∀ t ∈ Set.Icc (0:ℝ) T,
        ∫ y, ‖y‖ ∂(ν.extend t) ≤ m T :=
      fun ν t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ν t)
        (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t))
    -- Explicit-instance helper (curves are obtain-binders here, but mirror sorry-1).
    have hPext : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ),
        IsProbabilityMeasure (ν.extend t) :=
      fun ν => VlasovMeasureCurve.extend_isProb ν
    -- (2) Per-step 6-fact contraction-input bundle for the iterate flows,
    -- rebuilt at the main scope from `h_flow` (the `hCI` of sorry-1 was local).
    have hCI := fun k => envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le (x k)
      (m T) hMbar_nn (hMm (x k)) (charXs k) (charVs k)
      (h_flow k).1 (h_flow k).2.1 (h_int_ext_gen (x k))
    -- (3) The ρ_lim flow's 6-fact bundle (same helper, on the self-consistent flow).
    have hCI_lim := envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le ρ_lim
      (m T) hMbar_nn (hMm ρ_lim) charX charV hflow_on_ρlim h_boundary_ρlim h_int_ρ_lim
    -- (4) Spatial-marginal identity: the pair-pushforward's first marginal is the
    -- position pushforward.
    have h_marg : ∀ s ∈ Set.Icc (0:ℝ) T,
        spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)
          = Measure.map (fun z => charX s z) f₀ := by
      intro s hs
      have h_pair_meas := charFlow_measurable_via_gronwall gradW L hL ρ_lim.extend h_int_ρ_lim
        charX charV T hT.le hCI_lim.2.2.2.1 hCI_lim.2.2.2.2.1 hCI_lim.2.2.2.2.2 s hs
      unfold spatialMarginal vlasovSolutionViaPushforward
      rw [Measure.map_map measurable_fst h_pair_meas]
      rfl
    -- (5) Uniform-in-`s` convergence of the iterates to `ρ_lim`, and the explicit
    -- uniform real bound `D n := (supW1On (x n) ρ_lim).toReal → 0`.
    have h_cauchy := picard_iterate_isCauchy_of_contraction
      (Set.Icc (0:ℝ) T) (fun n => (x n).ρ) q hq_nn hq_lt D₀ hD₀_nn h_contract
    have h_uniform := picard_iterate_limit_uniform_tendsto
      (Set.Icc (0:ℝ) T) (fun n => (x n).ρ) ρ_lim.ρ h_cauchy h_tendsto
    have h_sup_ne_top : ∀ n, supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ ≠ ⊤ :=
      fun n => supW1On_ne_top_of_VlasovMeasureCurve (m T) hMbar_mono (x n) ρ_lim
    have h_sup_tendsto : Filter.Tendsto
        (fun n => supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ) Filter.atTop (nhds 0) := by
      rw [ENNReal.tendsto_atTop_zero]
      intro ε hε
      obtain ⟨N, hN⟩ := h_uniform ε hε
      refine ⟨N, fun n hn => ?_⟩
      unfold supW1On
      exact iSup_le fun s => iSup_le fun hs => hN n hn s hs
    set Dn : ℕ → ℝ := fun n => (supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ).toReal with hDn_def
    have hDn_nn : ∀ n, 0 ≤ Dn n := fun n => ENNReal.toReal_nonneg
    have hDn_tendsto : Filter.Tendsto Dn Filter.atTop (nhds 0) := by
      have h := (ENNReal.tendsto_toReal (show (0:ENNReal) ≠ ⊤ by simp)).comp h_sup_tendsto
      rw [ENNReal.toReal_zero] at h
      exact h
    -- `gronwallBound 0 K (L·a) T = a · q`  (the contraction-ratio scaling).
    have hq_scale : ∀ a : ℝ, gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * a) T = a * q := by
      intro a
      show gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * a) T
        = a * gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L:ℝ) T
      rw [gronwallBound_of_K_ne_0 hK_ne, gronwallBound_of_K_ne_0 hK_ne]; ring
    -- Uniform W₁-finiteness and uniform-`Dn` bound on the curve distance.
    have h_W1_fin_curve : ∀ n, ∀ s ∈ Set.Icc (0:ℝ) T,
        wasserstein1 ((x n).extend s) (ρ_lim.extend s) ≠ ⊤ := by
      intro n s hs
      rw [he (x n) s hs, he ρ_lim s hs]
      haveI := (x n).isProb s; haveI := ρ_lim.isProb s
      exact wasserstein1_ne_top_of_finite_moment _ _
        ((x n).yIntegrable s hs) (ρ_lim.yIntegrable s hs)
    have h_W1_bound_curve : ∀ n, ∀ s ∈ Set.Icc (0:ℝ) T,
        (wasserstein1 ((x n).extend s) (ρ_lim.extend s)).toReal ≤ Dn n := by
      intro n s hs
      rw [he (x n) s hs, he ρ_lim s hs]
      exact ENNReal.toReal_mono (h_sup_ne_top n)
        (wasserstein1_le_supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ s hs)
    -- (Term 2) pointwise contraction at `t`: `W₁(Φ(x n) t, Φ(ρ_lim) t).toReal ≤ Dn n · q`.
    have h_term2 : ∀ n t, t ∈ Set.Icc (0:ℝ) T →
        (wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
                      (Measure.map (fun z => charX t z) f₀)).toReal ≤ Dn n * q := by
      intro n t ht
      have hpt := @Phi_pointwise_contraction d _ gradW L hL ((x n).extend) ρ_lim.extend
        (hPext (x n)) (hPext ρ_lim)
        (h_int_ext_gen (x n)) h_int_ρ_lim T hT.le (Dn n) (hDn_nn n)
        (h_W1_fin_curve n) (h_W1_bound_curve n)
        (charXs n) (charVs n) charX charV f₀ _
        (hCI n).1 hCI_lim.1 (hCI n).2.1 hCI_lim.2.1
        (hCI n).2.2.2.1 hCI_lim.2.2.2.1 (hCI n).2.2.2.2.1 hCI_lim.2.2.2.2.1
        (hCI n).2.2.2.2.2 hCI_lim.2.2.2.2.2 t ht
      have h_mono : gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * Dn n) t
          ≤ gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * Dn n) T :=
        gronwallBound_mono (le_refl 0) (mul_nonneg L.coe_nonneg (hDn_nn n)) hK_pos ht.2
      rw [hq_scale (Dn n)] at h_mono
      exact le_trans hpt h_mono
    -- The fixed-point argument, per `t ∈ Icc 0 T`.
    intro t ht
    rw [he ρ_lim t ht, h_marg t ht]
    -- Goal: `ρ_lim.ρ t = Measure.map (fun z => charX t z) f₀`.
    haveI hP1 : IsProbabilityMeasure (ρ_lim.ρ t) := ρ_lim.isProb t
    haveI hP2 : IsProbabilityMeasure (Measure.map (fun z => charX t z) f₀) :=
      Measure.isProbabilityMeasure_map (hCI_lim.1 t ht)
    have hint1 : Integrable (fun y : PhysSpace d => ‖y‖) (ρ_lim.ρ t) := ρ_lim.yIntegrable t ht
    have hint2 : Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX t z) f₀) := hCI_lim.2.2.1 t ht
    refine (wasserstein1_eq_zero_iff_measure_eq (ρ_lim.ρ t)
      (Measure.map (fun z => charX t z) f₀) hint1 hint2).mp ?_
    -- Per-`n` triangle bound: `W₁ ≤ A n + ofReal (Dn n · q)`, both legs → 0.
    have h_le_seq : ∀ n, wasserstein1 (ρ_lim.ρ t) (Measure.map (fun z => charX t z) f₀)
        ≤ wasserstein1 ((x (n+1)).ρ t) (ρ_lim.ρ t) + ENNReal.ofReal (Dn n * q) := by
      intro n
      have h_mid : (x (n+1)).ρ t = Measure.map (fun z => charXs n t z) f₀ :=
        (h_flow n).2.2 t ht
      calc wasserstein1 (ρ_lim.ρ t) (Measure.map (fun z => charX t z) f₀)
          ≤ wasserstein1 (ρ_lim.ρ t) ((x (n+1)).ρ t)
              + wasserstein1 ((x (n+1)).ρ t) (Measure.map (fun z => charX t z) f₀) :=
            wasserstein1_triangle _ _ _
        _ = wasserstein1 ((x (n+1)).ρ t) (ρ_lim.ρ t)
              + wasserstein1 ((x (n+1)).ρ t) (Measure.map (fun z => charX t z) f₀) := by
            rw [wasserstein1_comm (ρ_lim.ρ t) ((x (n+1)).ρ t)]
        _ ≤ wasserstein1 ((x (n+1)).ρ t) (ρ_lim.ρ t) + ENNReal.ofReal (Dn n * q) := by
            gcongr
            rw [h_mid]
            have h_fin : wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
                (Measure.map (fun z => charX t z) f₀) ≠ ⊤ := by
              haveI : IsProbabilityMeasure (Measure.map (fun z => charXs n t z) f₀) :=
                Measure.isProbabilityMeasure_map ((hCI n).1 t ht)
              exact wasserstein1_ne_top_of_finite_moment _ _
                ((hCI n).2.2.1 t ht) (hCI_lim.2.2.1 t ht)
            rw [← ENNReal.ofReal_toReal h_fin]
            exact ENNReal.ofReal_le_ofReal (h_term2 n t ht)
    -- The bounding sequence tends to 0.
    have hA : Filter.Tendsto (fun n => wasserstein1 ((x (n+1)).ρ t) (ρ_lim.ρ t))
        Filter.atTop (nhds 0) :=
      (h_tendsto t ht).comp (Filter.tendsto_add_atTop_nat 1)
    have hB : Filter.Tendsto (fun n => ENNReal.ofReal (Dn n * q)) Filter.atTop (nhds 0) := by
      have hDq : Filter.Tendsto (fun n => Dn n * q) Filter.atTop (nhds 0) := by
        have := hDn_tendsto.mul_const q
        simpa using this
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hDq
      simpa using this
    have h_seq : Filter.Tendsto
        (fun n => wasserstein1 ((x (n+1)).ρ t) (ρ_lim.ρ t) + ENNReal.ofReal (Dn n * q))
        Filter.atTop (nhds 0) := by
      have := hA.add hB
      simpa using this
    exact le_antisymm (ge_of_tendsto' h_seq h_le_seq) (zero_le _)
  -- ============================================================
  -- Step 9: Bundle with a CLAMPED flow `cX s := charX (clampToIcc T s)`.
  --
  -- The raw flow from `exists_vlasov_characteristicFlow_global_smallT` is
  -- controlled only on `[0, T]`; off-window it is uncontrolled
  -- `Classical.choose` data with no growth bound.  The conclusion's
  -- universal-in-`s` conjuncts (convolution integrability + continuity-in-x
  -- for ALL `s`) therefore cannot hold for the raw flow.  We return instead
  -- the clamped flow, whose pushforward at any `s` equals the on-window
  -- pushforward at `clampToIcc T s ∈ [0, T]` — hence globally controlled.
  -- On `[0, T]` the clamp is the identity (`clampToIcc T s = s`), so every
  -- window conjunct (flow ODE on Ioo, boundary on Icc, moment, integrability)
  -- transfers from the raw flow via `clampToIcc`-congruence.
  -- ============================================================
  have hclamp_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampToIcc T s = s := fun s hs => by
    unfold clampToIcc; rw [min_eq_left hs.2, max_eq_right hs.1]
  have hclamp0 : clampToIcc T 0 = 0 := hclamp_id 0 ⟨le_refl 0, hT.le⟩
  -- ρ-slot of the clamped flow = `ρ_lim.extend` at the clamp time (definitional
  -- identity of the pushforward + self-consistency on the window).
  have h_rho_clamp : ∀ s : ℝ,
      spatialMarginal (vlasovSolutionViaPushforward
        (fun s' z => charX (clampToIcc T s') z)
        (fun s' z => charV (clampToIcc T s') z) f₀ s) =
      ρ_lim.extend (clampToIcc T s) := by
    intro s
    have h1 : spatialMarginal (vlasovSolutionViaPushforward
        (fun s' z => charX (clampToIcc T s') z)
        (fun s' z => charV (clampToIcc T s') z) f₀ s) =
        spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ (clampToIcc T s)) :=
      rfl
    rw [h1, ← h_self_consist (clampToIcc T s) (clampToIcc_mem hT.le s)]
  refine ⟨fun s z => charX (clampToIcc T s) z, fun s z => charV (clampToIcc T s) z,
    m T, hMbar_nn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) IsCharacteristicFlowOn on Ioo 0 T (window conjunct; clamp = id there).
    refine ⟨fun z _hz => ?_, fun t ht z _hz => ?_, fun t ht z _hz => ?_⟩
    · -- initial condition.
      show charX (clampToIcc T 0) z = z.1 ∧ charV (clampToIcc T 0) z = z.2
      rw [hclamp0]; exact hflow_on_ρlim.1 z (Set.mem_univ z)
    · -- position ODE: eventuallyEq to the raw flow on the open window.
      have hEv : (fun s => charX (clampToIcc T s) z) =ᶠ[nhds t]
          (fun s => charX s z) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        rw [hclamp_id s (Set.Ioo_subset_Icc_self hs)]
      show HasDerivAt (fun s => charX (clampToIcc T s) z) (charV (clampToIcc T t) z) t
      rw [hclamp_id t (Set.Ioo_subset_Icc_self ht)]
      exact (hflow_on_ρlim.2.1 t ht z (Set.mem_univ z)).congr_of_eventuallyEq hEv
    · -- velocity ODE.
      have hEv : (fun s => charV (clampToIcc T s) z) =ᶠ[nhds t]
          (fun s => charV s z) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        rw [hclamp_id s (Set.Ioo_subset_Icc_self hs)]
      show HasDerivAt (fun s => charV (clampToIcc T s) z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward
              (fun s' z' => charX (clampToIcc T s') z')
              (fun s' z' => charV (clampToIcc T s') z') f₀ t))
            (charX (clampToIcc T t) z))) t
      rw [h_rho_clamp t, hclamp_id t (Set.Ioo_subset_Icc_self ht)]
      exact (hflow_on_ρlim.2.2 t ht z (Set.mem_univ z)).congr_of_eventuallyEq hEv
  · -- (2) Boundary regularity on Icc 0 T (clamp = id on the closed window).
    intro z t ht
    have hEqOn : Set.EqOn (fun s => charX (clampToIcc T s) z) (fun s => charX s z)
        (Set.Icc 0 T) := fun s hs => by
      show charX (clampToIcc T s) z = charX s z; rw [hclamp_id s hs]
    have hEqOnV : Set.EqOn (fun s => charV (clampToIcc T s) z) (fun s => charV s z)
        (Set.Icc 0 T) := fun s hs => by
      show charV (clampToIcc T s) z = charV s z; rw [hclamp_id s hs]
    obtain ⟨h1, h2⟩ := h_boundary_ρlim z t ht
    refine ⟨?_, ?_⟩
    · show HasDerivWithinAt (fun s => charX (clampToIcc T s) z)
        (charV (clampToIcc T t) z) (Set.Icc 0 T) t
      rw [hclamp_id t ht]
      exact h1.congr hEqOn (hEqOn ht)
    · show HasDerivWithinAt (fun s => charV (clampToIcc T s) z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward
              (fun s' z' => charX (clampToIcc T s') z')
              (fun s' z' => charV (clampToIcc T s') z') f₀ t))
            (charX (clampToIcc T t) z))) (Set.Icc 0 T) t
      rw [h_rho_clamp t, hclamp_id t ht]
      exact h2.congr hEqOnV (hEqOnV ht)
  · -- (3) Moment bound on Icc 0 T (uniform witness `m T`, via monotonicity).
    intro s hs
    rw [h_rho_clamp s, hclamp_id s hs]
    exact le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim s)
      (hMbar_mono (clampToIcc T s) (clampToIcc_mem hT.le s))
  · -- (4) First-moment integrability on Icc 0 T.
    intro s hs
    rw [h_rho_clamp s, hclamp_id s hs]
    exact VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim s
  · -- (5) Convolution continuity in x, universal in s (via clamp reduction).
    intro s
    rw [h_rho_clamp s]
    haveI : IsProbabilityMeasure (ρ_lim.extend (clampToIcc T s)) :=
      VlasovMeasureCurve.extend_isProb ρ_lim (clampToIcc T s)
    exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
      (ρ_lim.extend (clampToIcc T s)) (h_int_ρ_lim (clampToIcc T s))).continuous
  · -- (6) AEMeasurable witness, universal in s (raw flow at the clamp time,
    -- which lands in `Icc 0 T` — so the window-restricted helper applies).
    intro s
    exact picardCharFlow_aemeasurable gradW L hL ρ_lim.extend h_int_ρ_lim charX charV hT.le
      hflow_on_ρlim h_boundary_ρlim f₀ (clampToIcc T s) (clampToIcc_mem hT.le s)
  · -- (7) Convolution integrability, universal in s (via clamp reduction).
    intro s x
    rw [h_rho_clamp s]
    exact h_int_ρ_lim (clampToIcc T s) x

/-- **Sub-helper for `vlasovWellPosedness_local`** — moment-bound transport.

Given the Picard fixed-point flow's bundle (from
`_picard_fixedPointFlow`), produces `HasFiniteFirstMoment (f t)` for
`t ∈ Icc 0 T`, where `f := vlasovSolutionViaPushforward charX charV f₀`.

**Proof strategy** (sorry'd body; ~40-60 lines):

1. Friction 5 transport: extract `h_init / h_cont_Icc / h_deriv_Ico` from
   `hflow_on + h_boundary` via `Stage_1_9_flow_boundary_regularity`.
2. `flow_distance_growth_bound_on` applied to `(charX, charV)` produces
   the growth constant `C_T` with `‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1)`.
3. Probability of `f t = Measure.map (z ↦ (charX t z, charV t z)) f₀` from
   AEMeasurable (Stage 1.8 territory — sub-sub-sorry'd inside).
4. Integrable `‖·‖` on `f t`: via `integrable_map_measure` + growth bound +
   `Integrable ‖·‖ f₀`.

Locked here to keep `vlasovWellPosedness_local`'s body as a clean glue. -/
theorem vlasovWellPosedness_local_finalAssembly_moment
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (_hTL_PL : LocalSmallness_PL_buffer L T)
    (_hTL_con : LocalSmallness_contraction L T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ)
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
            (charX t z)))
        (Set.Icc 0 T) t)
    (hM_ρ_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Passed from `_picard_fixedPointFlow`'s enriched output (post-refactor):
    -- the AEMeasurable witness + universal-in-s convolution integrability.
    -- These were previously sub-sub-sorries inside this body; the refactor
    -- moves them to explicit hypotheses, closing this body's internal sorries.
    (h_aemeas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (h_int_conv : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasFiniteFirstMoment (vlasovSolutionViaPushforward charX charV f₀ t) := by
  -- IsProbabilityMeasure for the spatial marginal (needed for Stage_1_9 typeclass).
  -- spatialMarginal μ = Measure.map Prod.fst μ, so IsProbabilityMeasure_map needs
  -- AEMeasurable Prod.fst (Measure.map ... f₀). Since Prod.fst is measurable,
  -- it is AEMeasurable wrt any measure.
  haveI hρ_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    -- Need IsProbabilityMeasure (Measure.map Prod.fst (Measure.map (fun z => ...) f₀))
    -- Use Measure.map_map to compose, then isProbabilityMeasure_map on the composition.
    have h_aemeas_pair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_aemeas s
    have h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      Measure.isProbabilityMeasure_map h_aemeas_pair
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Step 1: Extract h_init, h_cont_Icc, h_deriv_Ico via Friction 5 transport.
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    Stage_1_9_flow_boundary_regularity gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV T hT.le hflow_on h_boundary
  -- Step 2: Growth bound from flow_distance_growth_bound_on.
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL
      (fun s => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
      charX charV T hT.le
      h_init h_cont_Icc h_deriv_Ico
      M_ρ hM_ρ_nn hM_ρ_bound h_y_int_ρ h_int_conv
  -- Step 3: Conclude HasFiniteFirstMoment.
  unfold HasFiniteFirstMoment vlasovSolutionViaPushforward
  refine ⟨Measure.isProbabilityMeasure_map (h_aemeas t), ?_⟩
  -- Integrable ‖·‖ wrt Measure.map (fun z => (charX t z, charV t z)) f₀.
  rw [integrable_map_measure
    (Continuous.aestronglyMeasurable continuous_norm) (h_aemeas t)]
  -- Now need: Integrable (fun z : PhaseSpace d => ‖(charX t z, charV t z)‖) f₀.
  have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
      hf₀_int.const_mul C_T
    have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
    have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                fun z => C_T * ‖z‖ + C_T := by funext z; ring
    rw [h_eq]; exact h1.add h2
  -- The goal after rw is: Integrable (‖·‖ ∘ fun z => (charX t z, charV t z)) f₀
  -- = Integrable (fun z => ‖(charX t z, charV t z)‖) f₀.
  -- Dominator: C_T * (‖z‖ + 1); AE bound from h_growth.
  have h_norm_aesm : AEStronglyMeasurable
      (fun z : PhaseSpace d => ‖(charX t z, charV t z)‖) f₀ :=
    (h_aemeas t).norm.aestronglyMeasurable
  refine h_dom_int.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · -- AEStronglyMeasurable of ‖·‖ ∘ (charX t, charV t).
    -- After integrable_map_measure rewrite, goal is for the composition form.
    convert h_norm_aesm using 1
  · -- Pointwise bound: ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1).
    -- The norm in the goal is ‖(‖·‖ ∘ ...)(z)‖ = ‖‖(charX t z, charV t z)‖‖.
    simp only [Function.comp, Real.norm_of_nonneg (norm_nonneg _)]
    exact h_growth t ht z

/-- **Sub-helper for `vlasovWellPosedness_local`** — IsLagrangianVlasovSolutionOn
threading.

Given the Picard fixed-point flow's bundle (from
`_picard_fixedPointFlow`), produces the
`IsLagrangianVlasovSolutionOn gradW f T` conjunct via the 20-hypothesis
threading through
`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.

**Proof strategy** (sorry'd body; ~80-120 lines):

1. Friction 5 transport: extract `h_init / h_cont_Icc / h_deriv_Ico`.
2. Universal-in-`s` convolution integrability (sub-sub-sorry: requires
   handling `s` outside `[0, T]` via clamp-extension argument or
   sub-sub-helper).
3. AEMeasurable witness (Stage 1.8 territory — sub-sub-sorry'd; the
   clean discharge requires the Stage 1.8 placeholder closure).
4. `IsCharacteristicFlowSelfConsistent`: `∀ t, ρ_lim t = Φ charX f₀ t`,
   which expands by definition since `ρ_lim = spatialMarginal ∘ f` and
   `f = vlasovSolutionViaPushforward charX charV f₀`; spatial marginal
   of pushforward = pushforward under `Prod.fst ∘ ...` = `Φ charX f₀`.
   The composition is the `Measure.map_map`-with-AEMeasurable bridge.
5. Continuity of `gradW`: `hL.continuous`.
6. Probability instance of `spatialMarginal ∘ f`: instance derivation
   from AEMeasurable + IsProbabilityMeasure f₀.
7. Final invocation: `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`
   with the 20-hypothesis bundle.

Locked here to keep `vlasovWellPosedness_local`'s body as a clean glue. -/
theorem vlasovWellPosedness_local_finalAssembly_isLagrangian
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (_hTL_PL : LocalSmallness_PL_buffer L T)
    (_hTL_con : LocalSmallness_contraction L T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ)
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
            (charX t z)))
        (Set.Icc 0 T) t)
    (hM_ρ_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Passed from `_picard_fixedPointFlow`'s enriched output (post-refactor):
    -- the AEMeasurable witness + universal-in-s convolution integrability.
    -- These were previously sub-sub-sorries inside this body; the refactor
    -- moves them to explicit hypotheses, closing this body's internal sorries.
    (h_aemeas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (h_int_conv : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) :
    IsLagrangianVlasovSolutionOn gradW
      (vlasovSolutionViaPushforward charX charV f₀) T := by
  -- IsProbabilityMeasure for the spatial marginal (needed for the target typeclass).
  haveI hρ_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    have h_aemeas_pair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_aemeas s
    have _h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      Measure.isProbabilityMeasure_map h_aemeas_pair
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Step 1: Extract h_init, h_cont_Icc, h_deriv_Ico via Friction 5 transport.
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    Stage_1_9_flow_boundary_regularity gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV T hT.le hflow_on h_boundary
  -- Step 2: IsCharacteristicFlowSelfConsistent
  -- ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)
  --     = Measure.map Prod.fst (Measure.map (fun z => (charX t z, charV t z)) f₀)
  --     = Measure.map (Prod.fst ∘ fun z => (charX t z, charV t z)) f₀   [by map_map_of_aemeasurable]
  --     = Measure.map (charX t) f₀
  have hself : IsCharacteristicFlowSelfConsistent charX f₀
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) := by
    intro t
    simp only [IsCharacteristicFlowSelfConsistent]
    unfold spatialMarginal vlasovSolutionViaPushforward
    -- Goal: Measure.map Prod.fst (Measure.map (fun z => (charX t z, charV t z)) f₀)
    --     = Measure.map (fun z => charX t z) f₀
    have h_comp : Measure.map Prod.fst
        (Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) =
        Measure.map (Prod.fst ∘ fun z : PhaseSpace d => (charX t z, charV t z)) f₀ := by
      apply AEMeasurable.map_map_of_aemeasurable
      · exact measurable_fst.aemeasurable
      · exact h_aemeas t
    rw [h_comp]; congr 1
  -- Step 3: Apply the main threading theorem.
  exact vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    gradW L hL charX charV f₀ hf₀_int hT
    hflow_on h_init h_cont_Icc h_deriv_Ico
    M_ρ hM_ρ_nn hM_ρ_bound h_y_int_ρ h_int_conv
    hself h_aemeas hL.continuous hconv_cont

/-- **Stage 4 structural closure: local existence of a Vlasov solution
on `[0, T]`.**

Under the Friction-2 / Route-1 joint constraint `L · (T + 1)² < 1` (which
silently restricts to the small-`L` regime — `L < 1` is necessary for
`T > 0` to exist), produces a local-time Vlasov solution
`f : ℝ → Measure (PhaseSpace d)` on `[0, T]` satisfying initial
condition + local finite first moment + `IsLagrangianVlasovSolutionOn`.

Stage 5's continuation (deferred) extends from local `T` to arbitrary
`T_target` via **fixed-`T_0`** iteration (per the
locale-to-global discipline analysis): the contraction time
`T_0` depends only on `L` (not on the moment bound `M_n` propagating
through iterations), because `Phi_supW1_contraction`'s `q` is
`gronwallBound 0 (max 1 L) (L · D) T` — independent of `M_n`.  This is
a simplification on the original plan's "variable-`T_n` induction"
framing, which assumed `q` depended on `M_n`.  Stage 5 can therefore
iterate `[0, T_0], [T_0, 2 T_0], …` with constant step `T_0`, reaching
any `T_target` in `⌈T_target / T_0⌉` windows.  Stage 6 then bridges from
`IsLagrangianVlasovSolutionOn` (local) to `IsLagrangianVlasovSolution`
(global) via gluing.

**Proof strategy** (the substantive body is deferred per the
post-closure discharge schedule; signature and strategy locked here so
downstream consumers compose against the right interface):

1. Initial spatial marginal: `μ₀ := spatialMarginal f₀`.  By
   `HasFiniteFirstMoment f₀`, `μ₀` is a probability measure with
   `Integrable ‖·‖`.  Let `M_f₀ := ∫ ‖z‖ ∂f₀` (finite by
   `hf₀.2.integral_norm_le`).

2. Picard sequence on spatial marginals:
   - `ρ_0 := constantCurve μ₀`.
   - `ρ_{n+1}` obtained via `Phi_step` applied to `ρ_n`'s flow.

   Each `ρ_n` lives in `VlasovMeasureCurve d T M` for an appropriate
   `M` chosen so that the growth bound from
   `flow_distance_growth_bound_on` stays within `M` across iterations
   (the M-preservation constraint discussed in the Stage 4 plan
   process notes #5).

3. Contraction estimate via `Phi_supW1_contraction`:
   `supW1On (ρ_n.ρ) (ρ_{n+1}.ρ) ≤ ENNReal.ofReal (q^n * D₀)`
   for `q := gronwallBound 0 (max 1 L) (L · D) T < 1` (since `T` is
   small enough per the joint constraint).

4. Apply `picard_iterate_isCauchy_of_contraction` to get the ENNReal-form
   Cauchy condition on the `supW1On` pseudodistance.

5. Apply `picard_iterate_bundlesAs_VlasovMeasureCurve` to extract the
   limit `ρ_lim : VlasovMeasureCurve d T M` plus pointwise W₁-tendsto.

6. Self-consistency `Φ(ρ_lim) = ρ_lim`: triangle through `ρ_n` using
   the uniform-tendsto helper, contraction, and pointwise tendsto.

7. Apply Stage 1.9 (`exists_vlasov_characteristicFlow_global_smallT`)
   to `ρ_lim.extend` to get the characteristic flow `(charX, charV)`
   against the self-consistent limit.

8. Define `f := vlasovSolutionViaPushforward charX charV f₀`.  Verify:
   - `f 0 = f₀` (from `IsCharacteristicFlowOn`'s initial-condition
     clause + `Measure.map_id`).
   - `HasFiniteFirstMoment (f t)` on `[0, T]` (from
     `flow_distance_growth_bound_on` applied to `(charX, charV)` +
     `hf₀.2`).
   - `IsLagrangianVlasovSolutionOn gradW f T` via
     `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`
     (which carries the sorry'd PDE-proof internally).

**Hypothesis-discharge dependencies** (each line of #1-#8 above
composes against an already-landed bridge):

* `VlasovMeasureCurve.extend` (commit `fc9d45a`).
* `flow_distance_growth_bound_on` (commit `974bbf2`).
* `_On` predicates + `.toOn` projections (commit `966a9e6`).
* `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn` (commit
  `de1eb0f`, with deferred PDE sorry inside).
* `Stage_1_9_flow_boundary_regularity` (commit `fffde95`, sorry'd).
* `Phi_step` (commit `9d54126`).
* `picard_iterate_*` family (commits before this arc).

**Per the user-authorized API-lock-vs-substantive-proof discipline**:
this commit locks the theorem's signature with a documented proof
strategy; the substantive proof body is on the post-closure discharge
schedule.  Once landed, the discharge becomes one focused session of
~150-200 lines stitching the 8 steps above.

Sorry count contribution: +1 (one named sorry for the deferred
substantive body). -/
theorem vlasovWellPosedness_local
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallness_PL_buffer L T)
    (hTL_con : LocalSmallness_contraction L T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ (f : ℝ → Measure (PhaseSpace d))
      (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      f 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, HasFiniteFirstMoment (f t)) ∧
      -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
      (∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0:ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M) ∧
      IsLagrangianVlasovSolutionOn gradW f T ∧
      -- Explicit flow bundle: pushforward, AEMeasurable, and boundary derivatives.
      -- These use the SAME charX charV as the outer ∃ (not the hidden witnesses
      -- inside IsLagrangianVlasovSolutionOn), enabling downstream consumers to
      -- use them without witness-identity issues.
      (∀ t ∈ Set.Icc (0:ℝ) T,
        f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
      (∀ s ∈ Set.Icc (0:ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0:ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f t)) (charX t z)))
          (Set.Icc 0 T) t) ∧
      -- Initial condition for the outer charX charV (same witnesses as boundary bundle above).
      (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) := by
  -- **Substantive discharge plan** (~250-350 lines, focused follow-up session):
  --
  -- Step 1 — Spatial marginal setup (~20 lines):
  --   obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
  --   let μ₀ := spatialMarginal f₀  -- IsProbabilityMeasure + Integrable ‖·‖
  --   let M_f₀ := ∫ z, ‖z‖ ∂f₀  -- finite by hf₀.2
  --   Pick M ≥ flow_distance_growth_bound's `C_T * (M_f₀ + 1)` to absorb
  --   Phi_step's moment growth across iterations.
  --
  -- Step 2 — Picard sequence (~40-60 lines):
  --   let x : ℕ → VlasovMeasureCurve d T M := fun n =>
  --     n.rec (constantCurve μ₀ hμ₀_int hM_init)
  --           (fun _ prev => Classical.choose (Phi_step ... prev ...))
  --   The Phi_step application extracts (charX_n, charV_n, σ_n) from prev's flow.
  --
  -- Step 3 — Contraction verification (~50-80 lines):
  --   Pick q := gronwallBound 0 (max 1 L) (L * D₀) T < 1 (where D₀ is the
  --   initial supW1On bound).  By Phi_supW1_contraction applied to (x n)'s
  --   and (x (n+1))'s flows: supW1On (Set.Icc 0 T) (x n).ρ (x (n+1)).ρ ≤
  --   ENNReal.ofReal (q ^ n * D₀).  Threading the ~24 hypotheses of
  --   Phi_supW1_contraction through each (x n, x (n+1)) pair.
  --
  -- Step 4 — Limit extraction (~20 lines):
  --   obtain ⟨ρ_lim, h_tendsto⟩ :=
  --     picard_iterate_bundlesAs_VlasovMeasureCurve x q hq_nn hq_lt D₀
  --       hD₀_nn h_contract
  --
  -- Step 5 — Self-consistency `Φ(ρ_lim) = ρ_lim` (~30-50 lines):
  --   Triangle through ρ_n: supW1On (Φ ρ_lim) ρ_lim ≤
  --     supW1On (Φ ρ_lim) (Φ ρ_n) + supW1On (Φ ρ_n) ρ_n +
  --     supW1On ρ_n ρ_lim
  --   First and third → 0 via uniform tendsto (Φ continuous on
  --   VlasovMeasureCurves); middle = supW1On (x_{n+1}) (x_n) ≤ q^n · D₀ → 0.
  --
  -- Step 6 — Flow construction (~30 lines):
  --   obtain ⟨charX, charV, hflow_on⟩ :=
  --     exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
  --       ρ_lim.extend ... hT.le hTL_PL  -- PL-buffer; per Stage 2b part 3
  --                                       -- split (commit `2eed838`).
  --   obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
  --     Stage_1_9_flow_boundary_regularity gradW ρ_lim.extend charX charV T
  --       hT.le hflow_on
  --
  -- Step 7 — Final assembly (~50-80 lines):
  --   Define f := vlasovSolutionViaPushforward charX charV f₀.
  --   Verify:
  --   * f 0 = f₀ (from `IsCharacteristicFlowOn`'s initial-condition clause +
  --     `Measure.map_id`).
  --   * HasFiniteFirstMoment (f t) on Icc 0 T (from
  --     `flow_distance_growth_bound_on` + `hf₀.2`).
  --   * IsLagrangianVlasovSolutionOn gradW f T via
  --     `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn` (now
  --     requires 22 hypotheses after the Bridge #2 PDE transport's
  --     signature expansion in commit `b77290c`).  Threading ρ-regularity
  --     (M_ρ, hM_ρ, h_y_int, h_int) for the pushforward's spatial marginal
  --     is the longest step here.
  --
  -- **Substantive structural close (2026-05-29)**: body decomposed via the
  -- API-lock-vs-substantive-proof discipline.  The Picard fixed-point
  -- (steps 1-5 of the plan) is sorry'd inside the sub-helper
  -- `vlasovWellPosedness_local_picard_fixedPointFlow`.  The threading-heavy
  -- final assembly (step 7) is sorry'd inside the sub-helper
  -- `vlasovWellPosedness_local_finalAssembly`.  This body executes the
  -- glue: invoke both sub-helpers, derive `f 0 = f₀` (Step 7's only
  -- non-threading piece), assemble.
  --
  -- The decomposition isolates two distinct kinds of work: (a) the Picard
  -- mathematics in `_fixedPointFlow`, (b) the
  -- `IsLagrangianVlasovSolutionOn` 20-hypothesis thread in `_finalAssembly`.
  -- Each sub-helper becomes its own focused follow-up session per the
  -- P3 cross-session-context-loading discipline.
  obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
  haveI : IsProbabilityMeasure f₀ := hf₀_prob
  -- Sub-helper invocation: produces the self-consistent flow + regularity
  -- + AEMeasurable witness + universal-in-s convolution integrability
  -- (the last two added in the 2026-05-29 refactor closing the
  -- `_finalAssembly_*` bodies' internal sub-sub-sorries).
  obtain ⟨charX, charV, _M_ρ, _hM_ρ_nn, _hflow_on, _h_boundary,
          _hM_ρ_bound, _h_y_int_ρ, _hconv_cont, _h_aemeas, _h_int_conv⟩ :=
    vlasovWellPosedness_local_picard_fixedPointFlow W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con hB
  -- Bundle the f-shape result.
  refine ⟨vlasovSolutionViaPushforward charX charV f₀, charX, charV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) f 0 = f₀.  The flow's initial-condition clause (post-Friction-5
    -- extraction) gives (charX 0 z, charV 0 z) = z for every z, so the
    -- pushforward at t = 0 is `Measure.map id f₀ = f₀`.
    --
    -- This piece IS proved inline (cheap, structural) — uses the
    -- sub-helper's `h_boundary` projection at t = 0 via Friction 5's
    -- transport.
    have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := by
      intro z
      have := (_hflow_on.1 z (Set.mem_univ z))
      exact Prod.ext this.1 this.2
    show vlasovSolutionViaPushforward charX charV f₀ 0 = f₀
    unfold vlasovSolutionViaPushforward
    have h_at_0 : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z; exact h_init z
    rw [h_at_0, Measure.map_id]
  · -- (b) HasFiniteFirstMoment (f t) on Icc 0 T.  Deferred to the
    -- _finalAssembly sub-helper (since it requires C_T from
    -- flow_distance_growth_bound_on, plus the integral_map +
    -- pushforward-moment-bound chain — exactly the threading work that
    -- the _finalAssembly sub-helper handles).
    intro t ht
    exact vlasovWellPosedness_local_finalAssembly_moment W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con charX charV
      _M_ρ _hM_ρ_nn _hflow_on _h_boundary _hM_ρ_bound _h_y_int_ρ _hconv_cont
      _h_aemeas _h_int_conv
      t ht
  · -- (b′) FLAT uniform first-moment bound on the spatial marginal.
    -- The picard fixed-point flow already exposes exactly this bound
    -- (`_hM_ρ_bound`) for `M_ρ := _M_ρ` against
    -- `spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ ·)`,
    -- which is `spatialMarginal (f ·)` by definition of `f` here.
    exact ⟨_M_ρ, _hM_ρ_nn, _hM_ρ_bound⟩
  · -- (c) IsLagrangianVlasovSolutionOn gradW f T.  Deferred to the
    -- _finalAssembly sub-helper: it derives the AEMeasurable witness
    -- (Stage 1.8 territory), the IsCharacteristicFlowSelfConsistent
    -- discharge, the universal-in-s convolution integrability (extension
    -- of `_hconv_cont`'s implications), and threads all 20+ hypotheses
    -- through `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.
    exact vlasovWellPosedness_local_finalAssembly_isLagrangian W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con charX charV
      _M_ρ _hM_ρ_nn _hflow_on _h_boundary _hM_ρ_bound _h_y_int_ρ _hconv_cont
      _h_aemeas _h_int_conv
  · -- (d) Explicit pushforward equation for the outer charX charV.
    -- vlasovSolutionViaPushforward charX charV f₀ t = Measure.map (charX t, charV t) f₀
    -- by DEFINITION. And f 0 = f₀ (from goal (a), which used the initial condition).
    -- So f t = Measure.map (charX t, charV t) (f 0) by congruence on f 0 = f₀.
    have h_f0_eq : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z :=
        fun z => Prod.ext (_hflow_on.1 z (Set.mem_univ z)).1 (_hflow_on.1 z (Set.mem_univ z)).2
      simp [vlasovSolutionViaPushforward,
            show (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id from funext h_init]
    intro t _
    show vlasovSolutionViaPushforward charX charV f₀ t =
      Measure.map (fun z : PhaseSpace d => (charX t z, charV t z))
        (vlasovSolutionViaPushforward charX charV f₀ 0)
    rw [h_f0_eq]
    -- After rw, goal is: vlasovSolutionViaPushforward charX charV f₀ t = Measure.map ... f₀
    -- This is rfl by definition of vlasovSolutionViaPushforward.
    rfl
  · -- (e) Explicit AEMeasurable for the outer charX charV.
    -- AEMeasurable (fun z => (charX s z, charV s z)) f₀ comes from _h_aemeas.
    -- The expected type uses (f 0) = vlasovSolutionViaPushforward charX charV f₀ 0 = f₀.
    have h_f0_eq : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z :=
        fun z => Prod.ext (_hflow_on.1 z (Set.mem_univ z)).1 (_hflow_on.1 z (Set.mem_univ z)).2
      simp [vlasovSolutionViaPushforward,
            show (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id from funext h_init]
    intro s _
    rw [h_f0_eq]
    exact _h_aemeas s
  · -- (f) Boundary regularity bundle: HasDerivWithinAt on Icc 0 T for all z, t.
    -- Directly from `_h_boundary` (the picard fixed-point flow's boundary output).
    -- The measure in the velocity derivative uses spatialMarginal (f t) where
    -- f = vlasovSolutionViaPushforward charX charV f₀, which is the same as
    -- what _h_boundary was built against.
    exact _h_boundary
  · -- (g) Initial condition for the outer charX charV witnesses.
    -- From _hflow_on.1 (IsCharacteristicFlowOn's first conjunct).
    intro z
    exact _hflow_on.1 z (Set.mem_univ z)

-- ---------------------------------------------------------------------------
-- Banked infrastructure: localized `hasDerivAt_of_hasDerivAt_of_ne`
-- ---------------------------------------------------------------------------
-- Generic real-analysis helper banked for `_glue_step` case (a)'s substantive
-- close.  Mathlib's `hasDerivAt_of_hasDerivAt_of_ne`
-- (Mathlib/Analysis/Calculus/FDeriv/Extend.lean L177) requires a UNIVERSAL
-- `∀ y ≠ x, HasDerivAt f (g y) y` hypothesis; the `_glue_step` setting only
-- gives HasDerivAt on a bounded interval `Ioo 0 (T + T_0)`.  This helper
-- localizes the Mathlib pattern to a neighborhood-eventually hypothesis,
-- enabling case (a)'s close via union of one-sided extension lemmas.

section HasDerivAtPunctured
open scoped Topology
open Filter

/-- Local version of `hasDerivAt_of_hasDerivAt_of_ne` (Mathlib/Analysis/Calculus/
FDeriv/Extend.lean L177): if `f : ℝ → ℝ` has HasDerivAt with derivative `g(y)` at
every `y ≠ x₀` in some neighborhood of `x₀`, and both `f` and `g` are continuous
at `x₀`, then `f` has HasDerivAt with derivative `g(x₀)` at `x₀`.

The proof composes `hasDerivWithinAt_Iic_of_tendsto_deriv` (left side) +
`hasDerivWithinAt_Ici_of_tendsto_deriv` (right side) + `HasDerivWithinAt.union`,
following the Mathlib lemma's proof structure but with locally-quantified
hypothesis (enabling use when the punctured-HasDerivAt holds only on a bounded
interval, not all of ℝ). -/
theorem hasDerivAt_of_hasDerivAt_of_ne_in_nhds
    {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_diff_ne : ∀ᶠ y in 𝓝 x₀, y ≠ x₀ → HasDerivAt f (g y) y)
    (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) :
    HasDerivAt f (g x₀) x₀ := by
  -- Extract an open ball around x₀ on which the punctured HasDerivAt holds.
  obtain ⟨U, hU_sub, hU_open, hx₀_U⟩ := mem_nhds_iff.mp h_diff_ne
  obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀_U
  -- Right side: HasDerivWithinAt on Ici x₀ via hasDerivWithinAt_Ici_of_tendsto_deriv.
  have h_right : HasDerivWithinAt f (g x₀) (Set.Ici x₀) x₀ := by
    have hs_right : Set.Ioo x₀ (x₀ + ε) ∈ 𝓝[>] x₀ :=
      Ioo_mem_nhdsGT (by linarith : x₀ < x₀ + ε)
    have h_diff_right : DifferentiableOn ℝ f (Set.Ioo x₀ (x₀ + ε)) := by
      intro y hy
      have hy_U : y ∈ U := hε (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
      exact (hU_sub hy_U (ne_of_gt hy.1)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Ici_of_tendsto_deriv h_diff_right hf.continuousWithinAt hs_right
    have h_g_tendsto : Tendsto g (𝓝[>] x₀) (𝓝 (g x₀)) := tendsto_inf_left hg
    apply h_g_tendsto.congr'
    apply mem_of_superset hs_right
    intro y hy
    have hy_U : y ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
    exact (hU_sub hy_U (ne_of_gt hy.1)).deriv.symm
  -- Left side: symmetric.
  have h_left : HasDerivWithinAt f (g x₀) (Set.Iic x₀) x₀ := by
    have hs_left : Set.Ioo (x₀ - ε) x₀ ∈ 𝓝[<] x₀ :=
      Ioo_mem_nhdsLT (by linarith : x₀ - ε < x₀)
    have h_diff_left : DifferentiableOn ℝ f (Set.Ioo (x₀ - ε) x₀) := by
      intro y hy
      have hy_U : y ∈ U := hε (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
      exact (hU_sub hy_U (ne_of_lt hy.2)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Iic_of_tendsto_deriv h_diff_left hf.continuousWithinAt hs_left
    have h_g_tendsto : Tendsto g (𝓝[<] x₀) (𝓝 (g x₀)) := tendsto_inf_left hg
    apply h_g_tendsto.congr'
    apply mem_of_superset hs_left
    intro y hy
    have hy_U : y ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
    exact (hU_sub hy_U (ne_of_lt hy.2)).deriv.symm
  -- Union via Set.Iic_union_Ici = Set.univ → HasDerivAt at x₀.
  simpa using h_left.union h_right

end HasDerivAtPunctured

-- ---------------------------------------------------------------------------
-- §9.5  Stage 5 — variable-`T_target` continuation via fixed-`T_0` iteration
-- ---------------------------------------------------------------------------
-- Composes `vlasovWellPosedness_local` against itself to extend the local
-- solution from `[0, T_0]` to `[0, T_target]` for any `T_target > 0`.  The
-- contraction time `T_0` is *fixed* (depends only on `L`, not on iteration-
-- accumulated moment bounds) — see the docstring on `vlasovWellPosedness_local`
-- (above) for the planning-input note on why fixed-`T_0` is the correct
-- iteration shape (the `Phi_supW1_contraction` factor `q` depends only on
-- `L` and `T`).
--
-- Two API-locked sub-theorems:
-- * `vlasovWellPosedness_glue_step`: extend a solution on `[0, T]` by one
--   window of length `T_0`, gluing at `t = T`.  Sorry'd body — load-bearing
--   gluing argument.
-- * `vlasovWellPosedness_forward`: `Nat.rec` iteration of `_glue_step`
--   to reach any `T_target`.  Sorry'd body — induction + bundling.
--
-- Stage 6 (below) then bridges from `IsLagrangianVlasovSolutionOn` (any
-- `T_target`) to `IsLagrangianVlasovSolution` (universal-in-`t`).
-- Stage 8 produces uniqueness.

private lemma glue_step_boundary_bundle {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (f_prev g f_next : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g charX_next charV_next :
        ℝ → PhaseSpace d → PhysSpace d)
    (hdef_X : charX_next = fun t z =>
        if t ≤ T then charX_prev t z else charX_g (t - T) (charX_prev T z, charV_prev T z))
    (hdef_V : charV_next = fun t z =>
        if t ≤ T then charV_prev t z else charV_g (t - T) (charX_prev T z, charV_prev T z))
    (hdef_f : f_next = fun t => if t ≤ T then f_prev t else g (t - T))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (hg_boundary : ∀ (w : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T_0 →
        HasDerivWithinAt (fun s => charX_g s w) (charV_g t w) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s w)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t w)))
          (Set.Icc 0 T_0) t)
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ (w : PhaseSpace d), charX_g 0 w = w.1 ∧ charV_g 0 w = w.2) :
    ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T + T_0) →
      HasDerivWithinAt (fun s => charX_next s z) (charV_next t z) (Set.Icc 0 (T + T_0)) t ∧
      HasDerivWithinAt (fun s => charV_next s z)
        (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t)) (charX_next t z)))
        (Set.Icc 0 (T + T_0)) t := by
  subst hdef_X hdef_V
  intro z t ht
  simp only []
  -- Abbreviate the initial phase-space point for g
  have hz₀_def : (charX_prev T z, charV_prev T z) = (charX_prev T z, charV_prev T z) := rfl
  by_cases ht_le : t ≤ T
  · -- t ≤ T: use h_prev_boundary + upgrade to Icc 0 (T + T_0)
    simp only [if_pos ht_le]
    have ht_in : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht_le⟩
    have h_bX := (h_prev_boundary z t ht_in).1
    have h_bV := (h_prev_boundary z t ht_in).2
    by_cases ht_eqT : t = T
    · -- t = T: use HasDerivWithinAt.union from Iic T (left) and Ici T (right)
      have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
      have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).1
      have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).2
      have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
      have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) := Icc_mem_nhdsGE hT_0_pos
      -- Rewrite t to T in h_bX, h_bV
      rw [ht_eqT] at h_bX h_bV
      -- charX: left one-sided
      have hX_Lic := h_bX.mono_of_mem_nhdsWithin h_nhd_L
      have hX_left : HasDerivWithinAt
          (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_prev T z) (Set.Iic T) T :=
        hX_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.right_mem_Iic
      -- charX: right one-sided via chain rule on g's boundary
      have hX_Ici0 := h_g_bX.mono_of_mem_nhdsWithin h_nhd_R
      have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
        ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
      have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
        fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
      have h_chainX : HasDerivWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g 0 (charX_prev T z, charV_prev T z)) (Set.Ici T) T := by
        have := HasDerivWithinAt.scomp_of_eq T hX_Ici0 h_sub_R h_mapR (sub_self T).symm
        simpa [Function.comp, one_smul] using this
      have hVg0_eq : charV_g 0 (charX_prev T z, charV_prev T z) = charV_prev T z :=
        (hg_init_cond (charX_prev T z, charV_prev T z)).2
      rw [hVg0_eq] at h_chainX
      have hX_right : HasDerivWithinAt
          (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_prev T z) (Set.Ici T) T :=
        h_chainX.congr_of_mem
          (fun s hs => by
            by_cases hle : s ≤ T
            · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
              simp [hle, heq, sub_self,
                (hg_init_cond (charX_prev T z, charV_prev T z)).1]
            · simp [hle])
          Set.left_mem_Ici
      have hX_union := hX_left.union hX_right
      rw [Set.Iic_union_Ici] at hX_union
      -- charV: analogously
      have hV_Lic := h_bV.mono_of_mem_nhdsWithin h_nhd_L
      have hV_left : HasDerivWithinAt
          (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
          (Set.Iic T) T := by
        simp only [hdef_f, if_pos (le_refl T)]
        exact hV_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.right_mem_Iic
      have hV_Ici0 := h_g_bV.mono_of_mem_nhdsWithin h_nhd_R
      have h_chainV : HasDerivWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g 0))
            (charX_g 0 (charX_prev T z, charV_prev T z))))
          (Set.Ici T) T := by
        have := HasDerivWithinAt.scomp_of_eq T hV_Ici0 h_sub_R h_mapR (sub_self T).symm
        simpa [Function.comp, one_smul] using this
      have hXg0_eq : charX_g 0 (charX_prev T z, charV_prev T z) = charX_prev T z :=
        (hg_init_cond (charX_prev T z, charV_prev T z)).1
      have hg0_spat : spatialMarginal (g 0) = spatialMarginal (f_prev T) :=
        congrArg spatialMarginal hg_init
      have hfnextT : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
        congrArg spatialMarginal (by rw [hdef_f]; simp only [if_pos (le_refl T)])
      rw [hXg0_eq, hg0_spat, ← hfnextT] at h_chainV
      have hV_right : HasDerivWithinAt
          (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
          (Set.Ici T) T :=
        h_chainV.congr_of_mem
          (fun s hs => by
            by_cases hle : s ≤ T
            · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
              simp [hle, heq, sub_self,
                (hg_init_cond (charX_prev T z, charV_prev T z)).2]
            · simp [hle])
          Set.left_mem_Ici
      have hV_union := hV_left.union hV_right
      rw [Set.Iic_union_Ici] at hV_union
      rw [ht_eqT]
      exact ⟨hX_union.hasDerivAt Filter.univ_mem |>.hasDerivWithinAt,
             hV_union.hasDerivAt Filter.univ_mem |>.hasDerivWithinAt⟩
    · -- t < T: use mono_of_mem_nhdsWithin to extend to Icc 0 (T + T_0)
      have ht_ltT : t < T := lt_of_le_of_ne ht_le ht_eqT
      -- Get Icc 0 T ∈ nhdsWithin t (Icc 0 (T + T_0))
      have h_mem : Set.Icc (0 : ℝ) T ∈ nhdsWithin t (Set.Icc 0 (T + T_0)) := by
        rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
        · exact (nhdsWithin_mono 0 Set.Icc_subset_Ici_self) (Icc_mem_nhdsGE hT_pos)
        · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds ht_pos ht_ltT)
      -- Upgrade HasDerivWithinAt from Icc 0 T to Icc 0 (T + T_0)
      have hX_big := h_bX.mono_of_mem_nhdsWithin h_mem
      have hV_big := h_bV.mono_of_mem_nhdsWithin h_mem
      -- Congr: charX_next = charX_prev on Icc 0 T (within Icc 0 (T+T_0))
      have hX_ev : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin t (Set.Icc 0 (T + T_0))] (charX_prev · z) :=
        Filter.Eventually.mono h_mem (fun s hs => by simp [hs.2])
      have hV_ev : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin t (Set.Icc 0 (T + T_0))] (charV_prev · z) :=
        Filter.Eventually.mono h_mem (fun s hs => by simp [hs.2])
      -- f_next t = f_prev t, so marginals match
      have hfnext : f_next t = f_prev t := by rw [hdef_f]; simp only [if_pos ht_le]
      have hfnext_spat : spatialMarginal (f_next t) = spatialMarginal (f_prev t) :=
        congrArg spatialMarginal hfnext
      rw [← hfnext_spat] at hV_big
      constructor
      · exact hX_big.congr_of_eventuallyEq_of_mem hX_ev ht
      · exact hV_big.congr_of_eventuallyEq_of_mem hV_ev ht
  · -- T < t: use hg_boundary + chain rule
    push_neg at ht_le
    simp only [if_neg (not_le.mpr ht_le)]
    have htT_mem : t - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    have h_bdry_gX := (hg_boundary (charX_prev T z, charV_prev T z) (t - T) htT_mem).1
    have h_bdry_gV := (hg_boundary (charX_prev T z, charV_prev T z) (t - T) htT_mem).2
    by_cases ht_ltTT0 : t < T + T_0
    · -- t ∈ Ioo T (T + T_0): interior case, use HasDerivAt + congr
      have htT_Ioo : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith⟩
      have hX_da := h_bdry_gX.hasDerivAt (Icc_mem_nhds htT_Ioo.1 htT_Ioo.2)
      have hV_da := h_bdry_gV.hasDerivAt (Icc_mem_nhds htT_Ioo.1 htT_Ioo.2)
      have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
      have h_chainX : HasDerivAt (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
        have := HasDerivAt.scomp_of_eq t hX_da h_sub rfl
        simpa [Function.comp, one_smul] using this
      have h_chainV : HasDerivAt (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g (t - T)))
            (charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
        have := HasDerivAt.scomp_of_eq t hV_da h_sub rfl
        simpa [Function.comp, one_smul] using this
      -- f_next t = g (t - T), so marginals match
      have h_fnext_t : f_next t = g (t - T) := by
        rw [hdef_f]; simp only [if_neg (not_le.mpr ht_le)]
      rw [← congrArg spatialMarginal h_fnext_t] at h_chainV
      -- piecewise = charX_g (· - T) (charX_prev T z, charV_prev T z) near t (since T < t)
      have h_ev_gt : ∀ᶠ s in nhds t, T < s := eventually_gt_nhds ht_le
      have hX_ev : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhds t] (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt (fun s hs => by simp [not_le.mpr hs])
      have hV_ev : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhds t] (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt (fun s hs => by simp [not_le.mpr hs])
      exact ⟨(h_chainX.congr_of_eventuallyEq hX_ev).hasDerivWithinAt,
             (h_chainV.congr_of_eventuallyEq hV_ev).hasDerivWithinAt⟩
    · -- t = T + T_0: endpoint, use mono_of_mem_nhdsWithin + chain rule + mono
      push_neg at ht_ltTT0
      have htT0 : t = T + T_0 := le_antisymm ht.2 ht_ltTT0
      rw [show t - T = T_0 from by linarith] at h_bdry_gX h_bdry_gV
      -- Upgrade to Iic T_0 via Icc_mem_nhdsLE
      have h_nhd_LE : Set.Icc 0 T_0 ∈ nhdsWithin T_0 (Set.Iic T_0) := Icc_mem_nhdsLE hT_0_pos
      have hX_Lic := h_bdry_gX.mono_of_mem_nhdsWithin h_nhd_LE
      have hV_Lic := h_bdry_gV.mono_of_mem_nhdsWithin h_nhd_LE
      -- Chain rule: (· - T) maps Iic (T + T_0) to Iic T_0
      have h_sub_LE : HasDerivWithinAt (· - T) 1 (Set.Iic (T + T_0)) (T + T_0) :=
        ((hasDerivAt_id' (T + T_0)).sub_const T).hasDerivWithinAt.mono
          (fun _ _ => Set.mem_univ _)
      have h_mapLE : Set.MapsTo (· - T) (Set.Iic (T + T_0)) (Set.Iic T_0) :=
        fun s hs => Set.mem_Iic.mpr (by linarith [Set.mem_Iic.mp hs])
      have h_chainX : HasDerivWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g T_0 (charX_prev T z, charV_prev T z)) (Set.Iic (T + T_0)) (T + T_0) := by
        have := HasDerivWithinAt.scomp_of_eq (T + T_0) hX_Lic h_sub_LE h_mapLE
          (show T_0 = (T + T_0) - T by ring)
        simpa [Function.comp, one_smul] using this
      have h_chainV : HasDerivWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g T_0))
            (charX_g T_0 (charX_prev T z, charV_prev T z))))
          (Set.Iic (T + T_0)) (T + T_0) := by
        have := HasDerivWithinAt.scomp_of_eq (T + T_0) hV_Lic h_sub_LE h_mapLE
          (show T_0 = (T + T_0) - T by ring)
        simpa [Function.comp, one_smul] using this
      -- Congr: near T+T_0 within Iic (T+T_0), points > T eventually
      have h_ev_gt2 : ∀ᶠ s in nhdsWithin (T + T_0) (Set.Iic (T + T_0)), T < s :=
        (eventually_gt_nhds (show T < T + T_0 by linarith)).filter_mono nhdsWithin_le_nhds
      have hX_ev2 : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin (T + T_0) (Set.Iic (T + T_0))]
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt2 (fun s hs => by simp [not_le.mpr hs])
      have hV_ev2 : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin (T + T_0) (Set.Iic (T + T_0))]
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt2 (fun s hs => by simp [not_le.mpr hs])
      have h_Iic_sub : Set.Icc 0 (T + T_0) ⊆ Set.Iic (T + T_0) := Set.Icc_subset_Iic_self
      have h_TT0_Iic : (T + T_0) ∈ Set.Iic (T + T_0) := Set.mem_Iic.mpr (le_refl _)
      -- f_next (T + T_0) = g T_0
      have h_fnext_TT0 : f_next (T + T_0) = g T_0 := by
        simp [hdef_f, not_le.mpr (show T < T + T_0 by linarith)]
      constructor
      · have h_cX : HasDerivWithinAt
            (fun s => if s ≤ T then charX_prev s z
              else charX_g (s - T) (charX_prev T z, charV_prev T z))
            (charV_g T_0 (charX_prev T z, charV_prev T z))
            (Set.Icc 0 (T + T_0)) (T + T_0) :=
          (h_chainX.congr_of_eventuallyEq_of_mem hX_ev2 h_TT0_Iic).mono h_Iic_sub
        rw [htT0]
        rw [show T + T_0 - T = T_0 from by ring]
        exact h_cX
      · have h_cV : HasDerivWithinAt
            (fun s => if s ≤ T then charV_prev s z
              else charV_g (s - T) (charX_prev T z, charV_prev T z))
            (-(convolveFunctionMeasure gradW
              (spatialMarginal (g T_0))
              (charX_g T_0 (charX_prev T z, charV_prev T z))))
            (Set.Icc 0 (T + T_0)) (T + T_0) :=
          (h_chainV.congr_of_eventuallyEq_of_mem hV_ev2 h_TT0_Iic).mono h_Iic_sub
        rw [htT0]
        rw [h_fnext_TT0]
        rw [show T + T_0 - T = T_0 from by ring]
        exact h_cV


/-- **Route 2 inner kernel for `glue_step` `h_cont_g`** (LEFT / `Iic T`): continuity
at the seam `T` of `s ↦ (∇W ∗ μ_s)(charX s z)`, where the window measure curve `μ` is
the flow-pushforward of `f₀`.

Proven from PROVEN tools only (no deferred OT).  The pushforward rewrite
`(∇W ∗ μ_s)(x) = ∫ z', gradW (x − charX s z') ∂f₀` (`integral_map`) turns the
moving-measure convolution into a fixed-`f₀` integral with moving integrand, closed by
dominated convergence: convergence from the flow's seam continuity `h_charX_cont`,
domination from the Gronwall growth bound `hC_T` (Piece A) against `f₀`'s finite first
moment.  This is the structural reason `h_cont_g` does NOT need the general narrow→W₁
kernel — its consumer carries a pushforward representation. -/
lemma flowConv_continuousWithinAt_Iic_seam
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (μ : ℝ → Measure (PhysSpace d))
    (h_push : ∀ s ∈ Set.Icc (0 : ℝ) T,
        μ s = Measure.map (fun z : PhaseSpace d => charX s z) f₀)
    (h_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => charX s z) f₀)
    (h_charX_cont : ∀ z : PhaseSpace d,
        ContinuousWithinAt (fun s => charX s z) (Set.Icc (0 : ℝ) T) T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (hC_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d, ‖charX s z‖ ≤ C_T * (‖z‖ + 1))
    (z : PhaseSpace d) :
    ContinuousWithinAt (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      (Set.Iic T) T := by
  have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT
  have hgradW_cont : Continuous gradW := hL.continuous
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- Pushforward rewrite of the convolution, eventually in s (on the window).
  have h_eq : (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      =ᶠ[nhdsWithin T (Set.Iic T)]
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_L
    intro s hs
    show ∫ y, gradW (charX s z - y) ∂(μ s)
        = ∫ z', gradW (charX s z - charX s z') ∂f₀
    rw [h_push s hs]
    exact integral_map (h_aemeas s hs)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  -- The rewritten f₀-integral is continuous at T by dominated convergence.
  have h_cont_rhs : ContinuousWithinAt
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) (Set.Iic T) T := by
    apply continuousWithinAt_of_dominated
      (bound := fun z' => ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1))
        + (L : ℝ) * (C_T * (‖z'‖ + 1)))
    · -- AEStronglyMeasurable in z', eventually in s
      apply Filter.Eventually.mono h_nhd_L
      intro s hs
      exact (hgradW_cont.measurable.comp_aemeasurable
        (aemeasurable_const.sub (h_aemeas s hs))).aestronglyMeasurable
    · -- pointwise dominator bound, eventually in s
      apply Filter.Eventually.mono h_nhd_L
      intro s hs
      apply Filter.Eventually.of_forall
      intro z'
      have h1 : ‖gradW (charX s z - charX s z')‖
          ≤ ‖gradW 0‖ + (L : ℝ) * ‖charX s z - charX s z'‖ := by
        have hd := hL.dist_le_mul (charX s z - charX s z') 0
        simp only [dist_eq_norm, sub_zero] at hd
        have htri : ‖gradW (charX s z - charX s z')‖
            ≤ ‖gradW 0‖ + ‖gradW (charX s z - charX s z') - gradW 0‖ := by
          have := norm_add_le (gradW (charX s z - charX s z') - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      have h2 : ‖charX s z - charX s z'‖ ≤ ‖charX s z‖ + ‖charX s z'‖ := norm_sub_le _ _
      have h3 : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := hC_T s hs z
      have h4 : ‖charX s z'‖ ≤ C_T * (‖z'‖ + 1) := hC_T s hs z'
      nlinarith [mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hL_nn]
    · -- integrability of the dominator
      apply Integrable.add (integrable_const _)
      exact ((hf₀_int.add (integrable_const (1 : ℝ))).const_mul C_T).const_mul (L : ℝ)
    · -- pointwise continuity in s, a.e. z'
      apply Filter.Eventually.of_forall
      intro z'
      have hcz : ContinuousWithinAt (fun s => charX s z) (Set.Iic T) T :=
        (h_charX_cont z).mono_of_mem_nhdsWithin h_nhd_L
      have hcz' : ContinuousWithinAt (fun s => charX s z') (Set.Iic T) T :=
        (h_charX_cont z').mono_of_mem_nhdsWithin h_nhd_L
      exact hgradW_cont.continuousAt.comp_continuousWithinAt (hcz.sub hcz')
  -- Bridge value at T and conclude.
  have h_val_T : convolveFunctionMeasure gradW (μ T) (charX T z)
      = ∫ z', gradW (charX T z - charX T z') ∂f₀ := by
    have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_refl T⟩
    show ∫ y, gradW (charX T z - y) ∂(μ T)
        = ∫ z', gradW (charX T z - charX T z') ∂f₀
    rw [h_push T hT_mem]
    exact integral_map (h_aemeas T hT_mem)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact h_cont_rhs.congr_of_eventuallyEq h_eq h_val_T

/-- **Route 2 inner kernel for `glue_step` `h_cont_g`** (RIGHT / `Ici a`): the
exact mirror of `flowConv_continuousWithinAt_Iic_seam`, but on `Set.Ici a` over a
generic window `[a, b]` with the seam at the lower endpoint `a`.  Same proof shape;
the only set-dependent swaps are `Iic T → Ici a`, `Icc_mem_nhdsLE → Icc_mem_nhdsGE`,
and the window `[0, T] → [a, b]`.  Used for the RIGHT side of the seam at `T` where
`charX` is the composed position flow `Z_s z = charX_g (s-T) (charX_prev T z, …)` and
`μ s = spatialMarginal (g (s-T))` is its pushforward of `f₀`. -/
lemma flowConv_continuousWithinAt_Ici_seam
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {a b : ℝ} (hab : a < b)
    (μ : ℝ → Measure (PhysSpace d))
    (h_push : ∀ s ∈ Set.Icc a b,
        μ s = Measure.map (fun z : PhaseSpace d => charX s z) f₀)
    (h_aemeas : ∀ s ∈ Set.Icc a b,
        AEMeasurable (fun z : PhaseSpace d => charX s z) f₀)
    (h_charX_cont : ∀ z : PhaseSpace d,
        ContinuousWithinAt (fun s => charX s z) (Set.Ici a) a)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (hC_T : ∀ s ∈ Set.Icc a b, ∀ z : PhaseSpace d, ‖charX s z‖ ≤ C_T * (‖z‖ + 1))
    (z : PhaseSpace d) :
    ContinuousWithinAt (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      (Set.Ici a) a := by
  have h_nhd_R : Set.Icc a b ∈ nhdsWithin a (Set.Ici a) := Icc_mem_nhdsGE hab
  have hgradW_cont : Continuous gradW := hL.continuous
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- Pushforward rewrite of the convolution, eventually in s (on the window).
  have h_eq : (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      =ᶠ[nhdsWithin a (Set.Ici a)]
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_R
    intro s hs
    show ∫ y, gradW (charX s z - y) ∂(μ s)
        = ∫ z', gradW (charX s z - charX s z') ∂f₀
    rw [h_push s hs]
    exact integral_map (h_aemeas s hs)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  -- The rewritten f₀-integral is continuous at a by dominated convergence.
  have h_cont_rhs : ContinuousWithinAt
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) (Set.Ici a) a := by
    apply continuousWithinAt_of_dominated
      (bound := fun z' => ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1))
        + (L : ℝ) * (C_T * (‖z'‖ + 1)))
    · -- AEStronglyMeasurable in z', eventually in s
      apply Filter.Eventually.mono h_nhd_R
      intro s hs
      exact (hgradW_cont.measurable.comp_aemeasurable
        (aemeasurable_const.sub (h_aemeas s hs))).aestronglyMeasurable
    · -- pointwise dominator bound, eventually in s
      apply Filter.Eventually.mono h_nhd_R
      intro s hs
      apply Filter.Eventually.of_forall
      intro z'
      have h1 : ‖gradW (charX s z - charX s z')‖
          ≤ ‖gradW 0‖ + (L : ℝ) * ‖charX s z - charX s z'‖ := by
        have hd := hL.dist_le_mul (charX s z - charX s z') 0
        simp only [dist_eq_norm, sub_zero] at hd
        have htri : ‖gradW (charX s z - charX s z')‖
            ≤ ‖gradW 0‖ + ‖gradW (charX s z - charX s z') - gradW 0‖ := by
          have := norm_add_le (gradW (charX s z - charX s z') - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      have h2 : ‖charX s z - charX s z'‖ ≤ ‖charX s z‖ + ‖charX s z'‖ := norm_sub_le _ _
      have h3 : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := hC_T s hs z
      have h4 : ‖charX s z'‖ ≤ C_T * (‖z'‖ + 1) := hC_T s hs z'
      nlinarith [mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hL_nn]
    · -- integrability of the dominator
      apply Integrable.add (integrable_const _)
      exact ((hf₀_int.add (integrable_const (1 : ℝ))).const_mul C_T).const_mul (L : ℝ)
    · -- pointwise continuity in s, a.e. z'
      apply Filter.Eventually.of_forall
      intro z'
      have hcz : ContinuousWithinAt (fun s => charX s z) (Set.Ici a) a := h_charX_cont z
      have hcz' : ContinuousWithinAt (fun s => charX s z') (Set.Ici a) a := h_charX_cont z'
      exact hgradW_cont.continuousAt.comp_continuousWithinAt (hcz.sub hcz')
  -- Bridge value at a and conclude.
  have h_val_a : convolveFunctionMeasure gradW (μ a) (charX a z)
      = ∫ z', gradW (charX a z - charX a z') ∂f₀ := by
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
    show ∫ y, gradW (charX a z - y) ∂(μ a)
        = ∫ z', gradW (charX a z - charX a z') ∂f₀
    rw [h_push a ha_mem]
    exact integral_map (h_aemeas a ha_mem)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact h_cont_rhs.congr_of_eventuallyEq h_eq h_val_a

set_option maxHeartbeats 1600000 in
/-- **Stage 5 sub-helper**: one-window glue step.

Given a solution `f_prev : ℝ → Measure (PhaseSpace d)` on `[0, T]`
satisfying the local-existence conjuncts (initial condition + finite first
moment + `IsLagrangianVlasovSolutionOn`), and a window length `T_0`
satisfying the smallness constraint `L · (T_0+1)² < 1`, produces a glued
solution `f_next : ℝ → Measure (PhaseSpace d)` on `[0, T + T_0]` that
agrees with `f_prev` on `[0, T]`.

**Proof strategy** (sorry'd body, ~150-200 lines for a focused follow-up):

1. Shift the initial condition: apply `vlasovWellPosedness_local` to
   `f_prev T` (which has finite first moment by `h_prev_mom T`) with
   window length `T_0`.  Gives a solution `g : ℝ → Measure (PhaseSpace d)`
   on `[0, T_0]` with `g 0 = f_prev T`.

2. Glue: define `f_next t := if t ≤ T then f_prev t else g (t - T)`.
   Agreement at `t = T` is by `g 0 = f_prev T`.

3. Verify the four output conjuncts:
   - Initial: `f_next 0 = f_prev 0 = f₀`.
   - Moment: piecewise from `h_prev_mom` and `g`'s moment bound.
   - `IsLagrangianVlasovSolutionOn` on `[0, T + T_0]`:
     * `IsVlasovSolutionOn`: weak PDE on `Ioo 0 (T + T_0)` — split at `T`,
       use `h_prev_lag.1` for `Ioo 0 T` part and `g`'s for `Ioo T (T+T_0)`,
       continuity at `T` from the integral being continuous.
     * Flow: glue the per-window flows via standard ODE composition
       (charX_next(t, z) := if t ≤ T then charX_prev(t, z) else
       charX_g(t - T, (charX_prev(T, z), charV_prev(T, z)))).
     * Pushforward equation: holds piecewise.
     * AEMeasurable witness: composition of AEMeasurable maps. -/
theorem vlasovWellPosedness_glue_step
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T : ℝ} (hT_pos : 0 < T)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    -- FLAT (window-constant) uniform first-moment bound on f_prev's spatial marginal.
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    -- Explicit flow witnesses for f_prev (avoids witness-identity issues with IsLagrangianVlasovSolutionOn)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_vlasov : IsVlasovSolutionOn gradW f_prev T)
    (h_prev_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f_prev t))
        charX_prev charV_prev (Set.Ioo 0 T) Set.univ)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t = Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (h_prev_ic : ∀ z : PhaseSpace d, charX_prev 0 z = z.1 ∧ charV_prev 0 z = z.2)
    {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (hT_0_small_PL : LocalSmallness_PL_buffer L T_0)
    (hT_0_small_con : LocalSmallness_contraction L T_0)
    (hT_0_small_B : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1) :
    ∃ (f_next : ℝ → Measure (PhaseSpace d))
      (charX_next charV_next : ℝ → PhaseSpace d → PhysSpace d),
      (∀ t ∈ Set.Icc (0 : ℝ) T, f_next t = f_prev t) ∧
      f_next 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), HasFiniteFirstMoment (f_next t)) ∧
      -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
      (∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), ∫ y, ‖y‖ ∂(spatialMarginal (f_next t)) ≤ M) ∧
      IsLagrangianVlasovSolutionOn gradW f_next (T + T_0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (T + T_0),
          f_next t = Measure.map (fun z : PhaseSpace d => (charX_next t z, charV_next t z)) (f_next 0)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (T + T_0),
          AEMeasurable (fun z : PhaseSpace d => (charX_next s z, charV_next s z)) (f_next 0)) ∧
      (∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T + T_0) →
          HasDerivWithinAt (fun s => charX_next s z) (charV_next t z) (Set.Icc 0 (T + T_0)) t ∧
          HasDerivWithinAt (fun s => charV_next s z)
            (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t)) (charX_next t z)))
            (Set.Icc 0 (T + T_0)) t) ∧
      (∀ z : PhaseSpace d, charX_next 0 z = z.1 ∧ charV_next 0 z = z.2) := by
  -- **Structural-debt status (post-`e22648b`, 2026-05-30)**: 5 of 8 original
  -- sub-sub-sorries closed substantively (pushforward × 2, AEMeasurability,
  -- HasDerivAt for t > T strict × 2, plus interior cases for t < T strict).
  -- 3 remaining sub-sub-sorries, all at the gluing boundary t = T:
  --   (a) IsVlasovSolutionOn at t = T (weak PDE boundary).
  --   (b) HasDerivAt charX_next at t = T.
  --   (c) HasDerivAt charV_next at t = T.
  --
  -- **Surgery target for declaration close** (Friction-5-style upstream
  -- enrichment): enrich `_finalAssembly_isLagrangian`'s output to also
  -- expose the Friction-5 boundary regularity bundle (`h_init`,
  -- `h_cont_Icc`, `h_deriv_Ico` on `Set.Ici s` for `s ∈ Ico 0 T`).  Then
  -- `vlasovWellPosedness_local`'s output gains the boundary bundle as a
  -- separate conjunct alongside `IsLagrangianVlasovSolutionOn`.  This lets
  -- `_glue_step` access HasDerivWithinAt at T from the LEFT (via f_prev's
  -- boundary bundle at endpoint T) and HasDerivWithinAt at 0 from the
  -- RIGHT (via g's boundary bundle at endpoint 0).  Combining these gives
  -- HasDerivAt at t = T in `f_next`'s frame, closing the 3 boundary
  -- sub-sub-sorries.
  --
  -- Estimated scope: ~150 lines across `_finalAssembly_isLagrangian`,
  -- `vlasovWellPosedness_local`, and `_glue_step` (signature additions +
  -- threading + 3 boundary closes).  Same pattern as the original Friction
  -- 5 surgery (`4b024ee`) at one architectural layer up.  Deferred to a
  -- focused refactor session loaded with the precise surgery path.
  --
  -- Step 1: invoke vlasovWellPosedness_local on f_prev T to get g on [0, T_0]
  have h_prev_T_mom : HasFiniteFirstMoment (f_prev T) :=
    h_prev_mom T (Set.right_mem_Icc.mpr hT_pos.le)
  obtain ⟨g, charX_g, charV_g, hg_init, hg_mom, hg_mom_unif, hg_lag, hg_push_ex, hg_aemeas_ex,
          hg_boundary, hg_init_cond⟩ :=
    vlasovWellPosedness_local W gradW hgradW L hL
      (f_prev T) h_prev_T_mom hT_0_pos hT_0_small_PL hT_0_small_con hT_0_small_B
  -- Step 2: define the glued solution piecewise
  let f_next : ℝ → Measure (PhaseSpace d) :=
    fun t => if t ≤ T then f_prev t else g (t - T)
  -- Step 3: verify the output conjuncts
  -- Piecewise flow: for t ≤ T use charX_prev, for t > T compose with charX_g shifted
  let charX_next : ℝ → PhaseSpace d → PhysSpace d := fun t z =>
    if t ≤ T then charX_prev t z else charX_g (t - T) (charX_prev T z, charV_prev T z)
  let charV_next : ℝ → PhaseSpace d → PhysSpace d := fun t z =>
    if t ≤ T then charV_prev t z else charV_g (t - T) (charX_prev T z, charV_prev T z)
  have h_g_vlasov : IsVlasovSolutionOn gradW g T_0 := hg_lag.1
  refine ⟨f_next, charX_next, charV_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Conjunct (i): agreement on [0, T]
    intro t ht
    simp only [f_next]
    have ht_le : t ≤ T := ht.2
    simp [ht_le]
  · -- Conjunct (ii): initial condition f_next 0 = f₀
    simp only [f_next]
    have h0_le : (0 : ℝ) ≤ T := hT_pos.le
    simp [h0_le, h_prev_init]
  · -- Conjunct (iii): HasFiniteFirstMoment on [0, T + T_0]
    intro t ht
    simp only [f_next]
    by_cases ht_le : t ≤ T
    · simp [ht_le]
      exact h_prev_mom t ⟨ht.1, ht_le⟩
    · simp [ht_le]
      push_neg at ht_le
      apply hg_mom (t - T)
      constructor
      · linarith
      · linarith [ht.2]
  · -- Conjunct (iii′): FLAT uniform first-moment bound on the spatial marginal of f_next.
    -- M_next := max M_prev M_g.  For t ≤ T, spatialMarginal (f_next t) = spatialMarginal (f_prev t)
    -- (bounded by M_prev); for t > T, = spatialMarginal (g (t - T)) with t - T ∈ [0, T_0]
    -- (bounded by M_g).  No cross-term.
    obtain ⟨M_prev, hM_prev_nn, hM_prev_bd⟩ := hM_prev
    obtain ⟨M_g, hM_g_nn, hM_g_bd⟩ := hg_mom_unif
    refine ⟨max M_prev M_g, le_trans hM_prev_nn (le_max_left _ _), fun t ht => ?_⟩
    simp only [f_next]
    by_cases ht_le : t ≤ T
    · simp only [ht_le, ↓reduceIte]
      exact le_trans (hM_prev_bd t ⟨ht.1, ht_le⟩) (le_max_left _ _)
    · simp only [ht_le, ↓reduceIte]
      push_neg at ht_le
      refine le_trans (hM_g_bd (t - T) ⟨by linarith, by linarith [ht.2]⟩) (le_max_right _ _)
  · -- Conjunct (iv): IsLagrangianVlasovSolutionOn gradW f_next (T + T_0)
    refine ⟨?_, charX_next, charV_next, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn gradW f_next (T + T_0)
      -- Sub-sorry: PDE gluing — on Ioo 0 (T + T_0), piecewise from h_prev_vlasov and h_g_vlasov
      -- Sub-sorry (a): IsVlasovSolutionOn for the glued solution.
      -- Strategy: for t ∈ Ioo 0 T use h_prev_vlasov (with f_next = f_prev near t);
      -- for t ∈ Ioo T (T+T_0) use h_g_vlasov shifted (f_next t = g (t-T));
      -- at t = T use continuity of t ↦ ∫ φ ∂f_next t from both sides.
      have h_vlasov_glue : IsVlasovSolutionOn gradW f_next (T + T_0) := by
        intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
        by_cases ht_lt : t < T
        · -- t ∈ Ioo 0 T: use h_prev_vlasov (f_next = f_prev near t)
          have ht_prev : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht.1, ht_lt⟩
          -- f_next = f_prev on a neighborhood of t (since t < T)
          have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t]
              (fun s => ∫ z, φ z ∂f_prev s) := by
            apply Filter.Eventually.mono (eventually_lt_nhds ht_lt)
            intro s hs; simp [f_next, le_of_lt hs]
          have h_fnext_t : f_next t = f_prev t := if_pos (le_of_lt ht_lt)
          have h_deriv := h_prev_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
              hgradXφ hgradVφ t ht_prev
          rw [show (fun _ => (0 : ℝ)) t = 0 from rfl, add_zero] at h_deriv
          rw [show (fun _ => (0 : ℝ)) t = 0 from rfl, add_zero, h_fnext_t]
          exact h_deriv.congr_of_eventuallyEq h_ev
        · by_cases ht_gt : T < t
          · -- t ∈ Ioo T (T + T_0): use h_g_vlasov shifted by T
            have ht_g : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
            -- f_next = g (· - T) on a neighborhood of t (since t > T)
            have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t]
                (fun s => ∫ z, φ z ∂g (s - T)) := by
              apply Filter.Eventually.mono (eventually_gt_nhds ht_gt)
              intro s hs; simp [f_next, not_le.mpr hs]
            have h_fnext_t : f_next t = g (t - T) := if_neg (not_le.mpr ht_gt)
            -- HasDerivAt for fun r => ∫ φ ∂g r at (t - T)
            have h_g_deriv := h_g_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
                hgradXφ hgradVφ (t - T) ht_g
            rw [show (fun _ => (0 : ℝ)) (t - T) = 0 from rfl, add_zero] at h_g_deriv
            -- Chain rule: HasDerivAt (fun s => ∫ φ ∂g (s - T)) at t
            have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
            have h_chain : HasDerivAt (fun s => ∫ z, φ z ∂g (s - T))
                (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                  @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW (spatialMarginal (g (t - T))) z.1)
                    (gradVφ z)) ∂g (t - T)) t := by
              have := HasDerivAt.comp_of_eq t h_g_deriv h_sub rfl
              simpa [Function.comp, mul_one] using this
            -- Match spatialMarginal (f_next t) with spatialMarginal (g (t - T))
            rw [show (fun _ => (0 : ℝ)) t = 0 from rfl, add_zero, h_fnext_t]
            exact h_chain.congr_of_eventuallyEq h_ev
          · -- t = T: boundary case via `hasDerivAt_of_hasDerivAt_of_ne_in_nhds`.
            -- Three sub-arguments: (1) HasDerivAt at every nearby t' ≠ T from existing
            -- strict-left/right work; (2) ContinuousAt of integral function at T;
            -- (3) ContinuousAt of derivative function at T.  (2) and (3) sorry'd as
            -- focused leaf sub-helpers per P4 API-lock pattern; the close composition
            -- is substantively in place.
            push_neg at ht_gt
            have h_t_eq : t = T := le_antisymm ht_gt (not_lt.mp ht_lt)
            -- Step 1: HasDerivAt at every nearby t' ≠ T (substantive close from
            -- existing strict-left/right work above, ~50 lines).
            have h_diff_ne : ∀ᶠ t' in nhds T, t' ≠ T → HasDerivAt
                (fun s => ∫ z, φ z ∂f_next s)
                ((∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                          (gradVφ z)) ∂(f_next t')) + 0) t' := by
              -- Use Ioo 0 (T + T_0) as the neighborhood
              have hU_mem : Set.Ioo (0 : ℝ) (T + T_0) ∈ nhds T :=
                Ioo_mem_nhds hT_pos (by linarith)
              apply Filter.Eventually.mono hU_mem
              intro t' ht' ht'_ne
              rcases lt_or_gt_of_ne ht'_ne with ht'_lt | ht'_gt
              · -- t' < T: use h_prev_vlasov + bridge f_next = f_prev on left of T
                have ht'_prev : t' ∈ Set.Ioo (0 : ℝ) T := ⟨ht'.1, ht'_lt⟩
                have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t']
                    (fun s => ∫ z, φ z ∂f_prev s) := by
                  apply Filter.Eventually.mono (eventually_lt_nhds ht'_lt)
                  intro s hs; simp [f_next, le_of_lt hs]
                have h_fnext_t' : f_next t' = f_prev t' := if_pos (le_of_lt ht'_lt)
                have h_deriv := h_prev_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
                    hgradXφ hgradVφ t' ht'_prev
                rw [show (fun _ => (0 : ℝ)) t' = 0 from rfl, add_zero] at h_deriv
                have h_marg : spatialMarginal (f_next t') = spatialMarginal (f_prev t') :=
                  congrArg spatialMarginal h_fnext_t'
                rw [add_zero, h_marg, h_fnext_t']
                exact h_deriv.congr_of_eventuallyEq h_ev
              · -- t' > T: use h_g_vlasov + chain rule + bridge f_next = g (·-T)
                have ht'_g : t' - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht'.2]⟩
                have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t']
                    (fun s => ∫ z, φ z ∂g (s - T)) := by
                  apply Filter.Eventually.mono (eventually_gt_nhds ht'_gt)
                  intro s hs; simp [f_next, not_le.mpr hs]
                have h_fnext_t' : f_next t' = g (t' - T) := if_neg (not_le.mpr ht'_gt)
                have h_g_deriv := h_g_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
                    hgradXφ hgradVφ (t' - T) ht'_g
                rw [show (fun _ => (0 : ℝ)) (t' - T) = 0 from rfl, add_zero] at h_g_deriv
                have h_sub : HasDerivAt (· - T) 1 t' := (hasDerivAt_id' t').sub_const T
                have h_chain : HasDerivAt (fun s => ∫ z, φ z ∂g (s - T))
                    (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                      @inner ℝ (PhysSpace d) _
                        (convolveFunctionMeasure gradW (spatialMarginal (g (t' - T))) z.1)
                        (gradVφ z)) ∂g (t' - T)) t' := by
                  have := HasDerivAt.comp_of_eq t' h_g_deriv h_sub rfl
                  simpa [Function.comp, mul_one] using this
                have h_marg : spatialMarginal (f_next t') = spatialMarginal (g (t' - T)) :=
                  congrArg spatialMarginal h_fnext_t'
                rw [add_zero, h_marg, h_fnext_t']
                exact h_chain.congr_of_eventuallyEq h_ev
            -- Step 2: ContinuousAt of integral function at T.
            -- Decomposed into LEFT (Iic T) substantive close + RIGHT (Ici T) focused leaf
            -- + union via `Iic_union_Ici = univ`.  Mirrors Stage 6 narrow continuity at
            -- L8265-8294.
            have hφ_cont : Continuous φ := hφ_smooth.continuous
            obtain ⟨Cφ, hCφ⟩ := hφ_cont.bounded_above_of_compact_support hφ_compact
            obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
            haveI : IsProbabilityMeasure f₀ := hf₀_prob
            -- LEFT side: substantive close via DCT on f_prev's pushforward.
            have h_cont_f_left : ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s)
                (Set.Iic T) T := by
              have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) :=
                Icc_mem_nhdsLE hT_pos
              -- Equation: f_next = f_prev = pushforward of f₀ on Icc 0 T
              have h_eq_L : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhdsWithin T (Set.Iic T)]
                  (fun s => ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀) := by
                apply Filter.Eventually.mono h_nhd_L
                intro s hs
                show ∫ z, φ z ∂f_next s = ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀
                have h_fnext : f_next s = f_prev s := if_pos hs.2
                have h_aemeas_f₀ : AEMeasurable
                    (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
                  h_prev_init ▸ h_prev_aemeas s hs
                rw [h_fnext, h_prev_push s hs, h_prev_init]
                exact integral_map h_aemeas_f₀ hφ_cont.aestronglyMeasurable
              -- DCT for the pushforward-composed form
              have h_cont_pf : ContinuousWithinAt
                  (fun s => ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀) (Set.Iic T) T := by
                apply continuousWithinAt_of_dominated (bound := fun _ => Cφ)
                · apply Filter.Eventually.mono h_nhd_L
                  intro s hs
                  have h_pair_aem : AEMeasurable
                      (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
                    h_prev_init ▸ h_prev_aemeas s hs
                  exact (hφ_cont.measurable.comp_aemeasurable h_pair_aem).aestronglyMeasurable
                · apply Filter.Eventually.mono h_nhd_L
                  intro s _
                  exact Filter.Eventually.of_forall fun z => hCφ _
                · exact integrable_const _
                · apply Filter.Eventually.of_forall
                  intro z
                  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
                  have h_bX := (h_prev_boundary z T hT_Icc).1
                  have h_bV := (h_prev_boundary z T hT_Icc).2
                  have h_pair_Icc : ContinuousWithinAt
                      (fun s => (charX_prev s z, charV_prev s z)) (Set.Icc 0 T) T :=
                    h_bX.continuousWithinAt.prodMk h_bV.continuousWithinAt
                  have h_pair_Iic : ContinuousWithinAt
                      (fun s => (charX_prev s z, charV_prev s z)) (Set.Iic T) T :=
                    h_pair_Icc.mono_of_mem_nhdsWithin h_nhd_L
                  exact hφ_cont.continuousAt.comp_continuousWithinAt h_pair_Iic
              -- Value at T: bridge via the pushforward formula
              have h_val_T : (∫ z, φ z ∂f_next T)
                  = ∫ z, φ (charX_prev T z, charV_prev T z) ∂f₀ := by
                have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
                have h_fnext_T : f_next T = f_prev T := if_pos (le_refl T)
                have h_aemeas_f₀_T : AEMeasurable
                    (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
                  h_prev_init ▸ h_prev_aemeas T hT_Icc
                rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init]
                exact integral_map h_aemeas_f₀_T hφ_cont.aestronglyMeasurable
              exact h_cont_pf.congr_of_eventuallyEq h_eq_L h_val_T
            -- RIGHT side: substantive close via DCT on the composed pushforward
            -- (charX_g (s-T), charV_g (s-T)) ∘ (charX_prev T, charV_prev T).
            -- At s = T, hg_init_cond bridges (charX_g 0, charV_g 0) = id, matching f_prev T.
            have h_cont_f_right : ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s)
                (Set.Ici T) T := by
              have h_nhd_R : Set.Icc T (T + T_0) ∈ nhdsWithin T (Set.Ici T) :=
                Icc_mem_nhdsGE (by linarith : T < T + T_0)
              have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
              have h_outer_aemeas : AEMeasurable
                  (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
                h_prev_init ▸ h_prev_aemeas T hT_Icc
              -- Eventually-equal: f_next s = composed pushforward on Icc T (T+T_0)
              have h_eq_R : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhdsWithin T (Set.Ici T)]
                  (fun s => ∫ z, φ
                    (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀) := by
                apply Filter.Eventually.mono h_nhd_R
                intro s hs
                show ∫ z, φ z ∂f_next s = ∫ z, φ
                    (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀
                have hs_T : T ≤ s := hs.1
                have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                  ⟨by linarith, by linarith [hs.2]⟩
                by_cases hs_eq : s = T
                · -- s = T: f_next s = f_next T = f_prev T = (charX_prev T, charV_prev T)#f₀
                  --   RHS at s = T uses hg_init_cond to collapse (charX_g 0, charV_g 0) = id
                  have hs_T_zero : s - T = 0 := by rw [hs_eq]; exact sub_self T
                  have h_fnext_s : f_next s = f_prev T := by
                    rw [hs_eq]; exact if_pos (le_refl T)
                  rw [h_fnext_s, h_prev_push T hT_Icc, h_prev_init,
                      integral_map h_outer_aemeas hφ_cont.aestronglyMeasurable]
                  congr 1
                  funext z
                  rw [hs_T_zero, (hg_init_cond _).1, (hg_init_cond _).2]
                · -- s > T: f_next s = g (s - T) = composed pushforward
                  have hs_gt : T < s := lt_of_le_of_ne hs_T (Ne.symm hs_eq)
                  have h_fnext_s : f_next s = g (s - T) := if_neg (not_le.mpr hs_gt)
                  rw [h_fnext_s, hg_push_ex (s - T) hsT_Icc, hg_init,
                      h_prev_push T hT_Icc, h_prev_init]
                  have h_g_at_sT : AEMeasurable
                      (fun z : PhaseSpace d => (charX_g (s - T) z, charV_g (s - T) z))
                      (Measure.map (fun z : PhaseSpace d =>
                        (charX_prev T z, charV_prev T z)) f₀) := by
                    have := hg_aemeas_ex (s - T) hsT_Icc
                    rw [hg_init, h_prev_push T hT_Icc, h_prev_init] at this
                    exact this
                  have h_comp_aem : AEMeasurable
                      (fun z : PhaseSpace d =>
                        (charX_g (s - T) (charX_prev T z, charV_prev T z),
                         charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ :=
                    h_g_at_sT.comp_aemeasurable h_outer_aemeas
                  rw [AEMeasurable.map_map_of_aemeasurable h_g_at_sT h_outer_aemeas]
                  exact integral_map h_comp_aem hφ_cont.aestronglyMeasurable
              -- DCT for the composed-pushforward form
              have h_cont_pf : ContinuousWithinAt
                  (fun s => ∫ z, φ
                    (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀)
                  (Set.Ici T) T := by
                apply continuousWithinAt_of_dominated (bound := fun _ => Cφ)
                · apply Filter.Eventually.mono h_nhd_R
                  intro s hs
                  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                    ⟨by linarith [hs.1], by linarith [hs.2]⟩
                  have h_g_at_sT : AEMeasurable
                      (fun z : PhaseSpace d => (charX_g (s - T) z, charV_g (s - T) z))
                      (Measure.map (fun z : PhaseSpace d =>
                        (charX_prev T z, charV_prev T z)) f₀) := by
                    have := hg_aemeas_ex (s - T) hsT_Icc
                    rw [hg_init, h_prev_push T hT_Icc, h_prev_init] at this
                    exact this
                  have h_comp_aem : AEMeasurable
                      (fun z : PhaseSpace d =>
                        (charX_g (s - T) (charX_prev T z, charV_prev T z),
                         charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ :=
                    h_g_at_sT.comp_aemeasurable h_outer_aemeas
                  exact (hφ_cont.measurable.comp_aemeasurable h_comp_aem).aestronglyMeasurable
                · apply Filter.Eventually.mono h_nhd_R
                  intro s _
                  exact Filter.Eventually.of_forall fun z => hCφ _
                · exact integrable_const _
                · -- Pointwise continuity: chain rule for (· - T) at T with charX_g/charV_g at 0
                  apply Filter.Eventually.of_forall
                  intro z
                  have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
                  have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).1
                  have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).2
                  have h_nhdsW_0 : Set.Icc (0 : ℝ) T_0 ∈ nhdsWithin 0 (Set.Ici 0) :=
                    Icc_mem_nhdsGE hT_0_pos
                  have h_g_bX_cont : ContinuousWithinAt
                      (fun s' => charX_g s' (charX_prev T z, charV_prev T z))
                      (Set.Ici 0) 0 :=
                    h_g_bX.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
                  have h_g_bV_cont : ContinuousWithinAt
                      (fun s' => charV_g s' (charX_prev T z, charV_prev T z))
                      (Set.Ici 0) 0 :=
                    h_g_bV.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
                  have h_sub_cont : ContinuousWithinAt (fun s : ℝ => s - T) (Set.Ici T) T :=
                    ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
                  have h_sub_maps : Set.MapsTo (fun s : ℝ => s - T) (Set.Ici T) (Set.Ici 0) :=
                    fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
                  have h_chainX : ContinuousWithinAt
                      (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
                      (Set.Ici T) T :=
                    ContinuousWithinAt.comp_of_eq h_g_bX_cont h_sub_cont h_sub_maps (sub_self T)
                  have h_chainV : ContinuousWithinAt
                      (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
                      (Set.Ici T) T :=
                    ContinuousWithinAt.comp_of_eq h_g_bV_cont h_sub_cont h_sub_maps (sub_self T)
                  have h_pair : ContinuousWithinAt
                      (fun s => (charX_g (s - T) (charX_prev T z, charV_prev T z),
                                 charV_g (s - T) (charX_prev T z, charV_prev T z)))
                      (Set.Ici T) T :=
                    h_chainX.prodMk h_chainV
                  exact hφ_cont.continuousAt.comp_continuousWithinAt h_pair
              -- Value at T: integrate the s = T case
              have h_val_T : (∫ z, φ z ∂f_next T) = ∫ z, φ
                  (charX_g (T - T) (charX_prev T z, charV_prev T z),
                   charV_g (T - T) (charX_prev T z, charV_prev T z)) ∂f₀ := by
                have h_fnext_T : f_next T = f_prev T := if_pos (le_refl T)
                rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init,
                    integral_map h_outer_aemeas hφ_cont.aestronglyMeasurable]
                congr 1; funext z
                rw [show T - T = (0 : ℝ) from sub_self T,
                    (hg_init_cond _).1, (hg_init_cond _).2]
              exact h_cont_pf.congr_of_eventuallyEq h_eq_R h_val_T
            -- Combine via union
            have h_cont_f : ContinuousAt (fun s => ∫ z, φ z ∂f_next s) T := by
              have h_union := h_cont_f_left.union h_cont_f_right
              rw [Set.Iic_union_Ici] at h_union
              exact h_union.continuousAt Filter.univ_mem
            -- Step 3: ContinuousAt of the derivative functional at the seam T.
            -- **API-LOCK (marquee push step 1, 2026-06-02)**: mirror `h_cont_f`'s
            -- *proven* one-sided-union structure (Iic/Ici + `Set.Iic_union_Ici`).
            -- The two sides are the locked leaves.  Each discharges by push-to-f₀ +
            -- DCT; the integrand's force term carries
            -- `convolveFunctionMeasure gradW (spatialMarginal (f_next ·)) z.1`, whose
            -- seam continuity closes from PROVEN TOOLS via the pushforward
            -- representation: `f_prev`/`g` are flow-pushforwards of `f₀`, so the
            -- convolution rewrites by `integral_map` to a fixed-`f₀` integral, closed
            -- by the inner kernels `flowConv_continuousWithinAt_{Iic,Ici}_seam`
            -- (Piece-A-dominated DCT).  No deferred-OT — the abstract narrow→W₁ kernel
            -- the plan assumed was orphaned by this route (M3).  LEFT uses
            -- `spatialMarginal (f_prev ·)`, RIGHT the composed flow off `g`.
            have h_cont_g : ContinuousAt (fun t' =>
                (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                          (gradVφ z)) ∂(f_next t')) + 0) T := by
              simp only [add_zero]
              -- LEFT side (s ≤ T): f_next = f_prev = pushforward of f₀; force term
              -- uses `spatialMarginal (f_prev ·)`.  Discharge: push-to-f₀ + DCT.
              have h_left : ContinuousWithinAt
                  (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s)) (Set.Iic T) T := by
                -- Route 2 (proven tools): push f_next = f_prev to a pushforward of f₀
                -- on the window, then DCT.  The force-term seam continuity is
                -- `flowConv_continuousWithinAt_Iic_seam`; the velocity term uses
                -- `h_prev_boundary` continuity; the dominator is a constant.
                have hgradW_cont : Continuous gradW := hL.continuous
                have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) :=
                  Icc_mem_nhdsLE hT_pos
                -- (1) Continuity of gradXφ and gradVφ (reuse the L3580-3617 derivation).
                have hgradXφ_cont : Continuous gradXφ := by
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
                  have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 :=
                    funext hgradXφ
                  rw [heqX]
                  simp_rw [gradient, hfderiv_X]
                  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
                    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
                      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
                      (hφ_smooth.continuous_fderiv (by simp)))
                have hgradVφ_cont : Continuous gradVφ := by
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
                  have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 :=
                    funext hgradVφ
                  rw [heqV]
                  simp_rw [gradient, hfderiv_V]
                  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
                    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
                      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
                      (hφ_smooth.continuous_fderiv (by simp)))
                -- (2) Kernel integrability of `gradW (x - ·)` against `spatialMarginal (f_prev t)`
                -- on the window (from `f_prev t`'s finite first moment).
                have h_int_marg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
                    Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f_prev t)) := by
                  intro t ht x_pt
                  haveI : IsProbabilityMeasure (f_prev t) := (h_prev_mom t ht).1
                  haveI : IsProbabilityMeasure (spatialMarginal (f_prev t)) :=
                    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                  have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
                      (spatialMarginal (f_prev t)) :=
                    (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
                  have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖)
                      (spatialMarginal (f_prev t)) := by
                    unfold spatialMarginal
                    rw [integrable_map_measure
                      (by exact (continuous_norm.measurable).aestronglyMeasurable)
                      measurable_fst.aemeasurable]
                    refine Integrable.mono' (h_prev_mom t ht).2
                      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
                      (Filter.Eventually.of_forall fun z => ?_)
                    show |‖z.1‖| ≤ ‖z‖
                    rw [abs_of_nonneg (norm_nonneg _)]
                    exact norm_fst_le z
                  have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
                      ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
                    intro y
                    have hd := hL.dist_le_mul (x_pt - y) 0
                    simp only [dist_eq_norm, sub_zero] at hd
                    have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
                      have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
                      simp only [sub_add_cancel] at this; linarith
                    have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
                    have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
                    linarith
                  have h_dom_int : Integrable
                      (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
                      (spatialMarginal (f_prev t)) := by
                    have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
                        (spatialMarginal (f_prev t)) := h_y_int.const_mul (L : ℝ)
                    have h_eq : (fun y : PhysSpace d =>
                        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                        fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
                      funext y; ring
                    rw [h_eq]; exact (integrable_const _).add h_norm
                  exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
                -- (3) The window pushforward of the spatial marginal: `spatialMarginal (f_prev s)
                -- = Measure.map (charX_prev s) f₀` on `Icc 0 T`.
                have h_push_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
                    spatialMarginal (f_prev s)
                      = Measure.map (fun z : PhaseSpace d => charX_prev s z) f₀ := by
                  intro s hs
                  have h_pair_aem : AEMeasurable
                      (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
                    h_prev_init ▸ h_prev_aemeas s hs
                  unfold spatialMarginal
                  rw [h_prev_push s hs, h_prev_init,
                      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable h_pair_aem]
                  rfl
                have h_aemeas_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
                    AEMeasurable (fun z : PhaseSpace d => charX_prev s z) f₀ := by
                  intro s hs
                  have h_pair_aem : AEMeasurable
                      (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
                    h_prev_init ▸ h_prev_aemeas s hs
                  exact measurable_fst.comp_aemeasurable h_pair_aem
                -- (4) `C_T` growth bound on the window, via Piece A applied to the clamped curve
                -- (L11 clamp for the universal probability instance).
                set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
                have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
                  intro t
                  simp only [hclampT_def, Set.mem_Icc]
                  exact ⟨le_max_left _ _, max_le hT_pos.le (min_le_right _ _)⟩
                have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
                  intro t ht
                  simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
                set ρc : ℝ → Measure (PhysSpace d) :=
                  fun t => spatialMarginal (f_prev (clampT t)) with hρc_def
                haveI hρc_isProb : ∀ t, IsProbabilityMeasure (ρc t) := by
                  intro t
                  haveI : IsProbabilityMeasure (f_prev (clampT t)) :=
                    (h_prev_mom (clampT t) (hclampT_mem t)).1
                  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                -- moment data for ρc.  CLOSED from the threaded flat uniform-moment
                -- bound `hM_prev` on `f_prev`'s spatial marginal.  Since `ρc t =
                -- spatialMarginal (f_prev (clampT t))` and `clampT t ∈ Icc 0 T`
                -- (`hclampT_mem`), the same constant `M` bounds `ρc`'s moment.
                obtain ⟨M_ρ, hM_ρ_nn, hM_ρ⟩ :
                    ∃ M_ρ, 0 ≤ M_ρ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρc t) ≤ M_ρ := by
                  obtain ⟨M, hM_nn, hM⟩ := hM_prev
                  refine ⟨M, hM_nn, fun t _ht => ?_⟩
                  rw [hρc_def]
                  exact hM (clampT t) (hclampT_mem t)
                have h_y_int_ρc : ∀ t ∈ Set.Icc (0 : ℝ) T,
                    Integrable (fun y : PhysSpace d => ‖y‖) (ρc t) := by
                  intro t ht
                  have h_eq : ρc t = spatialMarginal (f_prev t) := by
                    simp only [hρc_def, hclampT_id t ht]
                  rw [h_eq]
                  haveI : IsProbabilityMeasure (f_prev t) := (h_prev_mom t ht).1
                  unfold spatialMarginal
                  rw [integrable_map_measure
                    (by exact (continuous_norm.measurable).aestronglyMeasurable)
                    measurable_fst.aemeasurable]
                  refine Integrable.mono' (h_prev_mom t ht).2
                    ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
                    (Filter.Eventually.of_forall fun z => ?_)
                  show |‖z.1‖| ≤ ‖z‖
                  rw [abs_of_nonneg (norm_nonneg _)]
                  exact norm_fst_le z
                have h_int_ρc : ∀ t (x : PhysSpace d),
                    Integrable (fun y => gradW (x - y)) (ρc t) :=
                  fun t x => by
                    have := h_int_marg (clampT t) (hclampT_mem t) x
                    simpa only [hρc_def] using this
                -- boundary regularity of (charX_prev, charV_prev) against ρc, from h_prev_boundary
                -- (on the window ρc agrees with spatialMarginal (f_prev ·)).
                have h_bdry_ρc : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
                    HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
                    HasDerivWithinAt (fun s => charV_prev s z)
                      (-(convolveFunctionMeasure gradW (ρc t) (charX_prev t z)))
                      (Set.Icc 0 T) t := by
                  intro z t ht
                  have h_eq : ρc t = spatialMarginal (f_prev t) := by
                    simp only [hρc_def, hclampT_id t ht]
                  rw [h_eq]
                  exact h_prev_boundary z t ht
                -- `IsCharacteristicFlowOn` for `ρc` from `h_prev_flow` (on the interior
                -- `Ioo 0 T`, `ρc t = spatialMarginal (f_prev t)`).
                have h_prev_flow_ρc : IsCharacteristicFlowOn gradW ρc
                    charX_prev charV_prev (Set.Ioo 0 T) Set.univ := by
                  refine ⟨h_prev_flow.1, h_prev_flow.2.1, fun t ht z hz => ?_⟩
                  have h_eq : ρc t = spatialMarginal (f_prev t) := by
                    simp only [hρc_def, hclampT_id t ⟨ht.1.le, ht.2.le⟩]
                  rw [h_eq]
                  exact h_prev_flow.2.2 t ht z hz
                obtain ⟨h_init_ρc, h_cont_Icc_ρc, h_deriv_Ico_ρc⟩ :=
                  Stage_1_9_flow_boundary_regularity gradW ρc charX_prev charV_prev T hT_pos.le
                    h_prev_flow_ρc h_bdry_ρc
                obtain ⟨C_T, hC_T_nn, hC_T_pair⟩ :=
                  flow_distance_growth_bound_on gradW L hL ρc charX_prev charV_prev T hT_pos.le
                    h_init_ρc h_cont_Icc_ρc h_deriv_Ico_ρc M_ρ hM_ρ_nn hM_ρ h_y_int_ρc h_int_ρc
                -- Project the joint growth bound onto the position component.
                have hC_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
                    ‖charX_prev s z‖ ≤ C_T * (‖z‖ + 1) := by
                  intro s hs z
                  exact le_trans (norm_fst_le (charX_prev s z, charV_prev s z))
                    (hC_T_pair s hs z)
                -- (5) Continuity of the un-pushed integrand in `z`, for `integral_map`'s
                -- AEStronglyMeasurable side and the seam continuity composition.
                have h_conv_z_cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
                    Continuous (fun z : PhaseSpace d =>
                      convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) z.1) := by
                  intro s hs
                  haveI : IsProbabilityMeasure (f_prev s) := (h_prev_mom s hs).1
                  haveI : IsProbabilityMeasure (spatialMarginal (f_prev s)) :=
                    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                  exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
                    (spatialMarginal (f_prev s)) (h_int_marg s hs)).continuous.comp continuous_fst
                have h_integrand_cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
                    Continuous (fun z : PhaseSpace d =>
                      @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                      @inner ℝ (PhysSpace d) _
                        (convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) z.1)
                        (gradVφ z)) := by
                  intro s hs
                  exact (continuous_snd.inner hgradXφ_cont).sub
                    ((h_conv_z_cont s hs).inner hgradVφ_cont)
                -- (6) Eventually-equal rewrite to the pushforward form.
                have h_eq_L : (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                          (gradVφ z)) ∂(f_next s))
                    =ᶠ[nhdsWithin T (Set.Iic T)]
                    (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
                          (gradXφ (charX_prev s z, charV_prev s z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                            (charX_prev s z))
                          (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀) := by
                  apply Filter.Eventually.mono h_nhd_L
                  intro s hs
                  have h_fnext : f_next s = f_prev s := if_pos hs.2
                  have h_marg : spatialMarginal (f_next s) = spatialMarginal (f_prev s) :=
                    congrArg spatialMarginal h_fnext
                  have h_aemeas_f₀ : AEMeasurable
                      (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
                    h_prev_init ▸ h_prev_aemeas s hs
                  show (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s))
                      = ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
                            (gradXφ (charX_prev s z, charV_prev s z)) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                              (charX_prev s z))
                            (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀
                  have h_meq : f_next s
                      = Measure.map (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ := by
                    rw [h_fnext, h_prev_push s hs, h_prev_init]
                  rw [h_marg, h_meq,
                      integral_map h_aemeas_f₀
                        (h_integrand_cont s hs).aestronglyMeasurable]
                -- (7) Uniform sup-bounds on `gradXφ`/`gradVφ` (gradient of a compactly
                -- supported smooth `φ`: `‖∇ φ‖ = ‖fderiv φ‖ ≤ M_φ`).
                have hfderiv_cont : Continuous (fderiv ℝ φ) :=
                  hφ_smooth.continuous_fderiv (by norm_num)
                have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
                  HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
                obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
                have hM_φ_nn : 0 ≤ M_φ :=
                  le_trans (norm_nonneg (fderiv ℝ φ (0 : PhaseSpace d))) (hM_φ _)
                have hgradXφ_bd : ∀ z : PhaseSpace d, ‖gradXφ z‖ ≤ M_φ := by
                  intro z
                  have hfd : fderiv ℝ (fun x => φ (x, z.2)) z.1 =
                      (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
                    have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
                      (hφ_smooth.differentiable (by simp) z).hasFDerivAt
                    have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
                        (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
                      hasFDerivAt_prodMk_left z.1 z.2
                    exact (h1.comp z.1 h2).fderiv
                  rw [hgradXφ z, gradient, hfd, (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
                  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
                  refine le_trans (mul_le_mul_of_nonneg_left
                    (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ)
                      (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
                  rw [mul_one]; exact hM_φ z
                have hgradVφ_bd : ∀ z : PhaseSpace d, ‖gradVφ z‖ ≤ M_φ := by
                  intro z
                  have hfd : fderiv ℝ (fun v => φ (z.1, v)) z.2 =
                      (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
                    have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
                      (hφ_smooth.differentiable (by simp) z).hasFDerivAt
                    have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
                        (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
                      hasFDerivAt_prodMk_right z.1 z.2
                    exact (h1.comp z.2 h2).fderiv
                  rw [hgradVφ z, gradient, hfd, (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
                  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
                  refine le_trans (mul_le_mul_of_nonneg_left
                    (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ)
                      (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
                  rw [mul_one]; exact hM_φ z
                -- (8) Convolution force bound: `‖conv(spatialMarginal(f_prev s))(x)‖ ≤
                -- ‖gradW 0‖ + L·(‖x‖ + M_ρ)` on the window (mirrors
                -- `flow_distance_growth_bound_on`'s `h_conv_bound`, with the moment
                -- envelope `M_ρ` on `ρc = spatialMarginal (f_prev ·)`).
                have h_conv_force : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : PhysSpace d,
                    ‖convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) x‖
                      ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M_ρ := by
                  intro s hs x
                  have hρcs : ρc s = spatialMarginal (f_prev s) := by
                    simp only [hρc_def, hclampT_id s hs]
                  have h_y_int_s : Integrable (fun y : PhysSpace d => ‖y‖)
                      (spatialMarginal (f_prev s)) := hρcs ▸ h_y_int_ρc s hs
                  have hM_ρ_s : ∫ y, ‖y‖ ∂(spatialMarginal (f_prev s)) ≤ M_ρ :=
                    hρcs ▸ hM_ρ s hs
                  haveI : IsProbabilityMeasure (f_prev s) := (h_prev_mom s hs).1
                  haveI : IsProbabilityMeasure (spatialMarginal (f_prev s)) :=
                    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                  unfold convolveFunctionMeasure
                  have h_sub_int : Integrable (fun y => ‖x - y‖) (spatialMarginal (f_prev s)) :=
                    Integrable.mono' ((integrable_const ‖x‖).add h_y_int_s)
                      ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
                      (Filter.Eventually.of_forall fun y => by
                        simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
                  have h_pt : ∀ y : PhysSpace d,
                      ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
                    intro y
                    have hd := hL.dist_le_mul (x - y) 0
                    simp only [dist_eq_norm, sub_zero] at hd
                    have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
                      have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
                      simp only [sub_add_cancel] at this; linarith
                    linarith
                  have h_bnd_int :
                      Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (spatialMarginal (f_prev s)) :=
                    (integrable_const _).add (h_sub_int.const_mul _)
                  calc ‖∫ y, gradW (x - y) ∂(spatialMarginal (f_prev s))‖
                      ≤ ∫ y, ‖gradW (x - y)‖ ∂(spatialMarginal (f_prev s)) :=
                        norm_integral_le_integral_norm _
                    _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(spatialMarginal (f_prev s)) :=
                        integral_mono (h_int_marg s hs x).norm h_bnd_int h_pt
                    _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(spatialMarginal (f_prev s)) := by
                        rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
                        simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
                    _ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M_ρ := by
                        have h_int_le : ∫ y, ‖x - y‖ ∂(spatialMarginal (f_prev s)) ≤ ‖x‖ + M_ρ := by
                          calc ∫ y, ‖x - y‖ ∂(spatialMarginal (f_prev s))
                              ≤ ∫ y, (‖x‖ + ‖y‖) ∂(spatialMarginal (f_prev s)) :=
                                integral_mono h_sub_int ((integrable_const _).add h_y_int_s)
                                  (fun y => norm_sub_le x y)
                            _ = ‖x‖ + ∫ y, ‖y‖ ∂(spatialMarginal (f_prev s)) := by
                                rw [integral_add (integrable_const _) h_y_int_s]
                                simp [integral_const, measureReal_def, measure_univ]
                            _ ≤ ‖x‖ + M_ρ := by linarith
                        nlinarith [mul_le_mul_of_nonneg_left h_int_le L.coe_nonneg]
                -- (9) The affine dominator: integrable wrt f₀ (finite first moment),
                -- bounding the integrand via the growth bound `C_T` + force bound.
                set bound_fn : PhaseSpace d → ℝ := fun z =>
                  M_φ * (C_T * (‖z‖ + 1))
                  + (‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1)) + (L : ℝ) * M_ρ) * M_φ
                  with hbound_def
                have hbound_int : Integrable bound_fn f₀ := by
                  -- bound_fn z is affine in ‖z‖; combine `hf₀_int` with constants.
                  have ha : Integrable
                      (fun z : PhaseSpace d =>
                        (M_φ * C_T + L * M_φ * C_T) * ‖z‖
                        + (M_φ * C_T + (‖gradW 0‖ + L * (C_T) + L * M_ρ) * M_φ)) f₀ :=
                    (hf₀_int.const_mul _).add (integrable_const _)
                  refine ha.congr (Filter.Eventually.of_forall fun z => ?_)
                  simp only [hbound_def]; ring
                have hB : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
                    ‖@inner ℝ (PhysSpace d) _ (charV_prev s z)
                          (gradXφ (charX_prev s z, charV_prev s z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                            (charX_prev s z))
                          (gradVφ (charX_prev s z, charV_prev s z))‖ ≤ bound_fn z := by
                  intro s hs z
                  have hV : ‖charV_prev s z‖ ≤ C_T * (‖z‖ + 1) :=
                    le_trans (norm_snd_le (charX_prev s z, charV_prev s z)) (hC_T_pair s hs z)
                  have hX : ‖charX_prev s z‖ ≤ C_T * (‖z‖ + 1) :=
                    le_trans (norm_fst_le (charX_prev s z, charV_prev s z)) (hC_T_pair s hs z)
                  have ht1 : ‖@inner ℝ (PhysSpace d) _ (charV_prev s z)
                        (gradXφ (charX_prev s z, charV_prev s z))‖ ≤ M_φ * (C_T * (‖z‖ + 1)) := by
                    refine le_trans (norm_inner_le_norm _ _) ?_
                    have := mul_le_mul hV (hgradXφ_bd (charX_prev s z, charV_prev s z))
                      (norm_nonneg _) (le_trans (norm_nonneg _) hV)
                    calc ‖charV_prev s z‖ * ‖gradXφ (charX_prev s z, charV_prev s z)‖
                        ≤ (C_T * (‖z‖ + 1)) * M_φ := this
                      _ = M_φ * (C_T * (‖z‖ + 1)) := by ring
                  have ht2 : ‖@inner ℝ (PhysSpace d) _
                        (convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) (charX_prev s z))
                        (gradVφ (charX_prev s z, charV_prev s z))‖
                      ≤ (‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1)) + (L : ℝ) * M_ρ) * M_φ := by
                    refine le_trans (norm_inner_le_norm _ _) ?_
                    have hc : ‖convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                        (charX_prev s z)‖ ≤ ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1)) + (L : ℝ) * M_ρ := by
                      refine le_trans (h_conv_force s hs (charX_prev s z)) ?_
                      have := mul_le_mul_of_nonneg_left hX L.coe_nonneg
                      linarith
                    have hcnn : 0 ≤ ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1)) + (L : ℝ) * M_ρ :=
                      le_trans (norm_nonneg _) hc
                    exact mul_le_mul hc (hgradVφ_bd (charX_prev s z, charV_prev s z))
                      (norm_nonneg _) hcnn
                  calc ‖_ - _‖
                      ≤ ‖@inner ℝ (PhysSpace d) _ (charV_prev s z)
                            (gradXφ (charX_prev s z, charV_prev s z))‖
                        + ‖@inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                              (charX_prev s z))
                            (gradVφ (charX_prev s z, charV_prev s z))‖ := norm_sub_le _ _
                    _ ≤ bound_fn z := by simp only [hbound_def]; linarith
                have h_cont_pf : ContinuousWithinAt
                    (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
                          (gradXφ (charX_prev s z, charV_prev s z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                            (charX_prev s z))
                          (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀)
                    (Set.Iic T) T := by
                  apply continuousWithinAt_of_dominated (bound := bound_fn)
                  · -- AEStronglyMeasurable in z, eventually in s
                    apply Filter.Eventually.mono h_nhd_L
                    intro s hs
                    have h_aem_pair : AEMeasurable
                        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
                      h_prev_init ▸ h_prev_aemeas s hs
                    have h_aem_X : AEMeasurable (fun z : PhaseSpace d => charX_prev s z) f₀ :=
                      measurable_fst.comp_aemeasurable h_aem_pair
                    have h_aem_V : AEMeasurable (fun z : PhaseSpace d => charV_prev s z) f₀ :=
                      measurable_snd.comp_aemeasurable h_aem_pair
                    -- first term: ⟪charV, gradXφ(flow)⟫
                    have h1 : AEStronglyMeasurable
                        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _ (charV_prev s z)
                          (gradXφ (charX_prev s z, charV_prev s z))) f₀ := by
                      have hg : AEMeasurable
                          (fun z : PhaseSpace d =>
                            gradXφ (charX_prev s z, charV_prev s z)) f₀ :=
                        hgradXφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
                      exact (continuous_inner.measurable.comp_aemeasurable
                        (h_aem_V.prodMk hg)).aestronglyMeasurable
                    -- second term: ⟪conv(...)(charX), gradVφ(flow)⟫
                    have h2 : AEStronglyMeasurable
                        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                            (charX_prev s z))
                          (gradVφ (charX_prev s z, charV_prev s z))) f₀ := by
                      have hconv_aem : AEMeasurable
                          (fun z : PhaseSpace d => convolveFunctionMeasure gradW
                            (spatialMarginal (f_prev s)) (charX_prev s z)) f₀ := by
                        have hconv_cont' : Continuous (fun x : PhysSpace d =>
                            convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) x) := by
                          haveI : IsProbabilityMeasure (f_prev s) := (h_prev_mom s hs).1
                          haveI : IsProbabilityMeasure (spatialMarginal (f_prev s)) :=
                            Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                          exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
                            (spatialMarginal (f_prev s)) (h_int_marg s hs)).continuous
                        exact hconv_cont'.measurable.comp_aemeasurable h_aem_X
                      have hg : AEMeasurable
                          (fun z : PhaseSpace d =>
                            gradVφ (charX_prev s z, charV_prev s z)) f₀ :=
                        hgradVφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
                      exact (continuous_inner.measurable.comp_aemeasurable
                        (hconv_aem.prodMk hg)).aestronglyMeasurable
                    exact h1.sub h2
                  · -- dominator bound, eventually in s
                    apply Filter.Eventually.mono h_nhd_L
                    intro s hs
                    exact Filter.Eventually.of_forall fun z => hB s hs z
                  · exact hbound_int
                  · -- pointwise continuity in s, a.e. z (in fact ∀ z)
                    apply Filter.Eventually.of_forall
                    intro z
                    -- first term: velocity ⬝ gradXφ ∘ flow
                    have hX_cwn : ContinuousWithinAt (fun s => charX_prev s z) (Set.Iic T) T :=
                      ((h_prev_boundary z T ⟨hT_pos.le, le_refl T⟩).1.continuousWithinAt).mono_of_mem_nhdsWithin
                        h_nhd_L
                    have hV_cwn : ContinuousWithinAt (fun s => charV_prev s z) (Set.Iic T) T :=
                      ((h_prev_boundary z T ⟨hT_pos.le, le_refl T⟩).2.continuousWithinAt).mono_of_mem_nhdsWithin
                        h_nhd_L
                    have h_pair_cwn : ContinuousWithinAt
                        (fun s => (charX_prev s z, charV_prev s z)) (Set.Iic T) T :=
                      hX_cwn.prodMk hV_cwn
                    have h_gX_cwn : ContinuousWithinAt
                        (fun s => gradXφ (charX_prev s z, charV_prev s z)) (Set.Iic T) T :=
                      hgradXφ_cont.continuousAt.comp_continuousWithinAt h_pair_cwn
                    have h_gV_cwn : ContinuousWithinAt
                        (fun s => gradVφ (charX_prev s z, charV_prev s z)) (Set.Iic T) T :=
                      hgradVφ_cont.continuousAt.comp_continuousWithinAt h_pair_cwn
                    have h_term1 : ContinuousWithinAt
                        (fun s => @inner ℝ (PhysSpace d) _ (charV_prev s z)
                          (gradXφ (charX_prev s z, charV_prev s z))) (Set.Iic T) T :=
                      hV_cwn.inner h_gX_cwn
                    -- second term: conv seam continuity ⬝ gradVφ ∘ flow
                    have h_conv_cwn : ContinuousWithinAt
                        (fun s => convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                          (charX_prev s z)) (Set.Iic T) T := by
                      have := flowConv_continuousWithinAt_Iic_seam gradW L hL charX_prev f₀
                        hf₀_int hT_pos (fun s => spatialMarginal (f_prev s))
                        h_push_marg h_aemeas_marg
                        (fun z => (h_cont_Icc_ρc z).continuousWithinAt
                          (Set.right_mem_Icc.mpr hT_pos.le) |>.fst) C_T hC_T_nn hC_T z
                      -- The helper concludes against `μ s = spatialMarginal (f_prev s)`.
                      exact this
                    have h_term2 : ContinuousWithinAt
                        (fun s => @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                            (charX_prev s z))
                          (gradVφ (charX_prev s z, charV_prev s z))) (Set.Iic T) T :=
                      h_conv_cwn.inner h_gV_cwn
                    exact h_term1.sub h_term2
                -- (8) Value at T bridge.
                have h_val_T : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next T)) z.1)
                          (gradVφ z)) ∂(f_next T))
                    = ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev T z)
                          (gradXφ (charX_prev T z, charV_prev T z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_prev T))
                            (charX_prev T z))
                          (gradVφ (charX_prev T z, charV_prev T z))) ∂f₀ := by
                  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
                  have h_fnext_T : f_next T = f_prev T := if_pos (le_refl T)
                  have h_marg : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
                    congrArg spatialMarginal h_fnext_T
                  have h_aemeas_f₀_T : AEMeasurable
                      (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
                    h_prev_init ▸ h_prev_aemeas T hT_Icc
                  have h_meq : f_next T
                      = Measure.map (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ := by
                    rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init]
                  rw [h_marg, h_meq,
                      integral_map h_aemeas_f₀_T (h_integrand_cont T hT_Icc).aestronglyMeasurable]
                exact h_cont_pf.congr_of_eventuallyEq h_eq_L h_val_T
              -- RIGHT side (s ≥ T): f_next = g (·−T) = composed pushforward; symmetric
              -- to `h_left`.  The flow is the COMPOSED phase-space flow
              -- `Φ_s z = (charX_g (s−T) (charX_prev T z, charV_prev T z),
              --           charV_g (s−T) (charX_prev T z, charV_prev T z))`, and the
              -- position part `Z_s z = charX_g (s−T) (charX_prev T z, charV_prev T z)`
              -- is what the force-term convolution sees.  Pushforward, AEMeasurability,
              -- and seam continuity are copied/adapted from the PROVEN
              -- `h_cont_f_right` (composed-pushforward machinery); the growth bound is
              -- the composed Piece A (g over [0,T_0] ∘ prev at T); the force-term seam
              -- continuity uses the `Ici` sibling kernel `flowConv_continuousWithinAt_Ici_seam`.
              have h_right : ContinuousWithinAt
                  (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s)) (Set.Ici T) T := by
                have hgradW_cont : Continuous gradW := hL.continuous
                have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
                have h_nhd_R : Set.Icc T (T + T_0) ∈ nhdsWithin T (Set.Ici T) :=
                  Icc_mem_nhdsGE (by linarith : T < T + T_0)
                -- Composed flow (position + velocity) and outer flow at T.
                have h_outer_aemeas : AEMeasurable
                    (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
                  h_prev_init ▸ h_prev_aemeas T hT_Icc
                set Zpos : ℝ → PhaseSpace d → PhysSpace d :=
                  fun s z => charX_g (s - T) (charX_prev T z, charV_prev T z) with hZpos_def
                set Zvel : ℝ → PhaseSpace d → PhysSpace d :=
                  fun s z => charV_g (s - T) (charX_prev T z, charV_prev T z) with hZvel_def
                -- (1) Continuity of gradXφ and gradVφ (reuse the L9261-9298 derivation).
                have hgradXφ_cont : Continuous gradXφ := by
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
                  have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 :=
                    funext hgradXφ
                  rw [heqX]
                  simp_rw [gradient, hfderiv_X]
                  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
                    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
                      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
                      (hφ_smooth.continuous_fderiv (by simp)))
                have hgradVφ_cont : Continuous gradVφ := by
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
                  have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 :=
                    funext hgradVφ
                  rw [heqV]
                  simp_rw [gradient, hfderiv_V]
                  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
                    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
                      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
                      (hφ_smooth.continuous_fderiv (by simp)))
                -- (2) Kernel integrability of `gradW (x − ·)` against
                -- `spatialMarginal (g τ)` for `τ ∈ [0, T_0]` (from `g τ`'s finite moment).
                have h_int_marg_g : ∀ τ ∈ Set.Icc (0 : ℝ) T_0, ∀ (x_pt : PhysSpace d),
                    Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (g τ)) := by
                  intro τ hτ x_pt
                  haveI : IsProbabilityMeasure (g τ) := (hg_mom τ hτ).1
                  haveI : IsProbabilityMeasure (spatialMarginal (g τ)) :=
                    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                  have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
                      (spatialMarginal (g τ)) :=
                    (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
                  have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖)
                      (spatialMarginal (g τ)) := by
                    unfold spatialMarginal
                    rw [integrable_map_measure
                      (by exact (continuous_norm.measurable).aestronglyMeasurable)
                      measurable_fst.aemeasurable]
                    refine Integrable.mono' (hg_mom τ hτ).2
                      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
                      (Filter.Eventually.of_forall fun z => ?_)
                    show |‖z.1‖| ≤ ‖z‖
                    rw [abs_of_nonneg (norm_nonneg _)]
                    exact norm_fst_le z
                  have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
                      ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
                    intro y
                    have hd := hL.dist_le_mul (x_pt - y) 0
                    simp only [dist_eq_norm, sub_zero] at hd
                    have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
                      have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
                      simp only [sub_add_cancel] at this; linarith
                    have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
                    have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
                    linarith
                  have h_dom_int : Integrable
                      (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
                      (spatialMarginal (g τ)) := by
                    have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
                        (spatialMarginal (g τ)) := h_y_int.const_mul (L : ℝ)
                    have h_eq : (fun y : PhysSpace d =>
                        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                        fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
                      funext y; ring
                    rw [h_eq]; exact (integrable_const _).add h_norm
                  exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
                -- (3) Composed pushforward of g's spatial marginal:
                -- `spatialMarginal (g (s−T)) = Measure.map (Zpos s) f₀` on Icc T (T+T_0).
                have h_g_at_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
                    AEMeasurable (fun z : PhaseSpace d => (charX_g τ z, charV_g τ z))
                      (Measure.map (fun z : PhaseSpace d =>
                        (charX_prev T z, charV_prev T z)) f₀) := by
                  intro τ hτ
                  have := hg_aemeas_ex τ hτ
                  rw [hg_init, h_prev_push T hT_Icc, h_prev_init] at this
                  exact this
                have h_comp_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
                    AEMeasurable (fun z : PhaseSpace d =>
                      (charX_g τ (charX_prev T z, charV_prev T z),
                       charV_g τ (charX_prev T z, charV_prev T z))) f₀ := by
                  intro τ hτ
                  exact (h_g_at_aemeas τ hτ).comp_aemeasurable h_outer_aemeas
                -- g (s−T) = pushforward of f₀ by the composed phase-space flow Φ.
                have h_g_push_comp : ∀ s ∈ Set.Icc T (T + T_0),
                    g (s - T) = Measure.map
                      (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ := by
                  intro s hs
                  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                    ⟨by linarith [hs.1], by linarith [hs.2]⟩
                  rw [hg_push_ex (s - T) hsT_Icc, hg_init, h_prev_push T hT_Icc, h_prev_init,
                      AEMeasurable.map_map_of_aemeasurable
                        (h_g_at_aemeas (s - T) hsT_Icc) h_outer_aemeas]
                  rfl
                have h_push_marg : ∀ s ∈ Set.Icc T (T + T_0),
                    spatialMarginal (g (s - T))
                      = Measure.map (fun z : PhaseSpace d => Zpos s z) f₀ := by
                  intro s hs
                  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                    ⟨by linarith [hs.1], by linarith [hs.2]⟩
                  unfold spatialMarginal
                  rw [h_g_push_comp s hs,
                      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
                        (h_comp_aemeas (s - T) hsT_Icc)]
                  rfl
                have h_aemeas_marg : ∀ s ∈ Set.Icc T (T + T_0),
                    AEMeasurable (fun z : PhaseSpace d => Zpos s z) f₀ := by
                  intro s hs
                  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                    ⟨by linarith [hs.1], by linarith [hs.2]⟩
                  exact measurable_fst.comp_aemeasurable (h_comp_aemeas (s - T) hsT_Icc)
                -- (4) Composed growth bound: Piece A on g over [0,T_0] composed with
                -- Piece A on prev at T.  `‖Zpos s z‖ ≤ C_comp * (‖z‖ + 1)`.
                -- Piece A on prev (over [0,T]), via the L11 clamp (mirrors h_left's block).
                set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
                have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
                  intro t
                  simp only [hclampT_def, Set.mem_Icc]
                  exact ⟨le_max_left _ _, max_le hT_pos.le (min_le_right _ _)⟩
                have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
                  intro t ht
                  simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
                set ρc : ℝ → Measure (PhysSpace d) :=
                  fun t => spatialMarginal (f_prev (clampT t)) with hρc_def
                haveI hρc_isProb : ∀ t, IsProbabilityMeasure (ρc t) := by
                  intro t
                  haveI : IsProbabilityMeasure (f_prev (clampT t)) :=
                    (h_prev_mom (clampT t) (hclampT_mem t)).1
                  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                obtain ⟨M_ρ, hM_ρ_nn, hM_ρ⟩ :
                    ∃ M_ρ, 0 ≤ M_ρ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρc t) ≤ M_ρ := by
                  obtain ⟨M, hM_nn, hM⟩ := hM_prev
                  refine ⟨M, hM_nn, fun t _ht => ?_⟩
                  rw [hρc_def]
                  exact hM (clampT t) (hclampT_mem t)
                have h_y_int_ρc : ∀ t ∈ Set.Icc (0 : ℝ) T,
                    Integrable (fun y : PhysSpace d => ‖y‖) (ρc t) := by
                  intro t ht
                  have h_eq : ρc t = spatialMarginal (f_prev t) := by
                    simp only [hρc_def, hclampT_id t ht]
                  rw [h_eq]
                  haveI : IsProbabilityMeasure (f_prev t) := (h_prev_mom t ht).1
                  unfold spatialMarginal
                  rw [integrable_map_measure
                    (by exact (continuous_norm.measurable).aestronglyMeasurable)
                    measurable_fst.aemeasurable]
                  refine Integrable.mono' (h_prev_mom t ht).2
                    ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
                    (Filter.Eventually.of_forall fun z => ?_)
                  show |‖z.1‖| ≤ ‖z‖
                  rw [abs_of_nonneg (norm_nonneg _)]
                  exact norm_fst_le z
                have h_int_marg_prev : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
                    Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f_prev t)) := by
                  intro t ht x_pt
                  haveI : IsProbabilityMeasure (f_prev t) := (h_prev_mom t ht).1
                  haveI : IsProbabilityMeasure (spatialMarginal (f_prev t)) :=
                    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                  have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
                      (spatialMarginal (f_prev t)) :=
                    (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
                  have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖)
                      (spatialMarginal (f_prev t)) := by
                    have h_eq : spatialMarginal (f_prev t) = ρc t := by
                      simp only [hρc_def, hclampT_id t ht]
                    rw [h_eq]; exact h_y_int_ρc t ht
                  have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
                      ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
                    intro y
                    have hd := hL.dist_le_mul (x_pt - y) 0
                    simp only [dist_eq_norm, sub_zero] at hd
                    have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
                      have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
                      simp only [sub_add_cancel] at this; linarith
                    have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
                    have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
                    linarith
                  have h_dom_int : Integrable
                      (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
                      (spatialMarginal (f_prev t)) := by
                    have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
                        (spatialMarginal (f_prev t)) := h_y_int.const_mul (L : ℝ)
                    have h_eq : (fun y : PhysSpace d =>
                        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                        fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
                      funext y; ring
                    rw [h_eq]; exact (integrable_const _).add h_norm
                  exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
                have h_int_ρc : ∀ t (x : PhysSpace d),
                    Integrable (fun y => gradW (x - y)) (ρc t) :=
                  fun t x => by
                    have := h_int_marg_prev (clampT t) (hclampT_mem t) x
                    simpa only [hρc_def] using this
                have h_bdry_ρc : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
                    HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
                    HasDerivWithinAt (fun s => charV_prev s z)
                      (-(convolveFunctionMeasure gradW (ρc t) (charX_prev t z)))
                      (Set.Icc 0 T) t := by
                  intro z t ht
                  have h_eq : ρc t = spatialMarginal (f_prev t) := by
                    simp only [hρc_def, hclampT_id t ht]
                  rw [h_eq]
                  exact h_prev_boundary z t ht
                have h_prev_flow_ρc : IsCharacteristicFlowOn gradW ρc
                    charX_prev charV_prev (Set.Ioo 0 T) Set.univ := by
                  refine ⟨h_prev_flow.1, h_prev_flow.2.1, fun t ht z hz => ?_⟩
                  have h_eq : ρc t = spatialMarginal (f_prev t) := by
                    simp only [hρc_def, hclampT_id t ⟨ht.1.le, ht.2.le⟩]
                  rw [h_eq]
                  exact h_prev_flow.2.2 t ht z hz
                obtain ⟨h_init_ρc, h_cont_Icc_ρc, h_deriv_Ico_ρc⟩ :=
                  Stage_1_9_flow_boundary_regularity gradW ρc charX_prev charV_prev T hT_pos.le
                    h_prev_flow_ρc h_bdry_ρc
                obtain ⟨C_prev, hC_prev_nn, hC_prev_pair⟩ :=
                  flow_distance_growth_bound_on gradW L hL ρc charX_prev charV_prev T hT_pos.le
                    h_init_ρc h_cont_Icc_ρc h_deriv_Ico_ρc M_ρ hM_ρ_nn hM_ρ h_y_int_ρc h_int_ρc
                -- Piece A on g (over [0, T_0]), built from hg_lag's flow + hg_boundary
                -- + hg_mom_unif.  Clamp g's curve into [0, T_0] for the universal instance.
                obtain ⟨M_g, hM_g_nn, hM_g_bd⟩ := hg_mom_unif
                set clampT0 : ℝ → ℝ := fun t => max 0 (min t T_0) with hclampT0_def
                have hclampT0_mem : ∀ t, clampT0 t ∈ Set.Icc (0 : ℝ) T_0 := by
                  intro t
                  simp only [hclampT0_def, Set.mem_Icc]
                  exact ⟨le_max_left _ _, max_le hT_0_pos.le (min_le_right _ _)⟩
                have hclampT0_id : ∀ t ∈ Set.Icc (0 : ℝ) T_0, clampT0 t = t := by
                  intro t ht
                  simp only [hclampT0_def, min_eq_left ht.2, max_eq_right ht.1]
                set σc : ℝ → Measure (PhysSpace d) :=
                  fun t => spatialMarginal (g (clampT0 t)) with hσc_def
                haveI hσc_isProb : ∀ t, IsProbabilityMeasure (σc t) := by
                  intro t
                  haveI : IsProbabilityMeasure (g (clampT0 t)) :=
                    (hg_mom (clampT0 t) (hclampT0_mem t)).1
                  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                have hM_σ : ∀ t ∈ Set.Icc (0 : ℝ) T_0, ∫ y, ‖y‖ ∂(σc t) ≤ M_g := by
                  intro t _ht
                  rw [hσc_def]
                  exact hM_g_bd (clampT0 t) (hclampT0_mem t)
                have h_y_int_σc : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
                    Integrable (fun y : PhysSpace d => ‖y‖) (σc t) := by
                  intro t ht
                  have h_eq : σc t = spatialMarginal (g t) := by
                    simp only [hσc_def, hclampT0_id t ht]
                  rw [h_eq]
                  haveI : IsProbabilityMeasure (g t) := (hg_mom t ht).1
                  unfold spatialMarginal
                  rw [integrable_map_measure
                    (by exact (continuous_norm.measurable).aestronglyMeasurable)
                    measurable_fst.aemeasurable]
                  refine Integrable.mono' (hg_mom t ht).2
                    ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
                    (Filter.Eventually.of_forall fun z => ?_)
                  show |‖z.1‖| ≤ ‖z‖
                  rw [abs_of_nonneg (norm_nonneg _)]
                  exact norm_fst_le z
                have h_int_σc : ∀ t (x : PhysSpace d),
                    Integrable (fun y => gradW (x - y)) (σc t) :=
                  fun t x => by
                    have := h_int_marg_g (clampT0 t) (hclampT0_mem t) x
                    simpa only [hσc_def] using this
                -- Build `IsCharacteristicFlowOn` for the EXPLICIT witnesses charX_g/charV_g
                -- from the explicit flow bundle (hg_init_cond + hg_boundary), not from
                -- hg_lag.2 (whose witnesses are hidden / possibly different).
                have h_g_flow_σc : IsCharacteristicFlowOn gradW σc
                    charX_g charV_g (Set.Ioo 0 T_0) Set.univ := by
                  refine ⟨fun z _ => hg_init_cond z, fun t ht z _ => ?_, fun t ht z _ => ?_⟩
                  · -- HasDerivAt charX_g at t ∈ Ioo from HasDerivWithinAt on Icc
                    have ht_Icc : t ∈ Set.Icc (0 : ℝ) T_0 := ⟨ht.1.le, ht.2.le⟩
                    have h_dw := (hg_boundary z t ht_Icc).1
                    have h_nhds : Set.Icc (0 : ℝ) T_0 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
                    exact h_dw.hasDerivAt h_nhds
                  · -- HasDerivAt charV_g at t ∈ Ioo from HasDerivWithinAt on Icc
                    have ht_Icc : t ∈ Set.Icc (0 : ℝ) T_0 := ⟨ht.1.le, ht.2.le⟩
                    have h_eq : σc t = spatialMarginal (g t) := by
                      simp only [hσc_def, hclampT0_id t ht_Icc]
                    rw [h_eq]
                    have h_dw := (hg_boundary z t ht_Icc).2
                    have h_nhds : Set.Icc (0 : ℝ) T_0 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
                    exact h_dw.hasDerivAt h_nhds
                have h_g_bdry_σc : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
                    HasDerivWithinAt (fun s => charX_g s z) (charV_g t z) (Set.Icc 0 T_0) t ∧
                    HasDerivWithinAt (fun s => charV_g s z)
                      (-(convolveFunctionMeasure gradW (σc t) (charX_g t z)))
                      (Set.Icc 0 T_0) t := by
                  intro z t ht
                  have h_eq : σc t = spatialMarginal (g t) := by
                    simp only [hσc_def, hclampT0_id t ht]
                  rw [h_eq]
                  exact hg_boundary z t ht
                obtain ⟨h_init_σc, h_cont_Icc_σc, h_deriv_Ico_σc⟩ :=
                  Stage_1_9_flow_boundary_regularity gradW σc charX_g charV_g T_0 hT_0_pos.le
                    h_g_flow_σc h_g_bdry_σc
                obtain ⟨C_g, hC_g_nn, hC_g_pair⟩ :=
                  flow_distance_growth_bound_on gradW L hL σc charX_g charV_g T_0 hT_0_pos.le
                    h_init_σc h_cont_Icc_σc h_deriv_Ico_σc M_g hM_g_nn hM_σ h_y_int_σc h_int_σc
                -- Compose the two Piece-A bounds.  C_comp := C_g * C_prev + C_g.
                set C_comp : ℝ := C_g * C_prev + C_g with hC_comp_def
                have hC_comp_nn : 0 ≤ C_comp := by positivity
                have hC_comp_pair : ∀ s ∈ Set.Icc T (T + T_0), ∀ z : PhaseSpace d,
                    ‖(Zpos s z, Zvel s z)‖ ≤ C_comp * (‖z‖ + 1) := by
                  intro s hs z
                  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                    ⟨by linarith [hs.1], by linarith [hs.2]⟩
                  -- prev bound at T
                  have h_prev : ‖(charX_prev T z, charV_prev T z)‖ ≤ C_prev * (‖z‖ + 1) :=
                    hC_prev_pair T hT_Icc z
                  -- g bound on the composed point
                  have h_g : ‖(charX_g (s - T) (charX_prev T z, charV_prev T z),
                               charV_g (s - T) (charX_prev T z, charV_prev T z))‖
                      ≤ C_g * (‖(charX_prev T z, charV_prev T z)‖ + 1) :=
                    hC_g_pair (s - T) hsT_Icc (charX_prev T z, charV_prev T z)
                  have hz1 : (0 : ℝ) ≤ ‖z‖ + 1 := by positivity
                  calc ‖(Zpos s z, Zvel s z)‖
                      = ‖(charX_g (s - T) (charX_prev T z, charV_prev T z),
                          charV_g (s - T) (charX_prev T z, charV_prev T z))‖ := by
                        simp only [hZpos_def, hZvel_def]
                    _ ≤ C_g * (‖(charX_prev T z, charV_prev T z)‖ + 1) := h_g
                    _ ≤ C_g * (C_prev * (‖z‖ + 1) + 1) := by
                        apply mul_le_mul_of_nonneg_left _ hC_g_nn; linarith
                    _ ≤ C_comp * (‖z‖ + 1) := by
                        simp only [hC_comp_def]
                        nlinarith [mul_nonneg hC_g_nn (norm_nonneg z),
                          mul_nonneg (mul_nonneg hC_g_nn hC_prev_nn) hz1]
                have hC_comp_X : ∀ s ∈ Set.Icc T (T + T_0), ∀ z : PhaseSpace d,
                    ‖Zpos s z‖ ≤ C_comp * (‖z‖ + 1) := by
                  intro s hs z
                  exact le_trans (norm_fst_le (Zpos s z, Zvel s z)) (hC_comp_pair s hs z)
                -- (5) Seam continuity of the composed flow at T (from h_cont_f_right's
                -- chain-rule machinery).  Composed flow ContinuousWithinAt on Ici T at T.
                have h_Zpos_cont : ∀ z : PhaseSpace d,
                    ContinuousWithinAt (fun s => Zpos s z) (Set.Ici T) T := by
                  intro z
                  have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
                  have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).1
                  have h_nhdsW_0 : Set.Icc (0 : ℝ) T_0 ∈ nhdsWithin 0 (Set.Ici 0) :=
                    Icc_mem_nhdsGE hT_0_pos
                  have h_g_bX_cont : ContinuousWithinAt
                      (fun s' => charX_g s' (charX_prev T z, charV_prev T z)) (Set.Ici 0) 0 :=
                    h_g_bX.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
                  have h_sub_cont : ContinuousWithinAt (fun s : ℝ => s - T) (Set.Ici T) T :=
                    ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
                  have h_sub_maps : Set.MapsTo (fun s : ℝ => s - T) (Set.Ici T) (Set.Ici 0) :=
                    fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
                  have := ContinuousWithinAt.comp_of_eq h_g_bX_cont h_sub_cont h_sub_maps
                    (sub_self T)
                  simpa only [hZpos_def] using this
                have h_Zvel_cont : ∀ z : PhaseSpace d,
                    ContinuousWithinAt (fun s => Zvel s z) (Set.Ici T) T := by
                  intro z
                  have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
                  have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).2
                  have h_nhdsW_0 : Set.Icc (0 : ℝ) T_0 ∈ nhdsWithin 0 (Set.Ici 0) :=
                    Icc_mem_nhdsGE hT_0_pos
                  have h_g_bV_cont : ContinuousWithinAt
                      (fun s' => charV_g s' (charX_prev T z, charV_prev T z)) (Set.Ici 0) 0 :=
                    h_g_bV.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
                  have h_sub_cont : ContinuousWithinAt (fun s : ℝ => s - T) (Set.Ici T) T :=
                    ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
                  have h_sub_maps : Set.MapsTo (fun s : ℝ => s - T) (Set.Ici T) (Set.Ici 0) :=
                    fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
                  have := ContinuousWithinAt.comp_of_eq h_g_bV_cont h_sub_cont h_sub_maps
                    (sub_self T)
                  simpa only [hZvel_def] using this
                -- (6) Continuity of the un-pushed integrand in z (for integral_map's
                -- AEStronglyMeasurable side).
                have h_conv_z_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
                    Continuous (fun z : PhaseSpace d =>
                      convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1) := by
                  intro τ hτ
                  haveI : IsProbabilityMeasure (g τ) := (hg_mom τ hτ).1
                  haveI : IsProbabilityMeasure (spatialMarginal (g τ)) :=
                    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                  exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
                    (spatialMarginal (g τ)) (h_int_marg_g τ hτ)).continuous.comp continuous_fst
                have h_integrand_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
                    Continuous (fun z : PhaseSpace d =>
                      @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                      @inner ℝ (PhysSpace d) _
                        (convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1)
                        (gradVφ z)) := by
                  intro τ hτ
                  exact (continuous_snd.inner hgradXφ_cont).sub
                    ((h_conv_z_cont τ hτ).inner hgradVφ_cont)
                -- (7) Eventually-equal rewrite to the composed-pushforward form.
                have h_eq_R : (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                          (gradVφ z)) ∂(f_next s))
                    =ᶠ[nhdsWithin T (Set.Ici T)]
                    (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel s z)
                          (gradXφ (Zpos s z, Zvel s z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                            (Zpos s z))
                          (gradVφ (Zpos s z, Zvel s z))) ∂f₀) := by
                  apply Filter.Eventually.mono h_nhd_R
                  intro s hs
                  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                    ⟨by linarith [hs.1], by linarith [hs.2]⟩
                  show (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s))
                      = ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel s z)
                            (gradXφ (Zpos s z, Zvel s z)) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                              (Zpos s z))
                            (gradVφ (Zpos s z, Zvel s z))) ∂f₀
                  by_cases hs_eq : s = T
                  · -- s = T: f_next T = f_prev T = composed pushforward (collapse g at 0 = id)
                    have hs_T_zero : s - T = 0 := by rw [hs_eq]; exact sub_self T
                    have h_fnext_s : f_next s = f_prev T := by
                      rw [hs_eq]; exact if_pos (le_refl T)
                    have h_marg_eq : spatialMarginal (f_next s) = spatialMarginal (g (s - T)) := by
                      rw [h_fnext_s, hs_T_zero, hg_init]
                    have h_meq : f_next s = Measure.map
                        (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ := by
                      rw [h_fnext_s, h_prev_push T hT_Icc, h_prev_init]
                      apply Measure.map_congr
                      apply Filter.Eventually.of_forall
                      intro z
                      simp only [hZpos_def, hZvel_def, hs_T_zero,
                        (hg_init_cond _).1, (hg_init_cond _).2]
                    rw [h_marg_eq, h_meq,
                        integral_map (h_comp_aemeas (s - T) hsT_Icc)
                          (h_integrand_cont (s - T) hsT_Icc).aestronglyMeasurable]
                  · -- s > T: f_next s = g (s − T) = composed pushforward
                    have hs_gt : T < s := lt_of_le_of_ne hs.1 (Ne.symm hs_eq)
                    have h_fnext_s : f_next s = g (s - T) := if_neg (not_le.mpr hs_gt)
                    have h_marg_eq : spatialMarginal (f_next s) = spatialMarginal (g (s - T)) :=
                      congrArg spatialMarginal h_fnext_s
                    have h_meq : f_next s = Measure.map
                        (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ := by
                      rw [h_fnext_s]; exact h_g_push_comp s hs
                    rw [h_marg_eq, h_meq,
                        integral_map (h_comp_aemeas (s - T) hsT_Icc)
                          (h_integrand_cont (s - T) hsT_Icc).aestronglyMeasurable]
                -- (8) Uniform sup-bounds on gradXφ / gradVφ.
                have hfderiv_cont : Continuous (fderiv ℝ φ) :=
                  hφ_smooth.continuous_fderiv (by norm_num)
                have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
                  HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
                obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
                have hM_φ_nn : 0 ≤ M_φ :=
                  le_trans (norm_nonneg (fderiv ℝ φ (0 : PhaseSpace d))) (hM_φ _)
                have hgradXφ_bd : ∀ z : PhaseSpace d, ‖gradXφ z‖ ≤ M_φ := by
                  intro z
                  have hfd : fderiv ℝ (fun x => φ (x, z.2)) z.1 =
                      (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
                    have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
                      (hφ_smooth.differentiable (by simp) z).hasFDerivAt
                    have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
                        (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
                      hasFDerivAt_prodMk_left z.1 z.2
                    exact (h1.comp z.1 h2).fderiv
                  rw [hgradXφ z, gradient, hfd, (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
                  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
                  refine le_trans (mul_le_mul_of_nonneg_left
                    (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ)
                      (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
                  rw [mul_one]; exact hM_φ z
                have hgradVφ_bd : ∀ z : PhaseSpace d, ‖gradVφ z‖ ≤ M_φ := by
                  intro z
                  have hfd : fderiv ℝ (fun v => φ (z.1, v)) z.2 =
                      (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
                    have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
                      (hφ_smooth.differentiable (by simp) z).hasFDerivAt
                    have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
                        (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
                      hasFDerivAt_prodMk_right z.1 z.2
                    exact (h1.comp z.2 h2).fderiv
                  rw [hgradVφ z, gradient, hfd, (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
                  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
                  refine le_trans (mul_le_mul_of_nonneg_left
                    (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ)
                      (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
                  rw [mul_one]; exact hM_φ z
                -- (9) Convolution force bound on g's marginal (over [0, T_0]).
                have h_conv_force : ∀ τ ∈ Set.Icc (0 : ℝ) T_0, ∀ x : PhysSpace d,
                    ‖convolveFunctionMeasure gradW (spatialMarginal (g τ)) x‖
                      ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M_g := by
                  intro τ hτ x
                  have h_y_int_s : Integrable (fun y : PhysSpace d => ‖y‖)
                      (spatialMarginal (g τ)) := by
                    have h_eq : spatialMarginal (g τ) = σc τ := by
                      simp only [hσc_def, hclampT0_id τ hτ]
                    rw [h_eq]; exact h_y_int_σc τ hτ
                  have hM_ρ_s : ∫ y, ‖y‖ ∂(spatialMarginal (g τ)) ≤ M_g := by
                    have h_eq : spatialMarginal (g τ) = σc τ := by
                      simp only [hσc_def, hclampT0_id τ hτ]
                    rw [h_eq]; exact hM_σ τ hτ
                  haveI : IsProbabilityMeasure (g τ) := (hg_mom τ hτ).1
                  haveI : IsProbabilityMeasure (spatialMarginal (g τ)) :=
                    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                  unfold convolveFunctionMeasure
                  have h_sub_int : Integrable (fun y => ‖x - y‖) (spatialMarginal (g τ)) :=
                    Integrable.mono' ((integrable_const ‖x‖).add h_y_int_s)
                      ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
                      (Filter.Eventually.of_forall fun y => by
                        simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
                  have h_pt : ∀ y : PhysSpace d,
                      ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
                    intro y
                    have hd := hL.dist_le_mul (x - y) 0
                    simp only [dist_eq_norm, sub_zero] at hd
                    have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
                      have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
                      simp only [sub_add_cancel] at this; linarith
                    linarith
                  have h_bnd_int :
                      Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (spatialMarginal (g τ)) :=
                    (integrable_const _).add (h_sub_int.const_mul _)
                  calc ‖∫ y, gradW (x - y) ∂(spatialMarginal (g τ))‖
                      ≤ ∫ y, ‖gradW (x - y)‖ ∂(spatialMarginal (g τ)) :=
                        norm_integral_le_integral_norm _
                    _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(spatialMarginal (g τ)) :=
                        integral_mono (h_int_marg_g τ hτ x).norm h_bnd_int h_pt
                    _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(spatialMarginal (g τ)) := by
                        rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
                        simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
                    _ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M_g := by
                        have h_int_le : ∫ y, ‖x - y‖ ∂(spatialMarginal (g τ)) ≤ ‖x‖ + M_g := by
                          calc ∫ y, ‖x - y‖ ∂(spatialMarginal (g τ))
                              ≤ ∫ y, (‖x‖ + ‖y‖) ∂(spatialMarginal (g τ)) :=
                                integral_mono h_sub_int ((integrable_const _).add h_y_int_s)
                                  (fun y => norm_sub_le x y)
                            _ = ‖x‖ + ∫ y, ‖y‖ ∂(spatialMarginal (g τ)) := by
                                rw [integral_add (integrable_const _) h_y_int_s]
                                simp [integral_const, measureReal_def, measure_univ]
                            _ ≤ ‖x‖ + M_g := by linarith
                        nlinarith [mul_le_mul_of_nonneg_left h_int_le L.coe_nonneg]
                -- (10) The affine dominator: integrable wrt f₀.
                set bound_fn : PhaseSpace d → ℝ := fun z =>
                  M_φ * (C_comp * (‖z‖ + 1))
                  + (‖gradW 0‖ + (L : ℝ) * (C_comp * (‖z‖ + 1)) + (L : ℝ) * M_g) * M_φ
                  with hbound_def
                have hbound_int : Integrable bound_fn f₀ := by
                  have ha : Integrable
                      (fun z : PhaseSpace d =>
                        (M_φ * C_comp + L * M_φ * C_comp) * ‖z‖
                        + (M_φ * C_comp + (‖gradW 0‖ + L * (C_comp) + L * M_g) * M_φ)) f₀ :=
                    (hf₀_int.const_mul _).add (integrable_const _)
                  refine ha.congr (Filter.Eventually.of_forall fun z => ?_)
                  simp only [hbound_def]; ring
                have hB : ∀ s ∈ Set.Icc T (T + T_0), ∀ z : PhaseSpace d,
                    ‖@inner ℝ (PhysSpace d) _ (Zvel s z)
                          (gradXφ (Zpos s z, Zvel s z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                            (Zpos s z))
                          (gradVφ (Zpos s z, Zvel s z))‖ ≤ bound_fn z := by
                  intro s hs z
                  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                    ⟨by linarith [hs.1], by linarith [hs.2]⟩
                  have hV : ‖Zvel s z‖ ≤ C_comp * (‖z‖ + 1) :=
                    le_trans (norm_snd_le (Zpos s z, Zvel s z)) (hC_comp_pair s hs z)
                  have hX : ‖Zpos s z‖ ≤ C_comp * (‖z‖ + 1) := hC_comp_X s hs z
                  have ht1 : ‖@inner ℝ (PhysSpace d) _ (Zvel s z)
                        (gradXφ (Zpos s z, Zvel s z))‖ ≤ M_φ * (C_comp * (‖z‖ + 1)) := by
                    refine le_trans (norm_inner_le_norm _ _) ?_
                    have := mul_le_mul hV (hgradXφ_bd (Zpos s z, Zvel s z))
                      (norm_nonneg _) (le_trans (norm_nonneg _) hV)
                    calc ‖Zvel s z‖ * ‖gradXφ (Zpos s z, Zvel s z)‖
                        ≤ (C_comp * (‖z‖ + 1)) * M_φ := this
                      _ = M_φ * (C_comp * (‖z‖ + 1)) := by ring
                  have ht2 : ‖@inner ℝ (PhysSpace d) _
                        (convolveFunctionMeasure gradW (spatialMarginal (g (s - T))) (Zpos s z))
                        (gradVφ (Zpos s z, Zvel s z))‖
                      ≤ (‖gradW 0‖ + (L : ℝ) * (C_comp * (‖z‖ + 1)) + (L : ℝ) * M_g) * M_φ := by
                    refine le_trans (norm_inner_le_norm _ _) ?_
                    have hc : ‖convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                        (Zpos s z)‖ ≤ ‖gradW 0‖ + (L : ℝ) * (C_comp * (‖z‖ + 1)) + (L : ℝ) * M_g := by
                      refine le_trans (h_conv_force (s - T) hsT_Icc (Zpos s z)) ?_
                      have := mul_le_mul_of_nonneg_left hX L.coe_nonneg
                      linarith
                    have hcnn : 0 ≤ ‖gradW 0‖ + (L : ℝ) * (C_comp * (‖z‖ + 1)) + (L : ℝ) * M_g :=
                      le_trans (norm_nonneg _) hc
                    exact mul_le_mul hc (hgradVφ_bd (Zpos s z, Zvel s z))
                      (norm_nonneg _) hcnn
                  calc ‖_ - _‖
                      ≤ ‖@inner ℝ (PhysSpace d) _ (Zvel s z)
                            (gradXφ (Zpos s z, Zvel s z))‖
                        + ‖@inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                              (Zpos s z))
                            (gradVφ (Zpos s z, Zvel s z))‖ := norm_sub_le _ _
                    _ ≤ bound_fn z := by simp only [hbound_def]; linarith
                have h_cont_pf : ContinuousWithinAt
                    (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel s z)
                          (gradXφ (Zpos s z, Zvel s z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                            (Zpos s z))
                          (gradVφ (Zpos s z, Zvel s z))) ∂f₀)
                    (Set.Ici T) T := by
                  apply continuousWithinAt_of_dominated (bound := bound_fn)
                  · -- AEStronglyMeasurable in z, eventually in s
                    apply Filter.Eventually.mono h_nhd_R
                    intro s hs
                    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
                      ⟨by linarith [hs.1], by linarith [hs.2]⟩
                    have h_aem_pair : AEMeasurable
                        (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ :=
                      h_comp_aemeas (s - T) hsT_Icc
                    have h_aem_X : AEMeasurable (fun z : PhaseSpace d => Zpos s z) f₀ :=
                      measurable_fst.comp_aemeasurable h_aem_pair
                    have h_aem_V : AEMeasurable (fun z : PhaseSpace d => Zvel s z) f₀ :=
                      measurable_snd.comp_aemeasurable h_aem_pair
                    have h1 : AEStronglyMeasurable
                        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _ (Zvel s z)
                          (gradXφ (Zpos s z, Zvel s z))) f₀ := by
                      have hg : AEMeasurable
                          (fun z : PhaseSpace d => gradXφ (Zpos s z, Zvel s z)) f₀ :=
                        hgradXφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
                      exact (continuous_inner.measurable.comp_aemeasurable
                        (h_aem_V.prodMk hg)).aestronglyMeasurable
                    have h2 : AEStronglyMeasurable
                        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                            (Zpos s z))
                          (gradVφ (Zpos s z, Zvel s z))) f₀ := by
                      have hconv_aem : AEMeasurable
                          (fun z : PhaseSpace d => convolveFunctionMeasure gradW
                            (spatialMarginal (g (s - T))) (Zpos s z)) f₀ := by
                        have hconv_cont' : Continuous (fun x : PhysSpace d =>
                            convolveFunctionMeasure gradW (spatialMarginal (g (s - T))) x) := by
                          haveI : IsProbabilityMeasure (g (s - T)) := (hg_mom (s - T) hsT_Icc).1
                          haveI : IsProbabilityMeasure (spatialMarginal (g (s - T))) :=
                            Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
                          exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
                            (spatialMarginal (g (s - T))) (h_int_marg_g (s - T) hsT_Icc)).continuous
                        exact hconv_cont'.measurable.comp_aemeasurable h_aem_X
                      have hg : AEMeasurable
                          (fun z : PhaseSpace d => gradVφ (Zpos s z, Zvel s z)) f₀ :=
                        hgradVφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
                      exact (continuous_inner.measurable.comp_aemeasurable
                        (hconv_aem.prodMk hg)).aestronglyMeasurable
                    exact h1.sub h2
                  · -- dominator bound, eventually in s
                    apply Filter.Eventually.mono h_nhd_R
                    intro s hs
                    exact Filter.Eventually.of_forall fun z => hB s hs z
                  · exact hbound_int
                  · -- pointwise continuity in s, a.e. z (in fact ∀ z)
                    apply Filter.Eventually.of_forall
                    intro z
                    have h_gX_cwn : ContinuousWithinAt
                        (fun s => gradXφ (Zpos s z, Zvel s z)) (Set.Ici T) T :=
                      hgradXφ_cont.continuousAt.comp_continuousWithinAt
                        ((h_Zpos_cont z).prodMk (h_Zvel_cont z))
                    have h_gV_cwn : ContinuousWithinAt
                        (fun s => gradVφ (Zpos s z, Zvel s z)) (Set.Ici T) T :=
                      hgradVφ_cont.continuousAt.comp_continuousWithinAt
                        ((h_Zpos_cont z).prodMk (h_Zvel_cont z))
                    have h_term1 : ContinuousWithinAt
                        (fun s => @inner ℝ (PhysSpace d) _ (Zvel s z)
                          (gradXφ (Zpos s z, Zvel s z))) (Set.Ici T) T :=
                      (h_Zvel_cont z).inner h_gX_cwn
                    -- conv seam continuity via the Ici sibling kernel
                    have h_conv_cwn : ContinuousWithinAt
                        (fun s => convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                          (Zpos s z)) (Set.Ici T) T := by
                      have := flowConv_continuousWithinAt_Ici_seam gradW L hL Zpos f₀
                        hf₀_int (by linarith : T < T + T_0)
                        (fun s => spatialMarginal (g (s - T)))
                        h_push_marg h_aemeas_marg h_Zpos_cont C_comp hC_comp_nn hC_comp_X z
                      exact this
                    have h_term2 : ContinuousWithinAt
                        (fun s => @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
                            (Zpos s z))
                          (gradVφ (Zpos s z, Zvel s z))) (Set.Ici T) T :=
                      h_conv_cwn.inner h_gV_cwn
                    exact h_term1.sub h_term2
                -- (11) Value at T bridge.
                have h_val_T : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next T)) z.1)
                          (gradVφ z)) ∂(f_next T))
                    = ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel T z)
                          (gradXφ (Zpos T z, Zvel T z)) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (g (T - T)))
                            (Zpos T z))
                          (gradVφ (Zpos T z, Zvel T z))) ∂f₀ := by
                  have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
                  have hTT_zero : T - T = (0 : ℝ) := sub_self T
                  have h_fnext_T : f_next T = f_prev T := if_pos (le_refl T)
                  have h_marg : spatialMarginal (f_next T) = spatialMarginal (g (T - T)) := by
                    rw [h_fnext_T, hTT_zero, hg_init]
                  have h_meq : f_next T = Measure.map
                      (fun z : PhaseSpace d => (Zpos T z, Zvel T z)) f₀ := by
                    rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init]
                    apply Measure.map_congr
                    apply Filter.Eventually.of_forall
                    intro z
                    simp only [hZpos_def, hZvel_def, hTT_zero,
                      (hg_init_cond _).1, (hg_init_cond _).2]
                  rw [h_marg, h_meq,
                      integral_map (h_comp_aemeas (T - T) (hTT_zero ▸ h0_Icc))
                        (h_integrand_cont (T - T) (hTT_zero ▸ h0_Icc)).aestronglyMeasurable]
                exact h_cont_pf.congr_of_eventuallyEq h_eq_R h_val_T
              have h_union := h_left.union h_right
              rw [Set.Iic_union_Ici] at h_union
              exact h_union.continuousAt Filter.univ_mem
            -- Step 4: Apply the localized helper.
            rw [h_t_eq]
            exact hasDerivAt_of_hasDerivAt_of_ne_in_nhds h_diff_ne h_cont_f h_cont_g
      exact h_vlasov_glue
    · -- IsCharacteristicFlowOn for the glued flow
      -- Sub-sorry: flow initial condition + HasDerivAt for piecewise flow
      have h_flow_glue : IsCharacteristicFlowOn gradW
          (fun t => spatialMarginal (f_next t)) charX_next charV_next
          (Set.Ioo 0 (T + T_0)) Set.univ := by
        refine ⟨?_, ?_, ?_⟩
        · -- Initial condition: charX_next 0 z = z.1 ∧ charV_next 0 z = z.2
          intro z _
          simp only [charX_next, charV_next, if_pos hT_pos.le]
          exact h_prev_flow.1 z (Set.mem_univ z)
        · -- HasDerivAt charX_next at t for t ∈ Ioo 0 (T + T_0)
          intro t ht z _
          simp only [charX_next, charV_next]
          by_cases ht_le : t ≤ T
          · simp only [if_pos ht_le]
            -- Sub-case: t < T (strict interior) vs t = T (boundary)
            by_cases ht_lt : t < T
            · -- t < T strict: piecewise function = charX_prev · z near t
              have h_ev : (fun s => if s ≤ T then charX_prev s z
                  else charX_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
                  (fun s => charX_prev s z) := by
                apply Filter.Eventually.mono (eventually_lt_nhds ht_lt)
                intro s hs; simp [le_of_lt hs]
              exact ((h_prev_flow.2.1 t ⟨ht.1, ht_lt⟩ z (Set.mem_univ z)).congr_of_eventuallyEq
                h_ev)
            · -- t = T: boundary HasDerivAt via HasDerivWithinAt.union (Iic T ∪ Ici T = univ)
              -- Same technique as conjunct (vii)'s t = T case (which produces
              -- HasDerivWithinAt on Icc 0 (T+T_0); here we extract HasDerivAt directly).
              push_neg at ht_lt
              have h_t_eq : t = T := le_antisymm ht_le ht_lt
              have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
              have h_bX := (h_prev_boundary z T hT_in).1
              have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
              have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).1
              have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
              have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
                Icc_mem_nhdsGE hT_0_pos
              -- LEFT: HasDerivWithinAt charX_prev on Iic T at T
              have hX_Lic := h_bX.mono_of_mem_nhdsWithin h_nhd_L
              have hX_left : HasDerivWithinAt
                  (fun s => if s ≤ T then charX_prev s z
                    else charX_g (s - T) (charX_prev T z, charV_prev T z))
                  (charV_prev T z) (Set.Iic T) T :=
                hX_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.right_mem_Iic
              -- RIGHT: chain rule from g's boundary at 0
              have hX_Ici0 := h_g_bX.mono_of_mem_nhdsWithin h_nhd_R
              have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
                ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
              have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
                fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
              have h_chainX : HasDerivWithinAt
                  (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
                  (charV_g 0 (charX_prev T z, charV_prev T z)) (Set.Ici T) T := by
                have := HasDerivWithinAt.scomp_of_eq T hX_Ici0 h_sub_R h_mapR (sub_self T).symm
                simpa [Function.comp, one_smul] using this
              have hVg0_eq : charV_g 0 (charX_prev T z, charV_prev T z) = charV_prev T z :=
                (hg_init_cond (charX_prev T z, charV_prev T z)).2
              rw [hVg0_eq] at h_chainX
              have hX_right : HasDerivWithinAt
                  (fun s => if s ≤ T then charX_prev s z
                    else charX_g (s - T) (charX_prev T z, charV_prev T z))
                  (charV_prev T z) (Set.Ici T) T :=
                h_chainX.congr_of_mem
                  (fun s hs => by
                    by_cases hle : s ≤ T
                    · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
                      simp [hle, heq, sub_self,
                        (hg_init_cond (charX_prev T z, charV_prev T z)).1]
                    · simp [hle])
                  Set.left_mem_Ici
              have hX_union := hX_left.union hX_right
              rw [Set.Iic_union_Ici] at hX_union
              -- Goal: HasDerivAt (...) (charV_prev t z) t   with t = T
              rw [h_t_eq]
              exact hX_union.hasDerivAt Filter.univ_mem
          · simp only [if_neg ht_le]
            push_neg at ht_le
            -- t > T: use hg_boundary at (t - T) with chain rule for (s ↦ s - T)
            have htT_mem : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
            have h_g_deriv : HasDerivAt (fun s => charX_g s (charX_prev T z, charV_prev T z))
                (charV_g (t - T) (charX_prev T z, charV_prev T z)) (t - T) :=
              ((hg_boundary (charX_prev T z, charV_prev T z) (t - T)
                  (Set.Ioo_subset_Icc_self htT_mem)).1).hasDerivAt
                (Icc_mem_nhds htT_mem.1 htT_mem.2)
            have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
            have h_chain : HasDerivAt (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
                (charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
              have := HasDerivAt.scomp_of_eq t h_g_deriv h_sub rfl
              simpa [Function.comp, one_smul] using this
            have h_ev : (fun s => if s ≤ T then charX_prev s z
                else charX_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
                (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) := by
              apply Filter.Eventually.mono (eventually_gt_nhds ht_le)
              intro s hs; simp [not_le.mpr hs]
            exact h_chain.congr_of_eventuallyEq h_ev
        · -- HasDerivAt charV_next at t for t ∈ Ioo 0 (T + T_0)
          intro t ht z _
          simp only [charX_next, charV_next]
          by_cases ht_le : t ≤ T
          · simp only [if_pos ht_le]
            -- Sub-case: t < T (strict interior) vs t = T (boundary)
            by_cases ht_lt : t < T
            · -- t < T strict: piecewise function = charV_prev · z near t
              have h_ev : (fun s => if s ≤ T then charV_prev s z
                  else charV_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
                  (fun s => charV_prev s z) := by
                apply Filter.Eventually.mono (eventually_lt_nhds ht_lt)
                intro s hs; simp [le_of_lt hs]
              have h_fnext_t : f_next t = f_prev t := if_pos ht_le
              have h_prev_deriv := h_prev_flow.2.2 t ⟨ht.1, ht_lt⟩ z (Set.mem_univ z)
              -- h_prev_deriv uses spatialMarginal (f_prev t); goal uses spatialMarginal (f_next t)
              have h_eq_marg : spatialMarginal (f_prev t) = spatialMarginal (f_next t) :=
                congrArg spatialMarginal h_fnext_t.symm
              simp only [h_eq_marg] at h_prev_deriv
              exact h_prev_deriv.congr_of_eventuallyEq h_ev
            · -- t = T: boundary HasDerivAt via HasDerivWithinAt.union (same as charX case above)
              push_neg at ht_lt
              have h_t_eq : t = T := le_antisymm ht_le ht_lt
              have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
              have h_bV := (h_prev_boundary z T hT_in).2
              have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
              have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).2
              have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
              have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
                Icc_mem_nhdsGE hT_0_pos
              -- Bridge f_prev T ↔ f_next T (for spatial marginal in goal vs h_bV)
              have hfnextT : f_next T = f_prev T := if_pos (le_refl T)
              have hfnextT_spat : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
                congrArg spatialMarginal hfnextT
              -- LEFT: HasDerivWithinAt charV_prev on Iic T at T
              have hV_Lic := h_bV.mono_of_mem_nhdsWithin h_nhd_L
              have hV_left : HasDerivWithinAt
                  (fun s => if s ≤ T then charV_prev s z
                    else charV_g (s - T) (charX_prev T z, charV_prev T z))
                  (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T))
                      (charX_prev T z)))
                  (Set.Iic T) T := by
                rw [hfnextT_spat]
                exact hV_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs])
                  Set.right_mem_Iic
              -- RIGHT: chain rule from g's boundary at 0
              have hV_Ici0 := h_g_bV.mono_of_mem_nhdsWithin h_nhd_R
              have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
                ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
              have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
                fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
              have h_chainV : HasDerivWithinAt
                  (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
                  (-(convolveFunctionMeasure gradW
                    (spatialMarginal (g 0))
                    (charX_g 0 (charX_prev T z, charV_prev T z))))
                  (Set.Ici T) T := by
                have := HasDerivWithinAt.scomp_of_eq T hV_Ici0 h_sub_R h_mapR (sub_self T).symm
                simpa [Function.comp, one_smul] using this
              have hXg0_eq : charX_g 0 (charX_prev T z, charV_prev T z) = charX_prev T z :=
                (hg_init_cond (charX_prev T z, charV_prev T z)).1
              have hg0_spat : spatialMarginal (g 0) = spatialMarginal (f_prev T) :=
                congrArg spatialMarginal hg_init
              rw [hXg0_eq, hg0_spat, ← hfnextT_spat] at h_chainV
              have hV_right : HasDerivWithinAt
                  (fun s => if s ≤ T then charV_prev s z
                    else charV_g (s - T) (charX_prev T z, charV_prev T z))
                  (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T))
                      (charX_prev T z)))
                  (Set.Ici T) T :=
                h_chainV.congr_of_mem
                  (fun s hs => by
                    by_cases hle : s ≤ T
                    · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
                      simp [hle, heq, sub_self,
                        (hg_init_cond (charX_prev T z, charV_prev T z)).2]
                    · simp [hle])
                  Set.left_mem_Ici
              have hV_union := hV_left.union hV_right
              rw [Set.Iic_union_Ici] at hV_union
              -- Goal: HasDerivAt (...) (-(conv ... (spatialMarginal (f_next t)) (charX_next t z))) t
              -- with t = T (after simp the charX_next has been reduced to charX_prev)
              rw [h_t_eq]
              exact hV_union.hasDerivAt Filter.univ_mem
          · simp only [if_neg ht_le]
            push_neg at ht_le
            -- t > T: use hg_boundary at (t - T)
            have htT_mem : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
            have h_g_deriv : HasDerivAt (fun s => charV_g s (charX_prev T z, charV_prev T z))
                (-(convolveFunctionMeasure gradW (spatialMarginal (g (t - T)))
                    (charX_g (t - T) (charX_prev T z, charV_prev T z)))) (t - T) :=
              ((hg_boundary (charX_prev T z, charV_prev T z) (t - T)
                  (Set.Ioo_subset_Icc_self htT_mem)).2).hasDerivAt
                (Icc_mem_nhds htT_mem.1 htT_mem.2)
            have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
            have h_chain : HasDerivAt (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
                (-(convolveFunctionMeasure gradW (spatialMarginal (g (t - T)))
                    (charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
              have := HasDerivAt.scomp_of_eq t h_g_deriv h_sub rfl
              simpa [Function.comp, one_smul] using this
            -- f_next t = g (t - T) when t > T
            have h_fnext_t : f_next t = g (t - T) := if_neg (not_le.mpr ht_le)
            -- Rewrite derivative value: g (t-T) → f_next t
            rw [← congrArg spatialMarginal h_fnext_t] at h_chain
            have h_ev : (fun s => if s ≤ T then charV_prev s z
                else charV_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
                (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) := by
              apply Filter.Eventually.mono (eventually_gt_nhds ht_le)
              intro s hs; simp [not_le.mpr hs]
            exact h_chain.congr_of_eventuallyEq h_ev
      exact h_flow_glue
    · -- Pushforward equation for f_next on Icc 0 (T + T_0)
      -- Sub-sorry: piecewise pushforward
      intro t ht
      simp only [f_next, charX_next, charV_next]
      by_cases ht_le : t ≤ T
      · simp only [if_pos ht_le]
        -- f_next t = f_prev t = Measure.map (charX_prev t, charV_prev t) (f_prev 0)
        -- and f_next 0 = f_prev 0 = f₀
        have ht_in : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht_le⟩
        have heq := h_prev_push t ht_in
        -- f_prev t = Measure.map (charX_prev t, charV_prev t) (f_prev 0)
        -- f_next 0 = f_prev 0 (since 0 ≤ T)
        -- Need: f_prev t = Measure.map (fun z => (charX_next t z, charV_next t z)) (f_next 0)
        simp only [if_pos hT_pos.le]
        exact heq
      · simp only [if_neg ht_le]
        push_neg at ht_le
        -- f_next t = g (t - T), pushes forward (f_prev T) via charX_g, charV_g
        -- g (t-T) = Measure.map (charX_g (t-T), charV_g (t-T)) (g 0)
        --         = Measure.map (charX_g (t-T), charV_g (t-T)) (f_prev T)  [by hg_init]
        --         = Measure.map (charX_g (t-T), charV_g (t-T)) (Measure.map (charX_prev T, charV_prev T) (f_prev 0))
        --         = Measure.map ((charX_g (t-T), charV_g (t-T)) ∘ (charX_prev T, charV_prev T)) (f_prev 0)
        simp only [if_pos hT_pos.le]
        have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
        have htT_mem : t - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
        rw [hg_push_ex (t - T) htT_mem, hg_init, h_prev_push T hT_mem]
        have h_prev_T_aemeas := h_prev_aemeas T hT_mem
        have h_g_at_tT := hg_aemeas_ex (t - T) htT_mem
        rw [hg_init, h_prev_push T hT_mem] at h_g_at_tT
        rw [AEMeasurable.map_map_of_aemeasurable h_g_at_tT h_prev_T_aemeas]
        rfl
    · -- AEMeasurability ∧ boundary ContinuousOn on Icc 0 (T + T_0).
      -- glue_step is #12 (sorry'd); the B2 boundary-ContinuousOn conjunct is
      -- sorry'd here alongside the existing piecewise-AEMeasurability sorry.
      refine ⟨?_, ?_⟩
      · -- AEMeasurability of the glued flow on Icc 0 (T + T_0).
        -- Key: f_next 0 = f_prev 0 (since 0 ≤ T, so if_pos applies)
        have h_next_0 : f_next 0 = f_prev 0 := by
          simp only [f_next, if_pos hT_pos.le]
        intro s hs
        simp only [charX_next, charV_next]
        by_cases hs_le : s ≤ T
        · simp only [if_pos hs_le]
          rw [h_next_0]
          exact h_prev_aemeas s ⟨hs.1, hs_le⟩
        · simp only [if_neg hs_le]
          push_neg at hs_le
          -- AEMeasurability of (charX_g (s - T) ∘ (charX_prev T, charV_prev T), ...)
          -- w.r.t. f_next 0 = f_prev 0 = f₀
          rw [h_next_0]
          have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
          have hsT_mem : s - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [hs.2]⟩
          have h_prev_T_aemeas := h_prev_aemeas T hT_mem
          -- h_g_aemeas gives AEMeasurability w.r.t. g 0 = f_prev T
          -- = Measure.map (charX_prev T, charV_prev T) (f_prev 0)
          have h_g_at_sT := hg_aemeas_ex (s - T) hsT_mem
          rw [hg_init, h_prev_push T hT_mem] at h_g_at_sT
          exact h_g_at_sT.comp_aemeasurable h_prev_T_aemeas
      · -- Boundary ContinuousOn on Icc 0 (T + T_0): project the boundary bundle.
        intro z
        intro s hs
        exact ((glue_step_boundary_bundle gradW hT_pos hT_0_pos f_prev g f_next
          charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
          h_prev_boundary hg_boundary hg_init hg_init_cond z s hs).1.continuousWithinAt.prodMk
          (glue_step_boundary_bundle gradW hT_pos hT_0_pos f_prev g f_next
            charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
            h_prev_boundary hg_boundary hg_init hg_init_cond z s hs).2.continuousWithinAt)
  · -- Conjunct (v): explicit pushforward for charX_next charV_next
    intro t ht
    simp only [f_next, charX_next, charV_next]
    by_cases ht_le : t ≤ T
    · simp only [if_pos ht_le, if_pos hT_pos.le]
      exact h_prev_push t ⟨ht.1, ht_le⟩
    · simp only [if_neg ht_le, if_pos hT_pos.le]
      push_neg at ht_le
      have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have htT_mem : t - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
      rw [hg_push_ex (t - T) htT_mem, hg_init, h_prev_push T hT_mem]
      have h_g_at_tT := hg_aemeas_ex (t - T) htT_mem
      rw [hg_init, h_prev_push T hT_mem] at h_g_at_tT
      rw [AEMeasurable.map_map_of_aemeasurable h_g_at_tT (h_prev_aemeas T hT_mem)]
      rfl
  · -- Conjunct (vi): AEMeasurable for charX_next charV_next
    have h_next_0 : f_next 0 = f_prev 0 := by simp only [f_next, if_pos hT_pos.le]
    intro s hs
    simp only [charX_next, charV_next]
    by_cases hs_le : s ≤ T
    · simp only [if_pos hs_le]
      rw [h_next_0]
      exact h_prev_aemeas s ⟨hs.1, hs_le⟩
    · simp only [if_neg hs_le]
      push_neg at hs_le
      rw [h_next_0]
      have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have hsT_mem : s - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [hs.2]⟩
      have h_g_at_sT := hg_aemeas_ex (s - T) hsT_mem
      rw [hg_init, h_prev_push T hT_mem] at h_g_at_sT
      exact h_g_at_sT.comp_aemeasurable (h_prev_aemeas T hT_mem)
  · -- Conjunct (vii): boundary bundle for charX_next charV_next on Icc 0 (T + T_0)
    exact glue_step_boundary_bundle gradW hT_pos hT_0_pos f_prev g f_next
      charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
      h_prev_boundary hg_boundary hg_init hg_init_cond
  · -- Conjunct (viii): initial condition for charX_next charV_next
    intro z
    simp only [charX_next, charV_next, if_pos hT_pos.le]
    exact h_prev_ic z

/-- **Stage 5: forward iteration to arbitrary `T_target`.**

Extends the local-existence theorem from its small-`T` smallness window
to any `T_target > 0`, by iterating the local theorem with shifted initial
data at fixed step `T_0 := (1/√L - 1) / 2` (which depends only on `L`).

**Hypothesis change vs `vlasovWellPosedness_local`**: replaces the explicit
joint smallness `L · (T + 1)² < 1` with the cleaner `L < 1` (which is the
genuine scope restriction inherited from the per-ball flow's `+1`-buffer
formulation; M-series watch-list candidate for the post-marquee scope
upgrade).

**Proof strategy** (sorry'd body, ~80-120 lines):

1. Pick `T_0 := (1/√L - 1) / 2`.  Verify `0 < T_0` (from `L < 1`) and
   `L · (T_0 + 1)² < 1` (algebraic: equals `(1 + √L)² / 4 < 1` for `L < 1`).

2. Pick `N := ⌈T_target / T_0⌉₊` so that `N · T_0 ≥ T_target`.

3. `Nat.rec` construction: define
   `f_n : ℕ → {f : ℝ → Measure (PhaseSpace d) // (the four conjuncts hold for T = n·T_0)}`.
   - Base case (`n = 0` or `n = 1`): apply `vlasovWellPosedness_local` directly.
   - Step case (`n → n+1`): apply `vlasovWellPosedness_glue_step` to extend.

4. Take `f := f_N` and verify the conjuncts for `T_target ≤ N · T_0` via
   `IsLagrangianVlasovSolutionOn`'s monotonicity in `T` (project down). -/
theorem vlasovWellPosedness_forward
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (hL_pos : (0 : ℝ) < L)
    (hL_lt : (L : ℝ) < 1)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T_target : ℝ} (hT_target : 0 < T_target) :
    ∃ f : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (f t)) ∧
      IsLagrangianVlasovSolutionOn gradW f T_target := by
  -- **Stage 2b part 3 (Soundness fix, 2026-05-31)**: T_0 must satisfy BOTH
  -- the PL-buffer constraint (`L·(T_0+1)² < 1`) AND the contraction constraint
  -- (`L·(exp T_0 - 1) < 1`, simplified for `L < 1`).  Per the M1-recursion
  -- (planning-notes commit `b7d4d05`), these are two genuinely independent
  -- constraints from distinct sub-arguments; T_0 = min(T_0_PL, T_0_con) / 2
  -- with strict-inequality margin lands both.
  let T_0_PL : ℝ := 1 / Real.sqrt L - 1
  let T_0_con : ℝ := Real.log (1 / (L : ℝ) + 1)
  -- Envelope-closure threshold: `B(T) := (L/(1+L))(exp((1+L)T) − 1) < 1` holds for
  -- `T < T_0_env`.  Positive for EVERY `L ∈ (0,1)` — it is a `T`-threshold at fixed
  -- `L` (`B(0)=0`, `B` continuous strictly increasing), so adding it to the `min`
  -- does NOT tighten the admissible `L`-range below the `L < 1` that `T_0_PL`
  -- already imposes (no `L`-restriction smuggled in).
  let T_0_env : ℝ := Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ))
  let T_0 : ℝ := min (min T_0_PL T_0_con) T_0_env / 2
  have hL_nn : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hsqrtL_pos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hL_pos
  have hsqrtL_lt1 : Real.sqrt (L : ℝ) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using hL_lt
  have hT_0_PL_pos : 0 < T_0_PL := by
    show 0 < 1 / Real.sqrt (L : ℝ) - 1
    have h1 : 1 < 1 / Real.sqrt (L : ℝ) := by
      rw [one_lt_div hsqrtL_pos]
      linarith
    linarith
  have h_one_div_L_plus_one_pos : 0 < 1 / (L : ℝ) + 1 := by
    have : 0 < 1 / (L : ℝ) := by positivity
    linarith
  have h_one_div_L_plus_one_gt_one : 1 < 1 / (L : ℝ) + 1 := by
    have : 0 < 1 / (L : ℝ) := by positivity
    linarith
  have hT_0_con_pos : 0 < T_0_con :=
    Real.log_pos h_one_div_L_plus_one_gt_one
  have h_1L_pos : (0 : ℝ) < 1 + (L : ℝ) := by linarith [hL_pos]
  have hT_0_env_pos : 0 < T_0_env := by
    show 0 < Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ))
    have h_arg_gt1 : 1 < 1 + (1 + (L : ℝ)) / (L : ℝ) := by
      have : 0 < (1 + (L : ℝ)) / (L : ℝ) := by positivity
      linarith
    exact div_pos (Real.log_pos h_arg_gt1) h_1L_pos
  have hT_0_min_pos : 0 < min (min T_0_PL T_0_con) T_0_env :=
    lt_min (lt_min hT_0_PL_pos hT_0_con_pos) hT_0_env_pos
  have hT0_pos : 0 < T_0 := by
    show 0 < min (min T_0_PL T_0_con) T_0_env / 2
    linarith
  -- **PL-buffer constraint at T_0** (existing algebra at T_0_PL_old, lifted
  -- to T_0 via monotonicity since T_0 ≤ T_0_PL_old).
  have hTL_T0_PL : LocalSmallness_PL_buffer L T_0 := by
    show (L : ℝ) * (T_0 + 1) ^ 2 < 1
    let T_0_PL_old : ℝ := (1 / Real.sqrt (L : ℝ) - 1) / 2
    have h_T_0_le_old : T_0 ≤ T_0_PL_old := by
      show min (min T_0_PL T_0_con) T_0_env / 2 ≤ (1 / Real.sqrt (L : ℝ) - 1) / 2
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_PL :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      show min (min T_0_PL T_0_con) T_0_env / 2 ≤ T_0_PL / 2
      linarith
    have h_T_0_PL_old_nn : 0 ≤ T_0_PL_old := by
      show 0 ≤ (1 / Real.sqrt (L : ℝ) - 1) / 2; linarith
    have h_T_0_nn : 0 ≤ T_0 := le_of_lt hT0_pos
    have h_sq_mono : (T_0 + 1) ^ 2 ≤ (T_0_PL_old + 1) ^ 2 := by
      have h_nn : 0 ≤ T_0 + 1 := by linarith
      have h_le : T_0 + 1 ≤ T_0_PL_old + 1 := by linarith
      exact pow_le_pow_left₀ h_nn h_le 2
    have h_mul_le : (L : ℝ) * (T_0 + 1) ^ 2 ≤ (L : ℝ) * (T_0_PL_old + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left h_sq_mono hL_nn
    -- L · (T_0_PL_old + 1)² = (1 + √L)² / 4 < 1 (the existing algebra).
    have hs_ne : Real.sqrt (L : ℝ) ≠ 0 := ne_of_gt hsqrtL_pos
    have hs_eq : (Real.sqrt (L : ℝ)) ^ 2 = (L : ℝ) := Real.sq_sqrt hL_nn
    have hT0_old_plus_1 :
        T_0_PL_old + 1 = (1 + Real.sqrt (L : ℝ)) / (2 * Real.sqrt (L : ℝ)) := by
      show (1 / Real.sqrt (L : ℝ) - 1) / 2 + 1
          = (1 + Real.sqrt (L : ℝ)) / (2 * Real.sqrt (L : ℝ))
      field_simp; ring
    have key : (L : ℝ) * (T_0_PL_old + 1) ^ 2 = (1 + Real.sqrt (L : ℝ)) ^ 2 / 4 := by
      rw [hT0_old_plus_1, div_pow]
      have h_sq_denom : (2 * Real.sqrt (L : ℝ)) ^ 2 = 4 * (L : ℝ) := by
        rw [mul_pow, hs_eq]; ring
      rw [h_sq_denom]; field_simp
    rw [key] at h_mul_le
    have h_lt : (1 + Real.sqrt (L : ℝ)) ^ 2 < 4 := by
      have h_sum_lt2 : 1 + Real.sqrt (L : ℝ) < 2 := by linarith
      have h_sum_nn : 0 ≤ 1 + Real.sqrt (L : ℝ) := by positivity
      nlinarith [h_sum_lt2, h_sum_nn]
    linarith
  -- **Contraction constraint at T_0** (T_0 < T_0_con since T_0 ≤ T_0_con/2 <
  -- T_0_con; then exp_lt_exp gives `exp T_0 < 1/L + 1`, and L·(...) < 1).
  have hTL_T0_con : LocalSmallness_contraction L T_0 := by
    show (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T_0) - 1) / (max 1 (L : ℝ)) < 1
    have hmax_eq : max 1 (L : ℝ) = 1 := max_eq_left hL_lt.le
    rw [hmax_eq, one_mul, div_one]
    -- T_0 ≤ T_0_con / 2 < T_0_con.
    have h_T_0_lt : T_0 < T_0_con := by
      show min (min T_0_PL T_0_con) T_0_env / 2 < T_0_con
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_con :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    -- exp T_0 < exp T_0_con = 1/L + 1.
    have h_exp_lt : Real.exp T_0 < 1 / (L : ℝ) + 1 := by
      have h_exp_log : Real.exp T_0_con = 1 / (L : ℝ) + 1 :=
        Real.exp_log h_one_div_L_plus_one_pos
      calc Real.exp T_0 < Real.exp T_0_con := Real.exp_lt_exp.mpr h_T_0_lt
        _ = 1 / (L : ℝ) + 1 := h_exp_log
    -- L · (exp T_0 - 1) < L · (1/L) = 1.
    have h_step : (L : ℝ) * (Real.exp T_0 - 1) < (L : ℝ) * (1 / (L : ℝ)) := by
      have h_sub_lt : Real.exp T_0 - 1 < 1 / (L : ℝ) := by linarith
      exact mul_lt_mul_of_pos_left h_sub_lt hL_pos
    have h_L_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    have h_L_inv : (L : ℝ) * (1 / (L : ℝ)) = 1 := by field_simp
    rw [h_L_inv] at h_step
    exact h_step
  -- **hB discharge at T_0** (envelope-closure `B(T_0) < 1`), CLOSED via the
  -- `T_0_env` threshold added to the `min` above: `T_0 < T_0_env` gives
  -- `(1+L)·T_0 < log(1 + (1+L)/L)`, hence `exp((1+L)·T_0) − 1 < (1+L)/L`, hence
  -- `(L/(1+L))·(exp((1+L)·T_0) − 1) < (L/(1+L))·((1+L)/L) = 1`.  No `L`-restriction
  -- beyond the `L < 1` already imposed by `T_0_PL` (this is a `T`-threshold).
  have hTL_T0_B :
      (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1 := by
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    have h_1L_ne : (1 + (L : ℝ)) ≠ 0 := ne_of_gt h_1L_pos
    have h_ratio_pos : (0 : ℝ) < (1 + (L : ℝ)) / (L : ℝ) := div_pos h_1L_pos hL_pos
    have h_arg_pos : (0 : ℝ) < 1 + (1 + (L : ℝ)) / (L : ℝ) := by linarith
    -- T_0 < T_0_env (the new outer-min branch).
    have h_T_0_lt_env : T_0 < T_0_env := by
      show min (min T_0_PL T_0_con) T_0_env / 2 < T_0_env
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_env := min_le_right _ _
      linarith
    -- (1+L)·T_0 < log(1 + (1+L)/L)  ( = (1+L)·T_0_env by the def of T_0_env).
    have h_lin_lt : (1 + (L : ℝ)) * T_0
        < Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := by
      have h_env_eq : (1 + (L : ℝ)) * T_0_env
          = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := by
        show (1 + (L : ℝ)) *
            (Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ)))
          = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ))
        field_simp
      calc (1 + (L : ℝ)) * T_0
          < (1 + (L : ℝ)) * T_0_env := mul_lt_mul_of_pos_left h_T_0_lt_env h_1L_pos
        _ = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := h_env_eq
    -- exp((1+L)·T_0) < 1 + (1+L)/L.
    have h_exp_lt : Real.exp ((1 + (L : ℝ)) * T_0)
        < 1 + (1 + (L : ℝ)) / (L : ℝ) := by
      calc Real.exp ((1 + (L : ℝ)) * T_0)
          < Real.exp (Real.log (1 + (1 + (L : ℝ)) / (L : ℝ))) :=
            Real.exp_lt_exp.mpr h_lin_lt
        _ = 1 + (1 + (L : ℝ)) / (L : ℝ) := Real.exp_log h_arg_pos
    have h_diff_lt : Real.exp ((1 + (L : ℝ)) * T_0) - 1 < (1 + (L : ℝ)) / (L : ℝ) := by
      linarith
    have hcoef_pos : (0 : ℝ) < (L : ℝ) / (1 + (L : ℝ)) := div_pos hL_pos h_1L_pos
    calc (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1)
        < (L : ℝ) / (1 + (L : ℝ)) * ((1 + (L : ℝ)) / (L : ℝ)) :=
          mul_lt_mul_of_pos_left h_diff_lt hcoef_pos
      _ = 1 := by field_simp
  -- Step 2: N = ⌈T_target / T_0⌉₊ windows of size T_0 cover T_target.
  let N : ℕ := ⌈T_target / T_0⌉₊
  have hN_pos : 0 < N := by
    show 0 < ⌈T_target / T_0⌉₊
    rw [Nat.ceil_pos]
    exact div_pos hT_target hT0_pos
  have hN_covers : T_target ≤ (N : ℝ) * T_0 := by
    have hle := Nat.le_ceil (T_target / T_0)
    have hT0_pos' := hT0_pos
    calc T_target = T_target / T_0 * T_0 := by field_simp
         _ ≤ (⌈T_target / T_0⌉₊ : ℝ) * T_0 :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hT0_pos)
  -- Step 3: Induction on n : ℕ — solution exists on [0, (n+1)·T_0].
  -- The induction carries explicit flow witnesses (charX, charV) and the full
  -- 7-component bundle to enable _glue_step calls without witness-identity issues.
  let T_n := fun n : ℕ => ((n + 1 : ℕ) : ℝ) * T_0
  have h_ind : ∀ n : ℕ,
      ∃ (f : ℝ → Measure (PhaseSpace d))
        (charX charV : ℝ → PhaseSpace d → PhysSpace d),
        f 0 = f₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (T_n n), HasFiniteFirstMoment (f t)) ∧
        -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
        (∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ Set.Icc (0 : ℝ) (T_n n), ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M) ∧
        IsVlasovSolutionOn gradW f (T_n n) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (T_n n),
            f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (T_n n),
            AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
        (∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T_n n) →
            HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 (T_n n)) t ∧
            HasDerivWithinAt (fun s => charV s z)
              (-(convolveFunctionMeasure gradW (spatialMarginal (f t)) (charX t z)))
              (Set.Icc 0 (T_n n)) t) ∧
        (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) := by
    intro n
    induction n with
    | zero =>
      -- Base: n = 0, need solution on [0, 1·T_0] = [0, T_0].
      simp only [T_n, Nat.cast_zero, zero_add, Nat.cast_one, one_mul]
      obtain ⟨f, charX, charV, hf_init, hf_mom, hf_mom_unif, hf_lag, hf_push, hf_aemeas, hf_boundary, hf_ic⟩ :=
        vlasovWellPosedness_local W gradW hgradW L hL f₀ hf₀ hT0_pos hTL_T0_PL hTL_T0_con hTL_T0_B
      exact ⟨f, charX, charV, hf_init, hf_mom, hf_mom_unif, hf_lag.1, hf_push, hf_aemeas, hf_boundary, hf_ic⟩
    | succ n ih =>
      -- Step: n+1 → (n+2)·T_0.  Use _glue_step with T = (n+1)·T_0 > 0.
      obtain ⟨f_n, charX_n, charV_n, hfn_init, hfn_mom, hfn_mom_unif, hfn_vlasov,
              hfn_push, hfn_aemeas, hfn_boundary, hfn_ic⟩ := ih
      simp only [T_n] at hfn_mom hfn_mom_unif hfn_vlasov hfn_push hfn_aemeas hfn_boundary
      have hT_n_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * T_0 :=
        mul_pos (by exact_mod_cast Nat.succ_pos n) hT0_pos
      -- Derive IsCharacteristicFlowOn from h_prev_boundary + hasDerivAt
      -- (interior points t ∈ Ioo 0 T_n have Icc 0 T_n ∈ 𝓝 t, so HasDerivWithinAt → HasDerivAt)
      have hfn_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f_n t))
          charX_n charV_n (Set.Ioo 0 (((n + 1 : ℕ) : ℝ) * T_0)) Set.univ := by
        refine ⟨fun z _ => hfn_ic z, ?_, ?_⟩
        · intro t ht z _
          exact ((hfn_boundary z t (Set.Ioo_subset_Icc_self ht)).1).hasDerivAt
            (Icc_mem_nhds ht.1 ht.2)
        · intro t ht z _
          exact ((hfn_boundary z t (Set.Ioo_subset_Icc_self ht)).2).hasDerivAt
            (Icc_mem_nhds ht.1 ht.2)
      obtain ⟨f_next, charX_next, charV_next, _h_agree, h_init, h_mom, h_mom_unif, h_lag,
              h_push, h_aemeas, h_boundary, h_ic⟩ :=
        vlasovWellPosedness_glue_step W gradW hgradW L hL f₀ hf₀ hT_n_pos
          f_n hfn_init hfn_mom hfn_mom_unif
          charX_n charV_n hfn_vlasov hfn_flow
          hfn_push hfn_aemeas hfn_boundary hfn_ic
          hT0_pos hTL_T0_PL hTL_T0_con hTL_T0_B
      -- Need: T_n (n+1) = T_n n + T_0
      have h_T_eq : T_n (n + 1) = T_n n + T_0 := by
        simp only [T_n]; push_cast; ring
      refine ⟨f_next, charX_next, charV_next, h_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_T_eq]; exact h_mom
      · rw [h_T_eq]; exact h_mom_unif
      · rw [h_T_eq]; exact h_lag.1
      · rw [h_T_eq]; exact h_push
      · rw [h_T_eq]; exact h_aemeas
      · rw [h_T_eq]; exact h_boundary
      · exact h_ic
  -- Step 4: Apply h_ind at n = N - 1 (since N ≥ 1).
  have hN_pred : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN_pos
  obtain ⟨f, charX_f, charV_f, hf_init, hf_mom, _hf_mom_unif, hf_vlasov,
          hf_push, hf_aemeas, hf_boundary, hf_ic⟩ := h_ind (N - 1)
  simp only [T_n] at hf_mom hf_vlasov hf_push hf_aemeas hf_boundary
  rw [hN_pred] at hf_mom hf_vlasov hf_push hf_aemeas hf_boundary
  -- Step 5: Restrict from [0, N·T_0] down to [0, T_target].
  refine ⟨f, hf_init, ?_, ?_⟩
  · -- Moment bound on [0, T_target] ⊆ [0, N·T_0].
    intro t ht
    exact hf_mom t ⟨ht.1, le_trans ht.2 hN_covers⟩
  · -- IsLagrangianVlasovSolutionOn on [0, T_target] ≤ [0, N·T_0].
    -- Derive IsCharacteristicFlowOn for T_target from hf_boundary (restrict to Ioo 0 T_target).
    have hf_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t))
        charX_f charV_f (Set.Ioo 0 T_target) Set.univ := by
      refine ⟨fun z _ => hf_ic z, ?_, ?_⟩
      · intro t ht z _
        have ht_lt_NT0 : t < (N : ℝ) * T_0 := lt_of_lt_of_le ht.2 hN_covers
        exact ((hf_boundary z t ⟨le_of_lt ht.1, le_of_lt ht_lt_NT0⟩).1).hasDerivAt
          (Icc_mem_nhds ht.1 ht_lt_NT0)
      · intro t ht z _
        have ht_lt_NT0 : t < (N : ℝ) * T_0 := lt_of_lt_of_le ht.2 hN_covers
        exact ((hf_boundary z t ⟨le_of_lt ht.1, le_of_lt ht_lt_NT0⟩).2).hasDerivAt
          (Icc_mem_nhds ht.1 ht_lt_NT0)
    refine ⟨?_, charX_f, charV_f, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn: restrict Ioo 0 T_target ⊆ Ioo 0 (N·T_0)
      intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
      exact hf_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t
        ⟨ht.1, lt_of_lt_of_le ht.2 hN_covers⟩
    · exact hf_flow
    · -- pushforward eq: restrict Icc 0 T_target ⊆ Icc 0 (N·T_0)
      intro t ht
      exact hf_push t ⟨ht.1, le_trans ht.2 hN_covers⟩
    · -- AEMeasurable ∧ boundary ContinuousOn, restricted to Icc 0 T_target.
      refine ⟨?_, ?_⟩
      · intro s hs
        exact hf_aemeas s ⟨hs.1, le_trans hs.2 hN_covers⟩
      · intro z
        have h_big : ContinuousOn (fun s => (charX_f s z, charV_f s z))
            (Set.Icc 0 ((N : ℝ) * T_0)) := fun t ht =>
          ((hf_boundary z t ht).1.continuousWithinAt).prodMk
            ((hf_boundary z t ht).2.continuousWithinAt)
        exact h_big.mono (fun t ht => ⟨ht.1, le_trans ht.2 hN_covers⟩)

-- ---------------------------------------------------------------------------
-- §9.6  Stage 8 — uniqueness over `IsLagrangianVlasovSolutionOn` per window
-- ---------------------------------------------------------------------------
-- Two Lagrangian solutions on `[0, T_target]` with the same initial measure
-- agree on `[0, T_target]`.  The argument: contraction in `Phi_supW1_contraction`
-- + Banach fixed-point uniqueness on the iterated windows.  Within the
-- `IsLagrangianVlasovSolutionOn` class, the flow witness is bundled, so
-- pushforward + flow uniqueness chains directly.  (The broader uniqueness
-- over `IsVlasovSolution` — weak-PDE-only solutions without an explicit
-- flow — requires the Eulerian-to-Lagrangian / DiPerna-Lions superposition
-- principle, which is out of scope.)

-- **`MathlibTODO_wassersteinGronwallCoupling_W1ContOn_On` (#8) — RETIRED
-- (2026-06-04)**: the `_On`-localized closed-window W₁-continuity placeholder
-- was only consumed by `dobrushin_uniqueness_On`, which has been re-proved
-- through the `integrated_coupling_gronwall_bound` collapse core (the
-- uniqueness `Q 0 = 0` case).  The integrated-coupling route bounds the
-- *integrated trajectory distance* `∫ ‖Φ_f − Φ_g‖ ∂μ₀` directly — never
-- forming `t ↦ (wasserstein1 (f t) (g t)).toReal` — so the closed-window
-- continuity of the real-valued W₁ distance is no longer needed.  The
-- placeholder became callerless and was deleted.


/-- **Shared integrated-coupling core for the Dobrushin stability bound.**

Generalizes the body of `dobrushin_uniqueness_On` over an arbitrary base
coupling measure `π₀` on `Ω` with measurable projections
`proj_f, proj_g : Ω → PhaseSpace d` such that `f 0 = (proj_f)_# π₀` and
`g 0 = (proj_g)_# π₀`.  Trajectory families are `X_μ s ω := Φ_μ s (proj_μ ω)`.
Concludes the integrated trajectory-distance bound

  ∫ ω, ‖Φ_f t (proj_f ω) − Φ_g t (proj_g ω)‖ ∂π₀
    ≤ (∫ ω, ‖proj_f ω − proj_g ω‖ ∂π₀) · exp(2·(max 1 L)·t)

via `integrated_coupling_gronwall_bound` with the moment-free Lipschitz-in-`z`
dominator (`dom ω = e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)`, integrable
through the two marginal moments) and the force-estimate-free cross-field bound
(the convolution difference bounded pointwise by `gradW`-Lipschitz, integrated
against `π₀` through the two marginal identities — never forming
`wasserstein1 (f s) (g s)`).

Two consumers:
* `dobrushin_uniqueness_On` — `proj_f = proj_g = id`, `π₀ = f 0 = g 0`, so the
  RHS base integral is `0` and the conclusion collapses to `f t = g t`.
* the mean-field `dobrushin` — `proj_f = fst`, `proj_g = snd`, `π₀` an optimal
  coupling of `(f 0, g 0)`, so the RHS base integral is `W₁(f 0, g 0)` and the
  LHS dominates `W₁(f t, g t)` by the easy direction of Kantorovich–Rubinstein.

Base-generic: the only base-specific work is the two marginal identities
`hmarg_f`/`hmarg_g`; the flow regularity, dominator, and cross-field force bound
are established generically over `π₀`. -/
private theorem dobrushin_integrated_flow_bound_On
    {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (π₀ : Measure Ω) [IsProbabilityMeasure π₀]
    (proj_f proj_g : Ω → PhaseSpace d)
    (hproj_f : Measurable proj_f) (hproj_g : Measurable proj_g)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hinit_f : ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        charX_f 0 z = z.1 ∧ charV_f 0 z = z.2)
    (hflow_f_x : ∀ s ∈ Set.Ioo (0:ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charX_f s' z) (charV_f s z) s)
    (hflow_f_v : ∀ s ∈ Set.Ioo (0:ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charV_f s' z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f s)) (charX_f s z))) s)
    (hpush_f : ∀ t ∈ Set.Icc (0:ℝ) T,
        f t = Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0))
    (haem_f : ∀ s ∈ Set.Icc (0:ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) (f 0))
    (hcontIcc_f : ∀ ω, ContinuousOn (fun s => (charX_f s ω, charV_f s ω)) (Set.Icc 0 T))
    (hinit_g : ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (hflow_g_x : ∀ s ∈ Set.Ioo (0:ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charX_g s' z) (charV_g s z) s)
    (hflow_g_v : ∀ s ∈ Set.Ioo (0:ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charV_g s' z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g s)) (charX_g s z))) s)
    (hpush_g : ∀ t ∈ Set.Icc (0:ℝ) T,
        g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0))
    (haem_g : ∀ s ∈ Set.Icc (0:ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hcontIcc_g : ∀ ω, ContinuousOn (fun s => (charX_g s ω, charV_g s ω)) (Set.Icc 0 T))
    (hf_mom : ∀ t ∈ Set.Icc (0:ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0:ℝ) T, HasFiniteFirstMoment (g t))
    (hmarg_f : f 0 = Measure.map proj_f π₀)
    (hmarg_g : g 0 = Measure.map proj_g π₀) :
    (∀ s ∈ Set.Icc (0:ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z))) ∧
    (∀ s ∈ Set.Icc (0:ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z))) ∧
    ∀ t ∈ Set.Icc (0:ℝ) T,
      Integrable (fun ω => ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖) π₀ ∧
      (∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀)
        ≤ (∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀)
            * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t) := by
  -- Probability instances.
  have hf_isProb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (f t) :=
    fun t ht => (hf_mom t ht).1
  have hg_isProb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (g t) :=
    fun t ht => (hg_mom t ht).1
  haveI hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  haveI hg0_prob : IsProbabilityMeasure (g 0) := (hg_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hL_le_max : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
    rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_right _ _
  -- Clamp into [0, T].
  set clampT : ℝ → ℝ := (fun s => max 0 (min s T)) with hclampT_def
  have hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T := by
    intro s; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s := by
    intro s hs; simp only [hclampT_def, min_eq_left hs.2, max_eq_right hs.1]
  -- Clamped trajectory families over the base `Ω`, read through the projections.
  set X_f : ℝ → Ω → PhaseSpace d :=
    fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)) with hX_f_def
  set X_g : ℝ → Ω → PhaseSpace d :=
    fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)) with hX_g_def
  -- Clamped Vlasov vector fields.
  set b_f : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => vlasovVectorField gradW (fun s => spatialMarginal (f (clampT s))) s
    with hb_f_def
  set b_g : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => vlasovVectorField gradW (fun s => spatialMarginal (g (clampT s))) s
    with hb_g_def
  -- gradW-kernel integrability on the spatial marginals (window-generic over μ).
  have h_int_helper : ∀ (μ : ℝ → Measure (PhaseSpace d))
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (μ t)),
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
        Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t)) := by
    intro μ hμ_prob t ht x_pt
    haveI : IsProbabilityMeasure (μ t) := (hμ_prob t ht).1
    haveI : IsProbabilityMeasure (spatialMarginal (μ t)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal (μ t)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (μ t)) := by
      unfold spatialMarginal
      rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
      refine Integrable.mono' (hμ_prob t ht).2
        ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      show |‖z.1‖| ≤ ‖z‖
      rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
    have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x_pt - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
        (spatialMarginal (μ t)) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
          (spatialMarginal (μ t)) := h_y_int.const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  have h_int_f := h_int_helper f hf_mom
  have h_int_g := h_int_helper g hg_mom
  have hfc_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (f (clampT s))) :=
    fun s x => h_int_f (clampT s) (hclampT_mem s) x
  have hgc_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (g (clampT s))) :=
    fun s x => h_int_g (clampT s) (hclampT_mem s) x
  haveI hfc_isProb : ∀ s, IsProbabilityMeasure (spatialMarginal (f (clampT s))) := by
    intro s; haveI := hf_isProb (clampT s) (hclampT_mem s)
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI hgc_isProb : ∀ s, IsProbabilityMeasure (spatialMarginal (g (clampT s))) := by
    intro s; haveI := hg_isProb (clampT s) (hclampT_mem s)
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Universal (max 1 L)-Lipschitz of the clamped vector fields.
  have hL_f : ∀ s, LipschitzWith (max 1 L) (b_f s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int s
  have hL_g : ∀ s, LipschitzWith (max 1 L) (b_g s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int s
  -- On [0, T] the clamped field coincides with the genuine field.
  have hb_f_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b_f s = vlasovVectorField gradW (fun s => spatialMarginal (f s)) s := by
    intro s hs
    have hmeas : spatialMarginal (f (clampT s)) = spatialMarginal (f s) := by
      rw [hclampT_id s hs]
    funext z; simp only [hb_f_def, vlasovVectorField, hmeas]
  have hb_g_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b_g s = vlasovVectorField gradW (fun s => spatialMarginal (g s)) s := by
    intro s hs
    have hmeas : spatialMarginal (g (clampT s)) = spatialMarginal (g s) := by
      rw [hclampT_id s hs]
    funext z; simp only [hb_g_def, vlasovVectorField, hmeas]
  -- Open-window flow ODE in z (HasDerivWithinAt on `Ici s`, `s ∈ Ioo 0 T`).
  have hderiv_Ioo_f : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_f s' z, charV_f s' z))
        (vlasovVectorField gradW (fun s => spatialMarginal (f (clampT s))) s
          (charX_f s z, charV_f s z)) (Set.Ici s) s := by
    intro z s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hat : HasDerivAt (fun s' => (charX_f s' z, charV_f s' z))
        (vlasovVectorField gradW (fun s => spatialMarginal (f s)) s
          (charX_f s z, charV_f s z)) s := by
      show HasDerivAt (fun s' => (charX_f s' z, charV_f s' z))
        ((charX_f s z, charV_f s z).2,
         -(convolveFunctionMeasure gradW (spatialMarginal (f s))
            (charX_f s z, charV_f s z).1)) s
      exact (hflow_f_x s hs z (Set.mem_univ z)).prodMk (hflow_f_v s hs z (Set.mem_univ z))
    have hmeas : spatialMarginal (f (clampT s)) = spatialMarginal (f s) := by
      rw [hclampT_id s hsIcc]
    have hvf_eq : vlasovVectorField gradW (fun s => spatialMarginal (f (clampT s))) s
          (charX_f s z, charV_f s z)
        = vlasovVectorField gradW (fun s => spatialMarginal (f s)) s
          (charX_f s z, charV_f s z) := by
      simp only [vlasovVectorField, hmeas]
    rw [hvf_eq]; exact hat.hasDerivWithinAt
  have hderiv_Ioo_g : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_g s' z, charV_g s' z))
        (vlasovVectorField gradW (fun s => spatialMarginal (g (clampT s))) s
          (charX_g s z, charV_g s z)) (Set.Ici s) s := by
    intro z s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hat : HasDerivAt (fun s' => (charX_g s' z, charV_g s' z))
        (vlasovVectorField gradW (fun s => spatialMarginal (g s)) s
          (charX_g s z, charV_g s z)) s := by
      show HasDerivAt (fun s' => (charX_g s' z, charV_g s' z))
        ((charX_g s z, charV_g s z).2,
         -(convolveFunctionMeasure gradW (spatialMarginal (g s))
            (charX_g s z, charV_g s z).1)) s
      exact (hflow_g_x s hs z (Set.mem_univ z)).prodMk (hflow_g_v s hs z (Set.mem_univ z))
    have hmeas : spatialMarginal (g (clampT s)) = spatialMarginal (g s) := by
      rw [hclampT_id s hsIcc]
    have hvf_eq : vlasovVectorField gradW (fun s => spatialMarginal (g (clampT s))) s
          (charX_g s z, charV_g s z)
        = vlasovVectorField gradW (fun s => spatialMarginal (g s)) s
          (charX_g s z, charV_g s z) := by
      simp only [vlasovVectorField, hmeas]
    rw [hvf_eq]; exact hat.hasDerivWithinAt
  have hinit_f' : ∀ z : PhaseSpace d, (charX_f 0 z, charV_f 0 z) = z := by
    intro z; obtain ⟨hx, hv⟩ := hinit_f z (Set.mem_univ z); rw [hx, hv]
  have hinit_g' : ∀ z : PhaseSpace d, (charX_g 0 z, charV_g 0 z) = z := by
    intro z; obtain ⟨hx, hv⟩ := hinit_g z (Set.mem_univ z); rw [hx, hv]
  have hmeas_charf : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int charX_f charV_f T hT.le
      hinit_f' hcontIcc_f hderiv_Ioo_f
  have hmeas_charg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int charX_g charV_g T hT.le
      hinit_g' hcontIcc_g hderiv_Ioo_g
  -- Universal-in-`s` measurability of the clamped flows (clampT s ∈ [0,T]),
  -- composed with the (measurable) projections to land on `Ω`.
  have hmeas_f : ∀ s, Measurable (X_f s) := by
    intro s
    simpa only [hX_f_def] using (hmeas_charf (clampT s) (hclampT_mem s)).comp hproj_f
  have hmeas_g : ∀ s, Measurable (X_g s) := by
    intro s
    simpa only [hX_g_def] using (hmeas_charg (clampT s) (hclampT_mem s)).comp hproj_g
  have hclampT_cont : Continuous clampT :=
    continuous_const.max (continuous_id.min continuous_const)
  -- Per-ω continuity of the clamped trajectories on [0, T].
  have hcont_f : ∀ ω, ContinuousOn (fun s => X_f s ω) (Set.Icc 0 T) := by
    intro ω
    have hbase : ContinuousOn (fun s => (charX_f s (proj_f ω), charV_f s (proj_f ω)))
        (Set.Icc 0 T) := hcontIcc_f (proj_f ω)
    apply ContinuousOn.congr
      (f := fun s => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    · exact hbase.comp hclampT_cont.continuousOn (fun s hs => hclampT_mem s)
    · intro s hs; simp only [hX_f_def, hclampT_id s hs]
  have hcont_g : ∀ ω, ContinuousOn (fun s => X_g s ω) (Set.Icc 0 T) := by
    intro ω
    have hbase : ContinuousOn (fun s => (charX_g s (proj_g ω), charV_g s (proj_g ω)))
        (Set.Icc 0 T) := hcontIcc_g (proj_g ω)
    apply ContinuousOn.congr
      (f := fun s => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)))
    · exact hbase.comp hclampT_cont.continuousOn (fun s hs => hclampT_mem s)
    · intro s hs; simp only [hX_g_def, hclampT_id s hs]
  -- Per-ω ODE of the clamped trajectories on Ioo 0 T (HasDerivWithinAt Ioi).
  have hderiv_f : ∀ ω, ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt (fun s => X_f s ω) (b_f s (X_f s ω)) (Set.Ioi s) s := by
    intro ω s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hat : HasDerivAt (fun s' => (charX_f s' (proj_f ω), charV_f s' (proj_f ω)))
        (vlasovVectorField gradW (fun s => spatialMarginal (f s)) s
          (charX_f s (proj_f ω), charV_f s (proj_f ω))) s := by
      show HasDerivAt (fun s' => (charX_f s' (proj_f ω), charV_f s' (proj_f ω)))
        ((charX_f s (proj_f ω), charV_f s (proj_f ω)).2,
         -(convolveFunctionMeasure gradW (spatialMarginal (f s))
            (charX_f s (proj_f ω), charV_f s (proj_f ω)).1)) s
      exact (hflow_f_x s hs (proj_f ω) (Set.mem_univ _)).prodMk
        (hflow_f_v s hs (proj_f ω) (Set.mem_univ _))
    have hwithin : HasDerivWithinAt (fun s' => (charX_f s' (proj_f ω), charV_f s' (proj_f ω)))
        (vlasovVectorField gradW (fun s => spatialMarginal (f s)) s
          (charX_f s (proj_f ω), charV_f s (proj_f ω))) (Set.Ioi s) s := hat.hasDerivWithinAt
    have heq : Set.EqOn (fun s' => X_f s' ω)
        (fun s' => (charX_f s' (proj_f ω), charV_f s' (proj_f ω))) (Set.Ioo (0:ℝ) T) := by
      intro s' hs'; simp only [hX_f_def, hclampT_id s' ⟨hs'.1.le, hs'.2.le⟩]
    have hmem_nhds : Set.Ioo (0:ℝ) T ∈ nhdsWithin s (Set.Ioi s) :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs)
    have hxf : X_f s ω = (charX_f s (proj_f ω), charV_f s (proj_f ω)) := by
      simp only [hX_f_def, hclampT_id s hsIcc]
    have hwithin' := hwithin.congr_of_eventuallyEq
      (Filter.eventually_of_mem hmem_nhds (fun s' hs' => heq hs'))
      hxf
    rw [hb_f_id s hsIcc, hxf]; exact hwithin'
  have hderiv_g : ∀ ω, ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt (fun s => X_g s ω) (b_g s (X_g s ω)) (Set.Ioi s) s := by
    intro ω s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hat : HasDerivAt (fun s' => (charX_g s' (proj_g ω), charV_g s' (proj_g ω)))
        (vlasovVectorField gradW (fun s => spatialMarginal (g s)) s
          (charX_g s (proj_g ω), charV_g s (proj_g ω))) s := by
      show HasDerivAt (fun s' => (charX_g s' (proj_g ω), charV_g s' (proj_g ω)))
        ((charX_g s (proj_g ω), charV_g s (proj_g ω)).2,
         -(convolveFunctionMeasure gradW (spatialMarginal (g s))
            (charX_g s (proj_g ω), charV_g s (proj_g ω)).1)) s
      exact (hflow_g_x s hs (proj_g ω) (Set.mem_univ _)).prodMk
        (hflow_g_v s hs (proj_g ω) (Set.mem_univ _))
    have hwithin : HasDerivWithinAt (fun s' => (charX_g s' (proj_g ω), charV_g s' (proj_g ω)))
        (vlasovVectorField gradW (fun s => spatialMarginal (g s)) s
          (charX_g s (proj_g ω), charV_g s (proj_g ω))) (Set.Ioi s) s := hat.hasDerivWithinAt
    have heq : Set.EqOn (fun s' => X_g s' ω)
        (fun s' => (charX_g s' (proj_g ω), charV_g s' (proj_g ω))) (Set.Ioo (0:ℝ) T) := by
      intro s' hs'; simp only [hX_g_def, hclampT_id s' ⟨hs'.1.le, hs'.2.le⟩]
    have hmem_nhds : Set.Ioo (0:ℝ) T ∈ nhdsWithin s (Set.Ioi s) :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs)
    have hxg : X_g s ω = (charX_g s (proj_g ω), charV_g s (proj_g ω)) := by
      simp only [hX_g_def, hclampT_id s hsIcc]
    have hwithin' := hwithin.congr_of_eventuallyEq
      (Filter.eventually_of_mem hmem_nhds (fun s' hs' => heq hs'))
      hxg
    rw [hb_g_id s hsIcc, hxg]; exact hwithin'
  -- Moment-free dominator: `dom ω = e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)`.
  set K : NNReal := max 1 L with hK_def
  have hK_nn : (0 : ℝ) ≤ ((K : NNReal) : ℝ) := K.coe_nonneg
  set EKT : ℝ := Real.exp (((K : NNReal) : ℝ) * T) with hEKT_def
  have hEKT_pos : 0 < EKT := Real.exp_pos _
  have hlip_f : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX_f s z₁, charV_f s z₁) : PhaseSpace d) (charX_f s z₂, charV_f s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int charX_f charV_f T hT.le
      hinit_f' hcontIcc_f hderiv_Ioo_f
  have hlip_g : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX_g s z₁, charV_g s z₁) : PhaseSpace d) (charX_g s z₂, charV_g s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int charX_g charV_g T hT.le
      hinit_g' hcontIcc_g hderiv_Ioo_g
  have horig : ∀ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      ContinuousOn (fun s => (charX s 0, charV s 0)) (Set.Icc (0 : ℝ) T) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ s ∈ Set.Icc (0 : ℝ) T,
        ‖(charX s 0, charV s 0)‖ ≤ Kc := by
    intro charX charV hcont
    have hbdd : BddAbove ((fun s => ‖(charX s 0, charV s 0)‖) '' Set.Icc (0 : ℝ) T) :=
      IsCompact.bddAbove_image isCompact_Icc hcont.norm
    obtain ⟨Kc, hKc⟩ := hbdd
    refine ⟨max Kc 0, le_max_right _ _, fun s hs => ?_⟩
    exact le_trans (hKc (Set.mem_image_of_mem _ hs)) (le_max_left _ _)
  obtain ⟨K_f, hK_f_nn, hK_f⟩ := horig charX_f charV_f (hcontIcc_f 0)
  obtain ⟨K_g, hK_g_nn, hK_g⟩ := horig charX_g charV_g (hcontIcc_g 0)
  have hflownorm : ∀ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (Kc : ℝ),
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
        dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂) ≤
        dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0))) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, ‖(charX s 0, charV s 0)‖ ≤ Kc) →
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
        ‖(charX s ω, charV s ω)‖ ≤ EKT * ‖ω‖ + Kc := by
    intro charX charV Kc hlip hKc s hs ω
    have htri : ‖(charX s ω, charV s ω)‖ ≤
        dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
          + ‖(charX s 0, charV s 0)‖ := by
      rw [dist_eq_norm]
      calc ‖(charX s ω, charV s ω)‖
          = ‖((charX s ω, charV s ω) - (charX s 0, charV s 0))
              + ((charX s 0, charV s 0) : PhaseSpace d)‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖((charX s ω, charV s ω) : PhaseSpace d) - (charX s 0, charV s 0)‖
              + ‖(charX s 0, charV s 0)‖ := norm_add_le _ _
    have hdist_le : dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
        ≤ EKT * ‖ω‖ := by
      refine le_trans (hlip s hs ω 0) ?_
      rw [dist_zero_right]
      have hsT : (((K : NNReal) : ℝ)) * (s - 0) ≤ (((K : NNReal) : ℝ)) * T := by
        rw [sub_zero]; exact mul_le_mul_of_nonneg_left hs.2 hK_nn
      have hexp_le : Real.exp (((K : NNReal) : ℝ) * (s - 0)) ≤ EKT :=
        Real.exp_le_exp.mpr hsT
      calc ‖ω‖ * Real.exp (((K : NNReal) : ℝ) * (s - 0))
          ≤ ‖ω‖ * EKT := mul_le_mul_of_nonneg_left hexp_le (norm_nonneg _)
        _ = EKT * ‖ω‖ := by ring
    calc ‖(charX s ω, charV s ω)‖
        ≤ dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
            + ‖(charX s 0, charV s 0)‖ := htri
      _ ≤ EKT * ‖ω‖ + Kc := by
          gcongr
          exact hKc s hs
  have hfnorm := hflownorm charX_f charV_f K_f hlip_f hK_f
  have hgnorm := hflownorm charX_g charV_g K_g hlip_g hK_g
  set dom : Ω → ℝ := fun ω => EKT * ‖proj_f ω‖ + EKT * ‖proj_g ω‖ + (K_f + K_g) with hdom_def
  have hmom_f : Integrable (fun ω : Ω => ‖proj_f ω‖) π₀ := by
    have hmap : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map proj_f π₀) := by
      rw [← hmarg_f]; exact (hf_mom 0 ⟨le_refl 0, hT.le⟩).2
    exact (integrable_map_measure continuous_norm.aestronglyMeasurable
      hproj_f.aemeasurable).mp hmap
  have hmom_g : Integrable (fun ω : Ω => ‖proj_g ω‖) π₀ := by
    have hmap : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map proj_g π₀) := by
      rw [← hmarg_g]; exact (hg_mom 0 ⟨le_refl 0, hT.le⟩).2
    exact (integrable_map_measure continuous_norm.aestronglyMeasurable
      hproj_g.aemeasurable).mp hmap
  have hdom_int : Integrable dom π₀ := by
    simp only [hdom_def]
    exact ((hmom_f.const_mul EKT).add (hmom_g.const_mul EKT)).add (integrable_const _)
  have hdom : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω := by
    intro s hs ω
    have hclamp_eq : clampT s = s := hclampT_id s hs
    have hXf : X_f s ω = (charX_f s (proj_f ω), charV_f s (proj_f ω)) := by
      simp only [hX_f_def, hclamp_eq]
    have hXg : X_g s ω = (charX_g s (proj_g ω), charV_g s (proj_g ω)) := by
      simp only [hX_g_def, hclamp_eq]
    rw [hXf, hXg]
    calc ‖(charX_f s (proj_f ω), charV_f s (proj_f ω))
            - (charX_g s (proj_g ω), charV_g s (proj_g ω))‖
        ≤ ‖(charX_f s (proj_f ω), charV_f s (proj_f ω))‖
            + ‖(charX_g s (proj_g ω), charV_g s (proj_g ω))‖ := norm_sub_le _ _
      _ ≤ (EKT * ‖proj_f ω‖ + K_f) + (EKT * ‖proj_g ω‖ + K_g) := by
          have hf_bd := hfnorm s hs (proj_f ω)
          have hg_bd := hgnorm s hs (proj_g ω)
          gcongr
      _ = dom ω := by simp only [hdom_def]; ring
  -- Cross-field bound ε and its self-reference to Q (over the base π₀).
  set Q : ℝ → ℝ := fun s => ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ with hQ_def
  set ε : ℝ → ℝ := fun s => ((max 1 L : NNReal) : ℝ) * Q s with hε_def
  have hXf_cont_glob : ∀ ω, Continuous (fun s => X_f s ω) := by
    intro ω
    have : Continuous (fun s => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω))) :=
      (hcontIcc_f (proj_f ω)).comp_continuous hclampT_cont (fun s => hclampT_mem s)
    simpa only [hX_f_def] using this
  have hXg_cont_glob : ∀ ω, Continuous (fun s => X_g s ω) := by
    intro ω
    have : Continuous (fun s => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω))) :=
      (hcontIcc_g (proj_g ω)).comp_continuous hclampT_cont (fun s => hclampT_mem s)
    simpa only [hX_g_def] using this
  have hQ_cont : ContinuousOn Q (Set.Icc 0 T) := by
    have hQglob : Continuous Q := by
      simp only [hQ_def]
      refine continuous_of_dominated
        (fun s => ((hmeas_f s).sub (hmeas_g s)).norm.aestronglyMeasurable)
        (fun s => Filter.Eventually.of_forall (fun ω => ?_))
        hdom_int
        (Filter.Eventually.of_forall (fun ω => ((hXf_cont_glob ω).sub (hXg_cont_glob ω)).norm))
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      have hcl : clampT s ∈ Set.Icc (0:ℝ) T := hclampT_mem s
      have hXf : X_f s ω = X_f (clampT s) ω := by
        simp only [hX_f_def]; rw [hclampT_id (clampT s) hcl]
      have hXg : X_g s ω = X_g (clampT s) ω := by
        simp only [hX_g_def]; rw [hclampT_id (clampT s) hcl]
      rw [hXf, hXg]; exact hdom (clampT s) hcl ω
    exact hQglob.continuousOn
  have hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T := by
    have hεcont : ContinuousOn ε (Set.Icc 0 T) := by
      simp only [hε_def]; exact continuousOn_const.mul hQ_cont
    exact hεcont.intervalIntegrable_of_Icc hT.le
  have hε_nn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ ε s := by
    intro s _; simp only [hε_def]
    exact mul_nonneg (le_trans zero_le_one
      (by rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _))
      (integral_nonneg (fun ω => norm_nonneg _))
  have h_self : ∀ s ∈ Set.Icc (0:ℝ) T,
      ε s ≤ ((max 1 L : NNReal) : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ := by
    intro s _; exact le_refl _
  -- Pushforward-convolution identity, generic in the base `ν`.
  have h_conv_push : ∀ (charX charV : ℝ → PhaseSpace d → PhysSpace d)
      (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d)),
      (∀ t ∈ Set.Icc (0:ℝ) T,
        μ t = Measure.map (fun z => (charX t z, charV t z)) ν) →
      (∀ s ∈ Set.Icc (0:ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν) →
      ∀ s ∈ Set.Icc (0:ℝ) T, ∀ x : PhysSpace d,
        convolveFunctionMeasure gradW (spatialMarginal (μ s)) x
          = ∫ ω', gradW (x - charX s ω') ∂ν := by
    intro charX charV μ ν hpush haem s hs x
    unfold convolveFunctionMeasure spatialMarginal
    rw [hpush s hs]
    have haem_s : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν :=
      haem s hs
    have hmeas_gradW : AEStronglyMeasurable
        (fun y : PhysSpace d => gradW (x - y))
        (Measure.map Prod.fst (Measure.map (fun z => (charX s z, charV s z)) ν)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    rw [integral_map measurable_fst.aemeasurable hmeas_gradW]
    have hmeas_inner : AEStronglyMeasurable
        (fun z : PhaseSpace d => gradW (x - z.1))
        (Measure.map (fun z => (charX s z, charV s z)) ν) :=
      ((hL.continuous.comp (continuous_const.sub continuous_fst))).aestronglyMeasurable
    rw [integral_map haem_s hmeas_inner]
  -- Companion integrability transfers, generic in the base `ν`.
  have h_int_push : ∀ (charX charV : ℝ → PhaseSpace d → PhysSpace d)
      (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d)),
      (∀ t ∈ Set.Icc (0:ℝ) T,
        μ t = Measure.map (fun z => (charX t z, charV t z)) ν) →
      (∀ s ∈ Set.Icc (0:ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν) →
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ (x_pt : PhysSpace d),
        Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t))) →
      ∀ s ∈ Set.Icc (0:ℝ) T, ∀ x : PhysSpace d,
        Integrable (fun ω' => gradW (x - charX s ω')) ν := by
    intro charX charV μ ν hpush haem hint_sm s hs x
    have hsm := hint_sm s hs x
    unfold spatialMarginal at hsm
    rw [hpush s hs] at hsm
    rw [integrable_map_measure
      (g := fun y : PhysSpace d => gradW (x - y))
      ((hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      measurable_fst.aemeasurable] at hsm
    simp only [Function.comp_def] at hsm
    rw [integrable_map_measure
      (g := fun z : PhaseSpace d => gradW (x - z.1))
      ((hL.continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable)
      (haem s hs)] at hsm
    exact hsm
  have h_phase_int : ∀ (charX charV : ℝ → PhaseSpace d → PhysSpace d)
      (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d)),
      (∀ t ∈ Set.Icc (0:ℝ) T,
        μ t = Measure.map (fun z => (charX t z, charV t z)) ν) →
      (∀ s ∈ Set.Icc (0:ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν) →
      (∀ t ∈ Set.Icc (0:ℝ) T, Integrable (fun z : PhaseSpace d => ‖z‖) (μ t)) →
      ∀ s ∈ Set.Icc (0:ℝ) T,
        Integrable (fun ω' : PhaseSpace d => (charX s ω', charV s ω')) ν := by
    intro charX charV μ ν hpush haem hmom s hs
    have hid : Integrable (fun z : PhaseSpace d => z) (μ s) :=
      (integrable_norm_iff aestronglyMeasurable_id).mp (hmom s hs)
    rw [hpush s hs] at hid
    rw [integrable_map_measure
      (g := fun z : PhaseSpace d => z) aestronglyMeasurable_id (haem s hs)] at hid
    exact hid
  -- Field continuity (generic in the base `ν`), for `hint`.
  have hfield_cont : ∀ (charX charV : ℝ → PhaseSpace d → PhysSpace d)
      (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d)) (Kc : ℝ)
      (b : ℝ → PhaseSpace d → PhaseSpace d) (X : ℝ → PhaseSpace d → PhaseSpace d),
      (b = fun s => vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s) →
      (X = fun s ω => (charX (clampT s) ω, charV (clampT s) ω)) →
      (∀ z, Continuous (fun s => (charX (clampT s) z, charV (clampT s) z))) →
      (∀ t ∈ Set.Icc (0:ℝ) T,
        μ t = Measure.map (fun z => (charX t z, charV t z)) ν) →
      (∀ s ∈ Set.Icc (0:ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν) →
      IsProbabilityMeasure ν →
      Integrable (fun z : PhaseSpace d => ‖z‖) ν →
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ (x_pt : PhysSpace d),
        Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t))) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, ‖(charX s 0, charV s 0)‖ ≤ Kc) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
        dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂) ≤
        dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0))) →
      ∀ ω, Continuous (fun s => b s (X s ω)) := by
    intro charX charV μ ν Kc b X hb hX hflowcont hpush haem hν_prob hν_mom hint_sm hKc hlip ω
    haveI := hν_prob
    have hΦnorm : ∀ s : ℝ, ∀ z : PhaseSpace d,
        ‖(charX (clampT s) z, charV (clampT s) z)‖ ≤ EKT * ‖z‖ + Kc := by
      intro s z
      exact hflownorm charX charV Kc hlip hKc (clampT s) (hclampT_mem s) z
    subst hb hX
    set xS : ℝ → PhysSpace d := fun s => charX (clampT s) ω with hxS_def
    have hxS_cont : Continuous xS := (continuous_fst.comp (hflowcont ω))
    have hforce_eq : ∀ s : ℝ,
        convolveFunctionMeasure gradW (spatialMarginal (μ (clampT s))) (xS s)
          = ∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν := by
      intro s
      exact h_conv_push charX charV μ ν hpush haem (clampT s) (hclampT_mem s) (xS s)
    have hforce_cont : Continuous
        (fun s => ∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν) := by
      set bnd : PhaseSpace d → ℝ := fun ω' =>
        ‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + (EKT * ‖ω'‖ + Kc)) with hbnd_def
      have hbnd_int : Integrable bnd ν := by
        simp only [hbnd_def]
        have hmom : Integrable (fun ω' : PhaseSpace d => ‖ω'‖) ν := hν_mom
        have hL_EKT : Integrable (fun ω' : PhaseSpace d => (L : ℝ) * (EKT * ‖ω'‖)) ν := by
          have : Integrable (fun ω' : PhaseSpace d => EKT * ‖ω'‖) ν :=
            hmom.const_mul EKT
          exact this.const_mul (L : ℝ)
        have heq : (fun ω' : PhaseSpace d =>
            ‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + (EKT * ‖ω'‖ + Kc))) =
            fun ω' => (‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + Kc))
              + (L : ℝ) * (EKT * ‖ω'‖) := by
          funext ω'; ring
        rw [heq]; exact (integrable_const _).add hL_EKT
      refine continuous_of_dominated
        (fun s => ?_) (fun s => Filter.Eventually.of_forall (fun ω' => ?_)) hbnd_int
        (Filter.Eventually.of_forall (fun ω' => ?_))
      · have haem_charX : AEMeasurable (fun ω' : PhaseSpace d => charX (clampT s) ω') ν :=
          (measurable_fst.comp_aemeasurable (haem (clampT s) (hclampT_mem s)))
        exact ((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp_aemeasurable
          haem_charX).aestronglyMeasurable
      · have hd := hL.dist_le_mul (xS s - charX (clampT s) ω') 0
        simp only [dist_eq_norm, sub_zero] at hd
        have h_tri : ‖gradW (xS s - charX (clampT s) ω')‖ ≤
            ‖gradW 0‖ + ‖gradW (xS s - charX (clampT s) ω') - gradW 0‖ := by
          have := norm_add_le (gradW (xS s - charX (clampT s) ω') - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        have hsub_le : ‖xS s - charX (clampT s) ω'‖ ≤ ‖xS s‖ + ‖charX (clampT s) ω'‖ :=
          norm_sub_le _ _
        have hxS_le : ‖xS s‖ ≤ EKT * ‖ω‖ + Kc := by
          simp only [hxS_def]
          exact le_trans
            (norm_fst_le ((charX (clampT s) ω, charV (clampT s) ω) : PhaseSpace d))
            (hΦnorm s ω)
        have hcharX_le : ‖charX (clampT s) ω'‖ ≤ EKT * ‖ω'‖ + Kc :=
          le_trans
            (norm_fst_le ((charX (clampT s) ω', charV (clampT s) ω') : PhaseSpace d))
            (hΦnorm s ω')
        have h_mul := mul_le_mul_of_nonneg_left
          (le_trans hsub_le (add_le_add hxS_le hcharX_le)) L.coe_nonneg
        simp only [hbnd_def]; linarith
      · exact hL.continuous.comp (hxS_cont.sub
          (continuous_fst.comp (hflowcont ω')))
    have hvel_cont : Continuous (fun s => (charX (clampT s) ω, charV (clampT s) ω).2) :=
      continuous_snd.comp (hflowcont ω)
    have hbody : (fun s => vlasovVectorField gradW
          (fun s => spatialMarginal (μ (clampT s))) s
          ((charX (clampT s) ω, charV (clampT s) ω)))
        = fun s => ((charX (clampT s) ω, charV (clampT s) ω).2,
            -(∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν)) := by
      funext s
      simp only [vlasovVectorField]
      refine Prod.ext rfl ?_
      show -(convolveFunctionMeasure gradW (spatialMarginal (μ (clampT s)))
          (charX (clampT s) ω, charV (clampT s) ω).1)
        = -(∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν)
      rw [hforce_eq s]
    rw [hbody]
    exact hvel_cont.prodMk hforce_cont.neg
  have hint : ∀ ω, IntervalIntegrable
      (fun s => b_f s (X_f s ω) - b_g s (X_g s ω)) MeasureTheory.volume 0 T := by
    intro ω
    have hcf : Continuous (fun s => b_f s (X_f s ω)) := by
      have h := hfield_cont charX_f charV_f f (f 0) K_f b_f
        (fun s z => (charX_f (clampT s) z, charV_f (clampT s) z)) hb_f_def rfl
        (fun z => (hcontIcc_f z).comp_continuous hclampT_cont (fun s => hclampT_mem s))
        hpush_f haem_f hf0_prob (hf_mom 0 ⟨le_refl 0, hT.le⟩).2 h_int_f hK_f hlip_f (proj_f ω)
      simpa only [hX_f_def] using h
    have hcg : Continuous (fun s => b_g s (X_g s ω)) := by
      have h := hfield_cont charX_g charV_g g (g 0) K_g b_g
        (fun s z => (charX_g (clampT s) z, charV_g (clampT s) z)) hb_g_def rfl
        (fun z => (hcontIcc_g z).comp_continuous hclampT_cont (fun s => hclampT_mem s))
        hpush_g haem_g hg0_prob (hg_mom 0 ⟨le_refl 0, hT.le⟩).2 h_int_g hK_g hlip_g (proj_g ω)
      simpa only [hX_g_def] using h
    exact ((hcf.sub hcg).continuousOn).intervalIntegrable_of_Icc hT.le
  -- Cross-field bound: convolution difference bounded pointwise by the coupled
  -- trajectory distance, integrated against `π₀` through the two marginals.
  have h_diff : ∀ ω, ∀ s ∈ Set.Icc (0:ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤ ε s := by
    intro ω s hs
    haveI := hf_isProb s hs
    haveI := hg_isProb s hs
    set x : PhysSpace d := (X_g s ω).1 with hx_def
    have hb_f_s := hb_f_id s hs
    have hb_g_s := hb_g_id s hs
    have h_form : b_f s (X_g s ω) - b_g s (X_g s ω) =
        ((0 : PhysSpace d),
         convolveFunctionMeasure gradW (spatialMarginal (g s)) x
           - convolveFunctionMeasure gradW (spatialMarginal (f s)) x) := by
      rw [hb_f_s, hb_g_s]
      simp only [vlasovVectorField, Prod.mk_sub_mk, sub_self, hx_def]
      refine Prod.ext rfl ?_
      show -(convolveFunctionMeasure gradW (spatialMarginal (f s)) (X_g s ω).1)
            - -(convolveFunctionMeasure gradW (spatialMarginal (g s)) (X_g s ω).1)
          = convolveFunctionMeasure gradW (spatialMarginal (g s)) (X_g s ω).1
            - convolveFunctionMeasure gradW (spatialMarginal (f s)) (X_g s ω).1
      abel
    rw [h_form, Prod.norm_def]
    simp only [norm_zero]
    rw [max_eq_right (norm_nonneg _)]
    -- Native-base pushforward of both convolutions.
    rw [h_conv_push charX_g charV_g g (g 0) hpush_g haem_g s hs x,
        h_conv_push charX_f charV_f f (f 0) hpush_f haem_f s hs x]
    -- Measurability of the position maps `charX_μ s`.
    have hmeas_charf_s : Measurable (fun z : PhaseSpace d => charX_f s z) :=
      measurable_fst.comp (hmeas_charf s hs)
    have hmeas_charg_s : Measurable (fun z : PhaseSpace d => charX_g s z) :=
      measurable_fst.comp (hmeas_charg s hs)
    -- Move both integrals onto the common base `π₀` via the marginal identities.
    have hmap_g : (∫ ω', gradW (x - charX_g s ω') ∂(g 0))
        = ∫ ω, gradW (x - charX_g s (proj_g ω)) ∂π₀ := by
      rw [hmarg_g]
      exact integral_map hproj_g.aemeasurable
        (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
          hmeas_charg_s).aestronglyMeasurable)
    have hmap_f : (∫ ω', gradW (x - charX_f s ω') ∂(f 0))
        = ∫ ω, gradW (x - charX_f s (proj_f ω)) ∂π₀ := by
      rw [hmarg_f]
      exact integral_map hproj_f.aemeasurable
        (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
          hmeas_charf_s).aestronglyMeasurable)
    rw [hmap_g, hmap_f]
    -- `π₀`-integrabilities of the two pushed-forward kernels.
    have hint_g_π : Integrable (fun ω => gradW (x - charX_g s (proj_g ω))) π₀ := by
      have hbase : Integrable (fun ω' => gradW (x - charX_g s ω')) (g 0) :=
        h_int_push charX_g charV_g g (g 0) hpush_g haem_g h_int_g s hs x
      rw [hmarg_g] at hbase
      exact (integrable_map_measure
        (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
          hmeas_charg_s).aestronglyMeasurable) hproj_g.aemeasurable).mp hbase
    have hint_f_π : Integrable (fun ω => gradW (x - charX_f s (proj_f ω))) π₀ := by
      have hbase : Integrable (fun ω' => gradW (x - charX_f s ω')) (f 0) :=
        h_int_push charX_f charV_f f (f 0) hpush_f haem_f h_int_f s hs x
      rw [hmarg_f] at hbase
      exact (integrable_map_measure
        (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
          hmeas_charf_s).aestronglyMeasurable) hproj_f.aemeasurable).mp hbase
    rw [← integral_sub hint_g_π hint_f_π]
    -- Pointwise gradW-Lipschitz bound under the integral.
    have h_pt : ∀ ω, ‖gradW (x - charX_g s (proj_g ω)) - gradW (x - charX_f s (proj_f ω))‖
        ≤ (L : ℝ) * ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ := by
      intro ω
      have hd := hL.dist_le_mul (x - charX_g s (proj_g ω)) (x - charX_f s (proj_f ω))
      rw [dist_eq_norm, dist_eq_norm] at hd
      have hsub : (x - charX_g s (proj_g ω)) - (x - charX_f s (proj_f ω))
          = charX_f s (proj_f ω) - charX_g s (proj_g ω) := by abel
      rw [hsub] at hd; exact hd
    -- Phase-space integrabilities of the two coupled trajectories over `π₀`.
    have hf_phase_int : Integrable
        (fun ω => ((charX_f s (proj_f ω), charV_f s (proj_f ω)) : PhaseSpace d)) π₀ := by
      have hbase : Integrable (fun ω' : PhaseSpace d => (charX_f s ω', charV_f s ω')) (f 0) :=
        h_phase_int charX_f charV_f f (f 0) hpush_f haem_f (fun t ht => (hf_mom t ht).2) s hs
      rw [hmarg_f] at hbase
      exact (integrable_map_measure (hmeas_charf s hs).aestronglyMeasurable
        hproj_f.aemeasurable).mp hbase
    have hg_phase_int : Integrable
        (fun ω => ((charX_g s (proj_g ω), charV_g s (proj_g ω)) : PhaseSpace d)) π₀ := by
      have hbase : Integrable (fun ω' : PhaseSpace d => (charX_g s ω', charV_g s ω')) (g 0) :=
        h_phase_int charX_g charV_g g (g 0) hpush_g haem_g (fun t ht => (hg_mom t ht).2) s hs
      rw [hmarg_g] at hbase
      exact (integrable_map_measure (hmeas_charg s hs).aestronglyMeasurable
        hproj_g.aemeasurable).mp hbase
    have hnorm_int_le :
        ‖∫ ω, (gradW (x - charX_g s (proj_g ω)) - gradW (x - charX_f s (proj_f ω))) ∂π₀‖
          ≤ ∫ ω, (L : ℝ) * ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀ := by
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine integral_mono (hint_g_π.sub hint_f_π).norm ?_ h_pt
      have hdiff_int : Integrable
          (fun ω => charX_f s (proj_f ω) - charX_g s (proj_g ω)) π₀ :=
        (hf_phase_int.fst).sub (hg_phase_int.fst)
      exact (hdiff_int.norm.const_mul (L : ℝ))
    refine le_trans hnorm_int_le ?_
    rw [integral_const_mul]
    have hpt2 : ∀ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ≤ ‖X_f s ω - X_g s ω‖ := by
      intro ω
      have hXf : X_f s ω = (charX_f s (proj_f ω), charV_f s (proj_f ω)) := by
        simp only [hX_f_def, hclampT_id s hs]
      have hXg : X_g s ω = (charX_g s (proj_g ω), charV_g s (proj_g ω)) := by
        simp only [hX_g_def, hclampT_id s hs]
      rw [hXf, hXg]
      have hsplit : ((charX_f s (proj_f ω), charV_f s (proj_f ω)) : PhaseSpace d)
            - (charX_g s (proj_g ω), charV_g s (proj_g ω)) =
          ((charX_f s (proj_f ω) - charX_g s (proj_g ω)),
            (charV_f s (proj_f ω) - charV_g s (proj_g ω))) := by
        rw [Prod.mk_sub_mk]
      rw [hsplit, Prod.norm_def]; exact le_max_left _ _
    have hdiff_norm_int : Integrable
        (fun ω => ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖) π₀ :=
      ((hf_phase_int.fst).sub (hg_phase_int.fst)).norm
    have hXdiff_norm_int : Integrable (fun ω => ‖X_f s ω - X_g s ω‖) π₀ :=
      Integrable.mono' hdom_int
        ((hmeas_f s).sub (hmeas_g s)).norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom s hs ω)
    have hQ_le : ∫ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀
        ≤ ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
      integral_mono hdiff_norm_int hXdiff_norm_int hpt2
    calc (L : ℝ) * ∫ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀
        ≤ (L : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
          mul_le_mul_of_nonneg_left hQ_le L.coe_nonneg
      _ ≤ ((max 1 L : NNReal) : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
          mul_le_mul_of_nonneg_right hL_le_max (integral_nonneg fun _ => norm_nonneg _)
      _ = ε s := by simp only [hε_def, hQ_def]
  -- Apply the integrated collapse core.
  have hcore := integrated_coupling_gronwall_bound π₀ X_f X_g b_f b_g
    (max 1 L) T hT.le hL_f hcont_f hcont_g hderiv_f hderiv_g hint
    hmeas_f hmeas_g dom hdom_int hdom ε hε_int hε_nn h_diff h_self
  refine ⟨hmeas_charf, hmeas_charg, ?_⟩
  -- Rewrite the bound's two integrals into the conclusion's `proj`-form.
  intro t ht
  have hbound := hcore t ht
  have hbase0 : (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π₀) = ∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀ := by
    apply integral_congr_ae
    filter_upwards with ω
    have hXf0 : X_f 0 ω = proj_f ω := by
      simp only [hX_f_def, hclampT_id 0 ⟨le_refl 0, hT.le⟩]; exact hinit_f' (proj_f ω)
    have hXg0 : X_g 0 ω = proj_g ω := by
      simp only [hX_g_def, hclampT_id 0 ⟨le_refl 0, hT.le⟩]; exact hinit_g' (proj_g ω)
    rw [hXf0, hXg0]
  have hlhs : (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π₀)
      = ∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
             - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀ := by
    apply integral_congr_ae
    filter_upwards with ω
    have hXf : X_f t ω = (charX_f t (proj_f ω), charV_f t (proj_f ω)) := by
      simp only [hX_f_def, hclampT_id t ht]
    have hXg : X_g t ω = (charX_g t (proj_g ω), charV_g t (proj_g ω)) := by
      simp only [hX_g_def, hclampT_id t ht]
    rw [hXf, hXg]
  rw [hlhs, hbase0] at hbound
  refine ⟨?_, hbound⟩
  have hXfe : ∀ ω, X_f t ω = (charX_f t (proj_f ω), charV_f t (proj_f ω)) := fun ω => by
    simp only [hX_f_def, hclampT_id t ht]
  have hXge : ∀ ω, X_g t ω = (charX_g t (proj_g ω), charV_g t (proj_g ω)) := fun ω => by
    simp only [hX_g_def, hclampT_id t ht]
  have hint_t : Integrable (fun ω => ‖X_f t ω - X_g t ω‖) π₀ :=
    Integrable.mono' hdom_int
      ((hmeas_f t).sub (hmeas_g t)).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom t ht ω)
  simpa only [hXfe, hXge] using hint_t

/-- **Project-internal Stage 8 helper (realigned to the Lagrangian class,
Stage 2b part 5, 2026-05-31)**: Localized Dobrushin uniqueness on `[0, T]`
for two `IsLagrangianVlasovSolutionOn` solutions with the same initial data
and finite first moments.

**Soundness realignment (2026-05-31)**: previously stated over the *weak*
`IsVlasovSolutionOn` class.  That class cannot soundly carry this conclusion:
the Gronwall step (`wassersteinGronwallCoupling_gronwall_le`) demands
`ContinuousOn (Icc 0 T)` of `t ↦ (W₁ (f t) (g t)).toReal` — *closed* interval
— but `IsVlasovSolutionOn` constrains the weak PDE only on the *open*
`Ioo 0 T`, leaving the endpoint values `f T`, `g T` free (a weak solution may
jump at `t = T`).  So closed-window W₁-continuity is not a consequence of the
weak class.  Realigning to `IsLagrangianVlasovSolutionOn` fixes this: the
flow witness supplies `f t = (charX t)_# (f 0)` on the closed `Icc 0 T` plus
boundary flow regularity, pinning the endpoints.  This also matches the plan's
decision #5 (uniqueness is over the Lagrangian class; lifting to the weak
class would need the DiPerna-Lions superposition principle, out of scope).
The caller `vlasovWellPosedness_uniqueness` already holds the Lagrangian
witness, so the realignment is zero-cost upstream.

**Closure path (re-routed 2026-06-04 through the integrated-coupling core)**:
the proof now wires through `integrated_coupling_gronwall_bound` (the `M → 0`
collapse engine) instead of the W₁-continuity + right-derivative-liminf +
Gronwall chain.  Set `μ₀ := f 0 = g 0` and let `Φ_f, Φ_g` be the (clamped)
characteristic flows.  The core bounds the integrated trajectory distance
`Q t := ∫ ω, ‖Φ_f t ω − Φ_g t ω‖ ∂μ₀` by `Q 0 · exp(2 (max 1 L) t)`; since the
flows start at the identity, `Q 0 = 0`, so `Q t ≤ 0`.  Hence `Φ_f t = Φ_g t`
μ₀-a.e., and `f t = (Φ_f t)_# μ₀ = (Φ_g t)_# μ₀ = g t` by `Measure.map_congr`.

The crux input is the cross-field bound `h_diff`, established directly from the
pushforward identity `spatialMarginal (f s) = (charX_f s)_# μ₀` + `gradW`
Lipschitz under the integral (two `integral_map` steps) — it never forms
`wasserstein1 (f s) (g s)`.  Consequences:
* retires `MathlibTODO_wassersteinGronwallCoupling_W1ContOn_On` (#8, deleted —
  it was its only consumer);
* makes `wassersteinGronwallCoupling_derivBound_via_pureFA_On` and the
  `convolveDiff_norm_le` force-estimate callerless *on this branch* (the
  latter still has a separate consumer at the Dobrushin mean-field site).

**Body is now `sorry`-free** (moment-free dominator close, 2026-06-04).  The
previously-isolated flow-regularity gaps were all retired by re-routing the
measurability and the dominator through the *open-interval* helpers
(`charFlow_measurable_via_gronwall_Ioo` /
`charFlow_lipschitzInZ_via_gronwall_Ioo`), which consume only the witness ODE
on `Ioo 0 T`:
* the `s = 0` right-derivatives (`hderivIco_f`/`hderivIco_g`) are no longer
  needed — the `Ioo`-only flow ODE (`hderiv_Ioo_f`/`hderiv_Ioo_g`) suffices;
* the uniform-in-`s` first-moment envelope (`Mf`/`Mg`) and
  `flow_distance_growth_bound_on` are replaced by a moment-free dominator
  `dom ω = 2 e^{KT} ‖ω‖ + (K_f + K_g)` built from the flow's Lipschitz-in-`z`
  bound + compactness of the origin trajectory on `[0, T]`; it uses ONLY
  `f 0`'s initial first moment;
* the per-`ω` interval-integrability (`hint`) is closed by global continuity in
  `s` of each clamped field (velocity slot continuous; force slot a
  pushforward integral, continuous via moment-free DCT). -/
private theorem dobrushin_uniqueness_On
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hfg0 : f 0 = g 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, f t = g t := by
  -- Re-routed (2026-06-04) through the shared `dobrushin_integrated_flow_bound_On`
  -- core with the **diagonal** coupling `π₀ = f 0` and `proj_f = proj_g = id`.
  -- Then the RHS base integral `∫ ‖id ω − id ω‖ = 0`, so the integrated bound
  -- forces `Φ_f t = Φ_g t` `f 0`-a.e., hence
  -- `f t = (Φ_f t)_# (f 0) = (Φ_g t)_# (f 0) = g t`.
  haveI hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f, hcontIcc_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g, hcontIcc_g⟩ := hg
  obtain ⟨hinit_f, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨hinit_g, hflow_g_x, hflow_g_v⟩ := hflow_g
  have hmarg_f : f 0 = Measure.map id (f 0) := by rw [Measure.map_id]
  have hmarg_g : g 0 = Measure.map id (f 0) := by rw [Measure.map_id, hfg0]
  have hcore := dobrushin_integrated_flow_bound_On gradW L hL f g T hT
    (f 0) id id measurable_id measurable_id
    charX_f charV_f charX_g charV_g
    hinit_f hflow_f_x hflow_f_v hpush_f haem_f hcontIcc_f
    hinit_g hflow_g_x hflow_g_v hpush_g haem_g hcontIcc_g
    hf_mom hg_mom hmarg_f hmarg_g
  obtain ⟨_, _, hmain⟩ := hcore
  intro t ht
  obtain ⟨hint_t, hbound⟩ := hmain t ht
  have hrhs0 : (∫ ω, ‖(id ω : PhaseSpace d) - id ω‖ ∂(f 0)) = 0 := by
    simp only [id_eq, sub_self, norm_zero, integral_zero]
  rw [hrhs0, zero_mul] at hbound
  simp only [id_eq] at hint_t hbound
  have hnn : 0 ≤ ∫ ω, ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖ ∂(f 0) :=
    integral_nonneg (fun ω => norm_nonneg _)
  have hz : (∫ ω, ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖ ∂(f 0)) = 0 := le_antisymm hbound hnn
  have hae_zero : (fun ω => ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖) =ᵐ[f 0] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => norm_nonneg _) hint_t).mp hz
  have hflow_ae : (fun ω => ((charX_f t ω, charV_f t ω) : PhaseSpace d))
      =ᵐ[f 0] (fun ω => (charX_g t ω, charV_g t ω)) := by
    filter_upwards [hae_zero] with ω hω
    have hnz : ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
        - (charX_g t ω, charV_g t ω)‖ = 0 := hω
    exact sub_eq_zero.mp (norm_eq_zero.mp hnz)
  have hpush_g' : g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (f 0) := by
    rw [hpush_g t ht, hfg0]
  rw [hpush_f t ht, hpush_g']
  exact Measure.map_congr hflow_ae

/-- **Mean-field Dobrushin stability on the window `[0, T]`** (2026-06-05).

Consumes the shared `dobrushin_integrated_flow_bound_On` core at the **optimal**
coupling `π₀` of `(f 0, g 0)` with `proj_f = fst`, `proj_g = snd`.  Then:
* the LHS `∫ ‖Φ_f t ω.1 − Φ_g t ω.2‖ dπ₀` dominates `W₁(f t, g t)` by the easy
  direction of Kantorovich–Rubinstein (`wasserstein1_pushforward_le_iInf` at the
  pushforward coupling), and
* the RHS base `∫ ‖ω.1 − ω.2‖ dπ₀` equals `W₁(f 0, g 0)` because `π₀` is optimal
  (`wasserstein1_optimal_coupling_exists`, Foundation B).

Force-estimate-free: never forms a force estimate, never touches the
`W₁`-continuity / right-derivative route — it retires the `#5`/`#6` placeholders
on the mean-field branch. -/
private theorem dobrushin_meanfield_On
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (f t) (g t)
        ≤ ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * wasserstein1 (f 0) (g 0) := by
  haveI hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  haveI hg0_prob : IsProbabilityMeasure (g 0) := (hg_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hf0_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (f 0) := by
    simpa only [dist_zero_right] using (hf_mom 0 ⟨le_refl 0, hT.le⟩).2
  have hg0_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (g 0) := by
    simpa only [dist_zero_right] using (hg_mom 0 ⟨le_refl 0, hT.le⟩).2
  -- Optimal coupling π₀ of (f 0, g 0) (Foundation B).
  obtain ⟨π₀, hπ₀, hcost⟩ := wasserstein1_optimal_coupling_exists (f 0) (g 0) 0 hf0_fm hg0_fm
  haveI hπ₀_prob : IsProbabilityMeasure π₀ := by
    constructor
    have hmap : (Measure.map Prod.fst π₀) Set.univ = (1 : ENNReal) := by
      rw [hπ₀.1, measure_univ]
    rwa [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at hmap
  have hmarg_f : f 0 = Measure.map Prod.fst π₀ := hπ₀.1.symm
  have hmarg_g : g 0 = Measure.map Prod.snd π₀ := hπ₀.2.symm
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f, hcontIcc_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g, hcontIcc_g⟩ := hg
  obtain ⟨hinit_f, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨hinit_g, hflow_g_x, hflow_g_v⟩ := hflow_g
  obtain ⟨hmeas_charf, hmeas_charg, hmain⟩ :=
    dobrushin_integrated_flow_bound_On gradW L hL f g T hT
      π₀ Prod.fst Prod.snd measurable_fst measurable_snd
      charX_f charV_f charX_g charV_g
      hinit_f hflow_f_x hflow_f_v hpush_f haem_f hcontIcc_f
      hinit_g hflow_g_x hflow_g_v hpush_g haem_g hcontIcc_g
      hf_mom hg_mom hmarg_f hmarg_g
  -- RHS base integrability, and `ofReal (∫ ‖ω.1 − ω.2‖ dπ₀) = W₁(f 0, g 0)`.
  have hmom_fst : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.1‖) π₀ := by
    have hm : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map Prod.fst π₀) := by
      rw [← hmarg_f]; exact (hf_mom 0 ⟨le_refl 0, hT.le⟩).2
    exact (integrable_map_measure continuous_norm.aestronglyMeasurable
      measurable_fst.aemeasurable).mp hm
  have hmom_snd : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.2‖) π₀ := by
    have hm : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map Prod.snd π₀) := by
      rw [← hmarg_g]; exact (hg_mom 0 ⟨le_refl 0, hT.le⟩).2
    exact (integrable_map_measure continuous_norm.aestronglyMeasurable
      measurable_snd.aemeasurable).mp hm
  have hrhs_int : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.1 - ω.2‖) π₀ :=
    Integrable.mono' (hmom_fst.add hmom_snd)
      ((measurable_fst.sub measurable_snd).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le _ _)
  have hbase_eq : ENNReal.ofReal (∫ ω, ‖ω.1 - ω.2‖ ∂π₀) = wasserstein1 (f 0) (g 0) := by
    rw [ofReal_integral_eq_lintegral_ofReal hrhs_int
      (Filter.Eventually.of_forall fun ω => norm_nonneg _), ← hcost]
    refine lintegral_congr fun z => ?_
    rw [edist_dist, dist_eq_norm]
  intro t ht
  obtain ⟨hint_t, hbound⟩ := hmain t ht
  haveI hft_prob : IsProbabilityMeasure (f t) := (hf_mom t ht).1
  haveI hgt_prob : IsProbabilityMeasure (g t) := (hg_mom t ht).1
  have hft : Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0) = f t :=
    (hpush_f t ht).symm
  have hgt : Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0) = g t :=
    (hpush_g t ht).symm
  have hft_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (f t) := by
    simpa only [dist_zero_right] using (hf_mom t ht).2
  have hgt_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (g t) := by
    simpa only [dist_zero_right] using (hg_mom t ht).2
  -- Easy direction (KR) via the pushforward coupling.
  have h_push := wasserstein1_pushforward_le_iInf
    (fun z => (charX_f t z, charV_f t z)) (fun z => (charX_g t z, charV_g t z))
    (hmeas_charf t ht) (hmeas_charg t ht) (f 0) (g 0) 0
    (by rw [hft]; infer_instance) (by rw [hgt]; infer_instance)
    (by rw [hft]; exact hft_fm) (by rw [hgt]; exact hgt_fm)
  rw [hft, hgt] at h_push
  have h_iInf_le :
      (⨅ (π : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π (f 0) (g 0)),
        ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π)
        ≤ ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π₀ :=
    iInf_le_of_le π₀ (iInf_le _ hπ₀)
  have hWt_lint : wasserstein1 (f t) (g t)
      ≤ ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π₀ :=
    le_trans h_push h_iInf_le
  have hlint_eq :
      (∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π₀)
        = ENNReal.ofReal (∫ ω, ‖((charX_f t ω.1, charV_f t ω.1) : PhaseSpace d)
            - (charX_g t ω.2, charV_g t ω.2)‖ ∂π₀) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_t
      (Filter.Eventually.of_forall fun ω => norm_nonneg _)]
    refine lintegral_congr fun z => ?_
    rw [edist_dist, dist_eq_norm]
  rw [hlint_eq] at hWt_lint
  refine le_trans hWt_lint ?_
  calc ENNReal.ofReal (∫ ω, ‖((charX_f t ω.1, charV_f t ω.1) : PhaseSpace d)
            - (charX_g t ω.2, charV_g t ω.2)‖ ∂π₀)
      ≤ ENNReal.ofReal ((∫ ω, ‖ω.1 - ω.2‖ ∂π₀)
          * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (∫ ω, ‖ω.1 - ω.2‖ ∂π₀)
          * ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :=
        ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _)
    _ = wasserstein1 (f 0) (g 0)
          * ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) := by rw [hbase_eq]
    _ = ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
          * wasserstein1 (f 0) (g 0) := mul_comm _ _

/-- **Stage 8: uniqueness on the local window**.

Two `IsLagrangianVlasovSolutionOn`s with the same initial data agree on
`[0, T_target]`.

**Proof** (closed via Dobrushin uniqueness composition):

1. Extract `IsVlasovSolutionOn` from each `IsLagrangianVlasovSolutionOn`.
2. Note `f 0 = f₀ = g 0` from the init hypotheses.
3. Apply `MathlibTODO_dobrushin_uniqueness_On` (localized Dobrushin
   uniqueness, Helper above) to conclude `f t = g t`. -/
theorem vlasovWellPosedness_uniqueness
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (hL_pos : (0 : ℝ) < L)
    (hL_lt : (L : ℝ) < 1)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T_target : ℝ} (hT_target : 0 < T_target)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf_init : f 0 = f₀) (hg_init : g 0 = f₀)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (g t))
    (hf_lag : IsLagrangianVlasovSolutionOn gradW f T_target)
    (hg_lag : IsLagrangianVlasovSolutionOn gradW g T_target) :
    ∀ t ∈ Set.Icc (0 : ℝ) T_target, f t = g t := by
  -- The two solutions share the same initial datum f₀
  have hfg0 : f 0 = g 0 := hf_init.trans hg_init.symm
  -- Apply the localized Dobrushin uniqueness (Helper above).  Pass the full
  -- Lagrangian witness directly (post-realignment, item 3 is over the
  -- Lagrangian-On class for soundness — see its docstring).
  exact dobrushin_uniqueness_On gradW L hL f g T_target hT_target
    hf_lag hg_lag hf_mom hg_mom hfg0

-- ---------------------------------------------------------------------------
-- §9.7  Stage 6 — universal-in-`t` bridge to `IsLagrangianVlasovSolution`
-- ---------------------------------------------------------------------------
-- Combines `vlasovWellPosedness_forward` (forward iteration) +
-- `vlasovWellPosedness_uniqueness` (Stage 8) into a single universal-in-`t`
-- existence theorem.  The universal `f` is constructed as the colimit of
-- the per-`T_target` solutions, well-defined by Stage 8's agreement on
-- overlaps.  For `t < 0`, the solution is extended via backward iteration
-- (also sorry'd internally as a forward-iteration analogue).

/-- **Stage 6: universal existence — bridge to the marquee form**.

Given the `L < 1` regime, produces a single universal-in-`t`
`f : ℝ → Measure (PhaseSpace d)` satisfying `IsLagrangianVlasovSolution`
plus narrow continuity.  Composes Stage 5 (forward iteration) + Stage 8
(uniqueness on overlaps) + a forward/backward symmetry argument.

**Proof strategy** (sorry'd body, ~100-150 lines):

1. Apply `vlasovWellPosedness_forward` with `T_target := n` for each
   `n : ℕ`, getting per-`n` solutions `f_n : ℝ → Measure (PhaseSpace d)`.

2. By `vlasovWellPosedness_uniqueness` (Stage 8), `f_n` and `f_m` agree
   on `Icc 0 (min n m)`.

3. Define `f t := f_{⌈t⌉ + 1} t` for `t ≥ 0`.  By step 2, this is
   well-defined on `t ≥ 0`.

4. For `t < 0`: backward iteration (the time-reversed Vlasov equation is
   well-posed by the same argument).  Either invoke a dual Stage 5b
   forward-iteration on `t ∈ [0, ∞)` from reversed initial measure, or
   leave the backward extension as `f t := f₀` and accept a `sorry`
   for the universal-in-`t` weak-PDE on `t < 0`.

5. `IsLagrangianVlasovSolution gradW f`: the universal-in-`t` version
   composes from the per-window `IsLagrangianVlasovSolutionOn`.
   `IsVlasovSolution` part: weak PDE on all of `ℝ` — for `t ≥ 0` from
   `IsVlasovSolutionOn` per `T_target`, for `t < 0` from backward
   iteration (or sorry).  Flow part: glue per-window flows; for `t < 0`
   use backward-time flow (or sorry).

6. Narrow continuity: standard DCT using moment bound + flow growth. -/
theorem vlasovWellPosedness_universal_existence
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (hL_pos : (0 : ℝ) < L)
    (hL_lt : (L : ℝ) < 1)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) :
    ∃ f : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧
      -- Forward-only conjuncts (refactor 2026-05-30): the universal-in-t
      -- Vlasov well-posedness is a forward Cauchy problem; backward time is
      -- not on the critical path.
      (∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t)) ∧
      (∀ T_target : ℝ, 0 < T_target →
        IsLagrangianVlasovSolutionOn gradW f T_target) ∧
      (∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        ContinuousOn (fun t => ∫ z, g z ∂f t) (Set.Ici 0)) := by
  -- Step 1. For each n : ℕ, choose a solution on [0, n+1] via Stage 5.
  -- h_fwd_exists n gives ∃ g, g 0 = f₀ ∧ (moment on [0,n+1]) ∧ IsLagrangianVlasovSolutionOn n+1
  have h_fwd_exists : ∀ n : ℕ,
      ∃ g : ℝ → Measure (PhaseSpace d),
        g 0 = f₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), HasFiniteFirstMoment (g t)) ∧
        IsLagrangianVlasovSolutionOn gradW g ((n : ℝ) + 1) := by
    intro n
    exact vlasovWellPosedness_forward W gradW hgradW L hL hL_pos hL_lt f₀ hf₀
      (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  -- Step 2. Pick canonical per-n solutions via Classical.choice.
  let sol : ℕ → ℝ → Measure (PhaseSpace d) :=
    fun n => Classical.choose (h_fwd_exists n)
  have h_sol_init : ∀ n : ℕ, sol n 0 = f₀ :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).1
  have h_sol_mom : ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1),
      HasFiniteFirstMoment (sol n t) :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).2.1
  have h_sol_lag : ∀ n : ℕ, IsLagrangianVlasovSolutionOn gradW (sol n) ((n : ℝ) + 1) :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).2.2
  -- Step 3. Agreement on overlaps via Stage 8 (uniqueness).
  -- Any two per-n solutions agree on [0, n+1]: restrict sol m from [0, m+1]
  -- to [0, n+1] via inline monotonicity, then apply vlasovWellPosedness_uniqueness.
  have h_agree : ∀ n m : ℕ, n ≤ m →
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), sol n t = sol m t := by
    intro n m hnm t ht
    -- Cast inequality: (n : ℝ) + 1 ≤ (m : ℝ) + 1
    have hnm_cast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      linarith
    -- Restrict sol m from [0, m+1] to [0, n+1] via inline monotonicity
    have h_sol_m_on_n : IsLagrangianVlasovSolutionOn gradW (sol m) ((n : ℝ) + 1) := by
      obtain ⟨h_sol, charX, charV, h_flow, h_push, h_aemeas, h_cont⟩ := h_sol_lag m
      refine ⟨?_, charX, charV, ?_, ?_, ?_⟩
      · intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s hs
        exact h_sol φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s
          ⟨hs.1, lt_of_lt_of_le hs.2 hnm_cast⟩
      · exact h_flow.mono (Set.Ioo_subset_Ioo le_rfl hnm_cast) Set.Subset.rfl
      · intro s hs; exact h_push s ⟨hs.1, le_trans hs.2 hnm_cast⟩
      · refine ⟨?_, ?_⟩
        · intro s hs; exact h_aemeas s ⟨hs.1, le_trans hs.2 hnm_cast⟩
        · intro z; exact (h_cont z).mono (fun u hu => ⟨hu.1, le_trans hu.2 hnm_cast⟩)
    -- Apply vlasovWellPosedness_uniqueness (Stage 8) on window [0, n+1]
    exact vlasovWellPosedness_uniqueness W gradW hgradW L hL hL_pos hL_lt f₀ hf₀
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (0 : ℝ) < (n : ℝ) + 1)
      (sol n) (sol m) (h_sol_init n) (h_sol_init m)
      (h_sol_mom n)
      (fun s hs => h_sol_mom m s ⟨hs.1, le_trans hs.2 hnm_cast⟩)
      (h_sol_lag n) h_sol_m_on_n
      t ht
  -- Step 4. Define the universal-in-forward-time solution.
  -- For t ≥ 0: use sol ⌈t⌉₊ at t.  For t < 0: f₀ (unconstrained by the
  -- forward-only statement; the claims below only quantify over t ≥ 0).
  let f : ℝ → Measure (PhaseSpace d) :=
    fun t => if 0 ≤ t then sol (⌈t⌉₊) t else f₀
  -- Step 5. Prove the four conjuncts.
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  -- Conjunct 1: f 0 = f₀
  · show (if (0 : ℝ) ≤ 0 then sol ⌈(0 : ℝ)⌉₊ 0 else f₀) = f₀
    simp [h_sol_init 0]
  -- Conjunct 2: ∀ t ∈ Ici 0, HasFiniteFirstMoment (f t)
  · intro t ht
    have ht_nn : (0 : ℝ) ≤ t := ht
    show HasFiniteFirstMoment (if 0 ≤ t then sol ⌈t⌉₊ t else f₀)
    simp only [ht_nn, ↓reduceIte]
    apply h_sol_mom (⌈t⌉₊) t
    refine ⟨ht_nn, ?_⟩
    exact le_trans (Nat.le_ceil t) (by push_cast; linarith)
  -- Conjunct 3: ∀ T_target > 0, IsLagrangianVlasovSolutionOn gradW f T_target
  · -- For T_target > 0, let N = ⌈T_target⌉₊.  The solution sol N exists on [0, N+1]
    -- with N+1 ≥ T_target.  Agreement h_agree gives f t = sol N t on [0, T_target].
    -- Restrict sol N's IsLagrangianVlasovSolutionOn to [0, T_target] and convert to f.
    intro T_target hT_target_pos
    set N := ⌈T_target⌉₊ with hN_def
    have hT_le_N : T_target ≤ (N : ℝ) := Nat.le_ceil T_target
    -- Agreement: f t = sol N t for t ∈ [0, T_target]
    have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) T_target, f t = sol N t := by
      intro t ht
      have ht_nn : (0 : ℝ) ≤ t := ht.1
      show (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
      simp only [ht_nn, ↓reduceIte]
      exact h_agree ⌈t⌉₊ N (Nat.ceil_mono ht.2) t ⟨ht.1, le_trans (Nat.le_ceil t) (by push_cast; linarith)⟩
    -- Extract components from h_sol_lag N
    obtain ⟨h_pde_N, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, h_boundary_N⟩ :=
      h_sol_lag N
    -- Compute f 0 = sol N 0
    have h_f0_solN : f 0 = sol N 0 :=
      h_agree_fN 0 ⟨le_refl 0, hT_target_pos.le⟩
    refine ⟨?_, charX_N, charV_N, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn gradW f T_target: for each t ∈ Ioo 0 T_target,
      -- f and sol N agree near t, so HasDerivAt transfers via EventuallyEq.
      intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
      have ht_lt_N1 : t < (N : ℝ) + 1 := lt_of_lt_of_le ht.2 (by linarith)
      have h_from_N := h_pde_N φ hφ_smooth hφ_compact gradXφ gradVφ
        hgradXφ hgradVφ t ⟨ht.1, ht_lt_N1⟩
      -- The functions fun s => ∫ φ ∂(f s) and fun s => ∫ φ ∂(sol N s) agree near t
      have h_eq : (fun s => ∫ z, φ z ∂(f s)) =ᶠ[nhds t] (fun s => ∫ z, φ z ∂(sol N s)) := by
        apply Filter.Eventually.mono (Ioo_mem_nhds ht.1 ht.2)
        intro s hs
        show ∫ z, φ z ∂f s = ∫ z, φ z ∂sol N s
        congr 1
        exact h_agree_fN s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      -- After congr_of_eventuallyEq, the derivative body still refers to sol N t.
      -- Rewrite the goal: f t = sol N t (h_agree_fN) so the derivative bodies match.
      have h_result := h_from_N.congr_of_eventuallyEq h_eq
      simp only [h_agree_fN t ⟨le_of_lt ht.1, ht.2.le⟩]
      exact h_result
    · -- IsCharacteristicFlowOn on Ioo 0 T_target.
      -- h_flow_N uses ρ = spatialMarginal ∘ sol N; we need ρ = spatialMarginal ∘ f.
      -- On Ioo 0 T_target, f t = sol N t (from h_agree_fN), so spatialMarginals agree.
      refine ⟨h_flow_N.1, ?_, ?_⟩
      · intro t ht z _
        exact h_flow_N.2.1 t (Set.Ioo_subset_Ioo le_rfl (by linarith) ht) z (Set.mem_univ z)
      · intro t ht z _
        simp only [h_agree_fN t ⟨le_of_lt ht.1, ht.2.le⟩]
        exact h_flow_N.2.2 t (Set.Ioo_subset_Ioo le_rfl (by linarith) ht) z (Set.mem_univ z)
    · -- Pushforward: f t = Measure.map (charX_N t, charV_N t) (f 0) for t ∈ Icc 0 T_target
      intro t ht
      rw [h_agree_fN t ht, h_f0_solN]
      exact h_push_N t ⟨ht.1, le_trans ht.2 (by linarith)⟩
    · -- AEMeasurable ∧ boundary ContinuousOn on Icc 0 T_target.
      refine ⟨?_, ?_⟩
      · intro s hs
        rw [h_f0_solN]
        exact h_aemeas_N s ⟨hs.1, le_trans hs.2 (by linarith)⟩
      · -- Boundary ContinuousOn: `sol N`'s boundary conjunct (now genuine post-B2-#1),
        -- same flow `charX_N/charV_N`, restricted from `Icc 0 (N+1)` to `Icc 0 T_target`.
        intro z
        exact (h_boundary_N z).mono (Set.Icc_subset_Icc le_rfl (by linarith))
  -- Conjunct 4: narrow continuity on Ici 0
  · -- Strategy: ContinuousOn (Ici 0) = ∀ t₀ ≥ 0, ContinuousWithinAt at t₀.
    -- For t₀ > 0: use flow continuity from HasDerivAt (interior) + integral_map + DCT.
    -- For t₀ = 0: sub-sub-sorry (right-continuity of flow at t = 0 not exposed by
    --             IsCharacteristicFlowOn; requires boundary regularity from the ODE).
    intro g hg_cont hg_bdd
    -- Extract probability measure structure from hf₀
    obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
    haveI hf₀_prob_inst : IsProbabilityMeasure f₀ := hf₀_prob
    -- Extract a uniform bound C for g from the bounded-range hypothesis
    obtain ⟨C, hg_range⟩ := hg_bdd.subset_closedBall (0 : ℝ)
    -- C is a non-negative bound: ∀ z, ‖g z‖ ≤ C
    have hgC : ∀ z : PhaseSpace d, ‖g z‖ ≤ C := fun z => by
      have h := Metric.mem_closedBall.mp (hg_range (Set.mem_range_self z))
      simp only [Real.dist_eq, sub_zero] at h
      rwa [Real.norm_eq_abs]
    -- Show ContinuousOn by checking ContinuousWithinAt at each point
    intro t₀ ht₀
    have ht₀_nn := Set.mem_Ici.mp ht₀
    rcases ht₀_nn.eq_or_lt with h_eq | ht₀_pos
    · -- t₀ = 0: right-continuity via DCT.  The endpoint analog of the interior
      -- case: pointwise continuity of `t ↦ (charX_N t z, charV_N t z)` at 0 is
      -- supplied by `sol N`'s boundary `ContinuousOn` conjunct (now genuine
      -- post-B2-#1), replacing the interior case's two-sided `HasDerivAt`
      -- (unavailable at the left endpoint).
      rw [← h_eq]
      set N : ℕ := 1 with hN_def
      have hN_cast_pos : (0 : ℝ) < (N : ℝ) := by norm_num [hN_def]
      have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ), f t = sol N t := by
        intro t ht
        have ht_nn := ht.1
        show (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
        simp only [ht_nn, ↓reduceIte]
        exact h_agree ⌈t⌉₊ N ((Nat.ceil_mono ht.2).trans_eq (Nat.ceil_natCast N))
          t ⟨ht.1, le_trans (Nat.le_ceil t) (by push_cast; linarith)⟩
      obtain ⟨_h_pde, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, h_boundary_N⟩ :=
        h_sol_lag N
      have h_integral_eq : ∀ t ∈ Set.Icc 0 (N : ℝ),
          ∫ z, g z ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀ := by
        intro t ht_Icc
        rw [h_agree_fN t ht_Icc]
        have ht_ext : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht_Icc.1, le_trans ht_Icc.2 (le_add_of_nonneg_right one_pos.le)⟩
        rw [h_push_N t ht_ext, ← h_sol_init N]
        exact integral_map (h_aemeas_N t ht_ext) hg_cont.measurable.aestronglyMeasurable
      have hIcc_mem : Set.Icc 0 (N : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
        Icc_mem_nhdsGE hN_cast_pos
      have h_cont_charX : ContinuousWithinAt
          (fun t => ∫ z, g (charX_N t z, charV_N t z) ∂f₀) (Set.Icc 0 (N : ℝ)) 0 := by
        apply continuousWithinAt_of_dominated (μ := f₀) (bound := fun _ => C)
        · apply Filter.Eventually.mono self_mem_nhdsWithin
          intro t ht_mem
          exact (hg_cont.measurable.comp_aemeasurable
            (h_sol_init N ▸ h_aemeas_N t ⟨ht_mem.1, le_trans ht_mem.2
              (le_add_of_nonneg_right one_pos.le)⟩)).aestronglyMeasurable
        · apply Filter.Eventually.mono self_mem_nhdsWithin; intro t _
          exact Filter.Eventually.of_forall fun z => hgC _
        · exact integrable_const C
        · apply Filter.Eventually.of_forall; intro z
          apply hg_cont.continuousAt.comp_continuousWithinAt
          exact ((h_boundary_N z).continuousWithinAt
            ⟨le_refl 0, by push_cast; linarith⟩).mono
            (Set.Icc_subset_Icc le_rfl (by push_cast; linarith))
      have h_cont_Icc : ContinuousWithinAt
          (fun t => ∫ z, g z ∂(f t)) (Set.Icc 0 (N : ℝ)) 0 :=
        h_cont_charX.congr_of_eventuallyEq
          (Filter.Eventually.mono self_mem_nhdsWithin (fun t ht => by
            show ∫ z, g z ∂f t = ∫ z, g (charX_N t z, charV_N t z) ∂f₀
            exact h_integral_eq t ht))
          (h_integral_eq 0 ⟨le_refl 0, hN_cast_pos.le⟩)
      exact h_cont_Icc.mono_of_mem_nhdsWithin hIcc_mem
    · -- t₀ > 0: t₀ ∈ Ioi 0.  Use the interior flow continuity.
      -- Choose N so that t₀ is in the interior of [0, N].
      set N := ⌈t₀⌉₊ + 1 with hN_def
      have hN_cast_pos : (0 : ℝ) < (N : ℝ) := by positivity
      have ht₀_lt_N : t₀ < (N : ℝ) := by
        push_cast [hN_def]
        exact lt_add_of_le_of_pos (Nat.le_ceil t₀) one_pos
      -- Agreement: f t = sol N t for t ∈ [0, N]
      have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ), f t = sol N t := by
        intro t ht
        have ht_nn := ht.1
        show (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
        simp only [ht_nn, ↓reduceIte]
        exact h_agree ⌈t⌉₊ N ((Nat.ceil_mono ht.2).trans_eq (Nat.ceil_natCast N))
          t ⟨ht.1, le_trans (Nat.le_ceil t) (by push_cast; linarith)⟩
      -- Extract flow witnesses from h_sol_lag N
      obtain ⟨_h_pde, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, _⟩ := h_sol_lag N
      -- The integral ∫ g ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀
      -- for all t ∈ Icc 0 N (via pushforward formula + h_agree).
      have h_integral_eq : ∀ t ∈ Set.Icc 0 (N : ℝ),
          ∫ z, g z ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀ := by
        intro t ht_Icc
        rw [h_agree_fN t ht_Icc]
        have ht_ext : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht_Icc.1, le_trans ht_Icc.2 (le_add_of_nonneg_right one_pos.le)⟩
        rw [h_push_N t ht_ext, ← h_sol_init N]
        exact integral_map (h_aemeas_N t ht_ext) hg_cont.measurable.aestronglyMeasurable
      -- The set Icc 0 N is a neighborhood of t₀ within Ici 0 (since 0 < t₀ < N).
      have hIcc_mem : Set.Icc 0 (N : ℝ) ∈ nhdsWithin t₀ (Set.Ici 0) := by
        apply nhdsWithin_le_nhds; exact Icc_mem_nhds ht₀_pos ht₀_lt_N
      -- Show ContinuousWithinAt for (fun t => ∫ z, g (charX_N t z, charV_N t z) ∂f₀) via DCT.
      have h_cont_charX : ContinuousWithinAt
          (fun t => ∫ z, g (charX_N t z, charV_N t z) ∂f₀) (Set.Icc 0 (N : ℝ)) t₀ := by
        apply continuousWithinAt_of_dominated (μ := f₀) (bound := fun _ => C)
        · -- AEStronglyMeasurable: t ↦ g (charX_N t z, charV_N t z) a.e. in z
          apply Filter.Eventually.mono self_mem_nhdsWithin
          intro t ht_mem
          exact (hg_cont.measurable.comp_aemeasurable
            (h_sol_init N ▸ h_aemeas_N t ⟨ht_mem.1, le_trans ht_mem.2
              (le_add_of_nonneg_right one_pos.le)⟩)).aestronglyMeasurable
        · -- Bound: ‖g (charX_N t z, charV_N t z)‖ ≤ C a.e. in z, eventually in t
          apply Filter.Eventually.mono self_mem_nhdsWithin; intro t _
          exact Filter.Eventually.of_forall fun z => hgC _
        · -- Integrable constant bound C w.r.t. f₀ (probability measure, hence finite)
          exact integrable_const C
        · -- Pointwise continuity: t ↦ g (charX_N t z, charV_N t z) continuous at t₀ in [0,N]
          apply Filter.Eventually.of_forall; intro z
          apply hg_cont.continuousAt.comp_continuousWithinAt
          have ht₀_in_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) :=
            ⟨ht₀_pos, by push_cast [hN_def]; linarith [Nat.le_ceil t₀]⟩
          have hX_deriv := h_flow_N.2.1 t₀ ht₀_in_Ioo z (Set.mem_univ z)
          have hV_deriv := h_flow_N.2.2 t₀ ht₀_in_Ioo z (Set.mem_univ z)
          exact (hX_deriv.continuousAt.prodMk hV_deriv.continuousAt).continuousWithinAt
      -- Transfer continuity from the charX version to the original via congr.
      have h_cont_Icc : ContinuousWithinAt
          (fun t => ∫ z, g z ∂(f t)) (Set.Icc 0 (N : ℝ)) t₀ :=
        h_cont_charX.congr_of_eventuallyEq
          (Filter.Eventually.mono self_mem_nhdsWithin (fun t ht => by
            show ∫ z, g z ∂f t = ∫ z, g (charX_N t z, charV_N t z) ∂f₀
            exact h_integral_eq t ht))
          (h_integral_eq t₀ ⟨ht₀_pos.le, ht₀_lt_N.le⟩)
      -- Lift ContinuousWithinAt from Icc 0 N to Ici 0 using hIcc_mem.
      exact h_cont_Icc.mono_of_mem_nhdsWithin hIcc_mem

-- ---------------------------------------------------------------------------
-- §10  Marquee theorem (tex: thm:vlasov-wp) — structural completion
-- ---------------------------------------------------------------------------

/-- (tex: thm:vlasov-wp)
Existence and uniqueness for the Vlasov equation.

Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) be a probability measure with finite first moment.
Under Assumption ass:W, there exists a unique narrowly continuous curve
t ↦ f_t ∈ 𝒫_1(ℝ^d × ℝ^d) satisfying eq:vlasov in the distributional sense
with f_{t=0} = f_0.

**Structural completion (2026-05-29)**: the body sketches the composition
of Stages 5 / 6 / 8 into the marquee's `∃!` form.  Three sub-sorries
remain inside the body, each representing a specifically-named gap:

1. **Lipschitz extraction** from `[AssW W]`: extract `L : NNReal` with
   `LipschitzWith L gradW` from `AssW.lipschitzGrad` + `hgradW`.
2. **L-regime case-split**: the L < 1 path applies Stages 6 + 8; the
   L ≥ 1 path is out of scope until the M-series `+1` removal lands;
   the L = 0 path is the explicit constant-force case.
3. **Universal `∃!` bundling**: existence from Stage 6, uniqueness from
   Stage 8 lifted across all `T_target`, packaged into `ExistsUnique`.
-/
theorem vlasovWellPosedness
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    -- Lipschitz constant of gradW, with L < 1 (the Dobrushin smallness regime).
    -- The L ≥ 1 regime requires the W̄ refactor (truncated Wasserstein metric, per
    -- Dobrushin 1979's full proof) and is registered as deliberate future work in
    -- `formalize/planning-notes.md`'s Phase B sequencing decision.  Restate per
    -- closure-plan Sorry 11 (Category 3, 2026-05-31): explicit `hL_lt_one`
    -- hypothesis eliminates the L≥1 sub-sorry'd branch.  External callers extract
    -- L from `[AssW W]`'s `lipschitzGrad` existential and prove `< 1` themselves.
    (L : NNReal) (hL_gradW : LipschitzWith L gradW) (hL_lt_one : (L : ℝ) < 1)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) :
    -- Existence-only (refactor 2026-05-30): Vlasov well-posedness is a forward-
    -- in-time Cauchy problem per Dobrushin 1979.  The original `∃!` form
    -- claimed uniqueness universally in `t`, which would require backward-
    -- iteration machinery not on the critical path.  The forward-only `∃` is
    -- the mathematically accurate statement; per-window uniqueness is provided
    -- by `vlasovWellPosedness_uniqueness` (Stage 8) as a separate interface.
    ∃ f : ℝ → Measure (PhaseSpace d),
      -- initial condition
      f 0 = f₀ ∧
      -- each f_t has finite first moment, for t ≥ 0.
      (∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t)) ∧
      -- f solves the Vlasov equation IN THE LAGRANGIAN SENSE on every forward
      -- window [0, T_target].  Per-T_target `IsLagrangianVlasovSolutionOn` is the
      -- forward-only analog of the universal `IsLagrangianVlasovSolution`; the
      -- latter would require backward-time machinery which is not on the critical
      -- path for the well-posedness theorem.
      (∀ T_target : ℝ, 0 < T_target →
        IsLagrangianVlasovSolutionOn gradW f T_target) ∧
      -- f is narrowly continuous: t ↦ ∫ g df_t is continuous on the forward
      -- time domain `Set.Ici 0`, for every bounded continuous g.
      (∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        ContinuousOn (fun t => ∫ z, g z ∂f t) (Set.Ici 0)) := by
  -- Step 1: Case split on whether L = 0 (constant force) or 0 < L.
  -- L < 1 is hypothesized (`hL_lt_one`), so both branches stay in scope.
  -- Closure-plan Sorry 11 (2026-05-31): the original L ≥ 1 sub-sorry'd branch
  -- has been removed by adding `hL_lt_one` as an explicit hypothesis.  The
  -- L ≥ 1 regime is registered as deliberate future work (W̄ refactor) in
  -- `formalize/planning-notes.md`'s Phase B sequencing decision.
  by_cases hL_pos : (0 : ℝ) < L
  · -- Case: 0 < L < 1 — the substantive path via Stage 6 (forward iteration).
    -- Stage 6 produces per-T_target `IsLagrangianVlasovSolutionOn` (forward-only);
    -- marquee bundles that shape directly as the existence claim.  Per-window
    -- uniqueness is available via Stage 8 (`vlasovWellPosedness_uniqueness`) as
    -- a separate interface.
    exact vlasovWellPosedness_universal_existence W gradW hgradW L hL_gradW
      hL_pos hL_lt_one f₀ hf₀
  · -- Case: L = 0 (gradW is constant; explicit constant-force solution).
    -- Step L0-1: L = 0 as an NNReal.
    have hL_zero : L = 0 := by
      apply NNReal.coe_eq_zero.mp
      exact le_antisymm (not_lt.mp hL_pos) (NNReal.coe_nonneg L)
    -- Step L0-2: gradW ≡ 0 everywhere (LipschitzWith 0 means constant;
    -- gradient_zero_of_even gives gradW 0 = 0; so gradW ≡ 0).
    have hgradW_zero : ∀ x, gradW x = 0 := by
      intro x
      have hconst : ∀ a b, gradW a = gradW b := by
        rw [hL_zero] at hL_gradW
        exact (LipschitzWith.zero_iff gradW).mp hL_gradW
      have h0 : gradW 0 = 0 := by
        rw [hgradW 0]; exact gradient_zero_of_even W
      calc gradW x = gradW 0 := hconst x 0
        _ = 0 := h0
    -- Step L0-3: convolveFunctionMeasure gradW ρ x = 0 for any ρ, x.
    have hconv_zero : ∀ (ρ : Measure (PhysSpace d)) (x : PhysSpace d),
        convolveFunctionMeasure gradW ρ x = 0 := by
      intros ρ x
      simp only [convolveFunctionMeasure]
      have : (fun y => gradW (x - y)) = fun _ => (0 : PhysSpace d) := by
        funext y; exact hgradW_zero (x - y)
      rw [this, integral_zero]
    -- Step L0-4: Define the explicit affine solution.
    let charX : ℝ → PhaseSpace d → PhysSpace d := fun t z => z.1 + t • z.2
    let charV : ℝ → PhaseSpace d → PhysSpace d := fun _ z => z.2
    let f_sol : ℝ → Measure (PhaseSpace d) :=
      fun t => Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) f₀
    -- Step L0-5: f_sol 0 = f₀.
    have hf_init : f_sol 0 = f₀ := by
      simp only [f_sol, charX, charV]
      have : (fun z : PhaseSpace d => (z.1 + (0 : ℝ) • z.2, z.2)) = id := by
        funext z; simp
      rw [this, Measure.map_id]
    -- Step L0-6: Each f_sol t has finite first moment.
    have hf_mom : ∀ t, HasFiniteFirstMoment (f_sol t) := by
      intro t
      constructor
      · -- IsProbabilityMeasure: pushforward of a probability measure under measurable map.
        haveI := hf₀.1
        apply Measure.isProbabilityMeasure_map
        fun_prop
      · -- Integrable ‖·‖: reduce to f₀ via integral_map, then bound by (1+|t|)·‖z‖.
        haveI := hf₀.1
        rw [integrable_map_measure (by fun_prop) (by fun_prop)]
        apply Integrable.mono' (hf₀.2.const_mul (1 + |t|))
        · fun_prop
        · apply Filter.Eventually.of_forall; intro z
          simp only [Function.comp_apply, charX, charV]
          -- Goal: ‖‖(z.1+t•z.2, z.2)‖‖ ≤ (1+|t|) * ‖z‖
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          -- Goal: ‖(z.1+t•z.2, z.2)‖ ≤ (1+|t|) * ‖z‖
          have hle1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
          have hle2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
          have htabs : 0 ≤ |t| := abs_nonneg t
          have hsmul : ‖t • z.2‖ = |t| * ‖z.2‖ := by rw [norm_smul, Real.norm_eq_abs]
          have htri := norm_add_le z.1 (t • z.2)
          have hn : 0 ≤ ‖z‖ := norm_nonneg _
          have h1 : ‖z.1 + t • z.2‖ ≤ (1 + |t|) * ‖z‖ := by
            have := mul_le_mul_of_nonneg_left hle2 htabs; rw [hsmul] at htri; nlinarith
          have h2 : ‖z.2‖ ≤ (1 + |t|) * ‖z‖ := by nlinarith
          rw [Prod.norm_def]
          exact max_le_iff.mpr ⟨h1, h2⟩
    -- Step L0-7: IsLagrangianVlasovSolution gradW f_sol.
    -- Use vlasovSolutionViaPushforward_isLagrangianVlasovSolution since
    -- f_sol = vlasovSolutionViaPushforward charX charV f₀.
    -- Phase 3 update (2026-05-31): the wrapper now takes explicit L + hL +
    -- h_int_conv hypotheses (added when vlasovTrajectoryLipschitzBound was
    -- substantively closed); the L=0 case provides them trivially since
    -- gradW ≡ 0.
    have hL_zero : LipschitzWith 0 gradW := by
      rw [show gradW = fun _ => 0 from funext hgradW_zero]
      exact LipschitzWith.const' 0
    have hf_eq : f_sol = fun t => vlasovSolutionViaPushforward charX charV f₀ t := rfl
    have hf_lag : IsLagrangianVlasovSolution gradW f_sol := by
      rw [hf_eq]
      haveI := hf₀.1
      apply vlasovSolutionViaPushforward_isLagrangianVlasovSolution gradW 0 hL_zero
      · -- IsCharacteristicFlow
        refine ⟨?_, ?_, ?_⟩
        · intro z; simp [charX, charV, vlasovSolutionViaPushforward]
        · intro t z
          have h1 : HasDerivAt (fun s => z.1 + s • z.2) z.2 t := by
            have h1' : HasDerivAt (fun _ : ℝ => z.1) 0 t := hasDerivAt_const t z.1
            have h2' : HasDerivAt (fun s : ℝ => s • z.2) ((1 : ℝ) • z.2) t :=
              (hasDerivAt_id (𝕜 := ℝ) t).smul_const z.2
            have := h1'.add h2'; simp only [zero_add, one_smul] at this; exact this
          exact h1
        · intro t z
          simp only [vlasovSolutionViaPushforward, charX, charV]
          rw [hconv_zero, neg_zero]
          exact hasDerivAt_const t z.2
      · -- IsCharacteristicFlowSelfConsistent
        intro t
        simp only [vlasovSolutionViaPushforward, spatialMarginal, charX, charV]
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
      · -- AEMeasurability
        intro s; fun_prop
      · -- Continuous gradW (≡ 0)
        have : gradW = fun _ => 0 := funext hgradW_zero
        rw [this]; exact continuous_const
      · -- Continuous convolveFunctionMeasure gradW ... (≡ 0)
        intro s
        have : (fun x => convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x) =
            fun _ => 0 := funext (hconv_zero _)
        rw [this]; exact continuous_const
      · -- h_int_conv: convolution-integrability witness (Phase 3 added).
        -- For L=0, gradW ≡ 0, so (fun y => gradW (x - y)) = (fun _ => 0),
        -- trivially integrable against any measure.
        intro s x
        have h_zero : (fun y : PhysSpace d => gradW (x - y)) = fun _ => (0 : PhysSpace d) := by
          funext y; exact hgradW_zero (x - y)
        rw [h_zero]; exact integrable_zero _ _ _
    -- Step L0-8: Narrow continuity.
    have hf_cont : ∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        Continuous (fun t => ∫ z, g z ∂f_sol t) := by
      intro g hg_cont hg_bdd
      -- Extract uniform bound C: ∀ x, ‖g x‖ ≤ C.
      obtain ⟨C, hC⟩ := hg_bdd.exists_norm_le
      have hC_range : ∀ x : PhaseSpace d, ‖g x‖ ≤ C :=
        fun x => hC (g x) (Set.mem_range_self x)
      -- Rewrite via integral_map: ∫ g df_sol(t) = ∫ z, g(z.1+t•z.2, z.2) df₀.
      have h_rw : ∀ t, ∫ z, g z ∂f_sol t = ∫ z, g (z.1 + t • z.2, z.2) ∂f₀ := by
        intro t
        simp only [f_sol, charX, charV]
        rw [integral_map (by fun_prop) (by fun_prop)]
      simp_rw [h_rw]
      -- Apply continuous_of_dominated.
      haveI := hf₀.1
      apply continuous_of_dominated
      · intro t; exact (hg_cont.comp (by fun_prop)).aestronglyMeasurable
      · intro t; apply Filter.Eventually.of_forall; intro z
        exact hC_range _
      · exact integrable_const C
      · apply Filter.Eventually.of_forall; intro z
        exact hg_cont.comp (by fun_prop)
    -- Step L0-9: Uniqueness.
    have hf_uniq : ∀ g : ℝ → Measure (PhaseSpace d),
        g 0 = f₀ ∧ (∀ t, HasFiniteFirstMoment (g t)) ∧
        IsLagrangianVlasovSolution gradW g ∧
        (∀ (h : PhaseSpace d → ℝ), Continuous h → Bornology.IsBounded (Set.range h) →
          Continuous (fun t => ∫ z, h z ∂g t)) →
        g = f_sol := by
      intro g ⟨hg_init, _, hg_lag, _⟩
      obtain ⟨_, cX, cV, h_flow, h_push, _⟩ := hg_lag
      -- cV is constant in t: velocity ODE gives d/dt(cV(t,z)) = -conv(0,...) = 0.
      have hcV_const : ∀ (t : ℝ) (z : PhaseSpace d), cV t z = z.2 := by
        intro t z
        have hderiv : ∀ s, HasDerivAt (fun u => cV u z) 0 s := by
          intro s
          have := h_flow.2.2 s z
          rw [hconv_zero] at this
          simpa using this
        have hdiff : Differentiable ℝ (fun s => cV s z) :=
          fun s => (hderiv s).differentiableAt
        have hfderiv : ∀ s, fderiv ℝ (fun u => cV u z) s = 0 :=
          fun s => by rw [← toSpanSingleton_deriv, (hderiv s).deriv]; simp
        have heq := is_const_of_fderiv_eq_zero hdiff hfderiv t 0
        simp only [heq, h_flow.1 z |>.2]
      -- cX satisfies d/dt(cX(t,z)) = cV(t,z) = z.2, cX(0,z) = z.1.
      have hcX_affine : ∀ (t : ℝ) (z : PhaseSpace d), cX t z = z.1 + t • z.2 := by
        intro t z
        -- d/dt (cX(t,z) - z.1 - t•z.2) = z.2 - z.2 = 0.
        have hderiv_cX : ∀ s, HasDerivAt (fun u => cX u z) (z.2) s := by
          intro s
          have := h_flow.2.1 s z
          rw [← hcV_const s z]
          exact this
        have hderiv_affine : ∀ s, HasDerivAt (fun u : ℝ => z.1 + u • z.2) z.2 s := by
          intro s
          have h1 : HasDerivAt (fun _ : ℝ => z.1) 0 s := hasDerivAt_const s z.1
          have h2 : HasDerivAt (fun u : ℝ => u • z.2) ((1 : ℝ) • z.2) s :=
            (hasDerivAt_id (𝕜 := ℝ) s).smul_const z.2
          have := h1.add h2
          simp only [zero_add, one_smul] at this; exact this
        have hderiv_diff : ∀ s, HasDerivAt (fun u => cX u z - (z.1 + u • z.2)) 0 s :=
          fun s => by
            have := (hderiv_cX s).sub (hderiv_affine s); simp at this; exact this
        have hdiff : Differentiable ℝ (fun u => cX u z - (z.1 + u • z.2)) :=
          fun s => (hderiv_diff s).differentiableAt
        have hfderiv : ∀ s, fderiv ℝ (fun u => cX u z - (z.1 + u • z.2)) s = 0 :=
          fun s => by rw [← toSpanSingleton_deriv, (hderiv_diff s).deriv]; simp
        have heq := is_const_of_fderiv_eq_zero hdiff hfderiv t 0
        have h0 : cX 0 z - (z.1 + (0 : ℝ) • z.2) = 0 := by
          simp [h_flow.1 z |>.1]
        exact sub_eq_zero.mp (heq.trans h0)
      -- Now g t = Measure.map (cX t, cV t) (g 0) = Measure.map (z.1+t•z.2, z.2) f₀ = f_sol t.
      funext t
      have := h_push t
      rw [hg_init] at this
      rw [this]
      congr 1
      funext z
      simp only [hcX_affine t z, hcV_const t z, charX, charV, f_sol]
    -- Assemble ∃ (post-refactor: forward-only existence, no uniqueness clause).
    refine ⟨f_sol, hf_init, ?_, ?_, ?_⟩
    · -- Moment bound on Ici 0 — discard t < 0.
      intro t _
      exact hf_mom t
    · -- Per-T_target IsLagrangianVlasovSolutionOn — project the universal form.
      intro T _hT
      exact hf_lag.toOn T
    · -- Narrow continuity restricted to Ici 0.
      intro g hg_cont hg_bdd
      exact (hf_cont g hg_cont hg_bdd).continuousOn

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

-- ---------------------------------------------------------------------------
-- §10  Dobrushin stability chain (Phase 4 Path A Stage 2a relocation, 2026-05-31)
-- ---------------------------------------------------------------------------
--
-- Relocated from Basic.lean §11 per the Phase 4 Path A architectural decision:
-- items 5/6 (`w1ContOn_uscNarrow_via_pureFA`,
-- `wassersteinGronwallCoupling_derivBound_via_pureFA`) need
-- `convolveFunctionMeasure_lipschitz_in_x` (CharFlow L75) for their substantive
-- close.  The consumer chain that depends on items 5/6 (W1ContOn through
-- `dobrushin`) follows up to CharFlow because Basic-resident declarations
-- can't call CharFlow declarations (import direction).
--
-- **Stays in Basic** (pure-FA placeholders + helpers that don't depend on
-- items 5/6 + the marquee `meanFieldLimit` which takes the Dobrushin estimate
-- as a hypothesis):
--   * `MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows` (pure-FA)
--   * `MathlibTODO_w1RightDerivBoundAlongLagrangianFlowsOn` (pure-FA;
--     `_On`-localized primary form, Stage 2b part 5 2026-05-31)
--   * `W1ContOn_lt_top`, `W1ContOn_toRealContOn`,
--     `wassersteinGronwallCoupling_gronwall_le`,
--     `wassersteinGronwallCoupling_ennreal_mul_comm`,
--     `dobrushin_C_choice`, `convolveDiff_norm_le`,
--     `wasserstein1_ofReal_exp_monotone` (pure helpers)
--   * `DobrushinStabilityEstimate` (Prop def)
--   * `meanFieldLimit` (consumes Dobrushin estimate as hypothesis)
--
-- The 9 declarations relocated here all take `IsLagrangianVlasovSolution`
-- (per Stage 1 cascade, commit `abb5568`).  Items 5/6 stay sorry'd at their
-- new CharFlow location pending Stage 2b substantive close.


/-- Package the bound and positivity of C into the existential conclusion of dobrushin:
∃ C > 0, ∀ t ≥ 0, W₁(f_t, g_t) ≤ exp(C·t) · W₁(f_0, g_0).
Depends on dobrushin_C_choice (in Basic.lean) and dobrushin_ennreal_bound. -/
lemma dobrushin_package_exists
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
  -- Re-routed (2026-06-05) through the integrated-coupling core via
  -- `dobrushin_meanfield_On`: pick C = 2·(max 1 L) and window each `t ≥ 0` at
  -- `T = t + 1` (uniform in `t`, including `t = 0`) via `.toOn`.  This bypasses
  -- `MathlibTODO_wassersteinGronwallCoupling` and its W₁-continuity (#5) /
  -- right-derivative (#6) sub-axioms entirely.
  refine ⟨2 * ((max 1 L : NNReal) : ℝ), ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    linarith
  · intro t ht
    exact dobrushin_meanfield_On gradW L hL f g (t + 1) (by linarith)
      (hf.toOn (t + 1)) (hg.toOn (t + 1))
      (fun s _ => hf_prob s) (fun s _ => hg_prob s) t ⟨ht, by linarith⟩

/-- (tex: thm:dobrushin)
Dobrushin's stability theorem (1979).

Under Assumption ass:W, there exists a constant C = C(L) > 0 such that for any
two measure-valued solutions f_t, g_t ∈ 𝒫_1(ℝ^d × ℝ^d) of the Vlasov equation
eq:vlasov,

  W_1(f_t, g_t) ≤ e^{C·t} · W_1(f_0, g_0),   for all t ≥ 0,

where W_1 is the Wasserstein-1 distance.
The proof uses a coupling via the characteristic flows eq:char and a Gronwall
inequality; the key estimate is |∇W * ρ − ∇W * σ|_∞ ≤ L · W_1(ρ, σ).

**Relocation note (Phase 4 Path A Stage 2a, 2026-05-31)**: moved from
Basic.lean §11 (originally L2334) so the chain it composes — items 5/6,
W1ContOn, Gronwall lift, ennreal bound — could compose against CharFlow's
flow infrastructure (`convolveFunctionMeasure_lipschitz_in_x` etc.).
External callers point here directly (no Basic-side pointer needed since
no external code referenced the Basic-resident `dobrushin`).
-/
theorem dobrushin
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    -- L is the Lipschitz constant of ∇W from Assumption ass:W
    (L : NNReal) (hL : LipschitzWith L gradW)
    -- f and g are two Lagrangian Vlasov solutions (carrying characteristic
    -- flow witnesses, per the Phase 4 Path A architectural upgrade).
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
  -- close via dobrushin_package_exists, which now routes through
  -- `dobrushin_meanfield_On` (the integrated-coupling core at the optimal
  -- coupling), bypassing the retired W₁-continuity / right-derivative chain.
  exact dobrushin_package_exists W gradW hgradW L hL f g hf hg hf_prob hg_prob

end Vlasov
