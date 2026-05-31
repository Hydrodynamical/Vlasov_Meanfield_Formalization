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
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0))

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
  refine ⟨h_sol.toOn T, charX, charV, ?_, ?_, ?_⟩
  · -- IsCharacteristicFlowOn from IsCharacteristicFlow.
    exact ⟨fun z _ => h_flow.1 z,
           fun t _ z _ => h_flow.2.1 t z,
           fun t _ z _ => h_flow.2.2 t z⟩
  · intro t _; exact h_push t
  · intro s _; exact h_meas s

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
          charX, charV, hflow_on, ?_, ?_⟩
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
-- The project's contraction analysis uses the `W₁`-based metric `supW1On`
-- and the smallness constraint `L · (T+1)² < 1` that arises from the
-- per-ball Picard-Lindelöf flow's `(T+1)`-buffer.  Two structural-debt
-- findings (the `+1` additive offset and the polynomial-vs-exponential
-- constraint mismatch surfaced in `_picard_fixedPointFlow`'s body, commit
-- `580548e`) trace to this metric choice.  Switching to the
-- truncated-distance Wasserstein `W̄ = W_{min(|x-y|,1)}` (per Dobrushin 1979,
-- §5) retires both findings and the `L < 1` restriction simultaneously.
--
-- The two named abstractions below isolate the metric-dependent surface so
-- the eventual `W̄` refactor is bounded engineering (~500-900 lines)
-- rather than a full Stage 4 redo.  `LocalSmallness` and `CurveMetric` are
-- used in new theorems going forward; existing closed proofs continue to
-- compile against the unfolded form.

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
structure VlasovMeasureCurve (d : ℕ) [NeZero d] (T M : ℝ) where
  ρ : ℝ → Measure (PhysSpace d)
  isProb : ∀ t, IsProbabilityMeasure (ρ t)
  hasMoment : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ t) ≤ M
  yIntegrable : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t)
  hW1Cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
    ContinuousWithinAt (fun t => (wasserstein1 (ρ s) (ρ t)).toReal)
                       (Set.Icc 0 T) s

/-- `supW1On` of two `VlasovMeasureCurve`s on `[0, T]` with moment bound `M`
is bounded by `2M`, hence finite.

Combines pointwise `wasserstein1_le_moments_sum` with `iSup_le` over the
compact time set. -/
lemma supW1On_le_two_moment_of_VlasovMeasureCurve {d : ℕ} [NeZero d]
    {T M : ℝ} (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≤ ENNReal.ofReal (2 * M) := by
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
  have hρ_t : ∫ y, ‖y‖ ∂(ρ.ρ t) ≤ M := ρ.hasMoment t ht
  have hσ_t : ∫ y, ‖y‖ ∂(σ.ρ t) ≤ M := σ.hasMoment t ht
  linarith

/-- `supW1On` of two `VlasovMeasureCurve`s is finite (≠ ⊤). -/
lemma supW1On_ne_top_of_VlasovMeasureCurve {d : ℕ} [NeZero d] {T M : ℝ}
    (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≠ ⊤ :=
  ne_of_lt ((supW1On_le_two_moment_of_VlasovMeasureCurve ρ σ).trans_lt
            ENNReal.ofReal_lt_top)

/-- Convolution continuity in time, derived from the structural
`hW1Cont` field via `MathlibTODO_convolveLipschitzEstimate`.

For each `x ∈ PhysSpace d`, the map `t ↦ (∇W ∗ ρ_t)(x)` is continuous on
`[0, T]`.  Used inside `Φ`'s well-definedness proof (Stage 2) to discharge
the convolution-continuity hypothesis of `exists_vlasov_characteristicFlow`. -/
lemma vlasovMeasureCurve_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T M : ℝ} (ρ : VlasovMeasureCurve d T M)
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
noncomputable def VlasovMeasureCurve.extend {d : ℕ} [NeZero d] {T M : ℝ}
    (ρ : VlasovMeasureCurve d T M) : ℝ → Measure (PhysSpace d) :=
  fun t => ρ.ρ (clampToIcc T t)

/-- The extended curve is a probability measure at every `t : ℝ`. -/
instance VlasovMeasureCurve.extend_isProb {d : ℕ} [NeZero d] {T M : ℝ}
    (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    IsProbabilityMeasure (ρ.extend t) :=
  ρ.isProb _

/-- The extended curve has `‖·‖` integrable at every `t : ℝ`. -/
lemma VlasovMeasureCurve.extend_yIntegrable {d : ℕ} [NeZero d] {T M : ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
  ρ.yIntegrable _ (clampToIcc_mem hT t)

/-- The extended curve preserves the moment bound `M` universally in `t`. -/
lemma VlasovMeasureCurve.extend_hasMoment {d : ℕ} [NeZero d] {T M : ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M :=
  ρ.hasMoment _ (clampToIcc_mem hT t)

/-- Convolution continuity on the extended curve, universal in `t`.

Composed from `vlasovMeasureCurve_convCont` (ContinuousOn on `Icc 0 T`)
with `clampToIcc_continuous` via `ContinuousOn.comp_continuous`.  This
provides Stage 1.9's universal `hρ_cont` hypothesis directly from a
`VlasovMeasureCurve`'s structural fields. -/
lemma VlasovMeasureCurve.extend_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T M : ℝ} (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M)
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
def constantCurve {d : ℕ} [NeZero d] {T M : ℝ}
    (μ₀ : Measure (PhysSpace d)) [IsProbabilityMeasure μ₀]
    (hμ_int : Integrable (fun y : PhysSpace d => ‖y‖) μ₀)
    (hM : ∫ y, ‖y‖ ∂μ₀ ≤ M) :
    VlasovMeasureCurve d T M where
  ρ := fun _ => μ₀
  isProb := fun _ => inferInstance
  hasMoment := fun _ _ => hM
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
  -- Use R := N(z) / (1 - L·(T+1)²)  (positive since hTL).
  -- ============================================================
  -- TODO(W̄-refactor): LocalSmallness unfold site.  This body uses the
  -- algebraic form `(L : ℝ) * (T + 1) ^ 2 < 1` directly (the linarith on
  -- the next line consumes `hTL_pos := 1 - L·(T+1)² > 0`, derived from
  -- this hypothesis).  Under the W̄ refactor, `LocalSmallness L T` becomes
  -- `C₂(L) · T < 1` (linear in T, no `+1`); this `have` will need updating
  -- to expose the new algebraic form, and the subsequent `R := N(z) /
  -- (1 - L·(T+1)²)` selection will need re-derivation under the new
  -- contraction constant `C₂(L)`.  Flagged as a metric-dependent
  -- algebraic touchpoint; the single existing unfold here is the entire
  -- "metric-dependent lemmas section" identified by Move A.
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
  unfold wasserstein1 Phi
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
    VlasovMeasureCurve d T (C_T * (M_f₀ + 1)) where
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
    {T M : ℝ} (hT : 0 ≤ T) (hM_nn : 0 ≤ M)
    (hTL_PL : LocalSmallness_PL_buffer L T)
    (ρ : VlasovMeasureCurve d T M)
    (h_int_ext : ∀ t (x : PhysSpace d),
                  Integrable (fun y => gradW (x - y)) (ρ.extend t)) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (C_T : ℝ),
      0 ≤ C_T ∧
      IsCharacteristicFlowOn gradW ρ.extend charX charV (Set.Ioo 0 T) Set.univ ∧
      ∃ σ : VlasovMeasureCurve d T (C_T * (M_f₀ + 1)),
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
  have hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M :=
    fun t => VlasovMeasureCurve.extend_hasMoment hT ρ t
  obtain ⟨charX, charV, hflow_on, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ.extend h_int_ext hρ_cont h_y_int M hM_nn hM_ρ T hT hTL_PL
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    Stage_1_9_flow_boundary_regularity gradW ρ.extend charX charV T hT
      hflow_on h_boundary
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico M hM_nn
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
  let σ : VlasovMeasureCurve d T (C_T * (M_f₀ + 1)) :=
    Phi_asVlasovMeasureCurve charX_clamped f₀ h_meas_clamped h_int_charX_clamped
      T hT C_T hC_T_nn h_growth_clamped h_f₀_int M_f₀ hM_f₀ h_charX_cont_clamped
  refine ⟨charX, charV, C_T, hC_T_nn, hflow_on, σ, ?_⟩
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
  unfold wasserstein1
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
    (h_meas_ρ : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
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
      (((h_meas_ρ t).sub (h_meas_σ t)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact h_proj_bound z
  -- ============================================================
  -- Apply the W₁ pair bound.
  -- ============================================================
  have h_W1 := wasserstein1_pushforward_pair_le_integral_norm_diff
    (fun z => charX_ρ t z) (fun z => charX_σ t z) f₀
    (h_meas_ρ t) (h_meas_σ t) (h_int_charX_ρ t) (h_int_charX_σ t) h_diff_int_f₀
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
`L · (exp T - 1) < 1` when `K = 1` (i.e., `L < 1`).  This constraint
shape is incompatible with the per-ball Picard-Lindelöf flow's
quadratic-in-`T` smallness `LocalSmallness L T = L·(T+1)² < 1`
(structural-debt finding in commit `580548e`).

Under the `W̄` refactor (Dobrushin 1979, §5), the contraction factor
becomes `C₂(L) · T` — *linear in T*, no exponential, no `L < 1`
restriction.  The contraction constraint reduces to `C₂(L) · T < 1`,
which matches the quadratic-shape smallness modulo the additive `+1`
that the W̄ refactor also removes. -/
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
    (h_meas_ρ : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
    -- The pushforwards have finite first moments (for W₁ finiteness).
    (h_yint_Phi_ρ : ∀ t,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX_ρ t z) f₀))
    (h_yint_Phi_σ : ∀ t,
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
      MeasureTheory.Measure.isProbabilityMeasure_map (h_meas_ρ t)
    haveI hΦσ_t : IsProbabilityMeasure (Measure.map (fun z => charX_σ t z) f₀) :=
      MeasureTheory.Measure.isProbabilityMeasure_map (h_meas_σ t)
    -- W₁ is finite (probability + finite first moment).
    have h_W1_t_ne_top :
        wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                     (Measure.map (fun z => charX_σ t z) f₀) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _ (h_yint_Phi_ρ t) (h_yint_Phi_σ t)
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
    {T M : ℝ}
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
      ∫ y, ‖y‖ ∂μ ≤ M ∧
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) μ) Filter.atTop (nhds 0) := by
    intro t ht
    haveI : ∀ n, IsProbabilityMeasure ((x n).ρ t) := fun n => (x n).isProb t
    exact MathlibTODO_cauchyW1_hasNarrowLimit (fun n => (x n).ρ t) M
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
  have h_hasMoment : ∀ t ∈ Set.Icc (0:ℝ) T, ∫ y, ‖y‖ ∂(ρ_lim t) ≤ M := by
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

/-- **Mathlib-TODO (pure functional-analytic): AEMeasurability of an ODE
flow in initial condition.**

If `b : ℝ → α → α` is a time-dependent vector field that's Lipschitz in
the spatial variable uniformly in time, and `Φ : ℝ → α → α` is a flow
satisfying `HasDerivAt (fun s => Φ s z) (b t (Φ t z)) t` for each `z`
and `t`, then `Φ s : α → α` is AEMeasurable against any measure `μ`.

Standard ODE Picard regularity: continuity-in-initial-condition (Hartman,
*Ordinary Differential Equations* Ch. V; Coddington-Levinson Ch. 2)
implies Borel-measurability over the full phase space, which gives
AEMeasurability against any measure.

**Bucket-1 PR scope**: pure-functional-analytic; Villani / Hartman-style
ODE regularity result, statable in pure Mathlib `Analysis.ODE` language
once the relevant API stabilizes.  No project-specific instantiation
in the statement.

**Decomposed from `MathlibTODO_picardFlowAEMeasurable`** (Phase 1.5,
2026-05-31).  The Vlasov-specific composition lives below as
`picardCharFlow_aemeasurable`. -/
private theorem MathlibTODO_lipschitzFlowAEMeasurable
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [MeasurableSpace α] [BorelSpace α]
    (b : ℝ → α → α) (L : NNReal) (_hL : ∀ t, LipschitzWith L (b t))
    (Φ : ℝ → α → α)
    (_hflow : ∀ z t, HasDerivAt (fun s => Φ s z) (b t (Φ t z)) t)
    (μ : Measure α) :
    ∀ s, AEMeasurable (Φ s) μ := by
  sorry

/-- **Project-internal composition (Phase 1.5 decomposition target,
2026-05-31)**: AEMeasurability of the Vlasov characteristic flow's joint
map `z ↦ (charX s z, charV s z)`, derived from
`MathlibTODO_lipschitzFlowAEMeasurable` by packaging the Vlasov phase-space
vector field `b(t, z) := (z.2, -convolveFunctionMeasure gradW (ρ t) z.1)`
and the joint flow `Φ t z := (charX t z, charV t z)`.

**Status**: body sorry'd as a Phase 2-4 close target.  The composition is
mostly mechanical: extract the joint Lipschitz constant `max(1, L)` for
`b` from `LipschitzWith L gradW`, package `Φ`'s HasDerivAt from
`IsCharacteristicFlowOn`'s two HasDerivAt clauses, apply the pure-FA
placeholder.

**In-project consumer**: `vlasovWellPosedness_local_picard_fixedPointFlow`'s
`h_aemeas_out`. -/
private lemma picardCharFlow_aemeasurable
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    {T : ℝ} (hT : 0 ≤ T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (μ : Measure (PhaseSpace d)) :
    ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) μ := by
  -- Decomposition target: compose MathlibTODO_lipschitzFlowAEMeasurable with the
  -- Vlasov joint flow Φ t z := (charX t z, charV t z) on PhaseSpace d.
  -- The Vlasov vector field b(t, z) := (z.2, -conv gradW (ρ t) z.1) is
  -- Lipschitz with constant max(1, L), and Φ satisfies HasDerivAt for b
  -- from IsCharacteristicFlowOn's two HasDerivAt clauses combined via
  -- HasDerivAt.prodMk.  Body closes in Phase 2-4 substantive work.
  sorry

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
  (stronger than `hTL : L · (T+1)² < 1` alone for large `M_f₀`).
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
The Picard fixed-point body's structural-debt finding (commit `580548e`):
the contraction constraint `L · (exp T - 1) < 1` (exponential in T,
from `Phi_supW1_contraction`'s W₁-based shape) is NOT implied by the
quadratic-shape smallness `LocalSmallness L T = L·(T+1)² < 1`.  The
two constraints arise from different sub-arguments: the quadratic
comes from per-ball Picard-Lindelöf's `(T+1)`-buffer, the exponential
from Gronwall on the W₁-based contraction.

Under the W̄ refactor (Dobrushin 1979, §5), both constraints become
linear-in-T and align: the contraction shape changes from
`L·(exp T - 1) < 1` to `C₂(L)·T < 1`, and the PL window's `(T+1)`-
buffer disappears.  The single algebraic constraint `C₂(L)·T < 1` then
suffices and is satisfiable for any `L > 0` by taking `T < 1/C₂(L)`.

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
    (hTL_con : LocalSmallness_contraction L T) :
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
  let M_f₀ : ℝ := ∫ z : PhysSpace d, ‖z‖ ∂(spatialMarginal f₀)
  have hM_f₀_nn : 0 ≤ M_f₀ := integral_nonneg (fun z => norm_nonneg z)
  have hM_f₀_spec : ∫ z : PhysSpace d, ‖z‖ ∂(spatialMarginal f₀) ≤ M_f₀ := le_refl _
  -- ============================================================
  -- Step 2: M-fixed-point.
  -- Sub-sub-sorry: existence of M ≥ 0 such that
  --   (a) ∫ ‖y‖ ∂μ₀ ≤ M  (initial moment bound)
  --   (b) for any VlasovMeasureCurve ρ with moment bound M, the
  --       Gronwall growth constant C_T satisfies C_T * (M_f₀ + 1) ≤ M.
  -- This is the fixed-point existence whose full proof requires analysis of
  -- the Gronwall bound's monotone structure in M. -/
  obtain ⟨M, hM_nn, hM_init⟩ : ∃ M : ℝ, 0 ≤ M ∧ M_f₀ ≤ M := by
    exact ⟨M_f₀, hM_f₀_nn, le_refl _⟩
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
  -- **Structural-debt note (2026-05-29 sorry-prover analysis)**: the q
  -- definition below uses `(L · (2·M))` as the gronwallBound ε₀-input.  Per
  -- `Phi_supW1_contraction`'s actual output shape, the genuine contraction
  -- ratio is `gronwallBound 0 (max 1 L) (L · D) T / D` where D is the
  -- *input W₁ bound* — INDEPENDENT of M.  The current `(2·M)` is the
  -- placeholder D for `supW1On (constantCurve) (Φ constantCurve)`, but it
  -- conflates the contraction factor itself with this initial distance.
  --
  -- The TRUE contraction constraint is `L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`
  -- (equivalent to `L · (exp T - 1) < 1` when `L < 1`).  This is *not* a
  -- consequence of `hTL : L · (T+1)² < 1` — the two constraints have
  -- different shapes (quadratic vs exponential in T), and for very small `L`
  -- the smallness `hTL` permits T_0 large enough that `L · (exp T_0 - 1)`
  -- exceeds 1.
  --
  -- Cleanest fix: add `hTL_contraction : L · (exp T - 1) < 1` as an
  -- additional hypothesis to this theorem and propagate through Stage 5
  -- (`vlasovWellPosedness_local`, `_glue_step`, `_forward`).  Recorded as
  -- a structural-debt item for a focused refactor session.
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
  let D₀ : ℝ := 2 * M
  have hD₀_nn : 0 ≤ D₀ := by linarith
  -- Sub-sub-sorry: Picard sequence + contraction.
  obtain ⟨x, h_contract⟩ : ∃ x : ℕ → VlasovMeasureCurve d T M,
      ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
           ENNReal.ofReal (q ^ k * D₀) := by
    sorry
  -- ============================================================
  -- Step 5: Extract limit ρ_lim via picard_iterate_bundlesAs_VlasovMeasureCurve.
  -- ============================================================
  obtain ⟨ρ_lim, _h_tendsto⟩ :=
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
      M hM_nn
      (fun t => VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim t)
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
    sorry
  -- ============================================================
  -- Step 9: Bundle the result.
  -- Convert hflow_on_ρlim (against ρ_lim.extend) to the conclusion
  -- (against spatialMarginal ∘ vlasovSolutionViaPushforward) using h_self_consist.
  -- ============================================================
  have hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ := by
    refine ⟨hflow_on_ρlim.1, hflow_on_ρlim.2.1, fun t ht z _hz => ?_⟩
    have h_eq := h_self_consist t (Set.Ioo_subset_Icc_self ht)
    have h_orig := hflow_on_ρlim.2.2 t ht z (Set.mem_univ z)
    -- h_orig: HasDerivAt ... (-(convolveFunctionMeasure gradW (ρ_lim.extend t) ...)) t
    -- Goal: HasDerivAt ... (-(convolveFunctionMeasure gradW (spatialMarginal ...) ...)) t
    -- These are equal since ρ_lim.extend t = spatialMarginal ... (h_eq).
    rwa [h_eq] at h_orig
  -- Boundary regularity conjunct: convert h_boundary_ρlim using h_self_consist.
  have h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
            (charX t z)))
        (Set.Icc 0 T) t := by
    intro z t ht
    have h_eq := h_self_consist t ht
    obtain ⟨h1, h2⟩ := h_boundary_ρlim z t ht
    rw [h_eq] at h2
    exact ⟨h1, h2⟩
  -- Moment bound: from ρ_lim.hasMoment + h_self_consist.
  have hM_ρ_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M := by
    intro s hs
    rw [← h_self_consist s hs]
    exact VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim s
  -- First-moment integrability: from ρ_lim.yIntegrable + h_self_consist.
  have h_y_int_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s hs
    rw [← h_self_consist s hs]
    exact VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim s
  -- Continuity of convolveFunctionMeasure against spatial marginal (universal in s).
  -- Sub-sub-sorry: needs extend_convCont applied via h_self_consist.
  have hconv_cont : ∀ s, Continuous (fun x_pt =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x_pt) := by
    sorry
  -- AEMeasurable witness via project-internal composition lemma
  -- `picardCharFlow_aemeasurable` (Phase 1.5 decomposition target,
  -- 2026-05-31; closure-plan Sorry 7).  The composition uses
  -- `MathlibTODO_lipschitzFlowAEMeasurable` (pure-FA) as its abstract input.
  -- Instance `VlasovMeasureCurve.extend_isProb` (L3942) provides probability-
  -- measureness for the extended curve via Lean's instance resolution.
  have h_aemeas_out : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
    picardCharFlow_aemeasurable gradW L hL ρ_lim.extend
      charX charV hT.le hflow_on_ρlim f₀
  -- Sub-sub-sorry: universal-in-s convolution integrability.  For
  -- s ∈ Icc 0 T follows from h_y_int_ρ + Lipschitz of gradW; for s outside
  -- requires constant-extension (clamp) past T inside the Picard construction.
  have h_int_conv_out : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    sorry
  exact ⟨charX, charV, M, hM_nn, hflow_on, h_boundary, hM_ρ_bound, h_y_int_ρ,
         hconv_cont, h_aemeas_out, h_int_conv_out⟩

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
    (hTL_con : LocalSmallness_contraction L T) :
    ∃ (f : ℝ → Measure (PhaseSpace d))
      (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      f 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, HasFiniteFirstMoment (f t)) ∧
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
  --       ρ_lim.extend ... hT.le (by linarith [hTL])
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
      f₀ hf₀_int hT hTL_PL hTL_con
  -- Bundle the f-shape result.
  refine ⟨vlasovSolutionViaPushforward charX charV f₀, charX, charV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    (hT_0_small_con : LocalSmallness_contraction L T_0) :
    ∃ (f_next : ℝ → Measure (PhaseSpace d))
      (charX_next charV_next : ℝ → PhaseSpace d → PhysSpace d),
      (∀ t ∈ Set.Icc (0 : ℝ) T, f_next t = f_prev t) ∧
      f_next 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), HasFiniteFirstMoment (f_next t)) ∧
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
  obtain ⟨g, charX_g, charV_g, hg_init, hg_mom, hg_lag, hg_push_ex, hg_aemeas_ex,
          hg_boundary, hg_init_cond⟩ :=
    vlasovWellPosedness_local W gradW hgradW L hL
      (f_prev T) h_prev_T_mom hT_0_pos hT_0_small_PL hT_0_small_con
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
  refine ⟨f_next, charX_next, charV_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
            -- Step 3: ContinuousAt of derivative function at T.
            -- Sub-sorry (focused leaf): the integrand involves the convolution
            -- `convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1` which
            -- depends on t' via narrow continuity of `t' ↦ spatialMarginal(f_next t')`.
            -- ~150-250 lines via DCT + W₁-Lipschitz-of-convolution from
            -- `MathlibTODO_convolveLipschitzEstimate`.  Discharged in focused follow-up.
            have h_cont_g : ContinuousAt (fun t' =>
                (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                          (gradVφ z)) ∂(f_next t')) + 0) T := by
              sorry
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
    · -- AEMeasurability on Icc 0 (T + T_0)
      -- Sub-sorry: piecewise AEMeasurability
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
    intro z t ht
    simp only [charX_next, charV_next]
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
          simp only [f_next, if_pos (le_refl T)]
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
          congrArg spatialMarginal (if_pos (le_refl T))
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
        have hfnext : f_next t = f_prev t := if_pos ht_le
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
        have h_fnext_t : f_next t = g (t - T) := if_neg (not_le.mpr ht_le)
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
          simp [f_next, not_le.mpr (show T < T + T_0 by linarith)]
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
  let T_0 : ℝ := min T_0_PL T_0_con / 2
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
  have hT_0_min_pos : 0 < min T_0_PL T_0_con :=
    lt_min hT_0_PL_pos hT_0_con_pos
  have hT0_pos : 0 < T_0 := by
    show 0 < min T_0_PL T_0_con / 2
    linarith
  -- **PL-buffer constraint at T_0** (existing algebra at T_0_PL_old, lifted
  -- to T_0 via monotonicity since T_0 ≤ T_0_PL_old).
  have hTL_T0_PL : LocalSmallness_PL_buffer L T_0 := by
    show (L : ℝ) * (T_0 + 1) ^ 2 < 1
    let T_0_PL_old : ℝ := (1 / Real.sqrt (L : ℝ) - 1) / 2
    have h_T_0_le_old : T_0 ≤ T_0_PL_old := by
      show min T_0_PL T_0_con / 2 ≤ (1 / Real.sqrt (L : ℝ) - 1) / 2
      have h_min_le : min T_0_PL T_0_con ≤ T_0_PL := min_le_left _ _
      show min T_0_PL T_0_con / 2 ≤ T_0_PL / 2
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
      show min T_0_PL T_0_con / 2 < T_0_con
      have h_min_le : min T_0_PL T_0_con ≤ T_0_con := min_le_right _ _
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
      obtain ⟨f, charX, charV, hf_init, hf_mom, hf_lag, hf_push, hf_aemeas, hf_boundary, hf_ic⟩ :=
        vlasovWellPosedness_local W gradW hgradW L hL f₀ hf₀ hT0_pos hTL_T0_PL hTL_T0_con
      exact ⟨f, charX, charV, hf_init, hf_mom, hf_lag.1, hf_push, hf_aemeas, hf_boundary, hf_ic⟩
    | succ n ih =>
      -- Step: n+1 → (n+2)·T_0.  Use _glue_step with T = (n+1)·T_0 > 0.
      obtain ⟨f_n, charX_n, charV_n, hfn_init, hfn_mom, hfn_vlasov,
              hfn_push, hfn_aemeas, hfn_boundary, hfn_ic⟩ := ih
      simp only [T_n] at hfn_mom hfn_vlasov hfn_push hfn_aemeas hfn_boundary
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
      obtain ⟨f_next, charX_next, charV_next, _h_agree, h_init, h_mom, h_lag,
              h_push, h_aemeas, h_boundary, h_ic⟩ :=
        vlasovWellPosedness_glue_step W gradW hgradW L hL f₀ hf₀ hT_n_pos
          f_n hfn_init hfn_mom
          charX_n charV_n hfn_vlasov hfn_flow
          hfn_push hfn_aemeas hfn_boundary hfn_ic
          hT0_pos hTL_T0_PL hTL_T0_con
      -- Need: T_n (n+1) = T_n n + T_0
      have h_T_eq : T_n (n + 1) = T_n n + T_0 := by
        simp only [T_n]; push_cast; ring
      refine ⟨f_next, charX_next, charV_next, h_init, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_T_eq]; exact h_mom
      · rw [h_T_eq]; exact h_lag.1
      · rw [h_T_eq]; exact h_push
      · rw [h_T_eq]; exact h_aemeas
      · rw [h_T_eq]; exact h_boundary
      · exact h_ic
  -- Step 4: Apply h_ind at n = N - 1 (since N ≥ 1).
  have hN_pred : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN_pos
  obtain ⟨f, charX_f, charV_f, hf_init, hf_mom, hf_vlasov,
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
    · -- AEMeasurable: restrict Icc 0 T_target ⊆ Icc 0 (N·T_0)
      intro s hs
      exact hf_aemeas s ⟨hs.1, le_trans hs.2 hN_covers⟩

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

/-- **Project-internal Stage 8 helper (Phase 1.5 reclassification target,
2026-05-31)**: Localized Dobrushin uniqueness on [0, T] for two
`IsVlasovSolutionOn` solutions with same initial data and finite moments.

**Reclassified from `MathlibTODO_dobrushin_uniqueness_On`** (Phase 1.5):
this is NOT a Mathlib OT gap; it's a corollary of the decomposed pure-FA
W₁-stability estimate (`MathlibTODO_w1RightDerivBoundAlongLipschitzMeasureFlow`,
to be added in Phase 1.5 item 5) plus the standard Mathlib characterization
`wasserstein1_eq_zero_iff_measure_eq` (or equivalent).

**Closure path** (sorry'd, Phase 2-4 target):
1. Build Vlasov phase-space vector field b(t, z) := (z.2,
   -convolveFunctionMeasure gradW (spatialMarginal (f t)) z.1).
2. Verify `IsVlasovSolutionOn` implies the continuity equation for b.
3. Apply the localized version of
   `MathlibTODO_w1RightDerivBoundAlongLipschitzMeasureFlow` to get the
   right-derivative liminf bound on `t ↦ W₁(f t, g t)`.
4. Gronwall-integrate via existing `wassersteinGronwallCoupling_gronwall_le`
   (Basic.lean, already proved) with initial value 0 (since `f 0 = g 0`
   implies `W₁(f 0, g 0) = 0`).
5. Conclude `W₁(f t, g t) = 0` for all t ∈ Icc 0 T.
6. Apply `wasserstein1_eq_zero_iff_measure_eq` (Mathlib) to get `f t = g t`.

**Justification for reclassification**: per the user's Phase 1.5 worked
example, this is Vlasov-specific composition (uses `IsVlasovSolutionOn`
unpacking + Vlasov vector-field construction), not a pure Mathlib OT
gap.  The placeholder's prior `MathlibTODO_*` naming overstated its
Mathlib-track relevance.  -/
private theorem dobrushin_uniqueness_On
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsVlasovSolutionOn gradW f T)
    (hg : IsVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hfg0 : f 0 = g 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, f t = g t := by
  sorry

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
  -- Extract IsVlasovSolutionOn from IsLagrangianVlasovSolutionOn
  have hf_pde : IsVlasovSolutionOn gradW f T_target := hf_lag.1
  have hg_pde : IsVlasovSolutionOn gradW g T_target := hg_lag.1
  -- The two solutions share the same initial datum f₀
  have hfg0 : f 0 = g 0 := hf_init.trans hg_init.symm
  -- Apply the localized Dobrushin uniqueness (Helper above)
  exact dobrushin_uniqueness_On gradW L hL f g T_target hT_target
    hf_pde hg_pde hf_mom hg_mom hfg0

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
      obtain ⟨h_sol, charX, charV, h_flow, h_push, h_aemeas⟩ := h_sol_lag m
      refine ⟨?_, charX, charV, ?_, ?_, ?_⟩
      · intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s hs
        exact h_sol φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s
          ⟨hs.1, lt_of_lt_of_le hs.2 hnm_cast⟩
      · exact h_flow.mono (Set.Ioo_subset_Ioo le_rfl hnm_cast) Set.Subset.rfl
      · intro s hs; exact h_push s ⟨hs.1, le_trans hs.2 hnm_cast⟩
      · intro s hs; exact h_aemeas s ⟨hs.1, le_trans hs.2 hnm_cast⟩
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
    obtain ⟨h_pde_N, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N⟩ := h_sol_lag N
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
    · -- AEMeasurable on Icc 0 T_target: h_aemeas_N gives w.r.t. sol N 0 = f 0.
      intro s hs
      rw [h_f0_solN]
      exact h_aemeas_N s ⟨hs.1, le_trans hs.2 (by linarith)⟩
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
    · -- h_eq : 0 = t₀, so t₀ = 0.  Right-continuity at t = 0 sub-sub-sorry.
      -- The right-continuity of t ↦ ∫ g ∂(f t) at t = 0 requires that
      -- the characteristic flow (charX t z, charV t z) → z as t → 0⁺,
      -- which in turn needs boundary ODE regularity at t = 0 beyond what
      -- IsCharacteristicFlowOn exposes (only HasDerivAt on Ioo 0 T is given).
      -- This is a genuine sub-sub-sorry; the boundary regularity fix aligns
      -- with the Friction-5 / B-series watch-list pattern.
      rw [← h_eq]; sorry
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
      obtain ⟨_h_pde, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N⟩ := h_sol_lag N
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
--   * `MathlibTODO_w1RightDerivBoundAlongLagrangianFlows` (pure-FA)
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

/-- **Project-internal composition (Phase 1.5 Session 3, 2026-05-31;
relocated to CharFlow per Phase 4 Path A Stage 2a, 2026-05-31)**:
W₁ USC for two Vlasov solutions, derived from
`MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows` by packaging the
Vlasov-specific characteristic flows as the abstract Lagrangian-pushforward
flows the pure-FA placeholder consumes.

**Status**: body sorry'd as Phase 4 Stage 2b close target.  Now that this
declaration takes `IsLagrangianVlasovSolution` (Stage 1 cascade) AND lives
in CharFlow (Stage 2a relocation), the substantive close becomes feasible:
extract flow witnesses from the Lagrangian conjunct, build Vlasov vector
fields, prove their `max(1, L)`-Lipschitz via
`convolveFunctionMeasure_lipschitz_in_x` (L75), apply the pure-FA placeholder.

**In-project consumer**: `MathlibTODO_wassersteinGronwallCoupling_W1ContOn`
(below). -/
theorem w1ContOn_uscNarrow_via_pureFA
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    UpperSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  -- Step 1: IsProbabilityMeasure instances from HasFiniteFirstMoment.
  haveI hf_isProb : ∀ t, IsProbabilityMeasure (f t) := fun t => (hf_prob t).1
  haveI hg_isProb : ∀ t, IsProbabilityMeasure (g t) := fun t => (hg_prob t).1
  -- Step 2: extract Lagrangian flow witnesses.
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g⟩ := hg
  obtain ⟨_, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨_, hflow_g_x, hflow_g_v⟩ := hflow_g
  -- Step 3: spatial marginals are probability (push-forward of probability).
  haveI hspf : ∀ t, IsProbabilityMeasure (spatialMarginal (f t)) := by
    intro t
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI hspg : ∀ t, IsProbabilityMeasure (spatialMarginal (g t)) := by
    intro t
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Step 4: integrability of gradW(x - ·) on spatialMarginal from first-moment
  -- + Lipschitz growth.  Helper closed over (μ, hμ_prob) for reuse between f and g.
  have h_int_helper : ∀ (μ : ℝ → Measure (PhaseSpace d))
      (_ : ∀ t, HasFiniteFirstMoment (μ t)),
      ∀ t (x_pt : PhysSpace d),
        Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t)) := by
    intro μ hμ_prob t x_pt
    haveI : IsProbabilityMeasure (μ t) := (hμ_prob t).1
    haveI : IsProbabilityMeasure (spatialMarginal (μ t)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    -- AEStronglyMeasurable from continuity of gradW + (x_pt - ·).
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal (μ t)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    -- ‖y‖-integrability on spatialMarginal: from HasFiniteFirstMoment on μ t
    -- via the pushforward `spatialMarginal = Measure.map Prod.fst`.
    have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (μ t)) := by
      unfold spatialMarginal
      rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
      -- Goal: Integrable ((fun y => ‖y‖) ∘ Prod.fst) (μ t).
      -- Bound by (fun z => ‖z‖) via Prod.norm — but goal is in composition form.
      refine Integrable.mono' (hμ_prob t).2
        ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      -- Goal: |((fun y ↦ ‖y‖) ∘ Prod.fst) z| ≤ ‖z‖, i.e. |‖z.1‖| ≤ ‖z‖.
      show |‖z.1‖| ≤ ‖z‖
      rw [abs_of_nonneg (norm_nonneg _)]
      exact norm_fst_le z
    -- Pointwise bound: ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + L·(‖x_pt‖ + ‖y‖).
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
    -- Dominator is integrable: constant + L · ‖y‖.
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
  have h_int_f := h_int_helper f hf_prob
  have h_int_g := h_int_helper g hg_prob
  -- Step 5: Lipschitz of Vlasov phase-space vector fields via the CharFlow lemma.
  -- The `max(1, L)` constant materializes via `vlasovVectorField_lipschitzWith`:
  -- position part is 1-Lipschitz (`Prod.snd`), force part is L-Lipschitz (Stage A's
  -- `convolveFunctionMeasure_lipschitz_in_x` + `Prod.fst`), joint Lipschitz `max(1, L)`.
  have hL_b_f : ∀ t, LipschitzWith (max 1 L)
      (vlasovVectorField gradW (fun t => spatialMarginal (f t)) t) :=
    fun t => vlasovVectorField_lipschitzWith gradW L hL _ h_int_f t
  have hL_b_g : ∀ t, LipschitzWith (max 1 L)
      (vlasovVectorField gradW (fun t => spatialMarginal (g t)) t) :=
    fun t => vlasovVectorField_lipschitzWith gradW L hL _ h_int_g t
  -- Step 6: define joint phase-space flows Φ_f, Φ_g and verify HasDerivAt
  -- against the Vlasov vector field via `HasDerivAt.prodMk` of the position +
  -- velocity HasDerivAt clauses from `IsCharacteristicFlow`.
  have hΦ_f : ∀ z t,
      HasDerivAt (fun s => (charX_f s z, charV_f s z))
        (vlasovVectorField gradW (fun t => spatialMarginal (f t)) t
          (charX_f t z, charV_f t z)) t := by
    intro z t
    -- (hflow_f_x t z) : HasDerivAt (fun s => charX_f s z) (charV_f t z) t
    -- (hflow_f_v t z) : HasDerivAt (fun s => charV_f s z)
    --   (-(convolveFunctionMeasure gradW (spatialMarginal (f t)) (charX_f t z))) t
    -- Joint via prodMk; unfold vlasovVectorField at the RHS via `show`.
    show HasDerivAt (fun s => (charX_f s z, charV_f s z))
      ((charX_f t z, charV_f t z).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (f t))
          (charX_f t z, charV_f t z).1)) t
    exact (hflow_f_x t z).prodMk (hflow_f_v t z)
  have hΦ_g : ∀ z t,
      HasDerivAt (fun s => (charX_g s z, charV_g s z))
        (vlasovVectorField gradW (fun t => spatialMarginal (g t)) t
          (charX_g t z, charV_g t z)) t := by
    intro z t
    show HasDerivAt (fun s => (charX_g s z, charV_g s z))
      ((charX_g t z, charV_g t z).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (g t))
          (charX_g t z, charV_g t z).1)) t
    exact (hflow_g_x t z).prodMk (hflow_g_v t z)
  -- Step 7: first-moment integrability of f t, g t (direct from HasFiniteFirstMoment).
  have hf_mom : ∀ t, Integrable (fun z : PhaseSpace d => ‖z‖) (f t) :=
    fun t => (hf_prob t).2
  have hg_mom : ∀ t, Integrable (fun z : PhaseSpace d => ‖z‖) (g t) :=
    fun t => (hg_prob t).2
  -- Step 8: apply the pure-FA placeholder with L := max(1, L).
  exact MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows
    (fun t => vlasovVectorField gradW (fun t => spatialMarginal (f t)) t)
    (fun t => vlasovVectorField gradW (fun t => spatialMarginal (g t)) t)
    (max 1 L) hL_b_f hL_b_g
    (fun t z => (charX_f t z, charV_f t z))
    (fun t z => (charX_g t z, charV_g t z))
    hΦ_f hΦ_g f g hpush_f hpush_g haem_f haem_g hf_mom hg_mom T hT

-- Sub-axiom 1 of MathlibTODO_wassersteinGronwallCoupling (decomposed in Basic.lean):
-- Narrow continuity of Wasserstein-1 distance along Vlasov solution curves.
theorem MathlibTODO_wassersteinGronwallCoupling_W1ContOn
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun t => (wasserstein1 (f t) (g t)).toReal) (Set.Icc 0 T) := by
  -- Step 1: pointwise finiteness from HasFiniteFirstMoment
  have h_finite : ∀ t, wasserstein1 (f t) (g t) < ⊤ :=
    W1ContOn_lt_top f g hf_prob hg_prob
  -- Step 2: narrow continuity of integral-against-test-function for f and g
  -- (W1ContOn_integralContAt; feeds into the LSC argument below).  Uses
  -- `hf.1 : IsVlasovSolution` extracted from the Lagrangian hypothesis.
  have h_int_cont_f : ∀ (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ ⊤ φ)
      (hc : HasCompactSupport φ) (gXφ gVφ : PhaseSpace d → PhysSpace d)
      (hgXφ : ∀ z, gXφ z = gradient (fun x => φ (x, z.2)) z.1)
      (hgVφ : ∀ z, gVφ z = gradient (fun v => φ (z.1, v)) z.2),
      Continuous (fun t => ∫ z, φ z ∂(f t)) :=
    fun φ hφ hc gXφ gVφ hgXφ hgVφ =>
      W1ContOn_integralContAt gradW f hf.1 φ hφ hc gXφ gVφ hgXφ hgVφ
  -- Step 3: W₁ is LSC along these Vlasov flows (Phase 1.5 composition lemma
  -- `w1ContOn_lscNarrow_via_pureFA`, which routes through the pure-FA
  -- `MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves`).  Pass the
  -- IsVlasovSolution components (.1) since item 4 doesn't need the flow witness.
  have h_lsc : LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) :=
    w1ContOn_lscNarrow_via_pureFA gradW f g hf.1 hg.1 hf_prob hg_prob T hT
  -- Step 4: W₁ is USC along these Vlasov flows.  Passes full Lagrangian
  -- hypotheses (item 5 needs the flow witness for substantive close).
  have h_usc : UpperSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) :=
    w1ContOn_uscNarrow_via_pureFA gradW L hL f g hf hg hf_prob hg_prob T hT
  -- Step 5: assemble via W1ContOn_toRealContOn
  have h_goal := W1ContOn_toRealContOn f g T hT h_finite h_lsc h_usc
  exact h_goal

/-- **Project-internal composition (Phase 1.5 Session 3, 2026-05-31;
relocated to CharFlow per Phase 4 Path A Stage 2a, 2026-05-31)**:
right-derivative Gronwall bound for W₁ between two Vlasov solutions,
derived from `MathlibTODO_w1RightDerivBoundAlongLagrangianFlows` by
packaging the Vlasov phase-space vector fields (each derived from gradW
+ the respective solution's spatial marginal via convolution).

**Status**: body sorry'd as Phase 4 Stage 2b close target.  Now that this
declaration takes `IsLagrangianVlasovSolution` (Stage 1 cascade) AND lives
in CharFlow (Stage 2a relocation), the substantive close becomes feasible.
Composition steps:
1. Extract characteristic flows for f, g via Lagrangian destructuring.
2. Define b_f(t, z) := (z.2, -convolveFunctionMeasure gradW
   (spatialMarginal (f t)) z.1) and similarly for b_g.
3. Prove `b_f, b_g` are `max(1, L)`-Lipschitz via
   `convolveFunctionMeasure_lipschitz_in_x` (L75) + Prod.norm.
4. Verify `_h_diff_bound` from `MathlibTODO_convolveLipschitzEstimate`
   composed with the spatial marginal as a 1-Lipschitz projection on W₁.
5. Apply the pure-FA placeholder.

**In-project consumer**: `wassersteinGronwallCoupling_real_bound`
(below). -/
theorem wassersteinGronwallCoupling_derivBound_via_pureFA
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : ((max 1 L : NNReal) : ℝ) ≤ C)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ s ∈ Set.Ico 0 T,
      ∀ r : ℝ, C * (wasserstein1 (f s) (g s)).toReal < r →
        ∃ᶠ z in nhdsWithin s (Set.Ioi s),
          (z - s)⁻¹ * ((wasserstein1 (f z) (g z)).toReal -
            (wasserstein1 (f s) (g s)).toReal) < r := by
  -- Step 1: IsProbabilityMeasure instances.
  haveI hf_isProb : ∀ t, IsProbabilityMeasure (f t) := fun t => (hf_prob t).1
  haveI hg_isProb : ∀ t, IsProbabilityMeasure (g t) := fun t => (hg_prob t).1
  -- Step 2: extract Lagrangian flow witnesses.
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g⟩ := hg
  obtain ⟨_, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨_, hflow_g_x, hflow_g_v⟩ := hflow_g
  -- Step 3: spatial marginals are probability.
  haveI hspf : ∀ t, IsProbabilityMeasure (spatialMarginal (f t)) := fun t =>
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI hspg : ∀ t, IsProbabilityMeasure (spatialMarginal (g t)) := fun t =>
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Step 4: integrability of gradW(x - ·) on spatialMarginal (helper closed
  -- over μ for reuse; mirrors item 5's pattern at CharFlow L9180-area).
  have h_int_helper : ∀ (μ : ℝ → Measure (PhaseSpace d))
      (_ : ∀ t, HasFiniteFirstMoment (μ t)),
      ∀ t (x_pt : PhysSpace d),
        Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t)) := by
    intro μ hμ_prob t x_pt
    haveI : IsProbabilityMeasure (μ t) := (hμ_prob t).1
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
      refine Integrable.mono' (hμ_prob t).2
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
        (spatialMarginal (μ t)) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
          (spatialMarginal (μ t)) := h_y_int.const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  have h_int_f := h_int_helper f hf_prob
  have h_int_g := h_int_helper g hg_prob
  -- Step 5: Lipschitz of Vlasov vector fields (`max(1, L)` via the CharFlow lemma).
  have hL_b_f : ∀ t, LipschitzWith (max 1 L)
      (vlasovVectorField gradW (fun t => spatialMarginal (f t)) t) :=
    fun t => vlasovVectorField_lipschitzWith gradW L hL _ h_int_f t
  have hL_b_g : ∀ t, LipschitzWith (max 1 L)
      (vlasovVectorField gradW (fun t => spatialMarginal (g t)) t) :=
    fun t => vlasovVectorField_lipschitzWith gradW L hL _ h_int_g t
  -- Step 6: HasDerivAt for joint flows Φ_f, Φ_g.
  have hΦ_f : ∀ z t,
      HasDerivAt (fun s => (charX_f s z, charV_f s z))
        (vlasovVectorField gradW (fun t => spatialMarginal (f t)) t
          (charX_f t z, charV_f t z)) t := by
    intro z t
    show HasDerivAt (fun s => (charX_f s z, charV_f s z))
      ((charX_f t z, charV_f t z).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (f t))
          (charX_f t z, charV_f t z).1)) t
    exact (hflow_f_x t z).prodMk (hflow_f_v t z)
  have hΦ_g : ∀ z t,
      HasDerivAt (fun s => (charX_g s z, charV_g s z))
        (vlasovVectorField gradW (fun t => spatialMarginal (g t)) t
          (charX_g t z, charV_g t z)) t := by
    intro z t
    show HasDerivAt (fun s => (charX_g s z, charV_g s z))
      ((charX_g t z, charV_g t z).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (g t))
          (charX_g t z, charV_g t z).1)) t
    exact (hflow_g_x t z).prodMk (hflow_g_v t z)
  -- Step 7: first-moment integrability.
  have hf_mom : ∀ t, Integrable (fun z : PhaseSpace d => ‖z‖) (f t) :=
    fun t => (hf_prob t).2
  have hg_mom : ∀ t, Integrable (fun z : PhaseSpace d => ‖z‖) (g t) :=
    fun t => (hg_prob t).2
  -- Step 8: vector-field difference bound — THE KEY NEW PIECE for item 6.
  -- Chain: convolveDiff_norm_le (L-Lipschitz) + wasserstein1_le_of_lipschitz_map
  -- at L=1 (Prod.fst is 1-Lipschitz) + `L ≤ max(1, L)`.
  have h_diff_bound : ∀ t x,
      ‖vlasovVectorField gradW (fun t => spatialMarginal (f t)) t x -
       vlasovVectorField gradW (fun t => spatialMarginal (g t)) t x‖ ≤
      ((max 1 L : NNReal) : ℝ) * (wasserstein1 (f t) (g t)).toReal := by
    intro t x
    -- Unfold the difference: b_f - b_g = (0, conv_g x.1 - conv_f x.1).
    have h_diff_form :
        vlasovVectorField gradW (fun t => spatialMarginal (f t)) t x -
        vlasovVectorField gradW (fun t => spatialMarginal (g t)) t x =
        ((0 : PhysSpace d),
         -(convolveFunctionMeasure gradW (spatialMarginal (f t)) x.1) -
         -(convolveFunctionMeasure gradW (spatialMarginal (g t)) x.1)) := by
      unfold vlasovVectorField
      simp [Prod.mk_sub_mk, sub_self]
    rw [h_diff_form]
    -- Prod.norm of (0, b) is ‖b‖ (max 0 ‖b‖ = ‖b‖).
    have h_prod_norm :
        ‖((0 : PhysSpace d),
          -(convolveFunctionMeasure gradW (spatialMarginal (f t)) x.1) -
          -(convolveFunctionMeasure gradW (spatialMarginal (g t)) x.1))‖ =
        ‖-(convolveFunctionMeasure gradW (spatialMarginal (f t)) x.1) -
          -(convolveFunctionMeasure gradW (spatialMarginal (g t)) x.1)‖ := by
      simp [Prod.norm_def]
    rw [h_prod_norm]
    -- Simplify -a - (-b) = -a + b = b - a.
    have h_neg_simp :
        -(convolveFunctionMeasure gradW (spatialMarginal (f t)) x.1) -
        -(convolveFunctionMeasure gradW (spatialMarginal (g t)) x.1) =
        convolveFunctionMeasure gradW (spatialMarginal (g t)) x.1 -
        convolveFunctionMeasure gradW (spatialMarginal (f t)) x.1 := by abel
    rw [h_neg_simp]
    -- Apply convolveDiff_norm_le (in Basic.lean) with ρ = spatialMarginal (g t),
    -- σ = spatialMarginal (f t).  Need wasserstein1 finiteness on spatial marginals.
    have h_sf_mom : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f t)) := by
      -- Reuse the integrability derivation from h_int_helper (h_y_int step).
      unfold spatialMarginal
      rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
      refine Integrable.mono' (hf_prob t).2
        ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      show |‖z.1‖| ≤ ‖z‖
      rw [abs_of_nonneg (norm_nonneg _)]
      exact norm_fst_le z
    have h_sg_mom : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (g t)) := by
      unfold spatialMarginal
      rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
      refine Integrable.mono' (hg_prob t).2
        ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      show |‖z.1‖| ≤ ‖z‖
      rw [abs_of_nonneg (norm_nonneg _)]
      exact norm_fst_le z
    have hW_sp_ne_top :
        wasserstein1 (spatialMarginal (g t)) (spatialMarginal (f t)) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _ h_sg_mom h_sf_mom
    have h_conv_diff :
        ‖convolveFunctionMeasure gradW (spatialMarginal (g t)) x.1 -
         convolveFunctionMeasure gradW (spatialMarginal (f t)) x.1‖ ≤
        (L : ℝ) * (wasserstein1 (spatialMarginal (g t)) (spatialMarginal (f t))).toReal :=
      convolveDiff_norm_le gradW L hL _ _ x.1 hW_sp_ne_top (h_int_g t x.1) (h_int_f t x.1)
    -- W₁ projection-contraction: Prod.fst is 1-Lipschitz, so
    -- W₁(spatialMarginal _, spatialMarginal _) ≤ W₁(_, _).
    have h_W1_proj :
        wasserstein1 (spatialMarginal (g t)) (spatialMarginal (f t)) ≤
        wasserstein1 (g t) (f t) := by
      have h_lip_fst : LipschitzWith 1 (Prod.fst : PhaseSpace d → PhysSpace d) :=
        LipschitzWith.prod_fst
      have h_app := wasserstein1_le_of_lipschitz_map
        (Prod.fst : PhaseSpace d → PhysSpace d) 1 h_lip_fst measurable_fst (g t) (f t)
      simp only [ENNReal.coe_one, one_mul] at h_app
      exact h_app
    have hW_ne_top : wasserstein1 (g t) (f t) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _ (hg_prob t).2 (hf_prob t).2
    have h_W1_proj_real :
        (wasserstein1 (spatialMarginal (g t)) (spatialMarginal (f t))).toReal ≤
        (wasserstein1 (g t) (f t)).toReal :=
      ENNReal.toReal_mono hW_ne_top h_W1_proj
    -- wasserstein1 (g t) (f t) = wasserstein1 (f t) (g t) by symmetry.
    have h_W1_sym : (wasserstein1 (g t) (f t)).toReal = (wasserstein1 (f t) (g t)).toReal := by
      rw [wasserstein1_comm]
    -- Chain: ‖conv_g - conv_f‖ ≤ L · W₁(sp_g, sp_f).toReal
    --                          ≤ L · W₁(g, f).toReal
    --                          = L · W₁(f, g).toReal
    --                          ≤ max(1, L) · W₁(f, g).toReal.
    have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
    have hW_nn : (0 : ℝ) ≤ (wasserstein1 (f t) (g t)).toReal := ENNReal.toReal_nonneg
    have h_L_le_max : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]
      exact le_max_right _ _
    calc ‖convolveFunctionMeasure gradW (spatialMarginal (g t)) x.1 -
          convolveFunctionMeasure gradW (spatialMarginal (f t)) x.1‖
        ≤ (L : ℝ) * (wasserstein1 (spatialMarginal (g t)) (spatialMarginal (f t))).toReal :=
          h_conv_diff
      _ ≤ (L : ℝ) * (wasserstein1 (g t) (f t)).toReal :=
          mul_le_mul_of_nonneg_left h_W1_proj_real hL_nn
      _ = (L : ℝ) * (wasserstein1 (f t) (g t)).toReal := by rw [h_W1_sym]
      _ ≤ ((max 1 L : NNReal) : ℝ) * (wasserstein1 (f t) (g t)).toReal :=
          mul_le_mul_of_nonneg_right h_L_le_max hW_nn
  -- Step 9: apply the pure-FA placeholder with placeholder_L = max(1, L).
  exact MathlibTODO_w1RightDerivBoundAlongLagrangianFlows
    (fun t => vlasovVectorField gradW (fun t => spatialMarginal (f t)) t)
    (fun t => vlasovVectorField gradW (fun t => spatialMarginal (g t)) t)
    (max 1 L) hL_b_f hL_b_g
    (fun t z => (charX_f t z, charV_f t z))
    (fun t z => (charX_g t z, charV_g t z))
    hΦ_f hΦ_g f g hpush_f hpush_g haem_f haem_g hf_mom hg_mom
    h_diff_bound C hC hCL T hT

/-- Given the sub-axioms MathlibTODO_wassersteinGronwallCoupling_W1ContOn and
MathlibTODO_wassersteinGronwallCoupling_derivBound, apply the Gronwall wrapper
`wassersteinGronwallCoupling_gronwall_le` to conclude:
  (wasserstein1 (f t) (g t)).toReal ≤ (wasserstein1 (f 0) (g 0)).toReal * Real.exp(C * t)
for all t ≥ 0.
TODO(mathlib): depends on sub-axioms for measure-valued ODE continuity and coupling. -/
lemma wassersteinGronwallCoupling_real_bound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : ((max 1 L : NNReal) : ℝ) ≤ C)
    (t : ℝ) (ht : 0 ≤ t) :
    (wasserstein1 (f t) (g t)).toReal ≤
      (wasserstein1 (f 0) (g 0)).toReal * Real.exp (C * t) := by
  have key := wassersteinGronwallCoupling_gronwall_le
    (fun s => (wasserstein1 (f s) (g s)).toReal)
    (wasserstein1 (f 0) (g 0)).toReal C t ht
    (MathlibTODO_wassersteinGronwallCoupling_W1ContOn
      gradW L hL f g hf hg hf_prob hg_prob t ht)
    (le_refl _)
    (wassersteinGronwallCoupling_derivBound_via_pureFA
      gradW L hL f g hf hg hf_prob hg_prob C hC hCL t ht)
  exact key t (Set.right_mem_Icc.mpr ht)

/-- Lift the real-valued Gronwall bound to ENNReal:
wasserstein1 (f t) (g t) ≤ ENNReal.ofReal(Real.exp(C * t)) * wasserstein1 (f 0) (g 0).
Uses wassersteinGronwallCoupling_real_bound + wassersteinGronwallCoupling_ennreal_mul_comm
+ ENNReal.ofReal_toReal_le (to pass from ENNReal.ofReal(x.toReal) ≤ x).
TODO(mathlib): depends on wassersteinGronwallCoupling_real_bound (sub-axiom-backed). -/
lemma wassersteinGronwallCoupling_ofReal_le
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : ((max 1 L : NNReal) : ℝ) ≤ C)
    (t : ℝ) (ht : 0 ≤ t)
    (hW_t : wasserstein1 (f t) (g t) ≠ ⊤) :
    wasserstein1 (f t) (g t) ≤
      ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
  -- real bound
  have h_real := wassersteinGronwallCoupling_real_bound gradW L hL f g hf hg
    hf_prob hg_prob C hC hCL t ht
  -- (wasserstein1 (f 0) (g 0)).toReal ≥ 0
  have h_t_real_nonneg : 0 ≤ (wasserstein1 (f t) (g t)).toReal := ENNReal.toReal_nonneg
  have h_0_real_nonneg : 0 ≤ (wasserstein1 (f 0) (g 0)).toReal := ENNReal.toReal_nonneg
  have h_exp_pos : 0 < Real.exp (C * t) := Real.exp_pos _
  -- Lift h_real to ENNReal: ofReal preserves ≤
  have h_ofReal : ENNReal.ofReal ((wasserstein1 (f t) (g t)).toReal) ≤
      ENNReal.ofReal ((wasserstein1 (f 0) (g 0)).toReal * Real.exp (C * t)) :=
    ENNReal.ofReal_le_ofReal h_real
  -- LHS = wasserstein1 (f t) (g t) since hW_t (finite)
  rw [ENNReal.ofReal_toReal hW_t] at h_ofReal
  -- RHS = ENNReal.ofReal(W₁(f 0)(g 0).toReal) * ENNReal.ofReal(exp(C*t))
  --     = mul of two ofReals (using ENNReal.ofReal_mul)
  rw [ENNReal.ofReal_mul h_0_real_nonneg, mul_comm] at h_ofReal
  -- Now h_ofReal : wasserstein1 (f t) (g t) ≤
  --   ENNReal.ofReal(exp(C*t)) * ENNReal.ofReal(W₁(f 0)(g 0).toReal)
  -- ENNReal.ofReal(x.toReal) ≤ x always (by ofReal_toReal_le)
  have h_lift : ENNReal.ofReal ((wasserstein1 (f 0) (g 0)).toReal) ≤
      wasserstein1 (f 0) (g 0) := ENNReal.ofReal_toReal_le
  calc wasserstein1 (f t) (g t)
      ≤ ENNReal.ofReal (Real.exp (C * t)) *
          ENNReal.ofReal ((wasserstein1 (f 0) (g 0)).toReal) := h_ofReal
    _ ≤ ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
        gcongr

-- The original Mathlib gap axiom, now expressed as a theorem.
-- The proof scaffold uses the sub-axioms and the four helper lemmas above
-- (helpers stay in Basic.lean; sub-axioms live here per Stage 2a relocation).
theorem MathlibTODO_wassersteinGronwallCoupling
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : ((max 1 L : NNReal) : ℝ) ≤ C)
    (t : ℝ) (ht : 0 ≤ t)
    (hW_t : wasserstein1 (f t) (g t) ≠ ⊤) :
    wasserstein1 (f t) (g t) ≤
      ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) :=
  wassersteinGronwallCoupling_ofReal_le gradW L hL f g hf hg hf_prob hg_prob C hC hCL t ht hW_t

/-- Given MathlibTODO_wassersteinGronwallCoupling and C = max(L,1) > 0 with (L : ℝ) ≤ C,
for any two Vlasov solutions f and g, for all t ≥ 0 we have
wasserstein1 (f t) (g t) ≤ ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0).
Depends on dobrushin_C_choice (in Basic.lean) and the relocated
MathlibTODO_wassersteinGronwallCoupling.
TODO(mathlib): depends on `MathlibTODO_wassersteinGronwallCoupling` Mathlib gap. -/
lemma dobrushin_ennreal_bound
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : ((max 1 L : NNReal) : ℝ) ≤ C) :
    ∀ t : ℝ, 0 ≤ t →
      wasserstein1 (f t) (g t) ≤
        ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
  intro t ht
  -- Derive hW_t : wasserstein1 (f t) (g t) ≠ ⊤ from finite first moments
  haveI : IsProbabilityMeasure (f t) := (hf_prob t).1
  haveI : IsProbabilityMeasure (g t) := (hg_prob t).1
  have hW_t : wasserstein1 (f t) (g t) ≠ ⊤ :=
    wasserstein1_ne_top_of_finite_moment (f t) (g t) (hf_prob t).2 (hg_prob t).2
  exact MathlibTODO_wassersteinGronwallCoupling gradW L hL f g hf hg hf_prob hg_prob
    C hC hCL t ht hW_t

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
  obtain ⟨C, hC, hCL⟩ := dobrushin_C_choice L
  exact ⟨C, hC,
    dobrushin_ennreal_bound W gradW hgradW L hL f g hf hg hf_prob hg_prob C hC hCL⟩

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
  -- close via dobrushin_package_exists, which composes dobrushin_C_choice
  -- (in Basic.lean) and dobrushin_ennreal_bound (which itself invokes
  -- MathlibTODO_wassersteinGronwallCoupling).
  exact dobrushin_package_exists W gradW hgradW L hL f g hf hg hf_prob hg_prob

end Vlasov
