/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Vlasov.OT.CharacteristicFlow

/-!
# Weak ⟹ Lagrangian: every weak Vlasov solution is transported by its characteristic flow

(tex: thm:weak-lagrangian)

The forward direction — a Lagrangian solution is weak — is immediate
(`IsLagrangianVlasovSolution.1`; the substantive pushforward-solves-weak content is
`vlasovSolutionViaPushforward_isVlasovSolutionOn`, `CharacteristicFlow.lean`).  This file builds
the **converse**: under the strengthened assumption `AssW2` (`W ∈ C²`, see `Basic.lean`), every
**weak** Vlasov solution on a window `[0,T]` is **Lagrangian** — i.e. it is the pushforward of its
initial datum under the characteristic flow it generates.  This is the superposition /
probabilistic-representation principle for the phase-space continuity equation
`∂_t f + div_{(x,v)}(b_f · f) = 0` with the Lipschitz field
`b_f(t,x,v) = (v, −(∇W ∗ ρ_t)(x))`, `ρ_t = spatialMarginal (f t)`.

It upgrades the project's uniqueness from "unique *Lagrangian* solution" to "unique *weak* (PDE)
solution".  The marquee `vlasovWellPosedness` / `dobrushin` are untouched and stay at `AssW`.

## Strategy (three ingredients)

Freeze the field at `ρ^f_t := spatialMarginal (f t)` (the field
`vlasovVectorField gradW ρ t z = (z.2, −(∇W ∗ ρ_t)(z.1))` is already parametric in `ρ`).  Let
`g_t := (Φ_t)_# (f 0)` be the pushforward along the flow `Φ` of this *frozen* field.  Then `f`
and `g` solve the **same linear** continuity equation with the same datum, so `f = g`, and `g` is
Lagrangian by construction.

1. **Flow existence for the frozen `ρ^f`** — reuse `exists_vlasov_characteristicFlow_global_smallT`.
2. **Pushforward solves the frozen linear weak eq** — reuse the *generic* helpers SC.1–SC.4
   (`vlasov_traj_chain_rule` etc., stated over an arbitrary `ρ`) at `ρ := ρ^f`, bypassing the
   self-consistent wrapper `vlasovSolutionViaPushforward_isVlasovSolutionOn`.
3. **Linear continuity-equation uniqueness `f = g`** — the crux (absent from Mathlib).  Dual
   transported test function `ψ_s(z) := φ(Φ_{s→T}(z))`: `s ↦ ∫ ψ_s dμ_s` is constant (the
   `∂_sψ + ⟨b,∇ψ⟩ = 0` cancellation), so `∫φ dμ_T = ∫ψ_0 dμ_0`, equal for `f` and `g` (shared
   `μ_0`); ranging over `φ` gives `f T = g T`.

## Decomposition roadmap (sub-lemmas added per build-layer)

Setup layer (C1):
* #1 `vlasov_frozenField_pushforward_isWeakSolOn` — `g` solves the frozen linear weak eq on
  `Ioo 0 T`; recompose SC.1 + SC.2 at `ρ := ρ^f`.
* #2 `exists_frozenField_charFlow_On` — instantiate `exists_vlasov_characteristicFlow_global_smallT`
  at `ρ := ρ^f`, discharging the integrability / continuity / moment hypotheses.

Final-step layer (C2, crux-independent):
* #7 `transportedIntegral_const_On` — zero derivative on `Ioo` + `ContinuousOn` on `Icc` ⟹ const.
* #9 `measure_eq_of_forall_Cc_integral_eq` — `∫φ dμ = ∫φ dν` for all `C_c^∞ φ` ⟹ `μ = ν`, via
  smooth approximation + `ext_of_forall_integral_eq_of_IsFiniteMeasure` (cf. `Wasserstein.lean`).

Crux layer (C3):
* #3 `charFlow_hasFDerivAt_in_initialPoint` — **the variational equation**: `z ↦ Φ_{s→T}(z)` is C¹
  (`HasFDerivAt`), derivative solving `Ṁ = (D_z b)·M`.  Sub-steps: 3.1 variational-ODE existence /
  uniqueness, 3.2 joint `(t,z)` continuity, 3.3 difference-quotient `o(‖h‖)` via Gronwall (the
  heart), 3.4 assemble `HasFDerivAt` → C¹.  Needs `AssW2.gradContDiff`.
* #4 `weakSolOn_test_C1c_of_Cinftyc` — extend `IsVlasovSolutionOn`'s test class from `C_c^∞` to
  `C¹_c` (mollification + DCT), since `ψ_s = φ∘Φ_{s→T}` is only `C¹_c` with a C¹ flow.
* #5 `transportedTestFunction_props` — `ψ_s` is `C¹`, compactly supported, with
  `∂_sψ_s + ⟨b,∇ψ_s⟩ = 0`.
* #6 `transportedIntegral_hasDerivWithinAt_zero` — `s ↦ ∫ ψ_s dμ_s` has zero derivative on
  `Ioo 0 T` for both `μ = f` and `μ = g`.

Assembly (C4):
* #8 `finalTime_integral_eq_of_weak` — combine #7 for `f` and `g` ⟹ `∫φ df_T = ∫φ dg_T` ∀ `C_c^∞ φ`.
* #10 the top theorem below — package `g`'s flow witness + `f = g` into
  `IsLagrangianVlasovSolutionOn`.

Universal (non-`_On`) form via window-gluing is a deferred follow-on (C5).
-/

namespace Vlasov

open MeasureTheory

variable {d : ℕ} [NeZero d]

/-! ## Linear (external-field) weak Vlasov solutions

The self-consistent weak predicate `IsVlasovSolutionOn` drives the convolution field by the
solution's *own* spatial marginal.  For the superposition argument we need the **linear**
version, where the field is driven by an *external* (frozen) measure curve `ρ` — both the given
weak solution `f` (with `ρ := spatialMarginal ∘ f`) and the pushforward `g` along the
frozen-field flow solve the *same* `IsLinearVlasovSolutionOn gradW ρ · T`, and uniqueness for it
(the crux, C3) forces `f = g`. -/

/-- Linear weak Vlasov evolution on `Ioo 0 T` for a test function `φ`, with the convolution field
driven by an **external** measure curve `ρ` (frozen), not the solution's own spatial marginal.
The self-consistent `WeakEvolutionEqOn gradW μ φ … (fun _ => 0) T` is the special case
`ρ = spatialMarginal ∘ μ` (modulo the `+ 0` remainder term). -/
def LinearWeakEvolutionEqOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (ρ t) z.1)
                (gradVφ z))
        ∂μ t) t

/-- A measure curve `μ` solves the **linear** Vlasov equation on `[0,T]` driven by the external
field `ρ`: the distributional identity `LinearWeakEvolutionEqOn` holds for every `C_c^∞` test
function.  Mirror of `IsVlasovSolutionOn` with the field externalized. -/
def IsLinearVlasovSolutionOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (μ : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      LinearWeakEvolutionEqOn gradW ρ μ φ gradXφ gradVφ T

/-- A self-consistent weak solution is a linear solution driven by its **own** spatial marginal.
The two differ only by `WeakEvolutionEqOn`'s `+ (fun _ => 0) t = + 0` remainder. -/
lemma IsVlasovSolutionOn.toLinearSelf
    {gradW : PhysSpace d → PhysSpace d} {f : ℝ → Measure (PhaseSpace d)} {T : ℝ}
    (h : IsVlasovSolutionOn gradW f T) :
    IsLinearVlasovSolutionOn gradW (fun t => spatialMarginal (f t)) f T := by
  intro φ hφ hφc gradXφ gradVφ hgradXφ hgradVφ t ht
  simpa using h φ hφ hφc gradXφ gradVφ hgradXφ hgradVφ t ht

/-- **C1 #1 — pushforward solves the frozen linear weak equation.**

For a characteristic flow `(charX, charV)` solving the ODE with an **external** field `ρ` on
`Ioo 0 T`, the pushforward `g := (charX t, charV t)_# f₀` solves the linear Vlasov equation
driven by that same `ρ`.  Proof: the generic SC.1–SC.3 machinery (change of variables +
chain rule + differentiation-under-the-integral, all parametric in `ρ`) recomposed at this `ρ`,
with SC.4's push-back inlined as `integral_map` (SC.4's packaged form hard-codes the
self-consistent marginal).  This is `vlasovSolutionViaPushforward_isVlasovSolutionOn` with `ρ`
left free — the `_hself` self-consistency hypothesis is unused. -/
theorem vlasov_frozenField_pushforward_isLinearVlasovSolutionOn
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (h_flow_meas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x => convolveFunctionMeasure gradW (ρ s) x)) :
    IsLinearVlasovSolutionOn gradW ρ (vlasovSolutionViaPushforward charX charV f₀) T := by
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_aesm_general : ∀ μ : Measure (PhaseSpace d), AEStronglyMeasurable φ μ :=
    fun μ => hφ_cont.aestronglyMeasurable
  -- SC.1: ∫ φ d(pushforward s) = ∫ (φ ∘ flow_s) df₀.
  have h_compose : ∀ s, ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := fun s =>
    vlasov_pushforward_integral_eq_compose charX charV f₀ s (h_flow_meas s) φ (hφ_aesm_general _)
  -- SC.2 `_at`: pointwise chain rule at every z, at this t.
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
  -- SC.3: differentiation under the integral via the DiffUnderIntegralData bundle.
  have h_diff_data : DiffUnderIntegralData gradW ρ charX charV f₀ φ gradXφ gradVφ t := by
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasov_trajectory_lipschitz_bound_on gradW L hL ρ charX charV f₀
        hf₀_fm φ hφ_smooth hφ_compact hT hflow_on h_init h_cont_Icc h_deriv_Ico
        hgradW_cont hconv_cont t ht M_ρ hM_ρ_nn hM_ρ h_y_int h_int
    refine ⟨nhd, bound, hnhd, ?_, ?_, ?_, h_lipsch, h_bound_int⟩
    · exact vlasov_compose_flow_aestronglymeas charX charV f₀ φ hφ_cont h_flow_meas t
    · exact vlasov_compose_flow_integrable_at charX charV f₀ φ hφ_cont hφ_compact t (h_flow_meas t)
    · exact vlasov_pointwise_deriv_aestronglymeas gradW ρ charX charV f₀
        φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ hconv_cont t (h_flow_meas t)
  have h_under_integral :=
    vlasov_pushforward_hasDerivAt_under_integral gradW ρ charX charV f₀
      φ gradXφ gradVφ t h_pointwise h_diff_data
  -- SC.4 (inlined; the packaged form hard-codes the self-consistent marginal): AE-strong-meas
  -- of the dot-product integrand, then push back through `integral_map`.
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
  -- Assemble: rewrite LHS via SC.1; push the derivative integral back through `integral_map`.
  have hLHS : (fun s => ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s)) =
              (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀) := funext h_compose
  have h_map_eq :
      ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
            - @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW (ρ t) z.1) (gradVφ z))
        ∂(vlasovSolutionViaPushforward charX charV f₀ t)
      = ∫ z, (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
            - @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW (ρ t) (charX t z))
                (gradVφ (charX t z, charV t z)))
        ∂f₀ := by
    unfold vlasovSolutionViaPushforward at h_integrand_aesm ⊢
    exact integral_map (h_flow_meas t) h_integrand_aesm
  rw [hLHS, h_map_eq]
  exact h_under_integral

/-- **C1 #2 — characteristic flow for a frozen field from window data (L11 clamp).**

Build the characteristic flow for the *given* external curve `ρ` on `Ioo 0 T` (with boundary
regularity), from probability/moment/integrability/continuity data on the window `[0,T]` only.
`exists_vlasov_characteristicFlow_global_smallT` demands *universal*-in-`t` instances; we clamp
`t ↦ ρ (max 0 (min t T))` into the window (L11), apply the universal producer to the clamped
curve, and transfer on `[0,T]` where the clamp is the identity. -/
theorem exists_frozenField_charFlow_On
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    (T : ℝ) (hT : 0 < T) (hTL_PL : LocalSmallness_PL_buffer L T)
    (hρ_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (ρ t))
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      ContinuousOn (fun t => convolveFunctionMeasure gradW (ρ t) x) (Set.Icc (0 : ℝ) T))
    (h_y_int : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ) :
    ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
      IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z) ∧
      (∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) ∧
      (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s) := by
  classical
  -- L11 clamp: `clampT t ∈ [0,T]` for every `t`, and `clampT t = t` on `[0,T]`.
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t
    simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht
    simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  have hclampT_cont : Continuous clampT := by
    simp only [hclampT_def]
    exact continuous_const.max (continuous_id.min continuous_const)
  -- Clamped curve `ρ' := ρ ∘ clampT`, which satisfies the universal hypotheses.
  set ρ' : ℝ → Measure (PhysSpace d) := fun t => ρ (clampT t) with hρ'_def
  haveI hρ'_prob : ∀ t, IsProbabilityMeasure (ρ' t) :=
    fun t => hρ_prob (clampT t) (hclampT_mem t)
  have h_int' : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' t) :=
    fun t x => h_int (clampT t) (hclampT_mem t) x
  have h_y_int' : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ' t) :=
    fun t => h_y_int (clampT t) (hclampT_mem t)
  have hM_ρ' : ∀ t, ∫ y, ‖y‖ ∂(ρ' t) ≤ M_ρ := fun t => hM_ρ (clampT t) (hclampT_mem t)
  have hρ'_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ' t) x) :=
    fun x => (hρ_cont x).comp_continuous hclampT_cont (fun t => hclampT_mem t)
  -- Apply the universal producer to `ρ'`.
  obtain ⟨charX, charV, hflow', h_bdry'⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL ρ'
      h_int' hρ'_cont h_y_int' M_ρ hM_ρ_nn hM_ρ' T hT.le hTL_PL
  -- On `Ioo`/`Icc 0 T`, `clampT = id` so `ρ' = ρ`: transfer the flow back to `ρ`.
  refine ⟨charX, charV, ⟨hflow'.1, hflow'.2.1, ?_⟩, ?_, ?_, ?_⟩
  · -- velocity ODE for `ρ` on `Ioo 0 T`
    intro t ht z hz
    have h := hflow'.2.2 t ht z hz
    have hρeq : ρ' t = ρ t := by
      simp only [hρ'_def, hclampT_id t (Set.Ioo_subset_Icc_self ht)]
    rwa [hρeq] at h
  · -- initial condition
    intro z
    have h := hflow'.1 z (Set.mem_univ z)
    exact Prod.ext h.1 h.2
  · -- `ContinuousOn` on `Icc 0 T` from the producer's boundary derivatives
    intro z t ht
    obtain ⟨hX, hV⟩ := h_bdry' z t ht
    exact (hX.prodMk hV).continuousWithinAt
  · -- `h_deriv_Ico` (Ici-joint) from the producer's `Icc`-component derivatives
    intro z s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self hs
    obtain ⟨hX, hV⟩ := h_bdry' z s hsIcc
    have hρeq : ρ' s = ρ s := by simp only [hρ'_def, hclampT_id s hsIcc]
    have hpair : HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ' s) (charX s z)))
        (Set.Icc 0 T) s := hX.prodMk hV
    rw [hρeq] at hpair
    -- convert the set `Icc 0 T` to `Ici s` (local subset near `s`, since `s < T`)
    have hmem : Set.Iic ((s + T) / 2) ∈ nhds s := Iic_mem_nhds (by linarith [hs.2])
    have hsub : Set.Ici s ∩ Set.Iic ((s + T) / 2) ⊆ Set.Icc 0 T := by
      rintro u ⟨hu1, hu2⟩
      exact ⟨le_trans hs.1 hu1, le_trans hu2 (by linarith [hs.2])⟩
    exact (hasDerivWithinAt_inter hmem).mp (hpair.mono hsub)

/-! ## Final-step layer (crux-independent): constancy + measure extensionality -/

/-- **C2 #7 — constancy from a vanishing derivative.**

If a real function is continuous on `[0,T]` and has zero derivative throughout the open
interval, its endpoint values agree.  This is the dual argument's payoff step: `s ↦ ∫ ψ_s dμ_s`
is constant, so its value at `T` (= `∫ φ dμ_T`) equals its value at `0` (= `∫ ψ_0 dμ_0`). Mean
value theorem (`exists_hasDerivAt_eq_slope`). -/
lemma transportedIntegral_const_On {h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn h (Set.Icc 0 T))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt h 0 s) :
    h 0 = h T := by
  obtain ⟨c, _hc, hc'⟩ :=
    exists_hasDerivAt_eq_slope h (fun _ => 0) hT hcont (fun s hs => hderiv s hs)
  have hc0 : (0 : ℝ) = (h T - h 0) / (T - 0) := hc'
  rcases div_eq_zero_iff.mp hc0.symm with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 (ne_of_gt (by linarith : (0 : ℝ) < T - 0))

/-- **C2 #9 — `C_c^∞` test functions determine a finite measure.**

If `∫ φ dμ = ∫ φ dν` for every smooth compactly-supported `φ`, then `μ = ν` (finite measures on
phase space).  The dual argument yields equality of integrals against the `IsVlasovSolution` test
class `C_c^∞`; this closes the bridge's final step `f T = g T`.  Route: extend `C_c^∞ →`
bounded-continuous (smooth approximation), then the in-house bounded-continuous extensionality
`ext_of_forall_integral_eq_of_IsFiniteMeasure` (cf. `Wasserstein.lean`). -/
lemma measure_eq_of_forall_Cc_integral_eq {μ ν : Measure (PhaseSpace d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : PhaseSpace d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ z, φ z ∂μ = ∫ z, φ z ∂ν) :
    μ = ν := by
  -- Haar instance on the ambient volume via the product reduction.
  haveI hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  haveI hvolReg : (volume : Measure (PhaseSpace d)).Regular := inferInstance
  haveI hμreg : μ.Regular := inferInstance
  haveI hνreg : ν.Regular := inferInstance
  -- Reduce `μ = ν` to equality of integrals against continuous compactly-supported `g`.
  refine MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported (fun g => ?_)
  set gf : PhaseSpace d → ℝ := ⇑g with hgf
  have hg_cont : Continuous gf := map_continuous g
  have hg_cs : HasCompactSupport gf := CompactlySupportedContinuousMap.hasCompactSupport g
  -- Uniform sup bound on `g`.
  obtain ⟨C, hC⟩ := hg_cont.bounded_above_of_compact_support hg_cs
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- A mollifier family `φ n` with outer radius `2/(n+2) → 0`.
  set φ : ℕ → ContDiffBump (0 : PhaseSpace d) :=
    fun n => ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ
  have hrout : ∀ n, (φ n).rOut = 2 / (n + 2) := fun n => rfl
  have hrout_tendsto : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) := by
    simp only [hrout]
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds)
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  -- The mollified functions.
  set gn : ℕ → PhaseSpace d → ℝ :=
    fun n => convolution ((φ n).normed volume) gf (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgn
  -- Each `gn n` is `C^∞` with compact support, hence covered by the hypothesis `h`.
  have hgn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (gn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left _
      (φ n).contDiff_normed (hg_cont.locallyIntegrable)
  have hgn_cs : ∀ n, HasCompactSupport (gn n) := fun n =>
    HasCompactSupport.convolution _ (φ n).hasCompactSupport_normed hg_cs
  have hgn_eq : ∀ n, ∫ z, gn n z ∂μ = ∫ z, gn n z ∂ν := fun n =>
    h (gn n) (hgn_smooth n) (hgn_cs n)
  -- Pointwise convergence `gn n → gf` (continuous `g`, shrinking bumps).
  have hgn_lim : ∀ x, Filter.Tendsto (fun n => gn n x) Filter.atTop (nhds (gf x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous hrout_tendsto hg_cont x
  -- Uniform bound `‖gn n x‖ ≤ C` (averaging keeps the sup bound).
  have hgn_bound : ∀ n, ∀ x, ‖gn n x‖ ≤ C := by
    intro n x
    rw [hgn]
    simp only
    rw [convolution_lsmul]
    calc ‖∫ t, (φ n).normed volume t • gf (x - t) ∂volume‖
        ≤ ∫ t, ‖(φ n).normed volume t • gf (x - t)‖ ∂volume := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (φ n).normed volume t * C ∂volume := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
          · exact ((φ n).integrable_normed).mul_const C
          · refine Filter.Eventually.of_forall (fun t => ?_)
            simp only
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((φ n).nonneg_normed t)]
            exact mul_le_mul_of_nonneg_left (hC _) ((φ n).nonneg_normed t)
      _ = C := by rw [integral_mul_const, (φ n).integral_normed, one_mul]
  -- DCT: `∫ gn n dμ → ∫ gf dμ` and likewise for `ν`.
  have hconv_μ : Filter.Tendsto (fun n => ∫ z, gn n z ∂μ) Filter.atTop (nhds (∫ z, gf z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => (hgn_smooth n).continuous.aestronglyMeasurable
    · exact integrable_const C
    · exact fun n => Filter.Eventually.of_forall (fun x => hgn_bound n x)
    · exact Filter.Eventually.of_forall hgn_lim
  have hconv_ν : Filter.Tendsto (fun n => ∫ z, gn n z ∂ν) Filter.atTop (nhds (∫ z, gf z ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => (hgn_smooth n).continuous.aestronglyMeasurable
    · exact integrable_const C
    · exact fun n => Filter.Eventually.of_forall (fun x => hgn_bound n x)
    · exact Filter.Eventually.of_forall hgn_lim
  -- The two limits coincide because the prelimit sequences are equal.
  have hμν : Filter.Tendsto (fun n => ∫ z, gn n z ∂μ) Filter.atTop (nhds (∫ z, gf z ∂ν)) := by
    simpa only [hgn_eq] using hconv_ν
  exact tendsto_nhds_unique hconv_μ hμν

/-- Convenience extractor: under `[AssW2 W]`, a gradient field `gradW = ∇W` is `C¹`.

`AssW2.gradContDiff` gives `ContDiff ℝ 1 (fun x => fderiv ℝ W x)`; composing with the (smooth,
linear) Riesz isometry `gradient W x = (toDual ℝ _).symm (fderiv ℝ W x)` and rewriting by `hgradW`
yields `ContDiff ℝ 1 gradW`. -/
lemma assW2_contDiff_gradW (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x) :
    ContDiff ℝ 1 gradW := by
  have heq : gradW =
      fun x => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm (fderiv ℝ W x) := by
    funext x; rw [hgradW]; rfl
  rw [heq]
  have hriesz : ContDiff ℝ 1 fun u => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm u :=
    (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.toContinuousLinearEquiv.contDiff
  exact hriesz.comp ‹AssW2 W›.gradContDiff

/-! ## Crux layer (C3): the variational equation and the dual-transport assembly

The two interfaces below are the load-bearing locks for the bridge.  `#3` is the genuine research
gap (C¹ dependence of an ODE flow on its initial point — absent from Mathlib); `#8` is the
bridge-specific dual-transported-test-function assembly that consumes it.  `#10` (the public
theorem) composes the proven reuse layer (`exists_frozenField_charFlow_On`, #2) with `#8`.

The dual-argument *internals* `#4`/`#5`/`#6` (test-class enlargement `C_c^∞ → C¹_c`, the
transported test function `ψ_s = φ ∘ Φ_{s→t}` and its transport identity, and the zero-derivative
of `s ↦ ∫ ψ_s dμ_s`) are **deliberately not locked as Lean signatures here** (P5): their exact
shapes depend on the two-time-flow representation `Φ_{s→t}` and the mollification regularity, both
C3-open design choices to be fixed by atom-level reading at the grind.  They are documented in
`#8`'s proof plan; only `#3` (route-independent conclusion) and `#8` (stable predicates) are
locked. -/

/-- **C3 F1 — the convolution force field is `C¹` in space (Fréchet derivative under the
integral).**  For `gradW ∈ C¹` (and `L`-Lipschitz, a probability measure `ρ` with the kernel
integrable), `x ↦ ∫ y, gradW (x − y) ∂ρ` is Fréchet-differentiable with derivative
`∫ y, fderiv ℝ gradW (x₀ − y) ∂ρ`.  This is the field-regularity foundation of the variational
equation (#3): it makes `D_z (vlasovVectorField …)` exist and continuous, so the variational ODE
`Ṁ = (D_z b)·M` has continuous coefficients.

Differentiation under the integral sign (`hasFDerivAt_integral_of_dominated_loc_of_lip`): the
per-fibre map `x ↦ gradW (x − y)` is `L`-Lipschitz (a uniform, integrable bound against a
probability measure) and differentiable, so the parametric integral differentiates with derivative
the integral of the fibrewise derivatives. -/
theorem convolveFunctionMeasure_hasFDerivAt
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ)
    (x₀ : PhysSpace d) :
    HasFDerivAt (fun x => convolveFunctionMeasure gradW ρ x)
      (∫ y, fderiv ℝ gradW (x₀ - y) ∂ρ) x₀ := by
  have hdiff : Differentiable ℝ gradW := hgradW_C1.differentiable one_ne_zero
  have hfderiv_cont : Continuous (fun z => fderiv ℝ gradW z) :=
    hgradW_C1.continuous_fderiv one_ne_zero
  have key := hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := ρ) (s := (Set.univ : Set (PhysSpace d))) (x₀ := x₀)
    (F := fun x y => gradW (x - y))
    (F' := fun y => fderiv ℝ gradW (x₀ - y))
    (bound := fun _ => (L : ℝ))
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x =>
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (h_int x₀)
    ((hfderiv_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun a => ?_)
  · have h2 := key.2
    simpa only [convolveFunctionMeasure] using h2
  · -- h_lip: `fun x => gradW (x - a)` is `L`-Lipschitz, hence `LipschitzOnWith (nnabs L)` on univ
    have hLip : LipschitzWith L (fun x : PhysSpace d => gradW (x - a)) := by
      refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      have hd : dist (x - a) (y - a) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
      calc dist (gradW (x - a)) (gradW (y - a))
          ≤ (L : ℝ) * dist (x - a) (y - a) := hL.dist_le_mul _ _
        _ = (L : ℝ) * dist x y := by rw [hd]
    rw [Real.nnabs_coe L]
    exact hLip.lipschitzOnWith
  · -- h_diff: `HasFDerivAt (fun x => gradW (x - a)) (fderiv ℝ gradW (x₀ - a)) x₀`
    have h1 : HasFDerivAt gradW (fderiv ℝ gradW (x₀ - a)) (x₀ - a) :=
      (hdiff (x₀ - a)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : PhysSpace d => x - a)
        (ContinuousLinearMap.id ℝ (PhysSpace d)) x₀ :=
      (hasFDerivAt_id x₀).sub_const a
    have hc := h1.comp x₀ h2
    simpa using hc

/-- **C3 F2 — the Vlasov field is `C¹` in the phase-space variable, with the block Jacobian.**
At fixed time `t`, `vlasovVectorField gradW ρ t = fun (x,v) ↦ (v, −conv(x))` is
Fréchet-differentiable in `z = (x,v)` with derivative the block continuous-linear map
`δ ↦ (δ.2, −(D_x conv)(δ.1))`, where `D_x conv = ∫ y, fderiv ℝ gradW (z.1 − y) ∂(ρ t)` (F1).
This is the coefficient `A(t) := D_z b(t, Φ_t z)` of the variational ODE `Ṁ = A(t)·M`. -/
theorem vlasovVectorField_hasFDerivAt_in_z
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (t : ℝ) (z : PhaseSpace d) :
    HasFDerivAt (vlasovVectorField gradW ρ t)
      ((ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) z := by
  have hconv : HasFDerivAt (fun x => convolveFunctionMeasure gradW (ρ t) x)
      (∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)) z.1 :=
    convolveFunctionMeasure_hasFDerivAt gradW hgradW_C1 L hL (ρ t) (h_int t) z.1
  have hfst : HasFDerivAt (fun w : PhaseSpace d => w.1)
      (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)) z :=
    (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : PhaseSpace d => w.2)
      (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)) z :=
    (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : PhaseSpace d => convolveFunctionMeasure gradW (ρ t) w.1)
      ((∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))) z :=
    hconv.comp z hfst
  have hprod := h1.prodMk h2.neg
  simpa only [vlasovVectorField] using hprod

/-- **C3 F1c — the convolution derivative is continuous in space.**  `x ↦ ∫ y, fderiv ℝ gradW
(x − y) ∂ρ` (the Fréchet derivative of the convolution field, F1) is continuous, by dominated
convergence: the integrand is continuous in `x` and bounded by `‖fderiv gradW‖ ≤ L` (a constant,
integrable against the probability measure `ρ`).  Continuity of the variational coefficient
`A(t)` in its spatial argument — half of the `t`-continuity of `A` (the other half is the
measure-curve regularity `t ↦ ρ t`, supplied at the V1c ODE-existence step). -/
theorem convolveFunctionMeasure_fderiv_continuous
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ] :
    Continuous (fun x => ∫ y, fderiv ℝ gradW (x - y) ∂ρ) := by
  have hfderiv_cont : Continuous (fun z => fderiv ℝ gradW z) :=
    hgradW_C1.continuous_fderiv one_ne_zero
  refine continuous_of_dominated
    (F := fun x y => fderiv ℝ gradW (x - y)) (bound := fun _ => (L : ℝ)) ?_ ?_ ?_ ?_
  · intro x
    exact (hfderiv_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hL)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun y =>
      hfderiv_cont.comp (continuous_id.sub continuous_const))

/-- Picard iterates for the linear IVP `ẋ = 𝒜(t)x`, `x(0)=x₀` (the V1c engine):
`I₀ ≡ x₀`, `I_{n+1}(t) = ∫₀ᵗ 𝒜(s)(Iₙ(s)) ds`. -/
noncomputable def picardIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) : ℕ → ℝ → E
  | 0, _ => x₀
  | (n + 1), t => ∫ s in (0:ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s)

@[simp] lemma picardIter_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (t : ℝ) : picardIter 𝒜 x₀ 0 t = x₀ := rfl

lemma picardIter_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (n : ℕ) (t : ℝ) :
    picardIter 𝒜 x₀ (n + 1) t = ∫ s in (0:ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s) := rfl

/-- **C3 V1c-engine — the Picard iterates are continuous and satisfy the geometric
`(Kt)ⁿ/n!`-bound on `[0,T]`.**  Proved by simultaneous induction (continuity feeds
integrability, which feeds the next bound).  This `Σ (KT)ⁿ/n! = e^{KT}`-summable bound is the
convergence driver for the V1c fixed point. -/
lemma picardIter_continuousOn_and_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E)
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T))
    (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K) :
    ∀ n, ContinuousOn (picardIter 𝒜 x₀ n) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, ‖picardIter 𝒜 x₀ n t‖ ≤ (K * t) ^ n / n.factorial * ‖x₀‖ := by
  intro n
  induction n with
  | zero =>
    refine ⟨continuousOn_const, fun t ht => ?_⟩
    simp
  | succ n ih =>
    obtain ⟨ih_cont, ih_bd⟩ := ih
    have hg_cont : ContinuousOn (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (Set.Icc 0 T) :=
      hcont𝒜.clm_apply ih_cont
    have hg_int : IntegrableOn (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (Set.Icc 0 T) :=
      hg_cont.integrableOn_Icc
    refine ⟨?_, ?_⟩
    · have hcp := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
        (f := fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (by rw [Set.uIcc_of_le hT]; exact hg_int)
      rw [Set.uIcc_of_le hT] at hcp
      exact hcp
    · intro t ht
      have ht0 : (0:ℝ) ≤ t := ht.1
      have htT : t ≤ T := ht.2
      have h_ptwise : ∀ s ∈ Set.Icc (0:ℝ) t,
          ‖𝒜 s (picardIter 𝒜 x₀ n s)‖ ≤ K * (K * s) ^ n / n.factorial * ‖x₀‖ := by
        intro s hs
        have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, le_trans hs.2 htT⟩
        calc ‖𝒜 s (picardIter 𝒜 x₀ n s)‖
            ≤ ‖𝒜 s‖ * ‖picardIter 𝒜 x₀ n s‖ := (𝒜 s).le_opNorm _
          _ ≤ K * ((K * s) ^ n / n.factorial * ‖x₀‖) :=
              mul_le_mul (hbound𝒜 s hsT) (ih_bd s hsT) (norm_nonneg _) hK
          _ = K * (K * s) ^ n / n.factorial * ‖x₀‖ := by ring
      have hRHS_int : IntervalIntegrable
          (fun s => K * (K * s) ^ n / n.factorial * ‖x₀‖) volume 0 t :=
        (Continuous.intervalIntegrable (by fun_prop) 0 t)
      have hLHS_int : IntervalIntegrable
          (fun s => ‖𝒜 s (picardIter 𝒜 x₀ n s)‖) volume 0 t := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le ht0]
        exact (hg_cont.mono (Set.Icc_subset_Icc_right htT)).norm
      calc ‖picardIter 𝒜 x₀ (n + 1) t‖
          = ‖∫ s in (0:ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s)‖ := by rw [picardIter_succ]
        _ ≤ ∫ s in (0:ℝ)..t, ‖𝒜 s (picardIter 𝒜 x₀ n s)‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht0
        _ ≤ ∫ s in (0:ℝ)..t, K * (K * s) ^ n / n.factorial * ‖x₀‖ :=
            intervalIntegral.integral_mono_on ht0 hLHS_int hRHS_int h_ptwise
        _ = (K * t) ^ (n + 1) / (n + 1).factorial * ‖x₀‖ := by
            have hpow : ∀ s : ℝ, K * (K * s) ^ n / n.factorial * ‖x₀‖
                = (K ^ (n + 1) * ‖x₀‖ / n.factorial) * s ^ n := by
              intro s; rw [mul_pow]; ring
            simp_rw [hpow]
            rw [intervalIntegral.integral_const_mul, integral_pow]
            rw [Nat.factorial_succ]
            push_cast
            rw [mul_pow]
            field_simp
            ring

/-- **C3 V1c-conv — the Dyson sum `M := ∑ₙ Iₙ` is continuous on `[0,T]`.**  Weierstrass M-test:
the terms are dominated by the summable majorant `(KT)ⁿ/n!·‖x₀‖`, so the series converges
uniformly; the uniform limit of the continuous partial sums is continuous.  (`M` is the candidate
solution: `M = x₀ + ∫₀ᵗ 𝒜(s)(M s) ds`, proved next.) -/
lemma picardSum_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K) :
    ContinuousOn (fun t => ∑' n, picardIter 𝒜 x₀ n t) (Set.Icc 0 T) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hbd : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) T →
      ‖picardIter 𝒜 x₀ n t‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n t ht
    refine le_trans ((hcb n).2 t ht) ?_
    have hKt : 0 ≤ K * t := mul_nonneg hK ht.1
    have hle : K * t ≤ K * T := mul_le_mul_of_nonneg_left ht.2 hK
    gcongr
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hunif : TendstoUniformlyOn
      (fun (u : Finset ℕ) (t : ℝ) => ∑ n ∈ u, picardIter 𝒜 x₀ n t)
      (fun t => ∑' n, picardIter 𝒜 x₀ n t) Filter.atTop (Set.Icc 0 T) :=
    tendstoUniformlyOn_tsum hsum hbd
  refine hunif.continuousOn ?_
  exact (Filter.Eventually.of_forall
    (fun u => continuousOn_finset_sum u (fun n _ => (hcb n).1))).frequently

/-- **C3 V1c-rec — finite Picard recurrence.**  The `(N+1)`-th partial Dyson sum equals
`x₀ + ∫₀ᵗ 𝒜(s)(Sₙ(s)) ds`, where `Sₙ = ∑_{n<N} Iₙ`.  Only finite-sum swaps
(`integral_finset_sum`, `map_sum`); no infinite interchange.  Passing `N → ∞` against the
uniform convergence (`picardSum_continuousOn`'s M-test) yields the integral equation for `M`. -/
lemma picardSum_finset_recurrence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K)
    (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) :
    ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t
      = x₀ + ∫ s in (0:ℝ)..t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hint : ∀ n, IntervalIntegrable
      (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) volume 0 t := by
    intro n
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.1]
    exact (hcont𝒜.clm_apply (hcb n).1).mono (Set.Icc_subset_Icc_right ht.2)
  rw [Finset.sum_range_succ', picardIter_zero]
  simp only [picardIter_succ]
  rw [add_comm]
  congr 1
  rw [← intervalIntegral.integral_finset_sum (fun i _ => hint i)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact (map_sum (𝒜 s) (fun i => picardIter 𝒜 x₀ i s) (Finset.range N)).symm

/-- **C3 V1c-inteq — the Dyson sum solves the integral equation.**
`M(t) = x₀ + ∫₀ᵗ 𝒜(s)(M s) ds` on `[0,T]`, where `M = ∑'ₙ Iₙ`.  Pass `N → ∞` in the finite
recurrence: LHS → `M t` (partial sums of the summable series); RHS via DCT (the terms
`𝒜(s)(S_N s) → 𝒜(s)(M s)` pointwise, dominated by the constant `K·∑'ₙ (KT)ⁿ/n!·‖x₀‖`). -/
lemma picardSum_solves_integralEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) :
    (∑' n, picardIter 𝒜 x₀ n t)
      = x₀ + ∫ s in (0:ℝ)..t, 𝒜 s (∑' n, picardIter 𝒜 x₀ n s) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have ht0 : (0:ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hmaj : ∀ n, ∀ s ∈ Set.Icc (0:ℝ) T,
      ‖picardIter 𝒜 x₀ n s‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n s hs
    refine le_trans ((hcb n).2 s hs) ?_
    have hKs : 0 ≤ K * s := mul_nonneg hK hs.1
    have hle : K * s ≤ K * T := mul_le_mul_of_nonneg_left hs.2 hK
    gcongr
  have hmaj_summable : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hsummable : ∀ s ∈ Set.Icc (0:ℝ) T, Summable (fun n => picardIter 𝒜 x₀ n s) := by
    intro s hs
    exact (hmaj_summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hmaj n s hs)).of_norm
  set C : ℝ := ∑' n, (K * T) ^ n / n.factorial * ‖x₀‖ with hC
  have hSbound : ∀ N, ∀ s ∈ Set.Icc (0:ℝ) T,
      ‖∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s‖ ≤ C := by
    intro N s hs
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n _ => hmaj n s hs)) ?_
    exact hmaj_summable.sum_le_tsum _ (fun n _ => by positivity)
  set M : ℝ → E := fun u => ∑' n, picardIter 𝒜 x₀ n u with hM
  have hLHS : Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t)
      Filter.atTop (nhds (M t)) :=
    ((hsummable t ht).hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hRHS_int : Filter.Tendsto
      (fun N => ∫ s in Set.Ioc (0:ℝ) t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s))
      Filter.atTop (nhds (∫ s in Set.Ioc (0:ℝ) t, 𝒜 s (M s))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun _ => K * C)
    · intro N
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
      exact (hcont𝒜.clm_apply (continuousOn_finset_sum _ (fun n _ => (hcb n).1))).mono
        (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT))
    · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
    · intro N
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
      calc ‖𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s)‖
          ≤ ‖𝒜 s‖ * ‖∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s‖ := (𝒜 s).le_opNorm _
        _ ≤ K * C := mul_le_mul (hbound𝒜 s hsT) (hSbound N s hsT) (norm_nonneg _) hK
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
      exact ((𝒜 s).continuous.tendsto (M s)).comp ((hsummable s hsT).hasSum.tendsto_sum_nat)
  rw [intervalIntegral.integral_of_le ht0]
  have hrec' : ∀ N, ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t
      = x₀ + ∫ s in Set.Ioc (0:ℝ) t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s) := by
    intro N
    rw [picardSum_finset_recurrence 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜 N t ht,
      intervalIntegral.integral_of_le ht0]
  exact tendsto_nhds_unique hLHS ((hRHS_int.const_add x₀).congr (fun N => (hrec' N).symm))

/-- **C3 V1c — existence for a linear ODE with continuous coefficients on a compact interval**
(the fundamental solution of the variational equation; a Mathlib gap).

For a continuous family of bounded linear maps `𝒜 : ℝ → (E →L[ℝ] E)` on a Banach space `E`, the
linear IVP `ẋ = 𝒜(t) x`, `x(0) = x₀` has a solution on `[0,T]`.  Generic and reusable
(promotable to `Mathlib/Analysis/ODE/`); instantiated for the variational equation with
`E := PhaseSpace d →L[ℝ] PhaseSpace d`, `𝒜(t) := (·).comp-by A(t)` (left composition), `x₀ := id`
to produce the fundamental matrix `M(t)`, where `A(t) = vlasovVectorField_hasFDerivAt_in_z`'s
block CLM evaluated along the flow.

**Why not Mathlib's `IsPicardLindelof`**: that needs a *globally bounded* field
(`norm_le : ‖f t x‖ ≤ L`); the linear field `x ↦ 𝒜(t) x` is unbounded, and confining to a ball
makes the Picard window-condition `K·e^{KT}·T ≤ e^{KT}−1` fail for a single window (⇒ tiling).

**Proof plan (integral-operator contraction, no tiling)**: on the Banach space
`C([0,T]; E)` the Picard operator `𝒯[M](t) := x₀ + ∫_0^t 𝒜(s) (M s) ds` is `K·T`-Lipschitz
(`K := sup_{[0,T]} ‖𝒜‖`, finite by continuity on the compact `[0,T]`), and its `n`-th iterate is
`(K·T)^n/n!`-Lipschitz (induction on the Bochner-integral bound), which is `< 1` for large `n`;
so `𝒯` has a unique fixed point by the iterated-contraction Banach theorem
(`ContractingWith` + `exists_fixedPoint`, `Mathlib/Topology/MetricSpace/Contracting.lean`).
Differentiating the fixed-point integral equation (FTC, `HasDerivWithinAt` of `t ↦ ∫_0^t …`)
recovers `ẋ = 𝒜(t) x`; `x(0) = x₀` from the lower integral limit. -/
theorem exists_linearODE_solution_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (T : ℝ) (hT : 0 ≤ T)
    (h𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (x₀ : E) :
    ∃ M : ℝ → E, M 0 = x₀ ∧ ContinuousOn M (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt M (𝒜 t (M t)) (Set.Icc 0 T) t := by
  obtain ⟨K, hbK⟩ := isCompact_Icc.exists_bound_of_continuousOn h𝒜
  have hK'0 : 0 ≤ max K 0 := le_max_right _ _
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) T, ‖𝒜 t‖ ≤ max K 0 :=
    fun t ht => le_trans (hbK t ht) (le_max_left _ _)
  set M : ℝ → E := fun u => ∑' n, picardIter 𝒜 x₀ n u with hM
  have hMcont : ContinuousOn M (Set.Icc 0 T) :=
    picardSum_continuousOn 𝒜 x₀ T hT (max K 0) hK'0 h𝒜 hbound
  have hMeq : ∀ t ∈ Set.Icc (0:ℝ) T, M t = x₀ + ∫ s in (0:ℝ)..t, 𝒜 s (M s) :=
    fun t ht => picardSum_solves_integralEq 𝒜 x₀ T hT (max K 0) hK'0 h𝒜 hbound t ht
  have hg_cont : ContinuousOn (fun s => 𝒜 s (M s)) (Set.Icc 0 T) := h𝒜.clm_apply hMcont
  refine ⟨M, ?_, hMcont, fun t ht => ?_⟩
  · rw [hMeq 0 ⟨le_refl 0, hT⟩, intervalIntegral.integral_same, add_zero]
  · haveI : Fact (t ∈ Set.Icc (0:ℝ) T) := ⟨ht⟩
    have hg_int : IntervalIntegrable (fun s => 𝒜 s (M s)) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]
      exact hg_cont.mono (Set.Icc_subset_Icc_right ht.2)
    have hg_meas : StronglyMeasurableAtFilter (fun s => 𝒜 s (M s)) (nhdsWithin t (Set.Icc 0 T)) :=
      ⟨Set.Icc 0 T, self_mem_nhdsWithin, hg_cont.aestronglyMeasurable measurableSet_Icc⟩
    have hFTC : HasDerivWithinAt (fun u => ∫ s in (0:ℝ)..u, 𝒜 s (M s)) (𝒜 t (M t))
        (Set.Icc 0 T) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hg_int hg_meas (hg_cont t ht)
    exact (hFTC.const_add x₀).congr (fun y hy => hMeq y hy) (hMeq t ht)

/-- **C3 V1c→matrix — the fundamental matrix of a linear ODE.**  Specialising
`exists_linearODE_solution_Icc` to the operator space `E := F →L[ℝ] F` with `𝒜(s) := A(s) ∘ (·)`
(left composition) and `x₀ := id` gives the fundamental solution `Ṁ = A(t)∘M`, `M(0) = id`.
This `M(t)` is the candidate `Dflow t z` of the variational equation (#3), once `A` is the Vlasov
field Jacobian `A(s) = D_z b(s, Φ_s z)` along the flow (F2). -/
lemma exists_fundamentalMatrix
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Set.Icc 0 T)) :
    ∃ M : ℝ → (F →L[ℝ] F), M 0 = ContinuousLinearMap.id ℝ F ∧ ContinuousOn M (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt M ((A t).comp (M t)) (Set.Icc 0 T) t := by
  obtain ⟨M, hM0, hMcont, hMderiv⟩ := exists_linearODE_solution_Icc
    (fun s => ContinuousLinearMap.compL ℝ F F F (A s)) T hT
    ((ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ F)
  refine ⟨M, hM0, hMcont, fun t ht => ?_⟩
  simpa [ContinuousLinearMap.compL_apply] using hMderiv t ht

/-- **C3 A-cont — the variational coefficient `A(s,z) = D_z b(s, Φ_s z)` is continuous in `s`.**
`A(s,z)` is the F2 block CLM `(snd).prod(−(∫ fderiv gradW (charX s z − y) ∂ρ_s) ∘ fst)`; its only
`s`-varying part is the convolution-derivative integral, continuous via `hρD_cont` composed with
the flow.  The block CLM is reassembled with `inl∘snd + inr∘(·)` (Mathlib has no `clm_prod`
continuity combinator).  This `ContinuousOn` is the coefficient input to `exists_fundamentalMatrix`
that produces the fundamental matrix `M_t(z) = Dflow t z` for `#3`. -/
lemma vlasovVariationalCoeff_continuousOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (z : PhaseSpace d)
    (hcontIcc : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0:ℝ) T))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ContinuousOn (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
      (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
          (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) (Set.Icc 0 T) := by
  have hX : ContinuousOn (fun s => charX s z) (Set.Icc (0:ℝ) T) :=
    continuous_fst.comp_continuousOn hcontIcc
  have hpair : ContinuousOn (fun s => ((s, charX s z) : ℝ × PhysSpace d)) (Set.Icc (0:ℝ) T) :=
    continuousOn_id.prodMk hX
  have hmaps : Set.MapsTo (fun s => ((s, charX s z) : ℝ × PhysSpace d))
      (Set.Icc (0:ℝ) T) (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun s hs => ⟨hs, Set.mem_univ _⟩
  have hD : ContinuousOn (fun s => ∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)) (Set.Icc 0 T) :=
    hρD_cont.comp hpair hmaps
  have hDcomp : ContinuousOn (fun s => -((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
      (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T) :=
    (hD.clm_comp continuousOn_const).neg
  have heq : (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))))
      = (fun s => (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
            (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
          + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
            (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
                (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) := by
    funext s; ext x <;> simp
  rw [heq]
  exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)

/-- **C3 D1 (Jacobian).**  The phase-space Jacobian `A(s, p) = D_w b(s, p)` of the frozen Vlasov
field at the base point `p`: the block continuous-linear map `δ ↦ (δ.2, −(D_x conv ρ_s)(p.1)·δ.1)`,
where `D_x conv ρ_s (p.1) = ∫ y, fderiv ℝ gradW (p.1 − y) ∂ρ_s` (F1).  This is the coefficient of
the linear variational ODE `Ṁ = A(s, Φ_s z)·M`; `vlasovVectorField_hasFDerivAt_in_z` (F2) says it
is the Fréchet derivative of `vlasovVectorField gradW ρ s` at `p.2`. -/
noncomputable def vlasovFieldJacobian (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d)) (p : ℝ × PhaseSpace d) : PhaseSpace d →L[ℝ] PhaseSpace d :=
  (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
    (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))

/-- **C3 D1a — the uniform-over-compact first-order Taylor remainder of the Vlasov field.**

For a fixed initial point `z`, the first-order remainder of the frozen field `b(s,·)` at the moving
base point `Φ_s z := (charX s z, charV s z)`,
`R(s,w) = b(s,w) − b(s,Φ_s z) − A(s,Φ_s z)·(w − Φ_s z)`, is `o(‖w − Φ_s z‖)` **uniformly in
`s ∈ [0,T]`**: for every `η > 0` there is a single `δ > 0` (independent of `s`) with
`‖R(s,w)‖ ≤ η·‖w − Φ_s z‖` whenever `‖w − Φ_s z‖ ≤ δ`.

This uniformity is the load-bearing analytic core of D1 (the variational-equation difference
quotient): it is what lets Grönwall bound `Φ_t(z+h) − Φ_t(z) − M_t(z)·h` by `o(‖h‖)` *uniformly
along the trajectory*.  Proof: the flow image `{Φ_s z : s ∈ [0,T]}` is compact (continuous image of
`[0,T]`), `A = D_w b` is jointly `(s,w)`-continuous (from `hρD_cont`), so `A` is **uniformly**
continuous on the compact tube `Γ = {(s, Φ_s z + e) : s ∈ [0,T], ‖e‖ ≤ 1}` (Heine–Cantor); the
mean-value inequality on `closedBall (Φ_s z) δ` then converts the modulus into the remainder
bound. -/
lemma vlasovField_taylorRemainder_uniform
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (z : PhaseSpace d)
    (hcontIcc : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0:ℝ) T))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Icc (0:ℝ) T, ∀ w : PhaseSpace d,
      ‖w - (charX s z, charV s z)‖ ≤ δ →
      ‖vlasovVectorField gradW ρ s w - vlasovVectorField gradW ρ s (charX s z, charV s z)
        - (vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z))) (w - (charX s z, charV s z))‖
        ≤ η * ‖w - (charX s z, charV s z)‖ := by
  set Φ : ℝ → PhaseSpace d := fun s => (charX s z, charV s z) with hΦ
  -- F2: the field is differentiable in the phase variable with derivative `vlasovFieldJacobian`.
  have hF2 : ∀ s (w : PhaseSpace d),
      HasFDerivAt (vlasovVectorField gradW ρ s) (vlasovFieldJacobian gradW ρ (s, w)) w :=
    fun s w => vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s w
  -- Joint continuity of the Jacobian on `Icc 0 T ×ˢ Set.univ` (from `hρD_cont`).
  have hg_cont : Continuous (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hD2 : ContinuousOn
      (fun p : ℝ × PhaseSpace d => ∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    hρD_cont.comp hg_cont.continuousOn hmaps
  have hDcomp : ContinuousOn
      (fun p : ℝ × PhaseSpace d => -((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T ×ˢ Set.univ) :=
    (hD2.clm_comp continuousOn_const).neg
  have heq : (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p) = fun p =>
        (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
          (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
        + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
          (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
              (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) := by
    funext p; ext x <;> simp [vlasovFieldJacobian]
  have hAj_cont : ContinuousOn (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p)
      (Set.Icc 0 T ×ˢ Set.univ) := by
    rw [heq]; exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)
  -- The compact tube `Γ = {(s, Φ s + e) : s ∈ [0,T], ‖e‖ ≤ 1}`.
  set ball1 : Set (PhaseSpace d) := Metric.closedBall 0 1 with hball1
  have hmap : ContinuousOn (fun q : ℝ × PhaseSpace d => ((q.1, Φ q.1 + q.2) : ℝ × PhaseSpace d))
      (Set.Icc 0 T ×ˢ ball1) :=
    continuousOn_fst.prodMk ((hcontIcc.comp continuousOn_fst (fun q hq => hq.1)).add continuousOn_snd)
  set Γ : Set (ℝ × PhaseSpace d) :=
    (fun q : ℝ × PhaseSpace d => ((q.1, Φ q.1 + q.2) : ℝ × PhaseSpace d)) '' (Set.Icc 0 T ×ˢ ball1)
    with hΓ
  have hΓcompact : IsCompact Γ :=
    (isCompact_Icc.prod (isCompact_closedBall 0 1)).image_of_continuousOn hmap
  have hΓsub : Γ ⊆ Set.Icc 0 T ×ˢ Set.univ := by
    rintro _ ⟨q, hq, rfl⟩; exact ⟨hq.1, Set.mem_univ _⟩
  have hUC : UniformContinuousOn (fun p => vlasovFieldJacobian gradW ρ p) Γ :=
    hΓcompact.uniformContinuousOn_of_continuous (hAj_cont.mono hΓsub)
  have hmemΓ : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ e : PhaseSpace d, ‖e‖ ≤ 1 →
      ((s, Φ s + e) : ℝ × PhaseSpace d) ∈ Γ := by
    intro s hs e he
    exact ⟨(s, e), ⟨hs, by simpa [hball1, Metric.mem_closedBall, dist_eq_norm] using he⟩, rfl⟩
  -- Extract the uniform-continuity modulus.
  intro η hη
  obtain ⟨δ₀, hδ₀, H⟩ := Metric.uniformContinuousOn_iff_le.mp hUC η hη
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, ?_⟩
  intro s hs w hw
  -- Mean value on the convex ball `C = closedBall (Φ s) (min δ₀ 1)`.
  set C : Set (PhaseSpace d) := Metric.closedBall (Φ s) (min δ₀ 1) with hC
  have hΦmem : Φ s ∈ C := Metric.mem_closedBall_self (le_min hδ₀.le zero_le_one)
  have hwmem : w ∈ C := by
    rw [hC, Metric.mem_closedBall, dist_eq_norm]; exact hw
  -- The fderiv bound on `C` from uniform continuity.
  have hbound : ∀ w' ∈ C,
      ‖vlasovFieldJacobian gradW ρ (s, w') - vlasovFieldJacobian gradW ρ (s, Φ s)‖ ≤ η := by
    intro w' hw'
    have hw'norm : ‖w' - Φ s‖ ≤ min δ₀ 1 := by
      rw [← dist_eq_norm]; rw [hC, Metric.mem_closedBall] at hw'; exact hw'
    have hw'le1 : ‖w' - Φ s‖ ≤ 1 := hw'norm.trans (min_le_right _ _)
    have hmem1 : ((s, w') : ℝ × PhaseSpace d) ∈ Γ := by
      have := hmemΓ s hs (w' - Φ s) hw'le1
      rwa [add_sub_cancel] at this
    have hmem2 : ((s, Φ s) : ℝ × PhaseSpace d) ∈ Γ := by
      have := hmemΓ s hs 0 (by simp)
      rwa [add_zero] at this
    have hdist : dist ((s, w') : ℝ × PhaseSpace d) (s, Φ s) ≤ δ₀ := by
      rw [Prod.dist_eq]
      simp only [dist_self, max_le_iff]
      refine ⟨hδ₀.le, ?_⟩
      rw [dist_eq_norm]; exact hw'norm.trans (min_le_left _ _)
    have := H _ hmem1 _ hmem2 hdist
    rwa [dist_eq_norm] at this
  -- Apply the mean value inequality to `g u = b(s,u) − A(s,Φ s)·u`.
  have hg : ∀ w' ∈ C, HasFDerivWithinAt
      (fun u => vlasovVectorField gradW ρ s u - vlasovFieldJacobian gradW ρ (s, Φ s) u)
      (vlasovFieldJacobian gradW ρ (s, w') - vlasovFieldJacobian gradW ρ (s, Φ s)) C w' := by
    intro w' _
    have h1 := hF2 s w'
    have h2 : HasFDerivAt (fun u => vlasovFieldJacobian gradW ρ (s, Φ s) u)
        (vlasovFieldJacobian gradW ρ (s, Φ s)) w' :=
      (vlasovFieldJacobian gradW ρ (s, Φ s)).hasFDerivAt
    exact (h1.sub h2).hasFDerivWithinAt
  have hmv := (convex_closedBall (Φ s) (min δ₀ 1)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hg hbound hΦmem hwmem
  -- Rewrite `g w − g (Φ s)` as the remainder.
  have hReq : (vlasovVectorField gradW ρ s w - vlasovFieldJacobian gradW ρ (s, Φ s) w)
        - (vlasovVectorField gradW ρ s (Φ s) - vlasovFieldJacobian gradW ρ (s, Φ s) (Φ s))
      = vlasovVectorField gradW ρ s w - vlasovVectorField gradW ρ s (Φ s)
        - vlasovFieldJacobian gradW ρ (s, Φ s) (w - Φ s) := by
    rw [map_sub]; abel
  simpa only [hReq] using hmv

/-- **C3 D1 — the difference-quotient heart of the variational equation.**

Given the fundamental matrix `Mz` of the linear variational ODE `Ṁ = A(s, Φ_s z)·M`, `M 0 = id`
(coefficient `A = vlasovFieldJacobian`), the time-`t` flow map `w ↦ (charX t w, charV t w)` is
Fréchet-differentiable **at the fixed point `z`** with derivative exactly `Mz t`.

This is the load-bearing difference-quotient estimate `Φ_t(z+h) − Φ_t(z) − Mz t·h = o(‖h‖)`.
The matrix is threaded as an explicit hypothesis (rather than `choose`-d) so the proof can use its
ODE/continuity data directly.

**Proof plan (route b — Grönwall on the linearisation remainder).**  Reduce via
`hasFDerivAt_iff_isLittleO_nhds_zero` + `Asymptotics.isLittleO_iff` to: `∀ c>0, ∀ᶠ h, ‖Φ_t(z+h) −
Φ_t(z) − Mz t·h‖ ≤ c‖h‖`.  For fixed small `h`, the two curves `u_h(s) := Φ_s(z+h) − Φ_s(z)`
(approximate) and `m_h(s) := Mz s·h` (exact) both solve `ẇ = A(s, Φ_s z)·w` from the same datum
`h` (`Φ_0 = id`, `Mz 0 = id`):
* `m_h` is exact — its defect is `0` (its derivative `(A·Mz)(s)·h = A(s)·m_h(s)` by `hMzderiv` +
  `HasDerivWithinAt.clm_apply`).
* `u_h`'s defect is the Taylor remainder `R(s, Φ_s(z+h))`, bounded by `η·‖u_h(s)‖` (D1a,
  `vlasovField_taylorRemainder_uniform`) once `‖u_h(s)‖ ≤ δ(η)`, which holds with
  `‖u_h(s)‖ ≤ exp(K T)·‖h‖` (flow Lipschitz-in-`z`, `charFlow_lipschitzInZ_via_gronwall_Ioo`) for
  `‖h‖` small.  So `εf = η·exp(K T)·‖h‖`, uniform in `s`.
The frozen field's two-sided ODE holds only on `Ioo 0 T`, so apply
`dist_le_of_approx_trajectories_ODE` on `[s₀, t]` (`s₀ ∈ Ioo 0 t`) and take `s₀ → 0⁺` (the initial
defect `dist(u_h s₀, m_h s₀) → 0` by continuity), giving `‖u_h t − m_h t‖ ≤ gronwallBound 0 K εf t =
εf·(exp(K t)−1)/K`.  Since `η` is arbitrary this is `o(‖h‖)`.  `K := max 1 L` is the uniform field
Lipschitz constant; `‖A(s,·)‖ ≤ K` via `norm_fderiv_le_of_lipschitz`. -/
theorem charFlow_hasFDerivAt_of_fundamentalMatrix
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (z : PhaseSpace d)
    (hcontIcc : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (Mz : ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d))
    (hMz0 : Mz 0 = ContinuousLinearMap.id ℝ (PhaseSpace d))
    (hMzcont : ContinuousOn Mz (Set.Icc 0 T))
    (hMzderiv : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt Mz
        ((vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z))).comp (Mz s))
        (Set.Icc 0 T) s) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, HasFDerivAt (fun w => (charX t w, charV t w)) (Mz t) z := by
  sorry

/-- **C3 #3 — the variational equation (`HasFDerivAt` of the flow in its initial point).**

For the frozen field `b(t,·) = vlasovVectorField gradW ρ t` with `gradW ∈ C¹` (supplied by the
consumer via `assW2_contDiff_gradW`), the time-`t` characteristic map
`z ↦ (charX t z, charV t z)` is Fréchet-differentiable in the initial point `z`, with a derivative
`Dflow t z` that is continuous in `z` (so the flow map is `C¹` in `z`).  The derivative solves the
linear matrix variational ODE `Ṁ = (D_z b(t, Φ_t z)) · M`, `M_0 = id`.

**This is the load-bearing research gap** — Mathlib has no C¹-dependence-of-an-ODE-flow-on-its-
initial-condition lemma.  Intended route (b), to be ground out in the C3 grind session
(`charFlow_lipschitzInZ_via_gronwall_Ioo`, `CharacteristicFlow.lean`, is the Lipschitz-in-`z`
scaffold; Mathlib Gronwall + the vendored `IsPicardLindelof` confinement are the analytic inputs):
3.1 existence/uniqueness of the continuous matrix solution `M_t(z)` of the variational ODE;
3.2 joint `(t,z)` continuity of `M`; 3.3 the difference-quotient estimate
`Φ_t(z+h) − Φ_t(z) − M_t(z)·h = o(‖h‖)` uniformly on compacts (Gronwall on the linearization
remainder, using `gradW ∈ C¹`); 3.4 assemble into `HasFDerivAt`.

The `HasFDerivAt`/continuity *conclusion* is route-independent, so this interface is stable; the
universal-`t` probability instance + force-integrability `h_int` are the field-regularity inputs
the proof consumes (the window-only application clamps, L11, at the grind).

**`hρD_cont` (joint continuity of the convolution-derivative field).**  This is the regularity that
makes the variational coefficient `A(s,z) = D_z b(s, Φ_s z)` continuous in `s` — its only non-flow
varying part is `D_x conv(ρ_s)(x) = ∫ fderiv gradW (x − y) ∂ρ_s`, evaluated at the *moving* point
`Φ_s z`, so per-`x` continuity is not enough; joint `(s,x)`-continuity is needed.  Note the
asymmetry with the *field*: `∫ gradW(x−y) dρ_s` gets joint continuity for free (per-`x` continuity
+ uniform Lipschitz-in-`x`, `convolveFunctionMeasure_lipschitz_in_x`), but the *derivative* field is
NOT uniformly Lipschitz in `x` (that needs `W ∈ C³`; `AssW2` gives only `C²`), so its joint
continuity must be supplied.

**Option-B note (running — eventual extension).**  `hρD_cont` is, in the complete theory, NOT a new
assumption: it is *derivable* from **narrow continuity of `s ↦ ρ_s`** (since `fderiv gradW` is
bounded continuous, `‖·‖ ≤ L`), which is in turn derivable from `IsVlasovSolutionOn` + tightness
(the uniform moment bound) via the standard **"`C_c^∞`-continuity + tight ⟹ narrow-continuity"**
upgrade — a self-contained measure-theory lemma not yet in the codebase.  We thread it as a
hypothesis (Option A) to unblock the variational-equation grind; folding it into a derived fact
(so the bridge assumes only the weak solution + moments) is the **Option-B extension**, tracked as
a follow-up. -/
theorem charFlow_hasFDerivAt_in_initialPoint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0:ℝ) T)) :
    ∃ Dflow : ℝ → PhaseSpace d → (PhaseSpace d →L[ℝ] PhaseSpace d),
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z : PhaseSpace d,
        HasFDerivAt (fun w => (charX t w, charV t w)) (Dflow t z) z) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, Continuous (Dflow t)) := by
  -- **Reduction (banked).**  The fundamental matrix `M z` of the variational ODE `Ṁ = A(s,z)·M`,
  -- `M 0 = id`, exists (`exists_fundamentalMatrix`) because `A(·,z)` is continuous on `[0,T]`
  -- (`vlasovVariationalCoeff_continuousOn`, needing `hcontIcc` + `hρD_cont`); set
  -- `Dflow t z := M z t`.  This reduces #3 to two INDEPENDENT hard cores, D1 and V2.
  -- (`hcontIcc` is the closed-interval flow continuity — supplied by `exists_frozenField_charFlow_On`
  -- at the #8 call site — that the `Ioo`-only `hflow` lacks.)
  have hAcont : ∀ z : PhaseSpace d, ContinuousOn
      (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) (Set.Icc 0 T) :=
    fun z => vlasovVariationalCoeff_continuousOn gradW ρ charX charV T z (hcontIcc z) hρD_cont
  choose M hM0 hMcont hMderiv using
    fun z : PhaseSpace d => exists_fundamentalMatrix
      (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) T hT.le (hAcont z)
  refine ⟨fun t z => M z t, ?_, ?_⟩
  · -- **D1 — the difference-quotient heart** (`charFlow_hasFDerivAt_of_fundamentalMatrix`): the
    -- flow is `HasFDerivAt` at each `z` with derivative the fundamental matrix `M z t`.  Threads the
    -- matrix `M z` and its ODE/continuity data explicitly into the standalone Grönwall lemma.
    intro t ht z
    exact charFlow_hasFDerivAt_of_fundamentalMatrix gradW hgradW_C1 L hL ρ charX charV T hT hflow
      h_int hρD_cont z (hcontIcc z) (M z) (hM0 z) (hMcont z) (hMderiv z) t ht
  · -- **V2 — continuity of the fundamental matrix `z ↦ M z t`**: `A(s,z)` is continuous in `z`
    -- (flow continuity-in-`z` + F1c), and continuity propagates through the V1c Dyson-series
    -- construction (each iterate continuous in `z`; uniform M-test limit).
    intro t ht
    sorry

/-- **C3 #8 — the weak solution equals its frozen-field pushforward on the window** (the dual
transported-test-function assembly; this is where the crux is spent).

Given the frozen-field characteristic flow `(charX, charV)` for `ρ^f := spatialMarginal ∘ f` (as
produced by `exists_frozenField_charFlow_On`, #2), the weak solution `f` coincides on `[0,T]` with
its pushforward `g t := (charX t, charV t)_# (f 0)`.

Proof plan (the dual transported test function `ψ_s(z) := φ(Φ_{s→t}(z))`), deferred to the C4
assembly:
* `g` solves the frozen *linear* weak equation `IsLinearVlasovSolutionOn gradW ρ^f g T`
  (`vlasov_frozenField_pushforward_isLinearVlasovSolutionOn`, #1), and `f` does too via its own
  marginal (`IsVlasovSolutionOn.toLinearSelf`); both share `μ_0 = f 0` (since `Φ_0 = id`, `hinit`).
* The flow is `C¹` in `z` (`charFlow_hasFDerivAt_in_initialPoint`, #3), so for a `C_c^∞` terminal
  test `φ` the transported `ψ_s = φ ∘ Φ_{s→t}` is `C¹_c`; the linear weak equation extends from
  the `C_c^∞` test class to this `C¹_c` test (**#4**, deferred — signature pending the C3-open
  mollification read, P5).
* `ψ_s` carries the transport identity `∂_sψ_s + ⟨b, ∇ψ_s⟩ = 0` (**#5**, deferred — needs the
  two-time flow `Φ_{s→t}`, a C3-open representation choice, P5), so `s ↦ ∫ ψ_s dμ_s` has zero
  derivative on `Ioo 0 t` for both `μ = f` and `μ = g` (**#6**, deferred), hence is constant
  (`transportedIntegral_const_On`, #7).
* Constancy at the endpoints gives `∫ φ d(f t) = ∫ φ ∘ Φ_t d(f 0) = ∫ φ d(g t)` for every
  `C_c^∞ φ`; `measure_eq_of_forall_Cc_integral_eq` (#9) upgrades this to `f t = g t`.

The moment bound `M_ρ` and the flow-boundary data (`hinit`/`hcontIcc`/`hderivIco`) are the inputs
`#1` and the differentiation-under-the-integral steps consume; `hT` is the window non-triviality. -/
theorem weak_eq_frozenField_pushforward_On
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hderivIco : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW (fun t => spatialMarginal (f t)) s (charX s z, charV s z))
        (Set.Ici s) s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) := by
  sorry

/-- **Weak ⟹ Lagrangian on `[0,T]`** (tex: thm:weak-lagrangian).

Under `AssW2` (`W ∈ C²`) and a per-window smallness, every weak Vlasov solution on `[0,T]` with
finite first moments (and the ρ-regularity the frozen-field flow construction needs) is the
pushforward of its initial datum under the characteristic flow it generates — i.e. it is
Lagrangian.  This is the localized, forward-window form matching `vlasovWellPosedness`'s
architecture; the universal form is obtained by window-gluing (deferred).

Hypotheses mirror what `exists_vlasov_characteristicFlow_global_smallT` consumes for the frozen
curve `ρ^f := fun t => spatialMarginal (f t)`.

`hf_cont_deriv` (joint continuity of the convolution-*derivative* field
`∫ fderiv gradW (x−y) ∂ρ^f_s`) is the regularity threaded down to the variational equation (`#3`);
like `hf_cont` it is *assumed* at the bridge boundary (**Option A**).  In the complete theory it is
derivable from `hf_weak` + `hf_mom` (tightness) via a narrow-continuity upgrade — the **Option-B**
extension that would let the bridge assume only the weak solution + moments; see `#3`'s docstring.

Proof (API-locked; body built over C1–C4 per the roadmap above):
freeze the field at `ρ^f`, build its flow `Φ` (#2) and the pushforward `g := (Φ_t)_# (f 0)` which
solves the frozen linear weak eq (#1); show `f = g` by the dual-transported-test-function
uniqueness (#3–#9, the variational-equation crux); conclude `f` is Lagrangian (#10). -/
theorem weak_isLagrangianVlasovSolutionOn
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (hTL_PL : LocalSmallness_PL_buffer L T) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  classical
  -- Frozen field `ρ^f := spatialMarginal ∘ f`: discharge the flow-construction hypotheses of #2.
  have hρ_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (spatialMarginal (f t)) := by
    intro t ht
    haveI : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_y_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f t)) := by
    intro t ht
    haveI : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    unfold spatialMarginal
    rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
    refine Integrable.mono' (hf_mom t ht).2
      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    change |‖z.1‖| ≤ ‖z‖
    rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
  have h_int : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f t)) := by
    intro t ht x_pt
    haveI : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    haveI : IsProbabilityMeasure (spatialMarginal (f t)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal (f t)) :=
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
        (spatialMarginal (f t)) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
          (spatialMarginal (f t)) := (h_y_int t ht).const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  have hρ_cont : ∀ x : PhysSpace d,
      ContinuousOn (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x)
        (Set.Icc (0 : ℝ) T) :=
    fun x => (hf_cont x).continuousOn
  -- #2: build the frozen-field characteristic flow on the window.
  obtain ⟨charX, charV, hflow, hinit, hcontIcc, hderivIco⟩ :=
    exists_frozenField_charFlow_On W gradW hgradW L hL (fun t => spatialMarginal (f t))
      T hT hTL_PL hρ_prob h_int hρ_cont h_y_int M_ρ hM_ρ_nn hM_ρ
  -- #8: `f` equals its frozen-field pushforward on the window (the dual-argument crux).
  have hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) :=
    weak_eq_frozenField_pushforward_On W gradW hgradW L hL f T hT hf_weak hf_mom hf_cont
      hf_cont_deriv M_ρ hM_ρ_nn hM_ρ charX charV hflow hinit hcontIcc hderivIco
  -- Assemble the localized Lagrangian witness.
  refine ⟨hf_weak, charX, charV, hflow, hpush, ?_, hcontIcc⟩
  -- AEMeasurability of the flow at each window time, from the pushforward identity: a
  -- non-measurable map would force `Measure.map _ (f 0) = 0 ≠ f s` (the latter a probability).
  intro s hs
  haveI hfs_prob : IsProbabilityMeasure (f s) := (hf_mom s hs).1
  by_contra hcon
  have h0 : f s = 0 := by
    rw [hpush s hs]; exact Measure.map_of_not_aemeasurable hcon
  have hone : (f s) Set.univ = 1 := measure_univ
  rw [h0] at hone
  simp at hone

end Vlasov
