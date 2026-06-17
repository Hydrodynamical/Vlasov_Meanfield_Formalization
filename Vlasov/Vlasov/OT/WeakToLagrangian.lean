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

/-- **C3 V2-core — the Dyson sum is continuous in a PARAMETER (the V2 ingredient).**  If the
coefficient family `𝒜 : Z → ℝ → (E →L E)` is jointly continuous in `(z, s)` (globally) and
uniformly `K`-bounded on `[0,T]` (with `x₀` constant in `z`), then `z ↦ ∑ₙ Iₙ(z)(t)` is continuous
for each fixed `t ∈ [0,T]`.  This is the parameter analogue of `picardSum_continuousOn`: each
iterate `z ↦ Iₙ(z)(t)` is continuous (joint `(z,s)`-continuity, by induction through the parametric
primitive `continuous_parametric_primitive_of_continuous`), and the M-test majorant `(KT)ⁿ/n!·‖x₀‖`
is **`z`-independent**, so the uniform-in-`z` limit of continuous maps is continuous.  This is what
makes the variational fundamental matrix `z ↦ M z t` continuous (V2) — the property the abstract
`exists_fundamentalMatrix` + `choose` cannot supply (the `choose`'d witness is an arbitrary
fiberwise section; see lesson L14). -/
lemma picardSum_continuous_param
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_cont : Continuous (fun p : Z × ℝ => 𝒜 p.1 p.2))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖𝒜 z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) :
    Continuous (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
  -- (1) joint continuity of each Picard iterate on `Z × ℝ`.
  have hiter_cont : ∀ n, Continuous (fun p : Z × ℝ => picardIter (𝒜 p.1) x₀ n p.2) := by
    intro n
    induction n with
    | zero =>
      simp only [picardIter_zero]
      exact continuous_const
    | succ n ih =>
      have hg : Continuous (Function.uncurry fun z v => 𝒜 z v (picardIter (𝒜 z) x₀ n v)) :=
        h𝒜_cont.clm_apply ih
      have hpp := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := volume) (a₀ := (0:ℝ)) hg
      simp only [picardIter_succ]
      exact hpp
  -- (2) per-`z` slice continuity + the `z`-independent M-test bound.
  have h𝒜cont_z : ∀ z, ContinuousOn (𝒜 z) (Set.Icc (0:ℝ) T) := fun z =>
    (h𝒜_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hbd : ∀ (n : ℕ) (z : Z), z ∈ (Set.univ : Set Z) →
      ‖picardIter (𝒜 z) x₀ n t‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n z _
    have hb := (picardIter_continuousOn_and_bound (𝒜 z) x₀ T hT K hK (h𝒜cont_z z)
      (h𝒜_bound z) n).2 t ht
    refine le_trans hb ?_
    have hKt : (0:ℝ) ≤ K * t := mul_nonneg hK ht.1
    have hle : K * t ≤ K * T := mul_le_mul_of_nonneg_left ht.2 hK
    gcongr
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hsummands_cont : ∀ n, Continuous (fun z => picardIter (𝒜 z) x₀ n t) := fun n =>
    (hiter_cont n).comp (continuous_id.prodMk continuous_const)
  have hunif : TendstoUniformlyOn
      (fun (u : Finset ℕ) (z : Z) => ∑ n ∈ u, picardIter (𝒜 z) x₀ n t)
      (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) Filter.atTop (Set.univ : Set Z) :=
    tendstoUniformlyOn_tsum hsum hbd
  rw [← continuousOn_univ]
  refine hunif.continuousOn ?_
  exact (Filter.Eventually.of_forall
    (fun u => continuousOn_finset_sum u (fun n _ => (hsummands_cont n).continuousOn))).frequently

/-- Window version of `picardSum_continuous_param`: only joint continuity ON `[0,T]` is needed.
The coefficient is clamped into `[0,T]` (`projIcc`, L11) so the global parametric-primitive lemma
applies, then transferred back by agreement of the iterates on `[0,T]` (they only integrate over
`[0,t] ⊆ [0,T]`).  This is the form the variational coefficient `A(s,z) = D_z b(s, Φ_s z)` needs —
it is jointly continuous only on the window `[0,T]` (the flow `Φ_s z` is). -/
lemma picardSum_continuous_param_Icc
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_contOn : ContinuousOn (fun p : Z × ℝ => 𝒜 p.1 p.2) (Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖𝒜 z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) :
    Continuous (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
  set cl : ℝ → ℝ := fun s => ↑(Set.projIcc 0 T hT s) with hcl
  have hcl_cont : Continuous cl := continuous_subtype_val.comp continuous_projIcc
  have hcl_mem : ∀ s, cl s ∈ Set.Icc (0:ℝ) T := fun s => (Set.projIcc 0 T hT s).2
  have hcl_eq : ∀ s ∈ Set.Icc (0:ℝ) T, cl s = s := by
    intro s hs; show (↑(Set.projIcc 0 T hT s) : ℝ) = s; rw [Set.projIcc_of_mem hT hs]
  set 𝒜c : Z → ℝ → (E →L[ℝ] E) := fun z s => 𝒜 z (cl s) with h𝒜c
  have h𝒜c_cont : Continuous (fun p : Z × ℝ => 𝒜c p.1 p.2) := by
    have hmap : Continuous (fun p : Z × ℝ => ((p.1, cl p.2) : Z × ℝ)) :=
      continuous_fst.prodMk (hcl_cont.comp continuous_snd)
    have hmem : ∀ p : Z × ℝ, ((p.1, cl p.2) : Z × ℝ) ∈ Set.univ ×ˢ Set.Icc (0:ℝ) T :=
      fun p => ⟨Set.mem_univ _, hcl_mem p.2⟩
    exact h𝒜_contOn.comp_continuous hmap hmem
  have h𝒜c_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖𝒜c z s‖ ≤ K :=
    fun z s _ => h𝒜_bound z (cl s) (hcl_mem s)
  have hagree : ∀ (n : ℕ) (z : Z), ∀ s ∈ Set.Icc (0:ℝ) T,
      picardIter (𝒜c z) x₀ n s = picardIter (𝒜 z) x₀ n s := by
    intro n
    induction n with
    | zero => intro z s _; simp
    | succ n ih =>
      intro z s hs
      simp only [picardIter_succ]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      have huIcc : u ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le hs.1] at hu; exact ⟨hu.1, le_trans hu.2 hs.2⟩
      have e1 : 𝒜c z u = 𝒜 z u := by simp only [h𝒜c, hcl_eq u huIcc]
      rw [e1, ih z u huIcc]
  have key := picardSum_continuous_param 𝒜c x₀ T hT K hK h𝒜c_cont h𝒜c_bound t ht
  have heq : (fun z => ∑' n, picardIter (𝒜c z) x₀ n t)
      = (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
    funext z; congr 1; funext n; exact hagree n z t ht
  rwa [heq] at key

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

/-- **C3 (shared) — joint continuity of the Jacobian** on `Icc 0 T ×ˢ univ` (used by V2's
`hA_contOn`).  The block CLM `vlasovFieldJacobian` is reassembled `inl∘snd + inr∘(·)` and its
varying part is continuous via `hρD_cont`. -/
lemma vlasovFieldJacobian_continuousOn
    (gradW : PhysSpace d → PhysSpace d) (ρ : ℝ → Measure (PhysSpace d)) (T : ℝ)
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ContinuousOn (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) := by
  have hg_cont : Continuous (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
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
  rw [heq]; exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)

/-- **C3 (shared) — Lipschitz-in-parameter + ContinuousOn-in-time ⇒ jointly ContinuousOn.**
A generic upgrade: if `G z ·` is `ContinuousOn (Icc 0 T)` for each `z` and `z ↦ G z s` is
`C`-Lipschitz uniformly over `s ∈ [0,T]`, then `(z,s) ↦ G z s` is jointly continuous on
`univ ×ˢ Icc 0 T`.  Used to derive flow joint continuity `(z,s) ↦ Φ_s z` from
`charFlow_lipschitzInZ_via_gronwall_Ioo` (Lipschitz-in-`z`) + per-`z` continuity in `s`. -/
lemma continuousOn_prod_of_lipschitz_continuousOn
    {Z E : Type*} [PseudoMetricSpace Z] [PseudoMetricSpace E]
    (G : Z → ℝ → E) (T C : ℝ)
    (hlip : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ z₁ z₂, dist (G z₁ s) (G z₂ s) ≤ C * dist z₁ z₂)
    (hcont : ∀ z, ContinuousOn (fun s => G z s) (Set.Icc (0:ℝ) T)) :
    ContinuousOn (fun p : Z × ℝ => G p.1 p.2) (Set.univ ×ˢ Set.Icc (0:ℝ) T) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨z₀, s₀⟩ ⟨_, hs₀⟩ ε hε
  obtain ⟨δ₁, hδ₁, hcs⟩ :=
    (Metric.continuousWithinAt_iff).mp (hcont z₀ s₀ hs₀) (ε/2) (by positivity)
  have hC1 : (0:ℝ) < |C| + 1 := by positivity
  refine ⟨min δ₁ (ε / (2 * (|C| + 1))), by positivity, ?_⟩
  rintro ⟨z, s⟩ ⟨_, hs⟩ hd
  rw [Prod.dist_eq, max_lt_iff] at hd
  obtain ⟨hdz, hds⟩ := hd
  have hterm1 : dist (G z s) (G z₀ s) < ε/2 := by
    calc dist (G z s) (G z₀ s)
        ≤ C * dist z z₀ := hlip s hs z z₀
      _ ≤ (|C| + 1) * dist z z₀ :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) dist_nonneg
      _ < (|C| + 1) * (ε / (2 * (|C| + 1))) :=
          mul_lt_mul_of_pos_left (lt_of_lt_of_le hdz (min_le_right _ _)) hC1
      _ = ε/2 := by field_simp
  have hterm2 : dist (G z₀ s) (G z₀ s₀) < ε/2 :=
    hcs hs (lt_of_lt_of_le hds (min_le_left _ _))
  calc dist (G z s) (G z₀ s₀)
      ≤ dist (G z s) (G z₀ s) + dist (G z₀ s) (G z₀ s₀) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add hterm1 hterm2
    _ = ε := by ring

/-- **C3 V2 — the explicit fundamental matrix** (Route A, lesson L14): the canonical Dyson-series
solution of `Ṁ = A(t)·M`, `M 0 = id`, as a *function* (not a `choose`-d witness), so its
parameter-regularity is accessible. -/
noncomputable def fundamentalMatrix {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (A : ℝ → (F →L[ℝ] F)) : ℝ → (F →L[ℝ] F) :=
  fun t => ∑' n, picardIter (fun s => ContinuousLinearMap.compL ℝ F F F (A s))
    (ContinuousLinearMap.id ℝ F) n t

/-- `fundamentalMatrix A` solves the fundamental-matrix IVP on `[0,T]` (the non-existential form of
`exists_fundamentalMatrix`; same proof through the picardSum lemmas). -/
lemma fundamentalMatrix_spec {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Set.Icc 0 T)) :
    fundamentalMatrix A 0 = ContinuousLinearMap.id ℝ F ∧
      ContinuousOn (fundamentalMatrix A) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fundamentalMatrix A)
        ((A t).comp (fundamentalMatrix A t)) (Set.Icc 0 T) t := by
  have h𝒜cont : ContinuousOn (fun s => ContinuousLinearMap.compL ℝ F F F (A s)) (Set.Icc 0 T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA
  obtain ⟨KA, hKA⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA
  have hK'0 : (0:ℝ) ≤ max KA 0 := le_max_right _ _
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) T, ‖ContinuousLinearMap.compL ℝ F F F (A t)‖ ≤ max KA 0 := by
    intro t ht
    have h1 : ‖ContinuousLinearMap.compL ℝ F F F (A t)‖ ≤ ‖A t‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
      rw [ContinuousLinearMap.compL_apply]; exact (A t).opNorm_comp_le g
    exact le_trans (le_trans h1 (hKA t ht)) (le_max_left KA 0)
  have hMcont : ContinuousOn (fundamentalMatrix A) (Set.Icc 0 T) :=
    picardSum_continuousOn (fun s => ContinuousLinearMap.compL ℝ F F F (A s))
      (ContinuousLinearMap.id ℝ F) T hT (max KA 0) hK'0 h𝒜cont hbound
  have hMeq : ∀ t ∈ Set.Icc (0:ℝ) T, fundamentalMatrix A t = ContinuousLinearMap.id ℝ F
      + ∫ s in (0:ℝ)..t, ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s) :=
    fun t ht => picardSum_solves_integralEq (fun s => ContinuousLinearMap.compL ℝ F F F (A s))
      (ContinuousLinearMap.id ℝ F) T hT (max KA 0) hK'0 h𝒜cont hbound t ht
  have hg_cont : ContinuousOn
      (fun s => ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s)) (Set.Icc 0 T) :=
    h𝒜cont.clm_apply hMcont
  refine ⟨?_, hMcont, fun t ht => ?_⟩
  · rw [hMeq 0 ⟨le_refl 0, hT⟩, intervalIntegral.integral_same, add_zero]
  · haveI : Fact (t ∈ Set.Icc (0:ℝ) T) := ⟨ht⟩
    have hg_int : IntervalIntegrable
        (fun s => ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s)) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]; exact hg_cont.mono (Set.Icc_subset_Icc_right ht.2)
    have hg_meas : StronglyMeasurableAtFilter
        (fun s => ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s))
        (nhdsWithin t (Set.Icc 0 T)) :=
      ⟨Set.Icc 0 T, self_mem_nhdsWithin, hg_cont.aestronglyMeasurable measurableSet_Icc⟩
    have hFTC : HasDerivWithinAt
        (fun u => ∫ s in (0:ℝ)..u, ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s))
        (ContinuousLinearMap.compL ℝ F F F (A t) (fundamentalMatrix A t)) (Set.Icc 0 T) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hg_int hg_meas (hg_cont t ht)
    have hHD := (hFTC.const_add (ContinuousLinearMap.id ℝ F)).congr
      (fun y hy => hMeq y hy) (hMeq t ht)
    rwa [ContinuousLinearMap.compL_apply] at hHD

/-- **C3 V2 — the fundamental matrix is continuous in a PARAMETER** (closes V2 via Route A).
Specialises `picardSum_continuous_param_Icc` to `𝒜 := compL∘A`, `x₀ := id`; the `compL` factor is
`1`-bounded so the `K`-bound transfers from `A`. -/
lemma fundamentalMatrix_continuous_param
    {Z F : Type*} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : Z → ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hA_contOn : ContinuousOn (fun p : Z × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hA_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖A z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) :
    Continuous (fun z => fundamentalMatrix (A z) t) := by
  have h𝒜_contOn : ContinuousOn
      (fun p : Z × ℝ => ContinuousLinearMap.compL ℝ F F F (A p.1 p.2))
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA_contOn
  have h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T,
      ‖ContinuousLinearMap.compL ℝ F F F (A z s)‖ ≤ K := by
    intro z s hs
    refine le_trans ?_ (hA_bound z s hs)
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
    rw [ContinuousLinearMap.compL_apply]
    exact (A z s).opNorm_comp_le g
  exact picardSum_continuous_param_Icc (fun z s => ContinuousLinearMap.compL ℝ F F F (A z s))
    (ContinuousLinearMap.id ℝ F) T hT K hK h𝒜_contOn h𝒜_bound t ht

/-- **Step 3 (i) — joint `(z,s)` continuity of the Dyson sum** (global-hypothesis form).
Mirror of `picardSum_continuous_param`, concluding JOINT `ContinuousOn` on `univ ×ˢ Icc 0 T`
instead of per-`t` continuity in `z`.  The proof reuses the same joint iterate continuity
(`hiter_cont` on `Z × ℝ`) and the same `(z,s)`-independent M-test majorant `(KT)ⁿ/n!·‖x₀‖`; only
the final `tendstoUniformlyOn` ranges over `univ ×ˢ Icc 0 T`.  Used to make the variational
fundamental matrix `(z,s) ↦ M z s` jointly continuous (the partial-derivative continuity the
two-time-flow joint `C¹`-ness needs). -/
lemma picardSum_continuous_param_joint
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_cont : Continuous (fun p : Z × ℝ => 𝒜 p.1 p.2))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖𝒜 z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => ∑' n, picardIter (𝒜 p.1) x₀ n p.2)
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) := by
  have hiter_cont : ∀ n, Continuous (fun p : Z × ℝ => picardIter (𝒜 p.1) x₀ n p.2) := by
    intro n
    induction n with
    | zero =>
      simp only [picardIter_zero]
      exact continuous_const
    | succ n ih =>
      have hg : Continuous (Function.uncurry fun z v => 𝒜 z v (picardIter (𝒜 z) x₀ n v)) :=
        h𝒜_cont.clm_apply ih
      have hpp := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := volume) (a₀ := (0:ℝ)) hg
      simp only [picardIter_succ]
      exact hpp
  have h𝒜cont_z : ∀ z, ContinuousOn (𝒜 z) (Set.Icc (0:ℝ) T) := fun z =>
    (h𝒜_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hbd : ∀ (n : ℕ) (p : Z × ℝ), p ∈ Set.univ ×ˢ Set.Icc (0:ℝ) T →
      ‖picardIter (𝒜 p.1) x₀ n p.2‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n p hp
    have hps : p.2 ∈ Set.Icc (0:ℝ) T := hp.2
    have hb := (picardIter_continuousOn_and_bound (𝒜 p.1) x₀ T hT K hK (h𝒜cont_z p.1)
      (h𝒜_bound p.1) n).2 p.2 hps
    refine le_trans hb ?_
    have hKt : (0:ℝ) ≤ K * p.2 := mul_nonneg hK hps.1
    have hle : K * p.2 ≤ K * T := mul_le_mul_of_nonneg_left hps.2 hK
    gcongr
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hunif : TendstoUniformlyOn
      (fun (u : Finset ℕ) (p : Z × ℝ) => ∑ n ∈ u, picardIter (𝒜 p.1) x₀ n p.2)
      (fun p => ∑' n, picardIter (𝒜 p.1) x₀ n p.2) Filter.atTop
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) :=
    tendstoUniformlyOn_tsum hsum hbd
  refine hunif.continuousOn ?_
  exact (Filter.Eventually.of_forall
    (fun u => continuousOn_finset_sum u (fun n _ => (hiter_cont n).continuousOn))).frequently

/-- **Step 3 (i) — joint `(z,s)` continuity of the Dyson sum** (window / `ContinuousOn`-hypothesis
form).  Mirror of `picardSum_continuous_param_Icc`: clamp `s` into `[0,T]` (`projIcc`, L11) so the
global form applies, then transfer back by iterate-agreement on `[0,T]`. -/
lemma picardSum_continuous_param_Icc_joint
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_contOn : ContinuousOn (fun p : Z × ℝ => 𝒜 p.1 p.2) (Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖𝒜 z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => ∑' n, picardIter (𝒜 p.1) x₀ n p.2)
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) := by
  set cl : ℝ → ℝ := fun s => ↑(Set.projIcc 0 T hT s) with hcl
  have hcl_cont : Continuous cl := continuous_subtype_val.comp continuous_projIcc
  have hcl_mem : ∀ s, cl s ∈ Set.Icc (0:ℝ) T := fun s => (Set.projIcc 0 T hT s).2
  have hcl_eq : ∀ s ∈ Set.Icc (0:ℝ) T, cl s = s := by
    intro s hs; show (↑(Set.projIcc 0 T hT s) : ℝ) = s; rw [Set.projIcc_of_mem hT hs]
  set 𝒜c : Z → ℝ → (E →L[ℝ] E) := fun z s => 𝒜 z (cl s) with h𝒜c
  have h𝒜c_cont : Continuous (fun p : Z × ℝ => 𝒜c p.1 p.2) := by
    have hmap : Continuous (fun p : Z × ℝ => ((p.1, cl p.2) : Z × ℝ)) :=
      continuous_fst.prodMk (hcl_cont.comp continuous_snd)
    have hmem : ∀ p : Z × ℝ, ((p.1, cl p.2) : Z × ℝ) ∈ Set.univ ×ˢ Set.Icc (0:ℝ) T :=
      fun p => ⟨Set.mem_univ _, hcl_mem p.2⟩
    exact h𝒜_contOn.comp_continuous hmap hmem
  have h𝒜c_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖𝒜c z s‖ ≤ K :=
    fun z s _ => h𝒜_bound z (cl s) (hcl_mem s)
  have hagree : ∀ (n : ℕ) (z : Z), ∀ s ∈ Set.Icc (0:ℝ) T,
      picardIter (𝒜c z) x₀ n s = picardIter (𝒜 z) x₀ n s := by
    intro n
    induction n with
    | zero => intro z s _; simp
    | succ n ih =>
      intro z s hs
      simp only [picardIter_succ]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      have huIcc : u ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le hs.1] at hu; exact ⟨hu.1, le_trans hu.2 hs.2⟩
      have e1 : 𝒜c z u = 𝒜 z u := by simp only [h𝒜c, hcl_eq u huIcc]
      rw [e1, ih z u huIcc]
  have key := picardSum_continuous_param_joint 𝒜c x₀ T hT K hK h𝒜c_cont h𝒜c_bound
  refine key.congr ?_
  rintro ⟨z, s⟩ ⟨_, hs⟩
  simp only
  congr 1; funext n; exact (hagree n z s hs).symm

/-- **Step 3 (i) — the fundamental matrix is jointly `(z,s)`-continuous.**  Joint companion of
`fundamentalMatrix_continuous_param`; specialises `picardSum_continuous_param_Icc_joint` to
`𝒜 := compL∘A`, `x₀ := id`.  This is the partial-`z`-derivative continuity input to the joint
`C¹`-ness of the forward flow `(s,z) ↦ Φ_s z` (Step 3 (iii)). -/
lemma fundamentalMatrix_continuous_param_joint
    {Z F : Type*} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : Z → ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hA_contOn : ContinuousOn (fun p : Z × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hA_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖A z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => fundamentalMatrix (A p.1) p.2)
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) := by
  have h𝒜_contOn : ContinuousOn
      (fun p : Z × ℝ => ContinuousLinearMap.compL ℝ F F F (A p.1 p.2))
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA_contOn
  have h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T,
      ‖ContinuousLinearMap.compL ℝ F F F (A z s)‖ ≤ K := by
    intro z s hs
    refine le_trans ?_ (hA_bound z s hs)
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
    rw [ContinuousLinearMap.compL_apply]
    exact (A z s).opNorm_comp_le g
  exact picardSum_continuous_param_Icc_joint
    (fun z s => ContinuousLinearMap.compL ℝ F F F (A z s))
    (ContinuousLinearMap.id ℝ F) T hT K hK h𝒜_contOn h𝒜_bound

section CharFlowDeriv
open Filter Topology

/-- Generic Grönwall difference-quotient bound (open-interval ODE + `s₀→0⁺` limit).  Two curves
`uh, mh` that approximately solve the same linear ODE `ẇ = vlin·w` on `Ioo 0 T` from the same datum
(`uh 0 = mh 0`), with `mh` exact and `uh`'s defect uniformly `≤ εf`, satisfy
`dist (uh t) (mh t) ≤ gronwallBound 0 K εf t`.  `vlin` is abstract (kept opaque to avoid unfolding
the heavy `vlasovFieldJacobian` integral in the Grönwall application). -/
lemma gronwall_diffQuotient_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (vlin : ℝ → (E →L[ℝ] E)) (K : NNReal) (hvlin_lip : ∀ s, LipschitzWith K (vlin s))
    (uh mh Fuh : ℝ → E) (εf : ℝ) (T t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) T)
    (huh_cont : ContinuousOn uh (Set.Icc 0 T)) (hmh_cont : ContinuousOn mh (Set.Icc 0 T))
    (huh_deriv : ∀ s ∈ Set.Ioo (0:ℝ) T, HasDerivAt uh (Fuh s) s)
    (hmh_deriv : ∀ s ∈ Set.Ioo (0:ℝ) T, HasDerivAt mh ((vlin s) (mh s)) s)
    (hdefect : ∀ s ∈ Set.Ioo (0:ℝ) T, dist (Fuh s) (vlin s (uh s)) ≤ εf)
    (h0 : uh 0 = mh 0) :
    dist (uh t) (mh t) ≤ gronwallBound 0 (K:ℝ) εf t := by
  have hbound_s0 : ∀ s₀ ∈ Set.Ioo (0:ℝ) t,
      dist (uh t) (mh t) ≤ gronwallBound (dist (uh s₀) (mh s₀)) (K:ℝ) εf (t - s₀) := by
    intro s₀ hs₀
    have hIco_sub : Set.Ico s₀ t ⊆ Set.Ioo 0 T := fun s hs =>
      ⟨lt_of_lt_of_le hs₀.1 hs.1, hs.2.trans ht.2⟩
    have hIcc_sub : Set.Icc s₀ t ⊆ Set.Icc 0 T := fun s hs =>
      ⟨le_trans hs₀.1.le hs.1, le_trans hs.2 ht.2.le⟩
    have key := dist_le_of_approx_trajectories_ODE (K := K)
      (εf := εf) (εg := 0) (δ := dist (uh s₀) (mh s₀))
      hvlin_lip (huh_cont.mono hIcc_sub)
      (fun s hs => (huh_deriv s (hIco_sub hs)).hasDerivWithinAt)
      (fun s hs => hdefect s (hIco_sub hs))
      (hmh_cont.mono hIcc_sub)
      (fun s hs => (hmh_deriv s (hIco_sub hs)).hasDerivWithinAt)
      (fun s _ => le_of_eq (dist_self _)) (le_refl _)
    have hkey := key t ⟨hs₀.2.le, le_refl t⟩
    simpa only [add_zero] using hkey
  haveI : (𝓝[Set.Ioo 0 t] (0:ℝ)).NeBot := left_nhdsWithin_Ioo_neBot ht.1
  have hT0 : (0:ℝ) ≤ T := le_trans ht.1.le ht.2.le
  have hsub_Icc : Set.Ioo (0:ℝ) t ⊆ Set.Icc 0 T := fun s hs => ⟨hs.1.le, le_trans hs.2.le ht.2.le⟩
  have htend_uh : Tendsto uh (𝓝[Set.Ioo 0 t] 0) (𝓝 (uh 0)) :=
    (huh_cont 0 ⟨le_refl 0, hT0⟩).tendsto.mono_left (nhdsWithin_mono 0 hsub_Icc)
  have htend_mh : Tendsto mh (𝓝[Set.Ioo 0 t] 0) (𝓝 (mh 0)) :=
    (hmh_cont 0 ⟨le_refl 0, hT0⟩).tendsto.mono_left (nhdsWithin_mono 0 hsub_Icc)
  have htend_δ : Tendsto (fun s₀ => dist (uh s₀) (mh s₀)) (𝓝[Set.Ioo 0 t] 0) (𝓝 0) := by
    have := htend_uh.dist htend_mh
    rwa [h0, dist_self] at this
  have htend_x : Tendsto (fun s₀ : ℝ => t - s₀) (𝓝[Set.Ioo 0 t] 0) (𝓝 t) := by
    have h0' : Tendsto (fun s₀ : ℝ => t - s₀) (𝓝 0) (𝓝 (t - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at h0'; exact h0'.mono_left nhdsWithin_le_nhds
  have hgb_cont : Continuous (fun p : ℝ × ℝ => gronwallBound p.1 (K:ℝ) εf p.2) := by
    by_cases hK : (K:ℝ) = 0
    · simp only [hK, gronwallBound_K0]; fun_prop
    · have heq : (fun p : ℝ × ℝ => gronwallBound p.1 (K:ℝ) εf p.2)
          = fun p => p.1 * Real.exp ((K:ℝ) * p.2) + εf / (K:ℝ) * (Real.exp ((K:ℝ) * p.2) - 1) := by
        funext p; rw [gronwallBound_of_K_ne_0 hK]
      rw [heq]; fun_prop
  have htend_gb : Tendsto (fun s₀ => gronwallBound (dist (uh s₀) (mh s₀)) (K:ℝ) εf (t - s₀))
      (𝓝[Set.Ioo 0 t] 0) (𝓝 (gronwallBound 0 (K:ℝ) εf t)) :=
    (hgb_cont.tendsto (0, t)).comp (htend_δ.prodMk_nhds htend_x)
  exact ge_of_tendsto htend_gb (eventually_nhdsWithin_of_forall (fun s₀ hs₀ => hbound_s0 s₀ hs₀))

set_option maxHeartbeats 800000 in
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
Lipschitz constant; `‖A(s,·)‖ ≤ K` via `norm_fderiv_le_of_lipschitz`.  (`hcontIcc` is universal in
the initial point because the `s₀→0⁺` limit needs continuity of `Φ_·(z+h)`, M2.) -/
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
    (hcontIcc : ∀ z' : PhaseSpace d,
      ContinuousOn (fun s => (charX s z', charV s z')) (Set.Icc (0 : ℝ) T))
    (Mz : ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d))
    (hMz0 : Mz 0 = ContinuousLinearMap.id ℝ (PhaseSpace d))
    (hMzcont : ContinuousOn Mz (Set.Icc 0 T))
    (hMzderiv : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt Mz
        ((vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z))).comp (Mz s))
        (Set.Icc 0 T) s) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, HasFDerivAt (fun w => (charX t w, charV t w)) (Mz t) z := by
  intro t ht
  set Kr : ℝ := ((max 1 L : NNReal) : ℝ) with hKr
  have hKr1 : (1:ℝ) ≤ Kr := by rw [hKr]; exact_mod_cast le_max_left 1 L
  have hKrpos : (0:ℝ) < Kr := lt_of_lt_of_le one_pos hKr1
  set Φ : ℝ → PhaseSpace d := fun s => (charX s z, charV s z) with hΦ
  have hF2 : ∀ s (w : PhaseSpace d),
      HasFDerivAt (vlasovVectorField gradW ρ s) (vlasovFieldJacobian gradW ρ (s, w)) w :=
    fun s w => vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s w
  have hVF_lip : ∀ s, LipschitzWith (max 1 L) (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  set vlin : ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) := fun s => vlasovFieldJacobian gradW ρ (s, Φ s)
    with hvlin
  have hvlin_norm : ∀ s, ‖vlin s‖ ≤ Kr := by
    intro s
    show ‖vlasovFieldJacobian gradW ρ (s, Φ s)‖ ≤ Kr
    rw [← (hF2 s (Φ s)).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (hVF_lip s)
  have hvlin_lip : ∀ s, LipschitzWith (max 1 L) (vlin s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖vlin s (x - y)‖ ≤ ‖vlin s‖ * ‖x - y‖ := (vlin s).le_opNorm _
      _ ≤ Kr * ‖x - y‖ := by gcongr; exact hvlin_norm s
  clear_value vlin
  have h_init : ∀ z' : PhaseSpace d, (charX 0 z', charV 0 z') = z' := fun z' =>
    Prod.ext_iff.mpr ⟨(hflow.1 z' (Set.mem_univ z')).1, (hflow.1 z' (Set.mem_univ z')).2⟩
  have h_derivAt : ∀ z', ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivAt (fun s => (charX s z', charV s z'))
        (vlasovVectorField gradW ρ s (charX s z', charV s z')) s := fun z' s hs =>
    HasDerivAt.prodMk (hflow.2.1 s hs z' (Set.mem_univ z')) (hflow.2.2 s hs z' (Set.mem_univ z'))
  have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
    h_init hcontIcc (fun z' s hs => (h_derivAt z' s hs).hasDerivWithinAt)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set Cexp : ℝ := Real.exp (Kr * T) with hCexp
  have hCexp_pos : 0 < Cexp := Real.exp_pos _
  set Cgron : ℝ := (Real.exp (Kr * t) - 1) / Kr with hCgron
  have hCgron_nonneg : 0 ≤ Cgron := by
    rw [hCgron]; apply div_nonneg _ hKrpos.le
    simp only [sub_nonneg]; exact Real.one_le_exp (mul_nonneg hKrpos.le ht.1.le)
  set G : ℝ := Cexp * Cgron with hG
  have hG_nonneg : 0 ≤ G := mul_nonneg hCexp_pos.le hCgron_nonneg
  set η : ℝ := c / (G + 1) with hη
  have hη_pos : 0 < η := by rw [hη]; positivity
  obtain ⟨δη, hδη_pos, hδη⟩ := vlasovField_taylorRemainder_uniform gradW hgradW_C1 L hL ρ h_int
    charX charV T z (hcontIcc z) hρD_cont η hη_pos
  refine Metric.eventually_nhds_iff.mpr
    ⟨δη / (Cexp + 1), div_pos hδη_pos (by linarith [hCexp_pos]), ?_⟩
  intro h hh
  rw [dist_zero_right] at hh
  have hCexph : Cexp * ‖h‖ ≤ δη := by
    have hle : ‖h‖ * (Cexp + 1) ≤ δη := by rw [← le_div_iff₀ (by linarith [hCexp_pos])]; exact hh.le
    nlinarith [norm_nonneg h, hCexp_pos, hle]
  set uh : ℝ → PhaseSpace d := fun s => (charX s (z + h), charV s (z + h)) - (charX s z, charV s z)
    with huh
  set mh : ℝ → PhaseSpace d := fun s => (Mz s) h with hmh
  set εf : ℝ := η * Cexp * ‖h‖ with hεf
  have huh_cont : ContinuousOn uh (Set.Icc 0 T) := (hcontIcc (z + h)).sub (hcontIcc z)
  have hmh_cont : ContinuousOn mh (Set.Icc 0 T) := hMzcont.clm_apply continuousOn_const
  have huh_bound : ∀ s ∈ Set.Icc (0:ℝ) T, ‖uh s‖ ≤ Cexp * ‖h‖ := by
    intro s hs
    show ‖(charX s (z + h), charV s (z + h)) - (charX s z, charV s z)‖ ≤ Cexp * ‖h‖
    rw [← dist_eq_norm]
    calc dist ((charX s (z + h), charV s (z + h)) : PhaseSpace d) (charX s z, charV s z)
        ≤ dist (z + h) z * Real.exp (Kr * (s - 0)) := hgron s hs (z + h) z
      _ = ‖h‖ * Real.exp (Kr * s) := by rw [dist_eq_norm, add_sub_cancel_left, sub_zero]
      _ ≤ ‖h‖ * Cexp := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg h)
          rw [hCexp]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hKrpos.le)
      _ = Cexp * ‖h‖ := mul_comm _ _
  have huh_derivAt : ∀ s ∈ Set.Ioo (0:ℝ) T, HasDerivAt uh
      (vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) s := fun s hs =>
    (h_derivAt (z + h) s hs).sub (h_derivAt z s hs)
  have hmh_derivAt : ∀ s ∈ Set.Ioo (0:ℝ) T, HasDerivAt mh ((vlin s) (mh s)) s := by
    intro s hs
    have hMz_at : HasDerivAt Mz ((vlin s).comp (Mz s)) s := by
      simp only [hvlin]
      exact (hMzderiv s (Set.Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hck := hMz_at.clm_apply (hasDerivAt_const s h)
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using hck
  have hdefect : ∀ s ∈ Set.Ioo (0:ℝ) T,
      dist (vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) (vlin s (uh s)) ≤ εf := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0:ℝ) T := Set.Ioo_subset_Icc_self hs
    have huhs_le : ‖uh s‖ ≤ δη := le_trans (huh_bound s hsIcc) hCexph
    have hR := hδη s hsIcc (charX s (z + h), charV s (z + h)) huhs_le
    rw [dist_eq_norm]; simp only [hvlin]
    calc ‖vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
            - vlasovVectorField gradW ρ s (charX s z, charV s z)
            - vlasovFieldJacobian gradW ρ (s, Φ s) (uh s)‖
        ≤ η * ‖uh s‖ := hR
      _ ≤ η * (Cexp * ‖h‖) := mul_le_mul_of_nonneg_left (huh_bound s hsIcc) hη_pos.le
      _ = εf := by rw [hεf]; ring
  have huh0 : uh 0 = h := by
    show (charX 0 (z + h), charV 0 (z + h)) - (charX 0 z, charV 0 z) = h
    rw [h_init (z + h), h_init z, add_sub_cancel_left]
  have hmh0 : mh 0 = h := by show (Mz 0) h = h; rw [hMz0]; rfl
  have hlim : dist (uh t) (mh t) ≤ gronwallBound 0 Kr εf t := by
    have := gronwall_diffQuotient_bound vlin (max 1 L) hvlin_lip uh mh
      (fun s => vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) εf T t ht
      huh_cont hmh_cont huh_derivAt hmh_derivAt hdefect (huh0.trans hmh0.symm)
    rwa [← hKr] at this
  have hgb_val : gronwallBound 0 Kr εf t = εf * Cgron := by
    rw [gronwallBound_of_K_ne_0 hKrpos.ne']; simp only [zero_mul, zero_add]; rw [hCgron]; ring
  have hηG : η * G ≤ c := by
    rw [hη]; rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith [hG_nonneg] : (0:ℝ) < G + 1)]
    nlinarith [hG_nonneg, hc.le]
  show ‖(charX t (z + h), charV t (z + h)) - (charX t z, charV t z) - (Mz t) h‖ ≤ c * ‖h‖
  rw [show (charX t (z + h), charV t (z + h)) - (charX t z, charV t z) - (Mz t) h
      = uh t - mh t from rfl, ← dist_eq_norm]
  calc dist (uh t) (mh t)
      ≤ gronwallBound 0 Kr εf t := hlim
    _ = εf * Cgron := hgb_val
    _ = η * G * ‖h‖ := by rw [hεf, hG]; ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hηG (norm_nonneg h)

end CharFlowDeriv

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
  -- **Reduction (Route A — explicit fundamental matrix, lesson L14).**  `M z := fundamentalMatrix
  -- (A z)` with `A z s := vlasovFieldJacobian gradW ρ (s, Φ_s z)`; its ODE/continuity data come from
  -- `fundamentalMatrix_spec` (feeds D1), and `z ↦ M z t` continuity (V2) from
  -- `fundamentalMatrix_continuous_param` — the parameter-regularity an existential `choose` could not
  -- supply.  `Dflow t z := fundamentalMatrix (A z) t`.
  set A : PhaseSpace d → ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun z s => vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z)) with hA_def
  have hAcont : ∀ z : PhaseSpace d, ContinuousOn (A z) (Set.Icc 0 T) := fun z =>
    vlasovVariationalCoeff_continuousOn gradW ρ charX charV T z (hcontIcc z) hρD_cont
  refine ⟨fun t z => fundamentalMatrix (A z) t, ?_, ?_⟩
  · -- **D1** — `charFlow_hasFDerivAt_of_fundamentalMatrix` fed by `fundamentalMatrix_spec`.
    intro t ht z
    obtain ⟨h0, hcont, hderiv⟩ := fundamentalMatrix_spec (A z) T hT.le (hAcont z)
    exact charFlow_hasFDerivAt_of_fundamentalMatrix gradW hgradW_C1 L hL ρ charX charV T hT hflow
      h_int hρD_cont z hcontIcc (fundamentalMatrix (A z)) h0 hcont hderiv t ht
  · -- **V2** — `fundamentalMatrix_continuous_param`: flow joint continuity ⇒ `A` jointly continuous
    -- ⇒ `z ↦ M z t` continuous.
    intro t ht
    -- Flow joint continuity `(z,s) ↦ Φ_s z` on `univ ×ˢ Icc 0 T` (Grönwall Lipschitz-in-`z` from
    -- `hflow` + per-`z` continuity in `s`).
    have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
      Prod.ext_iff.mpr ⟨(hflow.1 z (Set.mem_univ z)).1, (hflow.1 z (Set.mem_univ z)).2⟩
    have h_deriv : ∀ z, ∀ s ∈ Set.Ioo (0:ℝ) T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
      (HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z))
        (hflow.2.2 s hs z (Set.mem_univ z))).hasDerivWithinAt
    have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
      h_init hcontIcc h_deriv
    have hflowjoint : ContinuousOn
        (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1)) (Set.univ ×ˢ Set.Icc 0 T) := by
      refine continuousOn_prod_of_lipschitz_continuousOn (fun z s => (charX s z, charV s z)) T
        (Real.exp (((max 1 L : NNReal) : ℝ) * T)) (fun s hs z₁ z₂ => ?_) hcontIcc
      calc dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
          ≤ dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) := hgron s hs z₁ z₂
        _ = Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) * dist z₁ z₂ := by ring
        _ ≤ Real.exp (((max 1 L : NNReal) : ℝ) * T) * dist z₁ z₂ := by
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) dist_nonneg
            have hsT : s - 0 ≤ T := by simp only [sub_zero]; exact hs.2
            exact mul_le_mul_of_nonneg_left hsT (by positivity)
    -- `A` jointly continuous (Jacobian along the flow) and uniformly bounded by `max 1 L`.
    have hg : ContinuousOn
        (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) := continuousOn_snd.prodMk hflowjoint
    have hmapsg : Set.MapsTo
        (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
    have hA_contOn : ContinuousOn (fun p : PhaseSpace d × ℝ => A p.1 p.2)
        (Set.univ ×ˢ Set.Icc 0 T) :=
      (vlasovFieldJacobian_continuousOn gradW ρ T hρD_cont).comp hg hmapsg
    have hA_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖A z s‖ ≤ ((max 1 L : NNReal) : ℝ) := by
      intro z s _
      have heq : A z s = fderiv ℝ (vlasovVectorField gradW ρ s) (charX s z, charV s z) := by
        simp only [hA_def]
        exact (vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s
          (charX s z, charV s z)).fderiv.symm
      rw [heq]
      exact norm_fderiv_le_of_lipschitz ℝ (vlasovVectorField_lipschitzWith gradW L hL ρ h_int s)
    exact fundamentalMatrix_continuous_param A T hT.le ((max 1 L : NNReal) : ℝ) (by positivity)
      hA_contOn hA_bound t (Set.Ioo_subset_Icc_self ht)

open Filter Topology in
/-- **Step 1 (dual core) — lower Grönwall / anti-Lipschitz bound on the characteristic flow.**
For `t ∈ (0,T)`, the flow `Φ_t : z ↦ (charX t z, charV t z)` satisfies
`dist z₁ z₂ ≤ dist (Φ_t z₁) (Φ_t z₂) · exp(K t)` (K = max 1 L), i.e. `Φ_t` is `AntilipschitzWith`.
This is the keystone of the two-time-flow inverse construction (Step 2): bi-Lipschitz makes `Φ_t`
injective with closed range and `M_t = DΦ_t` invertible (no Liouville needed).

Proof: time-reverse the two trajectories on each `[s₀,t] ⊆ (0,T)` (so they solve
`w' = −b_{s₀+t−r}(w)`, still K-Lipschitz) and apply the existing forward
`dist_le_of_trajectories_ODE`; take `s₀→0⁺`.  `h_deriv2` is the two-sided `HasDerivAt` on the open
interval, supplied by `IsCharacteristicFlowOn`. -/
theorem charFlow_antilipschitzInZ_via_gronwall_Ioo
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤
        dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂)
          * Real.exp (((max 1 L : NNReal) : ℝ) * (t - 0)) := by
  intro t ht z₁ z₂
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  set F : ℝ → PhaseSpace d := fun s => (charX s z₁, charV s z₁) with hF_def
  set G : ℝ → PhaseSpace d := fun s => (charX s z₂, charV s z₂) with hG_def
  -- Per-`s₀` antilipschitz bound on `[s₀, t]`.
  have h_perS0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
      dist (F s₀) (G s₀) ≤ dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀)) := by
    intro s₀ hs₀
    have hsub_Ioo : Set.Icc s₀ t ⊆ Set.Ioo (0 : ℝ) T := fun r hr =>
      ⟨lt_of_lt_of_le hs₀.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    have hsub_Icc : Set.Icc s₀ t ⊆ Set.Icc (0 : ℝ) T := fun r hr =>
      ⟨le_of_lt (lt_of_lt_of_le hs₀.1 hr.1), le_of_lt (lt_of_le_of_lt hr.2 ht.2)⟩
    have hrefl_mem : ∀ r ∈ Set.Icc s₀ t, s₀ + t - r ∈ Set.Icc s₀ t := by
      intro r hr; exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hrefl_cont : ContinuousOn (fun r : ℝ => s₀ + t - r) (Set.Icc s₀ t) :=
      (continuous_const.sub continuous_id).continuousOn
    set vr : ℝ → PhaseSpace d → PhaseSpace d :=
      fun r w => -(vlasovVectorField gradW ρ (s₀ + t - r) w) with hvr_def
    have hvr_lip : ∀ r, LipschitzWith K (vr r) := fun r => (h_vf_lip (s₀ + t - r)).neg
    have hFr_cont : ContinuousOn (fun r => F (s₀ + t - r)) (Set.Icc s₀ t) :=
      (h_cont_Icc z₁).comp hrefl_cont (fun r hr => hsub_Icc (hrefl_mem r hr))
    have hGr_cont : ContinuousOn (fun r => G (s₀ + t - r)) (Set.Icc s₀ t) :=
      (h_cont_Icc z₂).comp hrefl_cont (fun r hr => hsub_Icc (hrefl_mem r hr))
    have hFr' : ∀ r ∈ Set.Ico s₀ t,
        HasDerivWithinAt (fun r => F (s₀ + t - r)) (vr r (F (s₀ + t - r))) (Set.Ici r) r := by
      intro r hr
      have hrIoo : s₀ + t - r ∈ Set.Ioo (0 : ℝ) T :=
        hsub_Ioo ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hlin : HasDerivAt (fun r : ℝ => s₀ + t - r) (-1) r := by
        simpa using (hasDerivAt_id r).const_sub (s₀ + t)
      have key : HasDerivAt (fun r => F (s₀ + t - r))
          ((-1 : ℝ) • vlasovVectorField gradW ρ (s₀ + t - r) (F (s₀ + t - r))) r :=
        HasDerivAt.scomp_of_eq r (h_deriv2 z₁ (s₀ + t - r) hrIoo) hlin rfl
      simp only [neg_one_smul] at key
      exact key.hasDerivWithinAt
    have hGr' : ∀ r ∈ Set.Ico s₀ t,
        HasDerivWithinAt (fun r => G (s₀ + t - r)) (vr r (G (s₀ + t - r))) (Set.Ici r) r := by
      intro r hr
      have hrIoo : s₀ + t - r ∈ Set.Ioo (0 : ℝ) T :=
        hsub_Ioo ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hlin : HasDerivAt (fun r : ℝ => s₀ + t - r) (-1) r := by
        simpa using (hasDerivAt_id r).const_sub (s₀ + t)
      have key : HasDerivAt (fun r => G (s₀ + t - r))
          ((-1 : ℝ) • vlasovVectorField gradW ρ (s₀ + t - r) (G (s₀ + t - r))) r :=
        HasDerivAt.scomp_of_eq r (h_deriv2 z₂ (s₀ + t - r) hrIoo) hlin rfl
      simp only [neg_one_smul] at key
      exact key.hasDerivWithinAt
    have hgron := dist_le_of_trajectories_ODE hvr_lip hFr_cont hFr' hGr_cont hGr'
      (le_refl (dist (F (s₀ + t - s₀)) (G (s₀ + t - s₀)))) t ⟨hs₀.2.le, le_refl t⟩
    simp only [show s₀ + t - t = s₀ from by ring, show s₀ + t - s₀ = t from by ring] at hgron
    exact hgron
  -- `s₀ → 0⁺` limit.
  have hfilt : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot := left_nhdsWithin_Ioo_neBot ht.1
  have hIoo_sub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun s hs =>
    ⟨hs.1.le, le_of_lt (lt_trans hs.2 ht.2)⟩
  have h_tendsto_F : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds z₁) := by
    have hcw : ContinuousWithinAt F (Set.Icc (0 : ℝ) T) 0 :=
      (h_cont_Icc z₁) 0 ⟨le_refl 0, le_of_lt (lt_trans ht.1 ht.2)⟩
    have h0 : Tendsto F (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (F 0)) := hcw
    rw [show F 0 = z₁ from h_init z₁] at h0
    exact h0.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
  have h_tendsto_G : Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds z₂) := by
    have hcw : ContinuousWithinAt G (Set.Icc (0 : ℝ) T) 0 :=
      (h_cont_Icc z₂) 0 ⟨le_refl 0, le_of_lt (lt_trans ht.1 ht.2)⟩
    have h0 : Tendsto G (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (G 0)) := hcw
    rw [show G 0 = z₂ from h_init z₂] at h0
    exact h0.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
  have h_tendsto_lhs : Tendsto (fun s₀ => dist (F s₀) (G s₀))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds (dist z₁ z₂)) :=
    h_tendsto_F.dist h_tendsto_G
  have h_tendsto_rhs : Tendsto (fun s₀ => dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀)))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
      (nhds (dist (F t) (G t) * Real.exp ((K : ℝ) * (t - 0)))) := by
    have hcont : Continuous (fun s₀ : ℝ => dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀))) := by
      fun_prop
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto h_tendsto_lhs h_tendsto_rhs
    (eventually_nhdsWithin_of_forall h_perS0)

section Step2Inverse
open Filter Topology

/-- **Step 2a (dual core, generic) — antilipschitz map ⇒ antilipschitz derivative.**
If `f` is antilipschitz and Fréchet-differentiable at `x`, its derivative `f'` is antilipschitz
(hence injective) with the same constant.  `f' u` is the limit of slopes `n•(f(x+n⁻¹•u)−f x)`, each
of norm `≥ ‖u‖/C` by antilipschitz; pass to the limit.  (Mathlib lacks this producer.) -/
theorem antilipschitzWith_fderiv_of_antilipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {x : E} {C : NNReal}
    (hf : AntilipschitzWith C f) (hf' : HasFDerivAt f f' x) :
    AntilipschitzWith C f' := by
  refine AntilipschitzWith.of_le_mul_dist (fun v w => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  set u := v - w with hu
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ))‖) atTop atTop := by
    simpa [Real.norm_natCast] using tendsto_natCast_atTop_atTop (R := ℝ)
  have hlim := hf'.lim u hc
  have hbd : ∀ᶠ n : ℕ in atTop,
      ‖u‖ ≤ (C : ℝ) * ‖(n : ℝ) • (f (x + ((n : ℝ))⁻¹ • u) - f x)‖ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hd := hf.le_mul_dist (x + ((n : ℝ))⁻¹ • u) x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv,
      Real.norm_natCast] at hd
    rw [norm_smul, Real.norm_natCast]
    calc ‖u‖ = (n : ℝ) * ((n : ℝ)⁻¹ * ‖u‖) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn0), one_mul]
      _ ≤ (n : ℝ) * ((C : ℝ) * ‖f (x + ((n : ℝ))⁻¹ • u) - f x‖) :=
              mul_le_mul_of_nonneg_left hd (le_of_lt hn0)
      _ = (C : ℝ) * ((n : ℝ) * ‖f (x + ((n : ℝ))⁻¹ • u) - f x‖) := by ring
  have hlim2 : Tendsto (fun n : ℕ => (C : ℝ) * ‖(n : ℝ) • (f (x + ((n : ℝ))⁻¹ • u) - f x)‖)
      atTop (𝓝 ((C : ℝ) * ‖f' u‖)) := hlim.norm.const_mul (C : ℝ)
  exact ge_of_tendsto hlim2 hbd

/-- **Step 2 (dual core, generic) — global `C¹` inverse of an antilipschitz `C¹` self-map.**
If `Φ : E → E` (finite-dim) is `C¹` (derivative `M z` at `z`), antilipschitz, and Lipschitz, then
each `M z` is invertible, `Φ` is bijective, and the global inverse `Ψ` is Lipschitz with
`HasFDerivAt Ψ (M (Ψ w))⁻¹ w`.  No Liouville/Hadamard: open range
(`isOpenMap_of_hasStrictFDerivAt_equiv`) + closed range (`AntilipschitzWith.isClosed_range`) ⇒
clopen ⇒ surjective; inverse derivative from `HasStrictFDerivAt.to_local_left_inverse`. -/
theorem exists_global_c1_inverse_of_antilipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : E → E} {M : E → (E →L[ℝ] E)} {Ca Cl : NNReal}
    (hderiv : ∀ z, HasFDerivAt Φ (M z) z)
    (hM_cont : Continuous M)
    (hanti : AntilipschitzWith Ca Φ)
    (hlip : LipschitzWith Cl Φ) :
    ∃ (Ψ : E → E) (e : ∀ z, E ≃L[ℝ] E),
      (∀ z, ((e z : E →L[ℝ] E)) = M z) ∧
      Function.LeftInverse Ψ Φ ∧ Function.RightInverse Ψ Φ ∧
      LipschitzWith Ca Ψ ∧
      (∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : E →L[ℝ] E) w) := by
  classical
  have hMz_anti : ∀ z, AntilipschitzWith Ca (M z) := fun z =>
    antilipschitzWith_fderiv_of_antilipschitz hanti (hderiv z)
  have hker : ∀ z, LinearMap.ker (M z : E →ₗ[ℝ] E) = ⊥ := fun z =>
    LinearMap.ker_eq_bot.mpr (hMz_anti z).injective
  have hsurj_lin : ∀ z, LinearMap.range (M z : E →ₗ[ℝ] E) = ⊤ := fun z =>
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (hMz_anti z).injective)
  set e : ∀ z, E ≃L[ℝ] E := fun z =>
    ContinuousLinearEquiv.ofBijective (M z) (hker z) (hsurj_lin z) with he_def
  have he_coe : ∀ z, ((e z : E →L[ℝ] E)) = M z := fun _ => rfl
  have hC1 : ContDiff ℝ 1 Φ := contDiff_one_iff_hasFDerivAt.mpr ⟨M, hM_cont, hderiv⟩
  have hstrict : ∀ z, HasStrictFDerivAt Φ ((e z : E →L[ℝ] E)) z := fun z => by
    rw [he_coe z]; exact hC1.contDiffAt.hasStrictFDerivAt' (hderiv z) (by norm_num)
  have hopen : IsOpenMap Φ := isOpenMap_of_hasStrictFDerivAt_equiv hstrict
  have hrange_open : IsOpen (Set.range Φ) := hopen.isOpen_range
  have hrange_closed : IsClosed (Set.range Φ) := hanti.isClosed_range hlip.uniformContinuous
  have hrange_univ : Set.range Φ = Set.univ :=
    IsClopen.eq_univ ⟨hrange_closed, hrange_open⟩ ⟨Φ 0, Set.mem_range_self 0⟩
  have hsurj : Function.Surjective Φ := Set.range_eq_univ.mp hrange_univ
  have hinj : Function.Injective Φ := hanti.injective
  set Ψ : E → E := Function.invFun Φ with hΨ_def
  have hLeft : Function.LeftInverse Ψ Φ := Function.leftInverse_invFun hinj
  have hRight : Function.RightInverse Ψ Φ := Function.rightInverse_invFun hsurj
  have hΨ_lip : LipschitzWith Ca Ψ := by
    refine LipschitzWith.of_dist_le_mul (fun w₁ w₂ => ?_)
    have h := hanti.le_mul_dist (Ψ w₁) (Ψ w₂)
    rwa [hRight w₁, hRight w₂] at h
  have hΨ_deriv : ∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : E →L[ℝ] E) w := by
    intro w
    have hz : Φ (Ψ w) = w := hRight w
    have hev : ∀ᶠ x in 𝓝 (Ψ w), Ψ (Φ x) = x := Filter.Eventually.of_forall hLeft
    have hsymm := (hstrict (Ψ w)).to_local_left_inverse hev
    rw [hz] at hsymm
    exact hsymm.hasFDerivAt
  exact ⟨Ψ, e, he_coe, hLeft, hRight, hΨ_lip, hΨ_deriv⟩

end Step2Inverse

/-- **Step 2 (dual core) — the characteristic flow `Φ_t` is a `C¹` diffeomorphism on `(0,T)`.**
Instantiates the generic global-inverse machinery at `Φ_t := (charX t, charV t)`: its derivative
`e z` (= `#3`'s `Dflow t z`) is invertible, `Φ_t` is bijective, and the inverse `Ψ` is continuous
with `HasFDerivAt Ψ (e (Ψ w))⁻¹ w`.  `hanti` comes from Step 1
(`charFlow_antilipschitzInZ_via_gronwall_Ioo`), `hlip` from the existing upper Grönwall bound
(`charFlow_lipschitzInZ_via_gronwall_Ioo`), the derivative family from `#3`. -/
theorem exists_charFlow_inverse_On
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
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∃ (Ψ : PhaseSpace d → PhaseSpace d)
        (e : PhaseSpace d → (PhaseSpace d ≃L[ℝ] PhaseSpace d)),
        (∀ z, HasFDerivAt (fun w => (charX t w, charV t w))
          ((e z : PhaseSpace d →L[ℝ] PhaseSpace d)) z) ∧
        Function.LeftInverse Ψ (fun z => (charX t z, charV t z)) ∧
        Function.RightInverse Ψ (fun z => (charX t z, charV t z)) ∧
        Continuous Ψ ∧
        (∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : PhaseSpace d →L[ℝ] PhaseSpace d) w) := by
  have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext_iff.mpr (hflow.1 z (Set.mem_univ z))
  have h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s := fun z s hs =>
    HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z)) (hflow.2.2 s hs z (Set.mem_univ z))
  have h_deriv_Ioo : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
    (h_deriv2 z s hs).hasDerivWithinAt
  obtain ⟨Dflow, hDeriv, hCont⟩ := charFlow_hasFDerivAt_in_initialPoint gradW hgradW_C1 L hL ρ
    charX charV T hT hflow h_int hρD_cont hcontIcc
  intro t ht
  set K : ℝ := ((max 1 L : NNReal) : ℝ) with hK
  have hCcoe : (((Real.exp (K * t)).toNNReal : NNReal) : ℝ) = Real.exp (K * t) :=
    Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _))
  have hderiv : ∀ z, HasFDerivAt (fun z => (charX t z, charV t z)) (Dflow t z) z := fun z =>
    hDeriv t ht z
  have hM_cont : Continuous (Dflow t) := hCont t ht
  have hanti : AntilipschitzWith (Real.exp (K * t)).toNNReal
      (fun z => (charX t z, charV t z)) := by
    refine AntilipschitzWith.of_le_mul_dist (fun z₁ z₂ => ?_)
    have h1 := charFlow_antilipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T
      h_init hcontIcc h_deriv2 t ht z₁ z₂
    rw [sub_zero] at h1
    rw [hCcoe, mul_comm]
    exact h1
  have hlip : LipschitzWith (Real.exp (K * t)).toNNReal
      (fun z => (charX t z, charV t z)) := by
    refine LipschitzWith.of_dist_le_mul (fun z₁ z₂ => ?_)
    have h1 := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
      h_init hcontIcc h_deriv_Ioo t (Set.Ioo_subset_Icc_self ht) z₁ z₂
    rw [sub_zero] at h1
    rw [hCcoe, mul_comm]
    exact h1
  obtain ⟨Ψ, e, he_coe, hLeft, hRight, hΨlip, hΨderiv⟩ :=
    exists_global_c1_inverse_of_antilipschitz hderiv hM_cont hanti hlip
  refine ⟨Ψ, e, ?_, hLeft, hRight, hΨlip.continuous, hΨderiv⟩
  intro z; rw [he_coe z]; exact hderiv z

section Step3Joint
open Filter Topology Asymptotics

/-- **Step 3 gating lemma (generic) — joint `C¹` from continuous partial derivatives** on a
`ℝ × E` domain (Mathlib-absent).  A partial `s`-derivative `Ds p` at every point (`Ds` continuous)
plus a partial `z`-derivative `Dz₀` at the base point ⇒ `f` is Fréchet-differentiable at `(s₀,z₀)`
with total derivative `(h,k) ↦ h•Ds(s₀,z₀) + Dz₀ k`.  Proof: split the increment into an
`s`-part (FTC `∫₀ʰ Ds(s₀+u,z₀+k)du ≈ h•Ds₀` by continuity of `Ds`) and a `z`-part (`= Dz₀ k + o(k)`).
This is the keystone for the joint `(s,w)` regularity of the two-time flow `Φ_{s→t}`: the flow's
partials are `M_s z` (jointly continuous, V2) in `z` and `b_s(Φ_s z)` in `s`.

**PR-ABLE (Mathlib upstream candidate).**  This is a general real-analysis result with no Vlasov
content — "a function on `ℝ × E` with a continuous partial derivative in the `ℝ` factor and a
Fréchet partial derivative in the `E` factor is Fréchet-differentiable" — filling a genuine gap in
`Mathlib/Analysis/Calculus`.  Generalisation worth doing before a PR: replace the `ℝ` factor by an
arbitrary first factor with an analogous "integrate the partial along segments" hypothesis, and
weaken `Continuous Ds` to `ContinuousAt Ds` at the base point (the proof only uses a neighbourhood
of `(s₀,z₀)`). -/
theorem hasFDerivAt_of_continuous_partials
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {Ds : ℝ × E → F} {Dz₀ : E →L[ℝ] F} (s₀ : ℝ) (z₀ : E)
    (hDs : ∀ p : ℝ × E, HasDerivAt (fun s => f (s, p.2)) (Ds p) p.1)
    (hDs_cont : Continuous Ds)
    (hDz₀ : HasFDerivAt (fun z => f (s₀, z)) Dz₀ z₀) :
    HasFDerivAt f
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (Ds (s₀, z₀))
        + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) (s₀, z₀) := by
  set Ds₀ : F := Ds (s₀, z₀) with hDs₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hBz : ∀ᶠ k in 𝓝 (0 : E),
      ‖f (s₀, z₀ + k) - f (s₀, z₀) - Dz₀ k‖ ≤ (ε / 2) * ‖k‖ := by
    have hz := hDz₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hz
    exact hz (half_pos hε)
  have hBz' : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ ≤ (ε / 2) * ‖p.2‖ :=
    (continuous_snd.tendsto (0 : ℝ × E)).eventually hBz
  have hball : ∀ᶠ q in 𝓝 ((s₀, z₀) : ℝ × E), ‖Ds q - Ds₀‖ ≤ ε / 2 := by
    have hc : Tendsto Ds (𝓝 (s₀, z₀)) (𝓝 Ds₀) := hDs_cont.continuousAt
    have hsub : Tendsto (fun q => Ds q - Ds₀) (𝓝 (s₀, z₀)) (𝓝 (Ds₀ - Ds₀)) :=
      hc.sub tendsto_const_nhds
    rw [sub_self] at hsub
    have h0 : Tendsto (fun q => ‖Ds q - Ds₀‖) (𝓝 (s₀, z₀)) (𝓝 0) := by
      simpa using hsub.norm
    exact h0.eventually (Iic_mem_nhds (half_pos hε))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hball
  have hAs : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖ ≤ (ε / 2) * ‖p‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hδpos] with p hp
    rw [mem_ball_zero_iff] at hp
    have hcont_u : Continuous (fun u => Ds (u, z₀ + p.2)) :=
      hDs_cont.comp (continuous_id.prodMk continuous_const)
    have hg_deriv : ∀ u : ℝ, HasDerivAt (fun s => f (s, z₀ + p.2)) (Ds (u, z₀ + p.2)) u :=
      fun u => hDs (u, z₀ + p.2)
    have hftc : ∫ u in s₀..(s₀ + p.1), Ds (u, z₀ + p.2)
        = f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hg_deriv u)
        (hcont_u.intervalIntegrable _ _)]
    have hbound_u : ∀ u ∈ Set.uIoc s₀ (s₀ + p.1), ‖Ds (u, z₀ + p.2) - Ds₀‖ ≤ ε / 2 := by
      intro u hu
      refine @hδ (u, z₀ + p.2) ?_
      have hple : |p.1| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le p
      have hp1 : |u - s₀| ≤ ‖p‖ := by
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hu) with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s₀)]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)] at hple; linarith
        · rw [abs_of_nonpos (by linarith : u - s₀ ≤ 0)]
          rw [abs_of_nonpos (by linarith : p.1 ≤ 0)] at hple; linarith
      have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      rw [Prod.dist_eq]
      simp only [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
      exact lt_of_le_of_lt (max_le hp1 hp2) hp
    have hA_eq : f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀
        = ∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀) := by
      rw [intervalIntegral.integral_sub (hcont_u.intervalIntegrable _ _)
          (intervalIntegrable_const), hftc, intervalIntegral.integral_const,
          add_sub_cancel_left]
    rw [hA_eq]
    calc ‖∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀)‖
        ≤ (ε / 2) * |(s₀ + p.1) - s₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound_u
      _ = (ε / 2) * ‖p.1‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
      _ ≤ (ε / 2) * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (by positivity)
  filter_upwards [hAs, hBz'] with p hAp hBp
  have hdecomp :
      f ((s₀, z₀) + p) - f (s₀, z₀)
        - ((ContinuousLinearMap.fst ℝ ℝ E).smulRight Ds₀
            + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) p
      = (f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
        + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2) := by
    rw [show ((s₀, z₀) + p : ℝ × E) = (s₀ + p.1, z₀ + p.2) from rfl]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
    abel
  rw [hdecomp]
  calc ‖(f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
          + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2)‖
      ≤ ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖
        + ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖p‖ + (ε / 2) * ‖p‖ :=
        add_le_add hAp (le_trans hBp (mul_le_mul_of_nonneg_left (norm_snd_le p) (by positivity)))
    _ = ε * ‖p‖ := by ring

/-- **Step 3 gating lemma (LOCAL / open-set form)** — joint `HasFDerivAt` from continuous partial
derivatives on an open set `U ⊆ ℝ × E`.  The open-set generalisation of
`hasFDerivAt_of_continuous_partials` (which is the `U := univ` special case) that the PR-note above
flagged: the `s`-partial is required only on `U`, and `Ds` only `ContinuousOn U`.  This is the form
the Vlasov flow needs — its partials exist and are continuous only on the open window
`Ioo 0 T ×ˢ univ`.  Proof = the global proof + ball-in-`U` bookkeeping (`B((s₀,z₀),r) ⊆ U`; the FTC
segment points `(u, z₀+p.2)`, `u ∈ uIcc s₀ (s₀+p.1)`, lie within `‖p‖ < min δ (r/2)` of `(s₀,z₀)`,
hence in `U` and within the continuity radius `δ`).

NOTE (consolidation TODO): the global `hasFDerivAt_of_continuous_partials` above is the `univ`
special case of this; a follow-up cleanup should rewrite it as the one-line corollary
`hasFDerivAt_of_continuous_partials_open isOpen_univ (Set.mem_univ _) (fun p _ => hDs p)
hDs_cont.continuousOn hDz₀` to drop the duplicated proof.  **PR-ABLE** (the more general statement). -/
theorem hasFDerivAt_of_continuous_partials_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {Ds : ℝ × E → F} {Dz₀ : E →L[ℝ] F}
    {U : Set (ℝ × E)} (hU : IsOpen U) {s₀ : ℝ} {z₀ : E} (hmem : (s₀, z₀) ∈ U)
    (hDs : ∀ p ∈ U, HasDerivAt (fun s => f (s, p.2)) (Ds p) p.1)
    (hDs_cont : ContinuousOn Ds U)
    (hDz₀ : HasFDerivAt (fun z => f (s₀, z)) Dz₀ z₀) :
    HasFDerivAt f
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (Ds (s₀, z₀))
        + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) (s₀, z₀) := by
  set Ds₀ : F := Ds (s₀, z₀) with hDs₀
  obtain ⟨r, hrpos, hrU⟩ := Metric.isOpen_iff.mp hU (s₀, z₀) hmem
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hBz : ∀ᶠ k in 𝓝 (0 : E),
      ‖f (s₀, z₀ + k) - f (s₀, z₀) - Dz₀ k‖ ≤ (ε / 2) * ‖k‖ := by
    have hz := hDz₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hz
    exact hz (half_pos hε)
  have hBz' : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ ≤ (ε / 2) * ‖p.2‖ :=
    (continuous_snd.tendsto (0 : ℝ × E)).eventually hBz
  have hball : ∀ᶠ q in 𝓝 ((s₀, z₀) : ℝ × E), ‖Ds q - Ds₀‖ ≤ ε / 2 := by
    have hc : Tendsto Ds (𝓝 (s₀, z₀)) (𝓝 Ds₀) := hDs_cont.continuousAt (hU.mem_nhds hmem)
    have hsub : Tendsto (fun q => Ds q - Ds₀) (𝓝 (s₀, z₀)) (𝓝 (Ds₀ - Ds₀)) :=
      hc.sub tendsto_const_nhds
    rw [sub_self] at hsub
    have h0 : Tendsto (fun q => ‖Ds q - Ds₀‖) (𝓝 (s₀, z₀)) (𝓝 0) := by
      simpa using hsub.norm
    exact h0.eventually (Iic_mem_nhds (half_pos hε))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hball
  set ρr : ℝ := min δ (r / 2) with hρr
  have hρrpos : 0 < ρr := lt_min hδpos (by positivity)
  have hAs : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖ ≤ (ε / 2) * ‖p‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hρrpos] with p hp
    rw [mem_ball_zero_iff] at hp
    have hdist : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1),
        dist ((u, z₀ + p.2) : ℝ × E) (s₀, z₀) ≤ ‖p‖ := by
      intro u hu
      have hple : |p.1| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le p
      have hp1 : |u - s₀| ≤ ‖p‖ := by
        rcases Set.mem_uIcc.mp hu with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s₀)]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)] at hple; linarith
        · rw [abs_of_nonpos (by linarith : u - s₀ ≤ 0)]
          rw [abs_of_nonpos (by linarith : p.1 ≤ 0)] at hple; linarith
      have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      rw [Prod.dist_eq]
      refine max_le ?_ ?_
      · rw [dist_eq_norm]; simpa [Real.norm_eq_abs] using hp1
      · rw [dist_eq_norm, add_sub_cancel_left]; exact hp2
    have hmemU : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1), ((u, z₀ + p.2) : ℝ × E) ∈ U := by
      intro u hu
      apply hrU
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (hdist u hu)
        (lt_of_lt_of_le hp (le_trans (min_le_right _ _) (by linarith)))
    have hcont_u : ContinuousOn (fun u => Ds (u, z₀ + p.2)) (Set.uIcc s₀ (s₀ + p.1)) := by
      refine hDs_cont.comp (continuous_id.prodMk continuous_const).continuousOn ?_
      exact fun u hu => hmemU u hu
    have hg_deriv : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1),
        HasDerivAt (fun s => f (s, z₀ + p.2)) (Ds (u, z₀ + p.2)) u :=
      fun u hu => hDs (u, z₀ + p.2) (hmemU u hu)
    have hftc : ∫ u in s₀..(s₀ + p.1), Ds (u, z₀ + p.2)
        = f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hg_deriv u hu)
        (hcont_u.intervalIntegrable)]
    have hbound_u : ∀ u ∈ Set.uIoc s₀ (s₀ + p.1), ‖Ds (u, z₀ + p.2) - Ds₀‖ ≤ ε / 2 := by
      intro u hu
      refine @hδ (u, z₀ + p.2) ?_
      have hmem' := hdist u (Set.uIoc_subset_uIcc hu)
      exact lt_of_le_of_lt hmem' (lt_of_lt_of_le hp (min_le_left _ _))
    have hA_eq : f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀
        = ∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀) := by
      rw [intervalIntegral.integral_sub (hcont_u.intervalIntegrable)
          (intervalIntegrable_const), hftc, intervalIntegral.integral_const,
          add_sub_cancel_left]
    rw [hA_eq]
    calc ‖∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀)‖
        ≤ (ε / 2) * |(s₀ + p.1) - s₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound_u
      _ = (ε / 2) * ‖p.1‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
      _ ≤ (ε / 2) * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (by positivity)
  filter_upwards [hAs, hBz'] with p hAp hBp
  have hdecomp :
      f ((s₀, z₀) + p) - f (s₀, z₀)
        - ((ContinuousLinearMap.fst ℝ ℝ E).smulRight Ds₀
            + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) p
      = (f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
        + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2) := by
    rw [show ((s₀, z₀) + p : ℝ × E) = (s₀ + p.1, z₀ + p.2) from rfl]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
    abel
  rw [hdecomp]
  calc ‖(f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
          + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2)‖
      ≤ ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖
        + ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖p‖ + (ε / 2) * ‖p‖ :=
        add_le_add hAp (le_trans hBp (mul_le_mul_of_nonneg_left (norm_snd_le p) (by positivity)))
    _ = ε * ‖p‖ := by ring

end Step3Joint

/-- **Step 3 — the forward flow `(s,z) ↦ Φ_s z` is jointly continuous** on `Icc 0 T ×ˢ univ`
(`(s,z)`-order).  Gronwall Lipschitz-in-`z` (uniform over `[0,T]`) + per-`z` continuity-in-`s`, via
the generic `continuousOn_prod_of_lipschitz_continuousOn`, then a prod-order swap.  Extracted from
`#3`'s V2-branch pattern so the joint `C¹`-ness (Step 3 (iii)) can reuse it directly. -/
lemma charFlow_continuousOn_joint
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (hT : 0 ≤ T)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0:ℝ) T))
    (hderiv : ∀ z, ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s) :
    ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) := by
  have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT
    hinit hcontIcc hderiv
  have hjoint_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1))
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) := by
    refine continuousOn_prod_of_lipschitz_continuousOn (fun z s => (charX s z, charV s z)) T
      (Real.exp (((max 1 L : NNReal) : ℝ) * T)) (fun s hs z₁ z₂ => ?_) hcontIcc
    calc dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        ≤ dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) := hgron s hs z₁ z₂
      _ = Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) * dist z₁ z₂ := by ring
      _ ≤ Real.exp (((max 1 L : NNReal) : ℝ) * T) * dist z₁ z₂ := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) dist_nonneg
          have hsT : s - 0 ≤ T := by simp only [sub_zero]; exact hs.2
          exact mul_le_mul_of_nonneg_left hsT (by positivity)
  have hswap : ContinuousOn (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) := (continuous_snd.prodMk continuous_fst).continuousOn
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc (0:ℝ) T) :=
    fun p hp => ⟨Set.mem_univ _, hp.1⟩
  exact hjoint_zs.comp hswap hmaps

/-- **Step 3 (ii) — the field along the flow `(s,z) ↦ b_s(Φ_s z)` is jointly continuous** on
`Icc 0 T ×ˢ univ`.  First component `charV` from flow joint continuity; second component
`-(∇W ∗ ρ_s)(charX s z)` from `(s,x) ↦ (∇W∗ρ_s)(x)` jointly continuous (equi-Lipschitz-in-`x` from
`convolveFunctionMeasure_lipschitz_in_x` + continuous-in-`s` from `hf_cont`) composed with the flow.
This is the partial-`s`-derivative continuity input to the joint `C¹`-ness (Step 3 (iii)). -/
lemma vlasovField_along_flow_continuousOn
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ)
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × PhaseSpace d =>
        vlasovVectorField gradW ρ p.1 (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) := by
  have hcomp1 : ContinuousOn (fun p : ℝ × PhaseSpace d => charV p.1 p.2)
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) := continuous_snd.comp_continuousOn hflowjoint
  have hcharX : ContinuousOn (fun p : ℝ × PhaseSpace d => charX p.1 p.2)
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) := continuous_fst.comp_continuousOn hflowjoint
  have hconv_joint : ContinuousOn
      (fun p : PhysSpace d × ℝ => convolveFunctionMeasure gradW (ρ p.2) p.1)
      (Set.univ ×ˢ Set.Icc (0:ℝ) T) :=
    continuousOn_prod_of_lipschitz_continuousOn
      (fun (x : PhysSpace d) (s : ℝ) => convolveFunctionMeasure gradW (ρ s) x) T (L:ℝ)
      (fun s _ x₁ x₂ =>
        (convolveFunctionMeasure_lipschitz_in_x gradW L hL (ρ s) (h_int s)).dist_le_mul x₁ x₂)
      (fun x => (hf_cont x).continuousOn)
  have hg2 : ContinuousOn (fun p : ℝ × PhaseSpace d => ((charX p.1 p.2, p.1) : PhysSpace d × ℝ))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) := hcharX.prodMk continuousOn_fst
  have hg2maps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((charX p.1 p.2, p.1) : PhysSpace d × ℝ))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc (0:ℝ) T) :=
    fun p hp => ⟨Set.mem_univ _, hp.1⟩
  have hconv_along : ContinuousOn
      (fun p : ℝ × PhaseSpace d => convolveFunctionMeasure gradW (ρ p.1) (charX p.1 p.2))
      (Set.Icc (0:ℝ) T ×ˢ Set.univ) := hconv_joint.comp hg2 hg2maps
  have heq : (fun p : ℝ × PhaseSpace d =>
        vlasovVectorField gradW ρ p.1 (charX p.1 p.2, charV p.1 p.2))
      = fun p => ((charV p.1 p.2),
          -(convolveFunctionMeasure gradW (ρ p.1) (charX p.1 p.2))) := by
    funext p; rfl
  rw [heq]
  exact hcomp1.prodMk hconv_along.neg

/-- **Step 3 (iii) — the forward flow `(s,z) ↦ Φ_s z` is jointly `C¹`** on `U := Ioo 0 T ×ˢ univ`:
Fréchet-differentiable at every point with a jointly-continuous total derivative `DΦ`.  Built by
composing the open-set gating theorem (`hasFDerivAt_of_continuous_partials_open`) — fed the
`s`-partial `b_s(Φ_s z)` (flow ODE, jointly continuous by item (ii)) and the `z`-partial `M_s z`
(the fundamental matrix, via D1c, jointly continuous by item (i)).  Per L14 the matrix is rebuilt
concretely (`fundamentalMatrix (A z) s`), NOT routed through `#3`'s existential.

The field `bfun` and matrix `Mfun` are made opaque locals (`clear_value`, the D1c lesson) so the
gating unification stays syntactic and never unfolds the `vlasovVectorField`/`vlasovFieldJacobian`
integrals — the per-point derivative facts are established in terms of them *before* clearing.
`A` is kept transparent through the D1c call (whose coefficient is `vlasovFieldJacobian`) and cleared
only afterwards (before the projection-reduction defeqs).  No `maxHeartbeats` bump needed. -/
theorem charFlow_hasFDerivAt_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0:ℝ) T)) :
    ∃ DΦ : ℝ × PhaseSpace d → (ℝ × PhaseSpace d →L[ℝ] PhaseSpace d),
      (∀ p ∈ Set.Ioo (0:ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
        HasFDerivAt (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (DΦ p) p) ∧
      ContinuousOn DΦ (Set.Ioo (0:ℝ) T ×ˢ Set.univ) := by
  set A : PhaseSpace d → ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun z s => vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z)) with hA_def
  have hAcont : ∀ z, ContinuousOn (A z) (Set.Icc 0 T) := fun z =>
    vlasovVariationalCoeff_continuousOn gradW ρ charX charV T z (hcontIcc z) hρD_cont
  have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext_iff.mpr ⟨(hflow.1 z (Set.mem_univ z)).1, (hflow.1 z (Set.mem_univ z)).2⟩
  have h_deriv : ∀ z, ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
    (HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z))
      (hflow.2.2 s hs z (Set.mem_univ z))).hasDerivWithinAt
  have hflowjoint_sz : ContinuousOn (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    charFlow_continuousOn_joint gradW L hL ρ h_int charX charV T hT.le h_init hcontIcc h_deriv
  -- field as an opaque local
  set bfun : ℝ × PhaseSpace d → PhaseSpace d :=
    fun q => vlasovVectorField gradW ρ q.1 (charX q.1 q.2, charV q.1 q.2) with hbfun_def
  have hb_cont : ContinuousOn bfun (Set.Icc 0 T ×ˢ Set.univ) :=
    vlasovField_along_flow_continuousOn gradW L hL ρ h_int hf_cont charX charV T hflowjoint_sz
  -- `A` jointly continuous + bounded ⇒ `M` jointly continuous (item (i))
  have hflowjoint_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1))
      (Set.univ ×ˢ Set.Icc 0 T) := by
    have hswap : ContinuousOn (fun p : PhaseSpace d × ℝ => ((p.2, p.1) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) := (continuous_snd.prodMk continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun p : PhaseSpace d × ℝ => ((p.2, p.1) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
    exact hflowjoint_sz.comp hswap hmaps
  have hg : ContinuousOn
      (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
      (Set.univ ×ˢ Set.Icc 0 T) := continuousOn_snd.prodMk hflowjoint_zs
  have hmapsg : Set.MapsTo
      (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
      (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
  have hA_contOn : ContinuousOn (fun p : PhaseSpace d × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc 0 T) :=
    (vlasovFieldJacobian_continuousOn gradW ρ T hρD_cont).comp hg hmapsg
  have hA_bound : ∀ z, ∀ s ∈ Set.Icc (0:ℝ) T, ‖A z s‖ ≤ ((max 1 L : NNReal) : ℝ) := by
    intro z s _
    have heq : A z s = fderiv ℝ (vlasovVectorField gradW ρ s) (charX s z, charV s z) := by
      simp only [hA_def]
      exact (vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s
        (charX s z, charV s z)).fderiv.symm
    rw [heq]
    exact norm_fderiv_le_of_lipschitz ℝ (vlasovVectorField_lipschitzWith gradW L hL ρ h_int s)
  have hM_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => fundamentalMatrix (A p.1) p.2)
      (Set.univ ×ˢ Set.Icc 0 T) :=
    fundamentalMatrix_continuous_param_joint A T hT.le ((max 1 L : NNReal) : ℝ) (by positivity)
      hA_contOn hA_bound
  have hU_open : IsOpen (Set.Ioo (0:ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  have hU_sub : Set.Ioo (0:ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) ⊆ Set.Icc 0 T ×ˢ Set.univ :=
    Set.prod_mono Set.Ioo_subset_Icc_self (subset_refl _)
  -- matrix as a local (kept transparent for the D1c call, which needs `A`'s coefficient)
  set Mfun : ℝ × PhaseSpace d → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun p => fundamentalMatrix (A p.2) p.1 with hMfun_def
  -- z-partial at base via D1c — needs `A` TRANSPARENT (its coefficient is `vlasovFieldJacobian`).
  have hDz_all : ∀ s₀ ∈ Set.Ioo (0:ℝ) T, ∀ z₀ : PhaseSpace d,
      HasFDerivAt (fun z => (charX s₀ z, charV s₀ z)) (Mfun (s₀, z₀)) z₀ := by
    intro s₀ hs₀ z₀
    obtain ⟨h0, hMcont, hMderiv⟩ := fundamentalMatrix_spec (A z₀) T hT.le (hAcont z₀)
    exact charFlow_hasFDerivAt_of_fundamentalMatrix gradW hgradW_C1 L hL ρ charX charV T hT hflow
      h_int hρD_cont z₀ hcontIcc (fundamentalMatrix (A z₀)) h0 hMcont hMderiv s₀ hs₀
  have hDs_all : ∀ p ∈ Set.Ioo (0:ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s => ((charX s p.2, charV s p.2) : PhaseSpace d)) (bfun p) p.1 := by
    intro p hp'
    exact HasDerivAt.prodMk (hflow.2.1 p.1 hp'.1 p.2 (Set.mem_univ _))
      (hflow.2.2 p.1 hp'.1 p.2 (Set.mem_univ _))
  -- NOW make `A`/field/matrix opaque so the projection-reduction defeqs below never unfold the
  -- heavy `vlasovFieldJacobian`/`vlasovVectorField` integrals (D1c lesson).
  clear_value A bfun Mfun
  have hM_sz : ContinuousOn Mfun (Set.Ioo (0:ℝ) T ×ˢ Set.univ) := by
    rw [hMfun_def]
    have hswap : ContinuousOn (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
        (Set.Ioo (0:ℝ) T ×ˢ Set.univ) := (continuous_snd.prodMk continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
        (Set.Ioo (0:ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc 0 T) :=
      fun p hp => ⟨Set.mem_univ _, Set.Ioo_subset_Icc_self hp.1⟩
    exact hM_zs.comp hswap hmaps
  refine ⟨fun p => (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight (bfun p)
      + (Mfun p).comp (ContinuousLinearMap.snd ℝ ℝ (PhaseSpace d)), ?_, ?_⟩
  · rintro ⟨s₀, z₀⟩ hp
    obtain ⟨hs₀, _⟩ := hp
    exact hasFDerivAt_of_continuous_partials_open
      (f := fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (Ds := bfun)
      hU_open ⟨hs₀, Set.mem_univ _⟩ hDs_all (hb_cont.mono hU_sub) (hDz_all s₀ hs₀ z₀)
  · have hT1 : ContinuousOn (fun p : ℝ × PhaseSpace d =>
        (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight (bfun p))
        (Set.Ioo (0:ℝ) T ×ˢ Set.univ) := by
      have hc : Continuous (fun v : PhaseSpace d =>
          (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight v) :=
        (ContinuousLinearMap.smulRightL ℝ (ℝ × PhaseSpace d) (PhaseSpace d)
          (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d))).continuous
      exact hc.comp_continuousOn (hb_cont.mono hU_sub)
    have hT2 : ContinuousOn (fun p : ℝ × PhaseSpace d =>
        (Mfun p).comp (ContinuousLinearMap.snd ℝ ℝ (PhaseSpace d)))
        (Set.Ioo (0:ℝ) T ×ˢ Set.univ) := hM_sz.clm_comp continuousOn_const
    exact hT1.add hT2

/-- **Step 3 (iv-A) — the forward flow `(s,z) ↦ Φ_s z` is `ContDiffAt ℝ 1`** at each point of the
open window (the chart-IFT input for item (iv)).  Lifts item (iii)'s `HasFDerivAt`-everywhere +
`ContinuousOn`-derivative to `ContDiffAt` via `contDiffAt_succ_iff_hasFDerivAt`. -/
lemma charFlow_contDiffAt_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0:ℝ) T)) :
    ∀ p ∈ Set.Ioo (0:ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      ContDiffAt ℝ 1 (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) p := by
  obtain ⟨DΦ, hFDeriv, hDΦ_cont⟩ := charFlow_hasFDerivAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hU_open : IsOpen (Set.Ioo (0:ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  intro p hp
  have hmain : ContDiffAt ℝ ((0:ℕ) + 1)
      (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) p := by
    rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨DΦ, ⟨Set.Ioo (0:ℝ) T ×ˢ Set.univ, hU_open.mem_nhds hp, fun y hy => hFDeriv y hy⟩, ?_⟩
    exact contDiffAt_zero.mpr ⟨Set.Ioo (0:ℝ) T ×ˢ Set.univ, hU_open.mem_nhds hp, hDΦ_cont⟩
  simpa using hmain

open Filter Topology in
/-- **Step 3 (iv) — the per-slice inverse `Ψ_s := Φ_s⁻¹` is jointly `C¹`** on `Ioo 0 T ×ˢ univ`,
the keystone of the two-time flow `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹`.

**PROVEN (axiom-clean)** via the space-time chart inverse-function theorem — see the proof plan
below, realized exactly as scouted: `charFlow_contDiffAt_joint` (iv-A) for the chart `ContDiffAt`,
the block-triangular `≃L` (invertibility from Step 2's `e z₀` via `HasFDerivAt.unique` +
`ofBijective`), `ContDiffAt.to_localInverse`, and the global patch via `localInverse_unique` (the
global per-slice inverse is a local left inverse of the chart, by injectivity on the window).

Per slice `s ∈ Ioo 0 T`, Step 2 (`exists_charFlow_inverse_On`) already gives the inverse `Ψ_s` and
its invertible derivative family `e` (`= M_s z`, `#3`/D1c); here we upgrade to JOINT `(s,w)`
regularity via the space-time chart.

**Proof plan (atoms scouted + verified, 2026-06-16):**
1. **Forward chart `Ξ : (s,z) ↦ (s, Φ_s z)` is `ContDiffAt ℝ 1` at each `(s₀,z₀) ∈ Ioo 0 T ×ˢ univ`.**
   `Φ := (charX·, charV·)` is jointly `C¹` (`charFlow_hasFDerivAt_joint`, item (iii) — `∃ DΦ`,
   `HasFDerivAt`-everywhere + `ContinuousOn DΦ`); lift to `ContDiffAt ℝ 1 Φ` via
   `contDiffAt_succ_iff_hasFDerivAt` (`Mathlib/.../ContDiff/Defs.lean:994`, `n := 0`: feed `DΦ`, the
   open nbhd `U ∈ 𝓝`, `HasFDerivAt`-on-`U`, and `ContDiffAt 0 DΦ` from `contDiffAt_zero` +
   `ContinuousOn DΦ U`).  `Ξ = (fst, Φ)` so `ContDiffAt ℝ 1 Ξ` via `ContDiffAt.prod` with
   `contDiffAt_fst`.
2. **`DΞ(s₀,z₀)` is an invertible `≃L`.**  Block-lower-triangular `(h,k) ↦ (h, h•b + M·k)` with
   `b := b_{s₀}(Φ_{s₀}z₀)`, `M := M_{s₀}z₀` invertible (Step 2's `e₀ z₀`).  Build the `ℝ×E ≃L ℝ×E`
   via `ContinuousLinearEquiv.ofBijective` (inject: `(h,k)↦0 ⇒ h=0`, then `M k=0 ⇒ k=0`; finite-dim
   `LinearMap.injective_iff_surjective`).  `HasStrictFDerivAt Ξ (this ≃L) (s₀,z₀)` via
   `ContDiffAt.hasStrictFDerivAt'`.
3. **Local `C¹` inverse + patch.**  `ContDiffAt.to_localInverse`
   (`Mathlib/.../InverseFunctionTheorem/ContDiff.lean:66`) ⇒ `Ξ.localInverse` is `ContDiffAt ℝ 1` at
   `Ξ(s₀,z₀) = (s₀, Φ_{s₀}z₀)`.  The global `(s,w)↦(s, Ψ_s w)` agrees with `Ξ.localInverse` on a nbhd
   (both left-inverses; `Ξ` injective on `Ioo 0 T ×ˢ univ` since `s` is preserved + each `Φ_s`
   injective per Step 2) ⇒ `ContDiffAt.congr` ⇒ `(s,w)↦(s,Ψ_s w)` is `ContDiffAt ℝ 1` at each point
   ⇒ `ContDiffOn ℝ 1` (projecting off the `s` component, `ContDiffAt.snd`).
4. **Bijectivity** is the per-slice `LeftInverse`/`RightInverse` from `exists_charFlow_inverse_On`,
   packaged into the `s`-indexed `Ψ`.
The two-time flow `Φ_{s→t} = Φ_t ∘ Ψ_s` is then jointly `C¹` by composing with `Φ_t` (`C¹` in its
argument, `#3`), and the dual core's transport identity differentiates it. -/
theorem charFlow_inverse_contDiffOn_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0:ℝ) T)) :
    ∃ Ψ : ℝ → PhaseSpace d → PhaseSpace d,
      (∀ s ∈ Set.Ioo (0:ℝ) T,
        Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      (∀ s ∈ Set.Ioo (0:ℝ) T,
        Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2) (Set.Ioo 0 T ×ˢ Set.univ) := by
  classical
  obtain ⟨DΦ, hFDeriv, -⟩ := charFlow_hasFDerivAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hΦ_cda := charFlow_contDiffAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hstep2 := exists_charFlow_inverse_On gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hρD_cont hcontIcc
  have hbij : ∀ s ∈ Set.Ioo (0:ℝ) T,
      Function.Bijective (fun z => ((charX s z, charV s z) : PhaseSpace d)) := by
    intro s hs
    obtain ⟨Ψ', e, _, hL', hR', _, _⟩ := hstep2 s hs
    exact ⟨hL'.injective, hR'.surjective⟩
  set Ψ : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => Function.invFun (fun z => (charX s z, charV s z)) with hΨ_def
  have hLeft : ∀ s ∈ Set.Ioo (0:ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)) :=
    fun s hs => Function.leftInverse_invFun (hbij s hs).1
  have hRight : ∀ s ∈ Set.Ioo (0:ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)) :=
    fun s hs => Function.rightInverse_invFun (hbij s hs).2
  refine ⟨Ψ, hLeft, hRight, ?_⟩
  set Ξ : ℝ × PhaseSpace d → ℝ × PhaseSpace d :=
    fun x => (x.1, (charX x.1 x.2, charV x.1 x.2)) with hΞ_def
  intro pt hpt
  obtain ⟨hs₀, -⟩ := hpt
  obtain ⟨Ψ', e, he_deriv, -, -, -, -⟩ := hstep2 pt.1 hs₀
  set z₀ : PhaseSpace d := Ψ pt.1 pt.2 with hz₀_def
  have hΦz₀ : (charX pt.1 z₀, charV pt.1 z₀) = pt.2 := hRight pt.1 hs₀ pt.2
  have hΞ_cda : ContDiffAt ℝ 1 Ξ (pt.1, z₀) :=
    contDiffAt_fst.prodMk (hΦ_cda (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩)
  set DΞ : (ℝ × PhaseSpace d) →L[ℝ] (ℝ × PhaseSpace d) :=
    (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).prod (DΦ (pt.1, z₀)) with hDΞ_def
  have hΞ_hd : HasFDerivAt Ξ DΞ (pt.1, z₀) :=
    (hasFDerivAt_fst).prodMk (hFDeriv (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩)
  have hincl : HasFDerivAt (fun z : PhaseSpace d => ((pt.1, z) : ℝ × PhaseSpace d))
      ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d))) z₀ :=
    (hasFDerivAt_const (pt.1 : ℝ) z₀).prodMk (hasFDerivAt_id z₀)
  have hslice : HasFDerivAt (fun z => (charX pt.1 z, charV pt.1 z))
      ((DΦ (pt.1, z₀)).comp
        ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d)))) z₀ :=
    (hFDeriv (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩).comp z₀ hincl
  have hcomp_eq : (DΦ (pt.1, z₀)).comp
      ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d)))
      = (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) :=
    hslice.unique (he_deriv z₀)
  have hslice_app : ∀ k : PhaseSpace d,
      DΦ (pt.1, z₀) ((0:ℝ), k) = (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) k := by
    intro k
    have h1 : ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d))) k
        = ((0:ℝ), k) := by simp
    rw [← h1, ← ContinuousLinearMap.comp_apply, hcomp_eq]
  have hker : LinearMap.ker (DΞ : (ℝ × PhaseSpace d) →ₗ[ℝ] (ℝ × PhaseSpace d)) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr (fun x hx => ?_)
    have hxapp : (x.1, DΦ (pt.1, z₀) x) = ((0:ℝ), (0 : PhaseSpace d)) := by
      have : DΞ x = ((0:ℝ), (0 : PhaseSpace d)) := hx
      simpa [hDΞ_def, ContinuousLinearMap.prod_apply] using this
    have hx1 : x.1 = 0 := (Prod.ext_iff.mp hxapp).1
    have hx2 : DΦ (pt.1, z₀) x = 0 := (Prod.ext_iff.mp hxapp).2
    have hxz : x = ((0:ℝ), x.2) := Prod.ext hx1 rfl
    have hez : (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) x.2 = 0 := by
      rw [← hslice_app x.2, ← hxz]; exact hx2
    have : x.2 = 0 := by
      have hinj := (e z₀).injective
      have : (e z₀) x.2 = (e z₀) 0 := by rw [map_zero]; exact_mod_cast hez
      exact hinj this
    exact Prod.ext hx1 this
  have hrange : LinearMap.range (DΞ : (ℝ × PhaseSpace d) →ₗ[ℝ] (ℝ × PhaseSpace d)) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker))
  set eΞ : (ℝ × PhaseSpace d) ≃L[ℝ] (ℝ × PhaseSpace d) :=
    ContinuousLinearEquiv.ofBijective DΞ hker hrange with heΞ_def
  have hΞ_hd' : HasFDerivAt Ξ (eΞ : (ℝ × PhaseSpace d) →L[ℝ] (ℝ × PhaseSpace d)) (pt.1, z₀) :=
    hΞ_hd
  have hlocinv : ContDiffAt ℝ 1 (hΞ_cda.localInverse hΞ_hd' one_ne_zero) (Ξ (pt.1, z₀)) :=
    hΞ_cda.to_localInverse hΞ_hd' one_ne_zero
  have hstrict := hΞ_cda.hasStrictFDerivAt' hΞ_hd' (one_ne_zero)
  have hloc : ∀ᶠ x in 𝓝 ((pt.1, z₀) : ℝ × PhaseSpace d),
      ((fun y : ℝ × PhaseSpace d => ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d)) (Ξ x)) = x := by
    have hIoo : ∀ᶠ x in 𝓝 ((pt.1, z₀) : ℝ × PhaseSpace d), x.1 ∈ Set.Ioo (0:ℝ) T :=
      continuous_fst.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hs₀)
    filter_upwards [hIoo] with x hx
    have hL2 : Ψ x.1 (charX x.1 x.2, charV x.1 x.2) = x.2 := hLeft x.1 hx x.2
    simp only [hΞ_def]
    rw [hL2]
  have huniq : ∀ᶠ y in 𝓝 (Ξ (pt.1, z₀)),
      ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d) = (hΞ_cda.localInverse hΞ_hd' one_ne_zero) y :=
    hstrict.localInverse_unique hloc
  have hΞeq : Ξ (pt.1, z₀) = (pt.1, pt.2) := by rw [hΞ_def]; exact Prod.ext rfl hΦz₀
  have hG_cda : ContDiffAt ℝ 1
      (fun y : ℝ × PhaseSpace d => ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d)) (pt.1, pt.2) := by
    rw [← hΞeq]
    exact hlocinv.congr_of_eventuallyEq huniq
  have hpt_eq : pt = (pt.1, pt.2) := rfl
  rw [hpt_eq]
  exact (hG_cda.snd).contDiffWithinAt

/-! ### Step 4 — the transported test function and the transport identity

The dual core's `s ↦ ∫ ψ_s d(f s)` argument rests on the backward-transported test
`ψ_s := φ ∘ Φ_{s→t}` where `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is the two-time flow (Step 3 gave it jointly
`C¹`).  Two deliverables, both taking the *outputs* of Step 3 (the inverse `Ψ` + the `C¹` terminal
map `Φ_t`) as hypotheses rather than re-deriving them from the flow-construction data: -/

/-- **Step 4 (4a) — the two-time flow `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is jointly `C¹`** on
`Ioo 0 T ×ˢ univ`.

The two-time flow `(s,w) ↦ (charX t (Ψ_s w), charV t (Ψ_s w))` is the composition of the terminal
map `Φ_t = (charX t ·, charV t ·)` (`C¹` in its argument — `hΦt_C1`, from Step 2 / item (iii) at the
fixed time `t`) with the jointly-`C¹` inverse family `(s,w) ↦ Ψ_s w` (`hΨ_C1`, item (iv)).  Proof:
`ContDiff.comp_contDiffOn`. -/
theorem twoTimeFlow_contDiffOn_joint
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T t : ℝ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z))) :
    ContDiffOn ℝ 1
      (fun p : ℝ × PhaseSpace d => ((charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) : PhaseSpace d))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
  hΦt_C1.comp_contDiffOn hΨ_C1

/-- **Step 4 (4b) — the transport identity `∂_s ψ_s + Dψ_s · b_s = 0`.**

For the backward-transported test `ψ_s(w) := φ(Φ_t(Ψ_s w)) = φ(Φ_{s→t} w)`, the partial
`s`-derivative cancels the spatial directional derivative along the field:
`∂_s ψ_s(w) = -(Dψ_s(w))(b_s(w))`, where `b_s = vlasovVectorField gradW ρ s` and
`Dψ_s(w) = fderiv ℝ (ψ s) w`.  This is the dual of `vlasov_traj_chain_rule` (the pushforward
direction) and the engine that makes `s ↦ ∫ ψ_s d(f s)` constant in Step 6.

Proof:
* `ψ` is jointly `C¹` on `Ioo 0 T ×ˢ univ` (4a + `φ` smooth), so `HasFDerivAt (uncurry ψ) Dψ (s,w)`
  at the interior point `(s,w)`, with `Dψ` the joint Fréchet derivative.
* Constancy curve: set `z₀ := Ψ_s w`, so `w = Φ_s z₀` (`hΨ_right`).  The composite
  `s' ↦ ψ_{s'}(Φ_{s'} z₀) = φ(Φ_t(Ψ_{s'}(Φ_{s'} z₀))) = φ(Φ_t z₀)` is **constant** in `s'`
  (`hΨ_left`: `Ψ_{s'} ∘ Φ_{s'} = id`), hence has zero `s'`-derivative.
* The curve `c(s') := (s', Φ_{s'} z₀)` has `HasDerivAt c (1, b_s w) s` (`hflow_ode` + `id`), with
  `c(s) = (s, w)`.  Chain rule: `0 = Dψ(s,w)(1, b_s w) = Dψ(s,w)(1,0) + Dψ(s,w)(0, b_s w)`.
* `Dψ(s,w)(1,0) = ∂_s ψ_s(w)` (compose `uncurry ψ` with `s' ↦ (s', w)`) and
  `Dψ(s,w)(0,k) = (fderiv ℝ (ψ s) w) k` (compose with `w' ↦ (s, w')`).  Surjectivity (`hΨ_right`)
  covers every `w`.  Rearrange to the claimed `HasDerivAt`. -/
theorem transportedTest_transport_identity
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T t : ℝ)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    (hflow_ode : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) (w : PhaseSpace d) :
    HasDerivAt (fun s' => φ (charX t (Ψ s' w), charV t (Ψ s' w)))
      (-(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w
          (vlasovVectorField gradW ρ s w))) s := by
  classical
  -- uncurried two-time flow and transported test
  set G2 : ℝ × PhaseSpace d → PhaseSpace d :=
    fun p => (charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) with hG2_def
  set g : ℝ × PhaseSpace d → ℝ := fun p => φ (G2 p) with hg_def
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : ((s, w) : ℝ × PhaseSpace d) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) :=
    ⟨hs, Set.mem_univ _⟩
  -- right-inverse identity: Φ_s (Ψ_s w) = w
  have hw : (charX s (Ψ s w), charV s (Ψ s w)) = w := hΨ_right s hs w
  -- g is jointly C¹, hence HasFDerivAt at the interior point (s,w)
  have hG2_cd : ContDiffOn ℝ 1 G2 (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    twoTimeFlow_contDiffOn_joint charX charV T t Ψ hΨ_C1 hΦt_C1
  have hG2_diff : DifferentiableAt ℝ G2 (s, w) :=
    hG2_cd.differentiableOn_one.differentiableAt (hopen.mem_nhds hmem)
  have hφ_diff : DifferentiableAt ℝ φ (G2 (s, w)) := hφ.differentiable (by simp) _
  have hg_fderiv : HasFDerivAt g (fderiv ℝ g (s, w)) (s, w) :=
    (hφ_diff.comp (s, w) hG2_diff).hasFDerivAt
  set G := fderiv ℝ g (s, w) with hG_def
  -- (A) spatial slice w' ↦ g (s, w') : fderiv = G ∘ inr
  have hslice_fderiv : HasFDerivAt (fun w' : PhaseSpace d => g (s, w'))
      (G.comp (ContinuousLinearMap.inr ℝ ℝ (PhaseSpace d))) w := by
    have := hg_fderiv.comp w (hasFDerivAt_prodMk_right s w)
    simpa only [Function.comp_def] using this
  -- (B) ∂_s slice s' ↦ g (s', w) : HasDerivAt with value G (1, 0)
  have hscurve : HasDerivAt (fun s' => ((s', w) : ℝ × PhaseSpace d))
      ((1 : ℝ), (0 : PhaseSpace d)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s w)
  have hs_slice : HasDerivAt (fun s' => g (s', w)) (G ((1 : ℝ), (0 : PhaseSpace d))) s := by
    have := hg_fderiv.comp_hasDerivAt s hscurve
    simpa only [Function.comp_def] using this
  -- (C) constancy curve c(s') = (s', Φ_{s'} (Ψ_s w)); chain rule gives G(1, b)
  have hccurve : HasDerivAt
      (fun s' => ((s', (charX s' (Ψ s w), charV s' (Ψ s w))) : ℝ × PhaseSpace d))
      ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) s :=
    (hasDerivAt_id s).prodMk (hflow_ode (Ψ s w) s hs)
  have hcs : ((s, (charX s (Ψ s w), charV s (Ψ s w))) : ℝ × PhaseSpace d) = (s, w) := by rw [hw]
  have hgc : HasDerivAt (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w))))
      (G ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))) s := by
    have hF := hg_fderiv
    rw [← hcs] at hF
    have := hF.comp_hasDerivAt s hccurve
    simpa only [Function.comp_def] using this
  -- (D) the composite is eventually constant near s, so its derivative is 0
  have hconst : (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w)))) =ᶠ[nhds s]
      (fun _ => φ (charX t (Ψ s w), charV t (Ψ s w))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
    simp only [hg_def, hG2_def]
    rw [hΨ_left s' hs' (Ψ s w)]
  have hgc0 : HasDerivAt (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w)))) 0 s :=
    (hasDerivAt_const s (φ (charX t (Ψ s w), charV t (Ψ s w)))).congr_of_eventuallyEq hconst
  -- (E) uniqueness: G (1, b) = 0
  have hGzero : G ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) = 0 :=
    hgc.unique hgc0
  -- (F) split G(1,b) = G(1,0) + G(0,b); identify G(0,b) with the target fderiv applied to b
  have hsplit : ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))
      = ((1 : ℝ), (0 : PhaseSpace d))
        + ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) := by
    ext <;> simp
  have hb_eq : vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))
      = vlasovVectorField gradW ρ s w := by rw [hw]
  have hG0b : G ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))
      = (fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w)
          (vlasovVectorField gradW ρ s w) := by
    have hfd : fderiv ℝ (fun w' : PhaseSpace d => g (s, w')) w
        = G.comp (ContinuousLinearMap.inr ℝ ℝ (PhaseSpace d)) := hslice_fderiv.fderiv
    have hfun : (fun w' : PhaseSpace d => g (s, w'))
        = (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) := rfl
    rw [hfun] at hfd
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hb_eq]
  -- (G) G(1,0) = -(target fderiv)(b)
  have hval : G ((1 : ℝ), (0 : PhaseSpace d))
      = -(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w)
          (vlasovVectorField gradW ρ s w) := by
    have hsum : G ((1 : ℝ), (0 : PhaseSpace d))
        + G ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) = 0 := by
      rw [← map_add, ← hsplit]; exact hGzero
    rw [hG0b] at hsum
    linarith [hsum]
  -- (H) conclude
  have hgoalfun : (fun s' => φ (charX t (Ψ s' w), charV t (Ψ s' w)))
      = (fun s' => g (s', w)) := rfl
  rw [hgoalfun, ← hval]
  exact hs_slice

/-- **C3 #8 (dual-transport core) — `∫ φ d(f t) = ∫ φ∘Φ_t d(f 0)` for every `C_c^∞` test.**

The genuine remaining crux: the dual transported-test-function argument showing the weak solution
`f` transports along its frozen-field characteristics.  Fix a terminal `t ∈ [0,T]` and a `C_c^∞`
test `φ`.  Let `Φ_{s→t}` be the two-time flow (forward from time `s` to time `t` along the
frozen-field characteristics) and `ψ_s := φ ∘ Φ_{s→t}` the backward-transported test
(so `ψ_t = φ` and `ψ_0 = φ ∘ Φ_t`).  Then:
* The flow is `C¹` in the initial point (`charFlow_hasFDerivAt_in_initialPoint`, #3 — proven), so
  with a `C¹` two-time flow `ψ_s` is `C¹_c`; the linear weak equation extends from the `C_c^∞`
  test class to this `C¹_c` test (**#4**, deferred — shape pending the two-time-flow representation).
* `ψ_s` satisfies the transport identity `∂_sψ_s + ⟨b, ∇ψ_s⟩ = 0` (**#5**, deferred — needs the
  two-time flow `Φ_{s→t}`), so `s ↦ ∫ ψ_s d(f s)` has zero derivative on `Ioo 0 t` (**#6**,
  deferred), hence is constant on `[0,t]` (`transportedIntegral_const_On`, #7 — proven).
* Constancy at the endpoints gives `∫ φ d(f t) = ∫ ψ_t d(f t) = ∫ ψ_0 d(f 0) = ∫ φ∘Φ_t d(f 0)`.

The pushforward side is `integral_map` by definition, so the dual argument is needed only for `f`
(the plan's `#1` pushforward-solves-linear lemma is not on this path).  `#4`/`#5`/`#6` are
**deliberately not locked** as Lean signatures (P5): their shapes depend on the two-time-flow
representation `Φ_{s→t}` (invertibility via Liouville `det M_s ≠ 0` + IFT, or a backward-flow
construction) — a C3-open architectural choice to be fixed by atom-level reading at the grind.

This is the project's last remaining `sorry`.  Its signature is `#8`'s hypothesis list verbatim
(the crux consumes essentially all of it). -/
theorem weak_eq_frozenField_pushforward_dualCore
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
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : PhaseSpace d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by
  sorry

/-- **C3 #8 — the weak solution equals its frozen-field pushforward on the window.**

`f t = (Φ_t)_# (f 0)` on `[0,T]`.  Skeleton: `measure_eq_of_forall_Cc_integral_eq` (#9) reduces
this to per-`C_c^∞`-test integral equality, and `integral_map` turns the pushforward side into
`∫ φ∘Φ_t d(f 0)` — leaving exactly the dual-transport core
`weak_eq_frozenField_pushforward_dualCore`.  Flow measurability on the window (needed by
`integral_map` and the probability-measure instances) comes from an L11 clamp of `ρ^f` into
`[0,T]` + `charFlow_measurable_via_gronwall_Ioo`. -/
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
  classical
  -- L11 clamp `ρ^f := spatialMarginal ∘ f` into the window so the universal-instance
  -- measurability lemma `charFlow_measurable_via_gronwall_Ioo` applies.
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht; simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  -- Windowed first-moment integrability for `ρ^f`.
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
  -- Windowed force integrability for `ρ^f`.
  have h_int_window : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
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
  -- Clamped curve `ρ'` with the universal probability instance + force integrability.
  set ρ' : ℝ → Measure (PhysSpace d) := fun t => spatialMarginal (f (clampT t)) with hρ'_def
  haveI hρ'_prob : ∀ t, IsProbabilityMeasure (ρ' t) := by
    intro t
    haveI : IsProbabilityMeasure (f (clampT t)) := (hf_mom (clampT t) (hclampT_mem t)).1
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_int' : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' t) :=
    fun t x => h_int_window (clampT t) (hclampT_mem t) x
  -- `ρ'`-flavoured velocity ODE on `Ioo 0 T` (clamp = id there, so the field is unchanged).
  have h_deriv_Ioo' : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ' s (charX s z, charV s z)) (Set.Ici s) s := by
    intro z s hs
    have h := hderivIco z s (Set.Ioo_subset_Ico_self hs)
    have hρeq : ρ' s = spatialMarginal (f s) := by
      simp only [hρ'_def, hclampT_id s (Set.Ioo_subset_Icc_self hs)]
    have hfield : vlasovVectorField gradW ρ' s (charX s z, charV s z)
        = vlasovVectorField gradW (fun t => spatialMarginal (f t)) s (charX s z, charV s z) := by
      simp only [vlasovVectorField, hρeq]
    rw [hfield]; exact h
  -- Flow measurability on the window.
  have hΦ_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL ρ' h_int' charX charV T hT.le
      hinit hcontIcc h_deriv_Ioo'
  -- Main reduction: `#9` + `integral_map` ⟹ the dual-transport core.
  intro t ht
  haveI hft_prob : IsProbabilityMeasure (f t) := (hf_mom t ht).1
  haveI hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hΦt_aem : AEMeasurable (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) :=
    (hΦ_meas t ht).aemeasurable
  haveI hmap_prob :
      IsProbabilityMeasure (Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) :=
    Measure.isProbabilityMeasure_map hΦt_aem
  refine measure_eq_of_forall_Cc_integral_eq (fun φ hφ hφc => ?_)
  rw [integral_map hΦt_aem hφ.continuous.aestronglyMeasurable]
  exact weak_eq_frozenField_pushforward_dualCore W gradW hgradW L hL f T hT hf_weak hf_mom
    hf_cont hf_cont_deriv M_ρ hM_ρ_nn hM_ρ charX charV hflow hinit hcontIcc hderivIco t ht φ hφ hφc

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
