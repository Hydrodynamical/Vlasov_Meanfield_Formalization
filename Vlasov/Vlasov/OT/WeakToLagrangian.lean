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
    ContDiff ℝ ⊤ φ → HasCompactSupport φ →
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

/-- Convenience extractor: under `[AssW2 W]`, a gradient field `gradW = ∇W` is `C¹`.

`AssW2.gradContDiff` gives `ContDiff ℝ 1 (fun x => fderiv ℝ W x)`; composing with the (smooth,
linear) Riesz isometry `gradient W x = (toDual ℝ _).symm (fderiv ℝ W x)` and rewriting by `hgradW`
yields `ContDiff ℝ 1 gradW`. -/
lemma assW2_contDiff_gradW (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x) :
    ContDiff ℝ 1 gradW := by
  sorry

/-- **Weak ⟹ Lagrangian on `[0,T]`** (tex: thm:weak-lagrangian).

Under `AssW2` (`W ∈ C²`) and a per-window smallness, every weak Vlasov solution on `[0,T]` with
finite first moments (and the ρ-regularity the frozen-field flow construction needs) is the
pushforward of its initial datum under the characteristic flow it generates — i.e. it is
Lagrangian.  This is the localized, forward-window form matching `vlasovWellPosedness`'s
architecture; the universal form is obtained by window-gluing (deferred).

Hypotheses mirror what `exists_vlasov_characteristicFlow_global_smallT` consumes for the frozen
curve `ρ^f := fun t => spatialMarginal (f t)`.

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
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (hTL_PL : LocalSmallness_PL_buffer L T) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  sorry

end Vlasov
