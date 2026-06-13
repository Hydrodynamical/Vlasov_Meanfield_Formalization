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
