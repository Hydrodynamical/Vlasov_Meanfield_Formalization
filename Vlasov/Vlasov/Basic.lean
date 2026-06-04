/-
Formalization skeleton for "Derivation of the Vlasov Equation from N-Particle Hamiltonian Dynamics".
Generated from vlasov.tex.
All proofs are `sorry`; this file is a statement-only scaffold.
-/

import Mathlib

open scoped BigOperators
open MeasureTheory

namespace Vlasov

/-!
## Basic type aliases and notation

Throughout, `d : ℕ` is the spatial dimension and `N : ℕ` is the number of particles.
Phase space for a single particle is `EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)`.
-/

variable {d : ℕ} [NeZero d]

/-- Abbreviation for ℝ^d as a Euclidean space. -/
abbrev PhysSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Abbreviation for the single-particle phase space ℝ^d × ℝ^d. -/
abbrev PhaseSpace (d : ℕ) := PhysSpace d × PhysSpace d

-- ---------------------------------------------------------------------------
-- §1  Equation (Hamiltonian)   (tex: eq:HN)
-- ---------------------------------------------------------------------------

/-- (tex: eq:HN)
The mean-field Hamiltonian for N identical unit-mass particles in ℝ^d:

  H_N(X, V) = Σ_{i=1}^{N} |v_i|² / 2  +  (1/N) Σ_{1 ≤ i < j ≤ N} W(x_i − x_j).

The factor 1/N normalises the interaction energy so that kinetic and potential
energies are of the same order as N → ∞.
-/
noncomputable def hamiltonianN (N : ℕ) (W : PhysSpace d → ℝ)
    (X V : Fin N → PhysSpace d) : ℝ :=
  (∑ i : Fin N, ‖V i‖ ^ 2 / 2)
  + (1 / (N : ℝ)) * ∑ i : Fin N, ∑ j : Fin N,
      if (i : ℕ) < j then W (X i - X j) else 0

-- ---------------------------------------------------------------------------
-- §2  Equation (Hamilton / Newton equations of motion)   (tex: eq:newton)
-- ---------------------------------------------------------------------------

/-- (tex: eq:newton)
Predicate asserting that a curve (X, V) : ℝ → (Fin N → PhysSpace d)²
satisfies the N-particle mean-field Newton equations

  ẋ_i = v_i,
  v̇_i = −(1/N) Σ_{j ≠ i} ∇W(x_i − x_j),   i = 1, …, N.

`gradW` is the gradient ∇W : ℝ^d → ℝ^d of the pair potential.
-/
def IsNewtonSolution (N : ℕ) (gradW : PhysSpace d → PhysSpace d)
    (X V : ℝ → Fin N → PhysSpace d) : Prop :=
  -- position equations: Ẋ_i(t) = V_i(t)
  (∀ t i, HasDerivAt (fun t => X t i) (V t i) t) ∧
  -- velocity equations: V̇_i(t) = −(1/N) Σ_{j ≠ i} ∇W(X_i(t) − X_j(t))
  (∀ t i, HasDerivAt (fun t => V t i)
      (-(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else 0)
      t)

-- ---------------------------------------------------------------------------
-- §3  Assumption   (tex: ass:W)
-- ---------------------------------------------------------------------------

/-- (tex: ass:W)
Standing assumption on the pair potential W : ℝ^d → ℝ.

W belongs to C^{1,1}(ℝ^d): it is differentiable with a globally Lipschitz
gradient.  Additionally W is even: W(−x) = W(x) for all x.
The Lipschitz constant L := Lip(∇W) is finite.
-/
class AssW (W : PhysSpace d → ℝ) : Prop where
  /-- W is continuously differentiable. -/
  differentiable : Differentiable ℝ W
  /-- W is even. -/
  even : ∀ x : PhysSpace d, W (-x) = W x
  /-- The gradient ∇W is Lipschitz with some constant L ≥ 0. -/
  lipschitzGrad : ∃ L : NNReal, LipschitzWith L (fun x => fderiv ℝ W x)

omit [NeZero d] in
/-- Helper: under `[AssW W]` (even + differentiable), the gradient of `W`
at the origin vanishes.

Mathematical content: differentiating `W(-x) = W(x)` at `x = 0` and using
`HasFDerivAt.unique` gives `fderiv W 0 = -fderiv W 0`, hence
`gradient W 0 = -gradient W 0`. In the real vector space `EuclideanSpace ℝ (Fin d)`
this forces `gradient W 0 = 0`.

Used by `empiricalMeasureSolvesVlasov` (cor:empirical-vlasov) to kill the
diagonal correction term in `weakEvolutionEmpiricalMeasure`. -/
lemma gradient_zero_of_even (W : PhysSpace d → ℝ) [hW : AssW W] :
    gradient W 0 = 0 := by
  -- Step A: the claim that the gradient at 0 equals its own negation.
  suffices h : gradient W 0 = -gradient W 0 by
    -- x = -x in a ℝ-vector space ⟹ x = 0.
    have h2 : gradient W 0 + gradient W 0 = 0 := by
      nth_rewrite 2 [h]
      exact add_neg_cancel (gradient W 0)
    -- Rewrite x + x as 2 • x and use the real-vector-space cancellation.
    have h3 : (2 : ℝ) • gradient W 0 = 0 := by
      rw [show (2 : ℝ) • gradient W 0 = gradient W 0 + gradient W 0 from by
            rw [two_smul]]
      exact h2
    exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
  -- Step B: prove gradient W 0 = -gradient W 0 via the fderiv chain rule on
  -- the (trivial) composition W ∘ Neg.neg = W.
  have hdiff : Differentiable ℝ W := hW.differentiable
  -- Strategy: prove `gradient W 0 = -gradient W 0` by exhibiting two
  -- HasFDerivAt witnesses for W at 0 and invoking uniqueness.
  -- The first witness is the standard `fderiv ℝ W 0`; the second comes
  -- from the chain rule on `(fun x => W (-x))`, which equals W by
  -- evenness.
  have h_W0 : HasFDerivAt W (fderiv ℝ W 0) 0 :=
    hdiff.differentiableAt.hasFDerivAt
  -- Derivative of `(fun x : PhysSpace d => -x)` at 0 is `-id` (as a CLM).
  -- We get it from `hasFDerivAt_id` and `.neg` (which negates the function
  -- pointwise, equivalent to applying negation to the argument).
  have h_neg : HasFDerivAt (fun x : PhysSpace d => -x)
      (-ContinuousLinearMap.id ℝ (PhysSpace d)) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : PhysSpace d)).neg
  -- Need h_W0 phrased at `-(0 : PhysSpace d)` for the chain rule below.
  have h_W_at_neg0 : HasFDerivAt W (fderiv ℝ W 0) (-(0 : PhysSpace d)) := by
    rw [neg_zero]; exact h_W0
  -- Chain rule applied to W ∘ (-·) gives `HasFDerivAt (fun x => W (-x)) ...`.
  have h_chain : HasFDerivAt (fun x : PhysSpace d => W (-x))
      ((fderiv ℝ W 0).comp (-ContinuousLinearMap.id ℝ (PhysSpace d))) 0 :=
    h_W_at_neg0.comp 0 h_neg
  -- Evenness rewrites `(fun x => W (-x))` to `W`, giving a second
  -- HasFDerivAt witness for W at 0.
  have hcomp_eq : (fun x : PhysSpace d => W (-x)) = W := funext hW.even
  rw [hcomp_eq] at h_chain
  -- Uniqueness of the Fréchet derivative.
  have h_fderiv : fderiv ℝ W 0
      = (fderiv ℝ W 0).comp (-ContinuousLinearMap.id ℝ (PhysSpace d)) :=
    h_W0.unique h_chain
  -- f.comp (-id) = -f for any CLM f.
  have h_comp_neg : (fderiv ℝ W 0).comp (-ContinuousLinearMap.id ℝ (PhysSpace d))
      = -(fderiv ℝ W 0) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
               ContinuousLinearMap.id_apply, ContinuousLinearMap.map_neg]
  rw [h_comp_neg] at h_fderiv
  -- Push `fderiv ℝ W 0 = -fderiv ℝ W 0` through `(toDual).symm`
  -- (a linear isomorphism) to land at `gradient W 0 = -gradient W 0`.
  have h_grad : gradient W 0 = -gradient W 0 :=
    (congrArg (InnerProductSpace.toDual ℝ (PhysSpace d)).symm h_fderiv).trans
      (map_neg _ _)
  exact h_grad

-- ---------------------------------------------------------------------------
-- §4  Definition (Empirical measure)   (tex: def:empirical)
-- ---------------------------------------------------------------------------

-- TODO(mathlib): Mathlib does not yet have a ready-made `empiricalMeasure`
-- construction returning a `ProbabilityMeasure`.  We define it here as a
-- placeholder using `MeasureTheory.Measure.dirac` and a finite sum.

/-- (tex: def:empirical)
The empirical measure of a configuration (X, V) ∈ (ℝ^d × ℝ^d)^N:

  μ^N[X, V] := (1/N) Σ_{i=1}^{N} δ_{(X_i, V_i)}.

Returns a `MeasureTheory.Measure (PhaseSpace d)`.  It is a probability measure
when N ≥ 1.
-/
noncomputable def empiricalMeasure (N : ℕ) (X V : Fin N → PhysSpace d) :
    Measure (PhaseSpace d) :=
  (1 / (N : ENNReal)) • ∑ i : Fin N, Measure.dirac (X i, V i)

omit [NeZero d] in
/-- (tex: def:empirical)
When N ≥ 1 the empirical measure is a probability measure.

Proof: μ(univ) = (1/N) · Σᵢ δ_{zᵢ}(univ) = (1/N) · N · 1 = 1, where each
Dirac mass evaluates to 1 on the universal set via the
`Measure.dirac.isProbabilityMeasure` instance. -/
lemma empiricalMeasure_isProbabilityMeasure (N : ℕ) [NeZero N]
    (X V : Fin N → PhysSpace d) :
    IsProbabilityMeasure (empiricalMeasure N X V) := by
  refine ⟨?_⟩
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finset_sum_apply,
             measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
             smul_eq_mul, nsmul_eq_mul, mul_one]
  exact ENNReal.div_mul_cancel
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) (ENNReal.natCast_ne_top N)

/-- (tex: def:empirical)
The time-dependent empirical measure μ_t^N along a solution of eq:newton. -/
noncomputable def empiricalMeasureCurve (N : ℕ) (X V : ℝ → Fin N → PhysSpace d) :
    ℝ → Measure (PhaseSpace d) :=
  fun t => empiricalMeasure N (X t) (V t)

-- ---------------------------------------------------------------------------
-- §5  Proposition (Weak evolution of the empirical measure)   (tex: prop:weak)
-- ---------------------------------------------------------------------------

-- TODO(mathlib): Convolution of a function with a measure (∇W * ρ) is used
-- below.  In Mathlib this would be `MeasureTheory.Measure.convolution` or a
-- hand-rolled integral.  We give a local definition as a placeholder.

/-- Convolution of a function k : ℝ^d → ℝ^d with a (finite) measure ρ on ℝ^d:
  (k * ρ)(x) := ∫ k(x − y) dρ(y).
-/
noncomputable def convolveFunctionMeasure (k : PhysSpace d → PhysSpace d)
    (ρ : Measure (PhysSpace d)) (x : PhysSpace d) : PhysSpace d :=
  ∫ y, k (x - y) ∂ρ

/-- Spatial marginal of a measure on phase space. -/
noncomputable def spatialMarginal (μ : Measure (PhaseSpace d)) :
    Measure (PhysSpace d) :=
  Measure.map Prod.fst μ

/-! Decomposed by sorry-decomposer.
    See `formalize/plans/weakEvolutionEmpiricalMeasure.json`. -/

/-- The integral of a function φ against the empirical measure `empiricalMeasure N X V`
equals `(1/N) * ∑ i, φ(X i, V i)`, by unfolding the weighted sum of Dirac masses. -/
lemma empiricalMeasure_integral_eq (N : ℕ) [NeZero N]
    (X V : Fin N → PhysSpace d)
    (φ : PhaseSpace d → ℝ) :
    ∫ z, φ z ∂(empiricalMeasure N X V) =
      (1 / (N : ℝ)) * ∑ i : Fin N, φ (X i, V i) := by
  simp only [empiricalMeasure]
  rw [integral_smul_measure]
  rw [integral_finset_sum_measure (fun i _ => integrable_dirac (by simp))]
  simp [integral_dirac, ENNReal.toReal_div, ENNReal.toReal_natCast, smul_eq_mul]

/-- For a smooth test function φ, the chain rule gives: the map `t ↦ φ(X t i, V t i)` has
derivative `⟨V t i, gradXφ (X t i, V t i)⟩ + ⟨a t i, gradVφ (X t i, V t i)⟩` at t,
where `a t i` is the acceleration vector at particle i and time t.

Signature refactored (Phase B of the 2026-05-25 plan): φ's Fréchet derivative is
an INPUT hypothesis `hφ_fderiv` instead of being derived inside the helper.  This
lifts the `ContDiff.hasFDerivAt + WithLp.toLp + gradient → toDual → toLinearMap`
type-class friction up to the call site (where `ContDiff ℝ ⊤ φ` is already a
hypothesis and the Fréchet derivative is a one-line `have`).  The body of this
helper is then a straight composition:
  · `HasDerivAt.prodMk hX hV` gives the curve derivative `t ↦ (X t i, V t i)`.
  · `(hφ_fderiv (X t i, V t i)).comp_hasDerivAt` composes through φ.
  · Unfolding `gradXφ`/`gradVφ` via `hgradXφ`/`hgradVφ` and rewriting the
    Fréchet derivative's action via `inner_product` partial-derivative
    identities gives the target inner-product form. -/
lemma hasDerivAt_phi_along_trajectory (N : ℕ)
    (X V : ℝ → Fin N → PhysSpace d)
    (hX : ∀ t i, HasDerivAt (fun t => X t i) (V t i) t)
    (a : ℝ → Fin N → PhysSpace d)
    (hV : ∀ t i, HasDerivAt (fun t => V t i) (a t i) t)
    (φ : PhaseSpace d → ℝ)
    (φ' : PhaseSpace d → (PhaseSpace d →L[ℝ] ℝ))
    (hφ_fderiv : ∀ z, HasFDerivAt φ (φ' z) z)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (t : ℝ) (i : Fin N) :
    HasDerivAt (fun s => φ (X s i, V s i))
      (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
       @inner ℝ (PhysSpace d) _ (a t i) (gradVφ (X t i, V t i))) t := by
  -- Step 1: curve derivative
  have hcurve : HasDerivAt (fun s => (X s i, V s i)) (V t i, a t i) t :=
    (hX t i).prodMk (hV t i)
  -- Step 2: compose φ through the curve
  have hcomp : HasDerivAt (fun s => φ (X s i, V s i))
      ((φ' (X t i, V t i)) (V t i, a t i)) t :=
    (hφ_fderiv (X t i, V t i)).comp_hasDerivAt t hcurve
  -- Step 3: rewrite the derivative value
  convert hcomp using 1
  -- Step 4: show φ'(z)(V,a) = ⟨V, gradXφ z⟩ + ⟨a, gradVφ z⟩
  set z := (X t i, V t i)
  -- partial x: HasFDerivAt (fun x => φ(x, z.2)) (φ' z ∘L inl ℝ _ _) z.1
  have hpX : HasFDerivAt (fun x => φ (x, z.2))
      ((φ' z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) z.1 :=
    (hφ_fderiv z).comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  have hpV : HasFDerivAt (fun v => φ (z.1, v))
      ((φ' z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) z.2 :=
    (hφ_fderiv z).comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)
  simp only [hgradXφ z, hgradVφ z]
  -- inner(V, ∇f z.1) = fderiv f z.1 V via inner_gradient_right (real case: conj = id)
  have hgX : @inner ℝ (PhysSpace d) _ (V t i) (gradient (fun x => φ (x, z.2)) z.1) =
      fderiv ℝ (fun x => φ (x, z.2)) z.1 (V t i) := by
    rw [inner_gradient_right hpX.differentiableAt]
    simp [RCLike.conj_eq_iff_re, conj_trivial]
  have hgV : @inner ℝ (PhysSpace d) _ (a t i) (gradient (fun v => φ (z.1, v)) z.2) =
      fderiv ℝ (fun v => φ (z.1, v)) z.2 (a t i) := by
    rw [inner_gradient_right hpV.differentiableAt]
    simp [RCLike.conj_eq_iff_re, conj_trivial]
  rw [hgX, hgV, hpX.fderiv, hpV.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp [Prod.mk_add_mk]

/-- The derivative of `t ↦ ∫ φ d(empiricalMeasureCurve N X V t)` equals the finite sum
expression `(1/N) * Σᵢ [⟨V t i, gradXφ (X t i, V t i)⟩ + ⟨aᵢ, gradVφ (X t i, V t i)⟩]`
where `aᵢ = -(1/N) Σ_{j≠i} gradW(X t i - X t j)` is the Newton acceleration,
obtained by combining `empiricalMeasure_integral_eq` and `hasDerivAt_phi_along_trajectory`
with `HasDerivAt.sum` and `HasDerivAt.const_smul`. -/
lemma hasDerivAt_empiricalIntegral_sum (N : ℕ) [NeZero N]
    (gradW : PhysSpace d → PhysSpace d)
    (X V : ℝ → Fin N → PhysSpace d)
    (hSol : IsNewtonSolution N gradW X V)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ z, φ z ∂(empiricalMeasureCurve N X V s))
      ((1 / (N : ℝ)) * ∑ i : Fin N,
        (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
         @inner ℝ (PhysSpace d) _ (
           -(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else 0)
           (gradVφ (X t i, V t i)))) t := by
  -- Construct φ's Fréchet derivative witness from smoothness.
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by norm_num)
  have hφ_fderiv : ∀ z, HasFDerivAt φ (fderiv ℝ φ z) z := fun z =>
    hφ_diff.differentiableAt.hasFDerivAt
  -- The Newton-acceleration function, packaged for hasDerivAt_phi_along_trajectory.
  let acc : ℝ → Fin N → PhysSpace d := fun s i =>
    -(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X s i - X s j) else 0
  -- Rewrite the integral via empiricalMeasure_integral_eq (per-time-slice).
  have hint : ∀ s : ℝ, ∫ z, φ z ∂(empiricalMeasureCurve N X V s) =
      (1 / (N : ℝ)) * ∑ i : Fin N, φ (X s i, V s i) := fun s => by
    simp only [empiricalMeasureCurve]
    exact empiricalMeasure_integral_eq N (X s) (V s) φ
  simp_rw [hint]
  -- Differentiate (1/N) * Σᵢ φ(Xₛᵢ, Vₛᵢ) wrt s.  Establish the per-particle
  -- derivative via hasDerivAt_phi_along_trajectory (using `acc` for the
  -- Newton acceleration), combine termwise via HasDerivAt.sum, then pull
  -- the (1/N) constant out via HasDerivAt.const_mul.
  have h_each : ∀ i : Fin N,
      HasDerivAt (fun s : ℝ => φ (X s i, V s i))
        (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
         @inner ℝ (PhysSpace d) _ (acc t i) (gradVφ (X t i, V t i))) t := fun i =>
    hasDerivAt_phi_along_trajectory N X V hSol.1 acc hSol.2 φ
      (fderiv ℝ φ) hφ_fderiv gradXφ gradVφ hgradXφ hgradVφ t i
  have h_sum : HasDerivAt (fun s : ℝ => ∑ i : Fin N, φ (X s i, V s i))
      (∑ i : Fin N,
        (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
         @inner ℝ (PhysSpace d) _ (acc t i) (gradVφ (X t i, V t i)))) t :=
    HasDerivAt.fun_sum (fun i _ => h_each i)
  exact h_sum.const_mul (1 / (N : ℝ))

/-- Convolution of the kernel `gradW` against the spatial marginal of the
empirical measure unfolds to the explicit finite sum
`(1/N) • Σⱼ gradW(X t i − X t j)`.  This is the API-navigation step that
separates the Measure-pushforward / Dirac-integration machinery from the
algebraic "add and subtract the diagonal" step in `diagonalCorrection_eq`.

Proof strategy (decomposer-supplied mathlib_hints, grep-validated against
Mathlib 4.x at `.lake/packages/mathlib/`):
  1. `empiricalMeasureCurve` and `empiricalMeasure` unfold to
     `(1/N : ℝ≥0∞) • Σⱼ Measure.dirac (X t j, V t j)`.
  2. `Measure.map_smul` (`MeasureTheory/Measure/Map.lean:127`) pushes
     `Prod.fst` through the scalar.
  3. `Measure.map_add` (`MeasureTheory/Measure/Map.lean:103`) + finset
     induction distributes `Prod.fst` over the sum, giving
     `(1/N : ℝ≥0∞) • Σⱼ Measure.dirac (X t j)`.
  4. `convolveFunctionMeasure` unfolds to `∫ y, gradW(X t i − y) ∂ρ`.
  5. `integral_smul_measure` (Bochner) extracts the `(1/N).toReal = 1/N`
     scalar; `integral_finset_sum_measure` (`Integral/Bochner/Basic.lean:1018`)
     distributes integration over the finite sum of Diracs;
     `integral_dirac'` (`Integral/Bochner/Basic.lean:1131`) collapses each
     summand to `gradW(X t i − X t j)`. -/
lemma convolveFunctionMeasure_empiricalSpatial_eq (N : ℕ) [NeZero N]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW_meas : Measurable gradW)
    (X V : ℝ → Fin N → PhysSpace d) (t : ℝ) (i : Fin N) :
    convolveFunctionMeasure gradW
        (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i) =
      (1 / (N : ℝ)) • ∑ j : Fin N, gradW (X t i - X t j) := by
  -- Measurability witnesses
  have hmeas_y : Measurable (fun y : PhysSpace d => gradW (X t i - y)) :=
    hgradW_meas.comp (measurable_const.sub measurable_id)
  have hsm_y : StronglyMeasurable (fun y : PhysSpace d => gradW (X t i - y)) :=
    hmeas_y.stronglyMeasurable
  have hmeas_z : Measurable (fun z : PhaseSpace d => gradW (X t i - z.1)) :=
    hgradW_meas.comp (measurable_const.sub measurable_fst)
  have hsm_z : StronglyMeasurable (fun z : PhaseSpace d => gradW (X t i - z.1)) :=
    hmeas_z.stronglyMeasurable
  -- Unfold the layered definitions.
  unfold convolveFunctionMeasure spatialMarginal empiricalMeasureCurve empiricalMeasure
  -- Convert integration against the pushforward (Prod.fst) to integration on the product.
  rw [integral_map measurable_fst.aemeasurable hsm_y.aestronglyMeasurable]
  -- Pull out the (1 / N : ℝ≥0∞) scalar.
  rw [integral_smul_measure]
  -- Distribute integration over the finite sum of Dirac measures.
  rw [integral_finset_sum_measure (fun j _ =>
        integrable_dirac' hsm_z (by simp [enorm_lt_top]))]
  -- Each Dirac integral collapses to the function value at the centre.
  simp only [integral_dirac' _ _ hsm_z]
  -- Normalize (1/(N:ℝ≥0∞)).toReal = 1/(N:ℝ); the .1 projection collapses on pairs.
  simp [ENNReal.toReal_div, ENNReal.toReal_natCast]

/-- The remainder term `r` in the weak evolution identity equals
`(1/N²) * Σᵢ ⟨gradW 0, gradVφ(X t i, V t i)⟩`: this is the diagonal correction
obtained when extending the Newton-equation sum `Σ_{j≠i}` to all `j` (the diagonal
`j = i` summand contributes `gradW(X t i - X t i) = gradW 0`).

This lemma is pure inner-product algebra atop
`convolveFunctionMeasure_empiricalSpatial_eq`: extend `Σ_{j≠i}` to `Σⱼ` via
`Finset.sum_ite_ne` or `Finset.sum_compl_add_sum`, distribute the inner
product with `inner_sub_left`/`inner_smul_left`, recognise the
`(1/N) • Σⱼ gradW` factor as the convolveFunctionMeasure unfolding. -/
lemma diagonalCorrection_eq (N : ℕ) [NeZero N]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW_meas : Measurable gradW)
    (X V : ℝ → Fin N → PhysSpace d)
    (gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ) :
    (1 / (N : ℝ)) * ∑ i : Fin N,
      @inner ℝ (PhysSpace d) _ (
        -(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else 0)
        (gradVφ (X t i, V t i))
    = -(1 / (N : ℝ)) * ∑ i : Fin N,
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW
            (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i))
          (gradVφ (X t i, V t i))
      + (1 / (N : ℝ)^2) * ∑ i : Fin N,
          @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i)) := by
  -- Step 1: unfold the convolution form on the RHS using the proved helper.
  have hconv : ∀ i : Fin N,
      convolveFunctionMeasure gradW
        (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i)
      = (1 / (N : ℝ)) • ∑ j : Fin N, gradW (X t i - X t j) := fun i =>
    convolveFunctionMeasure_empiricalSpatial_eq N gradW hgradW_meas X V t i
  -- Step 2: extend the LHS's `Σ_{j≠i}` (via the ite/0 pattern) to `Σ_j − gradW 0`.
  have hext : ∀ i : Fin N,
      (∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else (0 : PhysSpace d))
      = (∑ j : Fin N, gradW (X t i - X t j)) - gradW 0 := by
    intro i
    have hsub : ∀ j : Fin N,
        (if j ≠ i then gradW (X t i - X t j) else (0 : PhysSpace d))
        = gradW (X t i - X t j)
          - (if j = i then gradW (X t i - X t j) else (0 : PhysSpace d)) := fun j => by
      by_cases hj : j = i <;> simp [hj]
    simp_rw [hsub]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i]
    simp
  -- Step 3: rewrite each per-i LHS inner product into scalar form.
  -- Use `real_inner_smul_left` (not generic `inner_smul_left`) to avoid a
  -- `starRingEnd ℝ` wrapper on the scalar that `ring` can't see through.
  have hlhs_i : ∀ i : Fin N,
      @inner ℝ (PhysSpace d) _
        (-(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else (0 : PhysSpace d))
        (gradVφ (X t i, V t i))
      = -(1 / (N : ℝ)) *
          (@inner ℝ (PhysSpace d) _ (∑ j : Fin N, gradW (X t i - X t j)) (gradVφ (X t i, V t i))
           - @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))) := by
    intro i
    rw [hext i, real_inner_smul_left, inner_sub_left]
  -- Step 4: rewrite each per-i RHS conv-term into scalar form.
  have hrhs_i : ∀ i : Fin N,
      @inner ℝ (PhysSpace d) _
        (convolveFunctionMeasure gradW
          (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i))
        (gradVφ (X t i, V t i))
      = (1 / (N : ℝ)) * @inner ℝ (PhysSpace d) _
          (∑ j : Fin N, gradW (X t i - X t j)) (gradVφ (X t i, V t i)) := by
    intro i
    rw [hconv i, real_inner_smul_left]
  -- Step 5: substitute both rewrites and reduce to a ring identity on two abbreviated sums.
  simp_rw [hlhs_i, hrhs_i]
  -- Distribute the per-summand subtraction (mul_sub then sum_sub_distrib),
  -- pull constants outside via reverse Finset.mul_sum, then abbreviate.
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- Goal is now an equation in two structural sums; ring closes the scalar identity.
  ring

/-- The remainder bound: for the diagonal correction `r = (1/N²) * Σᵢ ⟨gradW 0, gradVφ(zᵢ)⟩`,
we have `|r| ≤ (1/N) * (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)`, using
`abs_inner_le_norm` on each summand and the fact that the sum has N terms.

The two `BddAbove` hypotheses are essential: `ciSup` over an unbounded
function returns junk value 0 on `ℝ`, which would make the inequality
false in the unbounded case. The .tex's `‖∇W‖_∞ ‖∇_v φ‖_∞` implicitly
assumes L^∞ boundedness; making it explicit here keeps the lemma
honest. (For `gradVφ`: it comes from `∇_v φ` of a smooth compactly
supported `φ`, so the bound is a consequence of `HasCompactSupport`
— but expressing that derivation requires Mathlib API that's awkward
to assemble; easier to pass the bound as a hypothesis.) -/
lemma diagonalCorrection_bound (N : ℕ) [NeZero N]
    (gradW : PhysSpace d → PhysSpace d)
    (X V : ℝ → Fin N → PhysSpace d)
    (gradVφ : PhaseSpace d → PhysSpace d)
    (hgradW_bdd : BddAbove (Set.range (fun x => ‖gradW x‖)))
    (hgradVφ_bdd : BddAbove (Set.range (fun z => ‖gradVφ z‖)))
    (t : ℝ) :
    |(1 / (N : ℝ)^2) * ∑ i : Fin N,
        @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))| ≤
      (1 / (N : ℝ)) * ⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖ := by
  -- Positivity facts.
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have h_sW : 0 ≤ ⨆ x, ‖gradW x‖ := le_trans (norm_nonneg _) (le_ciSup hgradW_bdd 0)
  have h_sV : 0 ≤ ⨆ z, ‖gradVφ z‖ := le_trans (norm_nonneg _)
    (le_ciSup hgradVφ_bdd ((X t ⟨0, NeZero.pos N⟩), V t ⟨0, NeZero.pos N⟩))
  -- Per-summand bound: Cauchy-Schwarz + sup bounds.
  have h_term : ∀ i : Fin N,
      |@inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))| ≤
        (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖) := fun i =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (le_ciSup hgradW_bdd 0) (le_ciSup hgradVφ_bdd _)
        (norm_nonneg _) h_sW)
  -- Sum bound: |Σ| ≤ Σ|·| ≤ N * sup·sup.
  have h_sum : |∑ i : Fin N, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
      ≤ (N : ℝ) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)) := by
    calc |∑ i : Fin N, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
        ≤ ∑ i : Fin N, |@inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖) :=
          Finset.sum_le_sum (fun i _ => h_term i)
      _ = (N : ℝ) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- The RHS's `⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖` parses with the x-lambda
  -- extending over the whole `‖gradW x‖ * ⨆ z, ‖gradVφ z‖` body.  Since
  -- `⨆ z, ‖gradVφ z‖` is x-independent and nonneg, we can pull it out via
  -- `Real.iSup_mul_of_nonneg`.
  rw [show (⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖) = (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖) from
    (Real.iSup_mul_of_nonneg h_sV _).symm]
  -- Finish with absolute-value + ring arithmetic.
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc (1 / (N : ℝ) ^ 2) * |∑ i : Fin N, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
      ≤ (1 / (N : ℝ) ^ 2) * ((N : ℝ) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖))) :=
        mul_le_mul_of_nonneg_left h_sum (by positivity)
    _ = (1 / (N : ℝ)) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)) := by
        field_simp

/-- (tex: prop:weak)
Weak evolution of the empirical measure.

Let (X, V) : [0, T] → (ℝ^d × ℝ^d)^N solve the Newton equations eq:newton,
and let ρ_t^N be the spatial marginal of the empirical measure μ_t^N.
Then for every test function φ ∈ C_c^∞(ℝ^d × ℝ^d) and every time t,
there is a real remainder r = R_N(t) such that

  d/dt ⟨μ_t^N, φ⟩ = ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩ + r,

with |r| ≤ (1/N) ‖∇W‖_∞ ‖∇_v φ‖_∞.  Concretely, r is the diagonal correction
+(1/N²) Σᵢ ∇W(0) · ∇_v φ(xᵢ, vᵢ).  (The positive sign arises because extending
the Newton-equation sum Σ_{j≠i} to Σ_j subtracts the j=i term `gradW(0)`,
which then gets multiplied by the outer `−(1/N)` acceleration coefficient,
yielding `+(1/N²)·gradW(0)·gradVφ`.)  Under Assumption ass:W (W even ⟹
∇W(0) = 0) the diagonal vanishes and r = 0; that strengthening is the
content of `empiricalMeasureSolvesVlasov` below.

The remainder is quantified existentially because `HasDerivAt` has a
unique derivative — a free `R_N` parameter would make the statement
false. -/
theorem weakEvolutionEmpiricalMeasure
    (N : ℕ) [NeZero N]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (X V : ℝ → Fin N → PhysSpace d)
    (hSol : IsNewtonSolution N gradW X V)
    -- φ is a smooth compactly supported test function on phase space
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_compact : HasCompactSupport φ)
    -- ∇_x φ and ∇_v φ regarded as functions
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    -- L^∞ boundedness for ‖gradW‖ and ‖gradVφ‖, needed for the bound
    -- conjunct's `ciSup` to be meaningful (without these, the sups on
    -- the RHS collapse to junk value 0 on `ℝ`, making the bound vacuous
    -- — and the helper `diagonalCorrection_bound` unprovable).  The
    -- .tex's `‖∇W‖_∞ ‖∇_v φ‖_∞` implicitly assumes these.
    (hgradW_bdd : BddAbove (Set.range (fun x => ‖gradW x‖)))
    (hgradVφ_bdd : BddAbove (Set.range (fun z => ‖gradVφ z‖)))
    (t : ℝ) :
    -- existential witness for the remainder, with its explicit form
    -- exposed so downstream corollaries (e.g. `empiricalMeasureSolvesVlasov`)
    -- can compute it without re-deriving from scratch.  Concretely,
    -- `r` is the diagonal correction term picked up when extending the
    -- Newton-equation sum from `j ≠ i` to all `j` (the `j = i` summand
    -- contributes `gradW 0`).
    ∃ r : ℝ,
      -- explicit formula for the remainder
      r = (1 / (N : ℝ)^2) * ∑ i : Fin N,
            @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i)) ∧
      -- derivative identity at t
      HasDerivAt (fun s => ∫ z, φ z ∂(empiricalMeasureCurve N X V s)) (
        ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                @inner ℝ (PhysSpace d) _
                  (convolveFunctionMeasure gradW
                    (spatialMarginal (empiricalMeasureCurve N X V t)) z.1)
                  (gradVφ z))
              ∂(empiricalMeasureCurve N X V t)
          + r) t
      -- pointwise remainder bound
      ∧ |r| ≤ (1 / (N : ℝ)) *
          ⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖ := by
  -- Provide the explicit diagonal correction as the remainder witness.
  refine ⟨(1 / (N : ℝ)^2) * ∑ i : Fin N,
      @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i)), rfl, ?_, ?_⟩
  · -- HasDerivAt: use hasDerivAt_empiricalIntegral_sum and diagonalCorrection_eq
    -- to relate the finite-sum derivative to the integral + remainder form.
    have hderiv := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ
      hφ_smooth gradXφ gradVφ hgradXφ hgradVφ t
    -- Derive Measurable gradW from AssW W (Lipschitz fderiv ⇒ continuous gradient ⇒ measurable).
    have hgradW_meas : Measurable gradW := by
      have hext : gradW = fun x => gradient W x := funext hgradW
      rw [hext]
      obtain ⟨_, hLip⟩ := (inferInstance : AssW W).lipschitzGrad
      exact ((InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        hLip.continuous).measurable
    have hcorr := diagonalCorrection_eq N gradW hgradW_meas X V gradVφ t
    -- Rearrange: the derivative value from hderiv equals (integral term) + r
    -- after applying hcorr to split the velocity inner products.
    refine hderiv.congr_deriv ?_
    -- Convert the integral on the goal's RHS into a finite sum so we can
    -- match against hderiv's value plus hcorr.
    have hint : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                  @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW
                      (spatialMarginal (empiricalMeasureCurve N X V t)) z.1)
                    (gradVφ z))
                ∂(empiricalMeasureCurve N X V t)) =
        (1 / (N : ℝ)) * ∑ i : Fin N,
          (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) -
           @inner ℝ (PhysSpace d) _
             (convolveFunctionMeasure gradW
               (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i))
             (gradVφ (X t i, V t i))) := by
      simp only [empiricalMeasureCurve]
      exact empiricalMeasure_integral_eq N (X t) (V t)
        (fun z => @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                  @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW
                      (spatialMarginal (empiricalMeasureCurve N X V t)) z.1)
                    (gradVφ z))
    rw [hint]
    -- Goal: D(t) = (1/N) * Σᵢ (Aᵢ - Cᵢ) + r
    -- where D(t) = (1/N) * Σᵢ (Aᵢ + Bᵢ),
    --   Aᵢ = ⟨V t i, gradXφ (X t i, V t i)⟩,
    --   Bᵢ = ⟨-(1/N) • Σⱼ≠ᵢ gradW(Xᵢ-Xⱼ), gradVφᵢ⟩,
    --   Cᵢ = ⟨conv_i, gradVφᵢ⟩,
    --   r  = (1/N²) * Σᵢ ⟨gradW 0, gradVφᵢ⟩.
    -- hcorr says: (1/N) * Σᵢ Bᵢ = -(1/N) * Σᵢ Cᵢ + r.
    -- So (1/N) * Σ (A+B) = (1/N) Σ A + (1/N) Σ B
    --                   = (1/N) Σ A − (1/N) Σ C + r       [by hcorr]
    --                   = (1/N) Σ (A − C) + r              [recombine]
    -- Distribute Σ over (+) and (−) on both sides (keeping (1/N) outside),
    -- then split (1/N) * (sum + sum) into (1/N)*sum + (1/N)*sum.  hcorr fits
    -- the resulting linear identity directly.
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
    linarith [hcorr]
  · -- Bound: direct application of diagonalCorrection_bound.
    exact diagonalCorrection_bound N gradW X V gradVφ hgradW_bdd hgradVφ_bdd t

-- ---------------------------------------------------------------------------
-- §6  Equation (Weak form of empirical-measure evolution)   (tex: eq:weak-eq)
-- ---------------------------------------------------------------------------

/-- (tex: eq:weak-eq)
The distributional evolution identity for the empirical measure (the content
of Proposition prop:weak):

  d/dt ⟨μ_t^N, φ⟩  =  ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩ + R_N(t),

for every φ ∈ C_c^∞(ℝ^d × ℝ^d), with |R_N(t)| ≤ (1/N) ‖∇W‖_∞ ‖∇_v φ‖_∞.

This is a `Prop`-valued definition packaging the statement of eq:weak-eq.
-/
def WeakEvolutionEq (gradW : PhysSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (R_N : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (μ t)) z.1)
                (gradVφ z))
        ∂μ t
        + R_N t) t

-- ---------------------------------------------------------------------------
-- §7  Corollary (Empirical measure solves Vlasov)   (tex: cor:empirical-vlasov)
-- ---------------------------------------------------------------------------

/-- (tex: cor:empirical-vlasov)
Under Assumption ass:W, the empirical measure μ_t^N satisfies the distributional
Vlasov equation eq:vlasov with remainder R_N ≡ 0: for every φ ∈ C_c^∞(ℝ^d × ℝ^d),

  d/dt ⟨μ_t^N, φ⟩ = ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩.
-/
theorem empiricalMeasureSolvesVlasov
    (N : ℕ) [NeZero N]
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (X V : ℝ → Fin N → PhysSpace d)
    (hSol : IsNewtonSolution N gradW X V)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    -- Threaded through from `weakEvolutionEmpiricalMeasure`'s bound conjunct.
    -- Not used in this corollary's body (we destructure the bound and
    -- ignore it), but required by the signature of the prop:weak call.
    (hgradW_bdd : BddAbove (Set.range (fun x => ‖gradW x‖)))
    (hgradVφ_bdd : BddAbove (Set.range (fun z => ‖gradVφ z‖))) :
    WeakEvolutionEq gradW (empiricalMeasureCurve N X V) φ gradXφ gradVφ (fun _ => 0) := by
  -- WeakEvolutionEq unfolds to `∀ t, HasDerivAt ... (... + (fun _ => 0) t) t`.
  intro t
  -- Invoke prop:weak at this `t` and destructure the now-explicit witness.
  obtain ⟨r, hr_eq, hr_deriv, _hr_bound⟩ :=
    weakEvolutionEmpiricalMeasure N W gradW hgradW X V hSol φ
      hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ hgradW_bdd hgradVφ_bdd t
  -- Under [AssW W] we have gradW 0 = gradient W 0 = 0 (the latter via
  -- the even-implies-zero-gradient helper).
  have hgrad0 : gradW 0 = 0 := by
    rw [hgradW]; exact gradient_zero_of_even W
  -- The explicit formula for `r` collapses to 0 once gradW 0 = 0:
  -- each inner product becomes ⟨0, _⟩ = 0, the finite sum is 0, and
  -- the leading scalar multiplication is 0.
  have hr_zero : r = 0 := by
    rw [hr_eq, hgrad0]
    simp [inner_zero_left]
  -- Substitute r = 0 into the HasDerivAt witness; the conclusion's
  -- `(fun _ => 0) t` is definitionally 0.
  simpa [hr_zero] using hr_deriv

-- ---------------------------------------------------------------------------
-- §8  Equation (Vlasov equation)   (tex: eq:vlasov)
-- ---------------------------------------------------------------------------

-- TODO(mathlib): A full measure-valued notion of distributional solution to
-- the nonlinear Vlasov PDE is not in Mathlib.  We define a placeholder
-- predicate capturing the weak formulation.

/-- (tex: eq:vlasov)
The nonlinear Vlasov equation for a curve of probability measures f_t on ℝ^d × ℝ^d:

  ∂_t f + v · ∇_x f − (∇W * ρ_t)(x) · ∇_v f = 0,   ρ_t(x) = ∫ f_t(x, dv).

We encode this as the distributional statement: for every φ ∈ C_c^∞(ℝ^d × ℝ^d)
the map t ↦ ∫ φ df_t satisfies

  d/dt ∫ φ df_t = ∫ [v · ∇_x φ − (∇W * ρ_t)(x) · ∇_v φ] df_t.
-/
def IsVlasovSolution (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ ⊤ φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      WeakEvolutionEq gradW f φ gradXφ gradVφ (fun _ => 0)

-- ---------------------------------------------------------------------------
-- §9  Theorem (Existence and uniqueness for Vlasov)   (tex: thm:vlasov-wp)
-- ---------------------------------------------------------------------------

-- TODO(mathlib): `𝒫_1` (probability measures with finite first moment) is
-- expressed here via `IsProbabilityMeasure` together with a `HasFiniteIntegral`
-- condition on the norm.

/-- Predicate: μ is a probability measure on PhaseSpace d with finite first moment. -/
def HasFiniteFirstMoment (μ : Measure (PhaseSpace d)) : Prop :=
  IsProbabilityMeasure μ ∧ Integrable (fun z : PhaseSpace d => ‖z‖) μ

-- The §9 statement `vlasovWellPosedness` (tex: thm:vlasov-wp) has been
-- relocated to `Vlasov/OT/CharacteristicFlow.lean` so its proof can compose
-- directly with the characteristic-flow infrastructure
-- (`exists_vlasov_characteristicFlow`, `flow_distance_growth_bound`,
-- `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`).  See the
-- declaration site in `CharacteristicFlow.lean` for the full statement and
-- proof status; the `HasFiniteFirstMoment` predicate above stays here, used
-- by `vlasovWellPosedness`'s hypothesis and by the `_lag` cascade.

-- ---------------------------------------------------------------------------
-- §10  Equation (Characteristic / mean-field ODE)   (tex: eq:char)
-- ---------------------------------------------------------------------------

-- TODO(mathlib): The self-consistent / mean-field characteristic ODE involves
-- a fixed-point condition coupling the flow to the pushforward measure.
-- We define the notion of a characteristic flow for a *given* curve of measures.

/-- (tex: eq:char)
Predicate asserting that (charX, charV) : ℝ → PhaseSpace d → PhysSpace d × PhysSpace d
is the characteristic flow associated to a given curve of spatial marginal measures
ρ : ℝ → Measure (PhysSpace d) and pair-potential gradient gradW:

  Ẋ(t, z) = V(t, z),
  V̇(t, z) = −(∇W * ρ_t)(X(t, z)),
  (X, V)(0, z) = z.

The self-consistent condition (ρ_t is the pushforward of f_0 under X(t, ·)) is
captured by `IsCharacteristicFlowSelfConsistent`.
-/
def IsCharacteristicFlow
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) : Prop :=
  -- initial condition
  (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) ∧
  -- position ODE: Ẋ(t, z) = V(t, z)
  (∀ t z, HasDerivAt (fun s => charX s z) (charV t z) t) ∧
  -- velocity ODE: V̇(t, z) = −(∇W * ρ_t)(X(t, z))
  (∀ t z, HasDerivAt (fun s => charV s z)
      (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)

/-- (tex: eq:char)
The self-consistency condition: the spatial marginal ρ_t equals the pushforward
of the initial spatial marginal f₀_x under the position map X(t, ·). -/
def IsCharacteristicFlowSelfConsistent
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (ρ : ℝ → Measure (PhysSpace d)) : Prop :=
  ∀ t, ρ t = Measure.map (fun z => charX t z) f₀

/-- (tex: eq:char)
The Vlasov solution f_t is the pushforward of f_0 under the characteristic map
(X(t,·), V(t,·)). -/
noncomputable def vlasovSolutionViaPushforward
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) (t : ℝ) : Measure (PhaseSpace d) :=
  Measure.map (fun z => (charX t z, charV t z)) f₀

/-- A Vlasov solution with an explicit characteristic-flow representation.

Strictly stronger than `IsVlasovSolution`: every `IsLagrangianVlasovSolution`
satisfies the weak PDE AND admits a global characteristic flow `(charX, charV)`
such that `f t = (charX t, charV t)_# (f 0)` for every `t`.

This is the regularity level at which the dynamic-continuity / Lipschitz-on-
flow / dominated-convergence-on-trajectory proofs (USC of W₁ under narrow
convergence, derivative bound for Gronwall, narrow continuity in the KR-dual
formulation) compose cleanly.  The session's three structural-failure
datapoints (`MathlibTODO_W1ContOn_uscNarrow`, `vlasov_trajectory_lipschitz_bound`,
`w1_lscNarrow_integralContOn_lip`) all root-cause to the absence of these
witnesses in the abstract `IsVlasovSolution`.

Proved producers:
  * `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`
    (`Vlasov/OT/CharacteristicFlow.lean`) — trivially, since the Stage C
    wrapper already takes the flow as a hypothesis and the pushforward
    equation holds by `vlasovSolutionViaPushforward`'s definition.
  * `vlasovWellPosedness` produces `IsLagrangianVlasovSolution` from a
    Banach fixed-point construction on spatial marginals — the characteristic
    flow falls out of the existence proof as a byproduct, so the predicate's
    stronger conclusion is free of additional infrastructure cost.

Strict additivity: `IsLagrangianVlasovSolution gradW f → IsVlasovSolution gradW f`
by `.1`.  No existing `IsVlasovSolution` consumer needs to migrate; opt-in
`_lag` variants of targets that need the flow witness (uscNarrow, derivBound,
H1, SC.8) are introduced as new declarations alongside the originals. -/
def IsLagrangianVlasovSolution (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) : Prop :=
  IsVlasovSolution gradW f ∧
  ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
    IsCharacteristicFlow gradW (fun t => spatialMarginal (f t)) charX charV ∧
    (∀ t, f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
    (∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0))

-- ---------------------------------------------------------------------------
-- §11  Theorem (Dobrushin, 1979)   (tex: thm:dobrushin)
-- ---------------------------------------------------------------------------

-- TODO(mathlib): Wasserstein-1 distance between probability measures is
-- available in Mathlib as `MeasureTheory.ProbabilityMeasure.FiniteWasserstein`
-- or via `MeasureTheory.Measure.HasFiniteWasserstein`, but the API is still
-- developing.  We introduce a local placeholder `wasserstein1`.

/- Wasserstein-1 distance between two measures on a (pseudo)metric space,
defined via the Kantorovich–Rubinstein dual formula

  W₁(μ, ν) = sup { ∫ f dμ − ∫ f dν | f : 1-Lipschitz, f : α → ℝ }.

Returns `ℝ≥0∞` so that unbounded suprema (e.g. when a measure has no finite
first moment) are represented honestly as `⊤` rather than collapsing to the
conditional-sup junk value `0` that `⨆` produces on `ℝ`.  Negative
arguments to `ENNReal.ofReal` round up to `0`; that is consistent with the
dual formula because the family of 1-Lipschitz `f` is closed under `f ↦ -f`,
so the positive parts already realise the absolute value of the signed
difference.

-- TODO(mathlib): replace with Mathlib's `MeasureTheory.Measure.wasserstein`
-- once the API is stable. -/
/-- **Cost-parameterized Wasserstein-1 functional.**  KR-dual sup over functions
whose oscillation is controlled by a cost `c`.  Using the explicit oscillation
bound `|f x − f y| ≤ c x y` (rather than `LipschitzWith 1 f` w.r.t. an ambient
metric) decouples the definition from the `PseudoMetricSpace` instance, so a
cost like `min (dist x y) 1` (the truncated-metric "W̄" cost) instantiates with
no new instance.  `wasserstein1` is the `c = dist` case. -/
noncomputable def wassersteinCost {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) : ENNReal :=
  ⨆ (f : α → ℝ) (_ : ∀ x y, |f x - f y| ≤ c x y),
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)

/-- The oscillation test class `∀ x y, |f x − f y| ≤ dist x y` coincides with
`LipschitzWith 1 f` for real-valued `f` on a pseudometric space.  Bridge between
`wassersteinCost dist` (the cost-parameterized form) and the `LipschitzWith`-
phrased property lemmas. -/
lemma lipschitzWith_one_iff_oscillation {α : Type*} [PseudoMetricSpace α]
    (f : α → ℝ) : LipschitzWith 1 f ↔ ∀ x y, |f x - f y| ≤ dist x y := by
  constructor
  · intro hf x y
    have := hf.dist_le_mul x y
    rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this
  · intro h
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact h x y

/-- The Kantorovich–Rubinstein dual Wasserstein-1 distance: the `c = dist` case
of `wassersteinCost`. -/
noncomputable def wasserstein1 {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ENNReal :=
  wassersteinCost (fun x y => dist x y) μ ν

/-- `wasserstein1` equals the original `LipschitzWith 1`-phrased sup.  The
property/API lemmas below `rw` through this so their bodies are unchanged from
the original definition (the only structural-touch sites; consumers reference
`wasserstein1` only through these property lemmas). -/
lemma wasserstein1_eq_iSup_lipschitz {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) :
    wasserstein1 μ ν = ⨆ (f : α → ℝ) (_ : LipschitzWith 1 f),
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
  unfold wasserstein1 wassersteinCost
  simp only [lipschitzWith_one_iff_oscillation]

/-- For probability measures μ, ν on a normed space `E` with finite first moments
(i.e. `Integrable (fun y => ‖y‖) μ` and same for ν), the Wasserstein-1 distance
is finite: `wasserstein1 μ ν < ⊤`.

Proof sketch:  For any 1-Lipschitz `φ : E → ℝ`, set `ψ y := φ y - φ 0`.  Then
|ψ(y)| ≤ ‖y‖ by 1-Lipschitz-ness, and ∫φdμ − ∫φdν = ∫ψdμ − ∫ψdν (the constants
φ(0)·μ(univ) = φ(0)·ν(univ) cancel since both are probability measures).
So ∫φdμ − ∫φdν ≤ ∫|ψ|dμ + ∫|ψ|dν ≤ ∫‖y‖dμ + ∫‖y‖dν =: M, finite.
Taking sup over 1-Lip φ: `wasserstein1 μ ν ≤ ENNReal.ofReal M < ⊤`. -/
lemma wasserstein1_lt_top_of_finite_moment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y => ‖y‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    wasserstein1 μ ν < ⊤ := by
  -- Bound: sup over 1-Lip φ of ∫φd(μ-ν) ≤ ∫‖y‖dμ + ∫‖y‖dν =: M, which is finite.
  set M : ℝ := ∫ y, ‖y‖ ∂μ + ∫ y, ‖y‖ ∂ν with hM_def
  suffices h : wasserstein1 μ ν ≤ ENNReal.ofReal M from
    h.trans_lt ENNReal.ofReal_lt_top
  rw [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  -- Pointwise: |φ y - φ 0| ≤ ‖y‖ (1-Lipschitz)
  have hψ_bound : ∀ y, |φ y - φ 0| ≤ ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    exact h_lip
  -- φ is integrable on both μ and ν (bounded a.e. by integrable |φ 0| + ‖y‖)
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_μ : AEStronglyMeasurable φ μ := hφ_cont.aestronglyMeasurable
  have hφ_meas_ν : AEStronglyMeasurable φ ν := hφ_cont.aestronglyMeasurable
  have h_bound_abs : ∀ y, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith [hψ_bound y]
      _ = |φ 0| + ‖y‖ := by ring
  have h_dom_μ : Integrable (fun y => |φ 0| + ‖y‖) μ :=
    (integrable_const _).add hμ
  have h_dom_ν : Integrable (fun y => |φ 0| + ‖y‖) ν :=
    (integrable_const _).add hν
  have hφ_int_μ : Integrable φ μ :=
    h_dom_μ.mono hφ_meas_μ (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  have hφ_int_ν : Integrable φ ν :=
    h_dom_ν.mono hφ_meas_ν (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  -- ∫(φ y - φ 0) dμ = ∫φ dμ - φ 0  (since μ is a probability measure)
  have h_int_μ_const : ∫ _ : E, φ 0 ∂μ = φ 0 := by
    simp [integral_const, measure_univ]
  have h_int_ν_const : ∫ _ : E, φ 0 ∂ν = φ 0 := by
    simp [integral_const, measure_univ]
  have h_int_μ_sub : ∫ y, (φ y - φ 0) ∂μ = ∫ y, φ y ∂μ - φ 0 := by
    rw [integral_sub hφ_int_μ (integrable_const _), h_int_μ_const]
  have h_int_ν_sub : ∫ y, (φ y - φ 0) ∂ν = ∫ y, φ y ∂ν - φ 0 := by
    rw [integral_sub hφ_int_ν (integrable_const _), h_int_ν_const]
  -- ∫φ dμ - ∫φ dν = ∫(φ - φ 0)dμ - ∫(φ - φ 0)dν  (constants cancel)
  have h_diff_eq : ∫ y, φ y ∂μ - ∫ y, φ y ∂ν =
      ∫ y, (φ y - φ 0) ∂μ - ∫ y, (φ y - φ 0) ∂ν := by
    rw [h_int_μ_sub, h_int_ν_sub]; ring
  rw [h_diff_eq]
  -- Bound each side: ∫(φ-φ 0)dμ ≤ ∫‖y‖dμ and -∫(φ-φ 0)dν ≤ ∫‖y‖dν
  have hψ_int_μ : Integrable (fun y => φ y - φ 0) μ :=
    hφ_int_μ.sub (integrable_const _)
  have hψ_int_ν : Integrable (fun y => φ y - φ 0) ν :=
    hφ_int_ν.sub (integrable_const _)
  have h_bound_μ : ∫ y, (φ y - φ 0) ∂μ ≤ ∫ y, ‖y‖ ∂μ := by
    calc ∫ y, (φ y - φ 0) ∂μ
        ≤ ∫ y, |φ y - φ 0| ∂μ :=
          integral_mono_ae hψ_int_μ hψ_int_μ.abs (Filter.Eventually.of_forall fun _ => le_abs_self _)
      _ ≤ ∫ y, ‖y‖ ∂μ :=
          integral_mono_ae hψ_int_μ.abs hμ (Filter.Eventually.of_forall hψ_bound)
  have h_bound_ν : -∫ y, (φ y - φ 0) ∂ν ≤ ∫ y, ‖y‖ ∂ν := by
    rw [← integral_neg]
    calc ∫ y, -(φ y - φ 0) ∂ν
        ≤ ∫ y, |φ y - φ 0| ∂ν :=
          integral_mono_ae hψ_int_ν.neg hψ_int_ν.abs (Filter.Eventually.of_forall fun y => neg_le_abs _)
      _ ≤ ∫ y, ‖y‖ ∂ν :=
          integral_mono_ae hψ_int_ν.abs hν (Filter.Eventually.of_forall hψ_bound)
  linarith

/-- Convenience corollary: under the same hypotheses, `wasserstein1 μ ν ≠ ⊤`. -/
lemma wasserstein1_ne_top_of_finite_moment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y => ‖y‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    wasserstein1 μ ν ≠ ⊤ :=
  (wasserstein1_lt_top_of_finite_moment μ ν hμ hν).ne

/-! ### Basic algebra of `wasserstein1`

The KR-dual sup-formula makes `wasserstein1` a pseudometric on `Measure α` (we
only get a *pseudo*-metric, not a metric, because `wasserstein1 μ ν = 0` does
not characterise `μ = ν` in this generality).  The three lemmas below are
self-distance / symmetry / triangle, all derived directly from the sup-formula.
Together they make `wasserstein1` usable as the codomain of a sup-W₁ pseudo-
distance on time-indexed measure curves (see `supW1On` in
`Vlasov/OT/CharacteristicFlow.lean`). -/

/-- `wassersteinCost c μ μ = 0` (cost-generic; no hypothesis on `c`).  Self-distance
is zero; `wasserstein1_self` is the `c = dist` corollary. -/
lemma wassersteinCost_self {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ : Measure α) : wassersteinCost c μ μ = 0 := by
  unfold wassersteinCost
  apply le_antisymm _ (zero_le _)
  refine iSup_le fun _ => iSup_le fun _ => ?_
  simp

lemma wasserstein1_self {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ : Measure α) : wasserstein1 μ μ = 0 :=
  wassersteinCost_self (fun x y => dist x y) μ

/-- Symmetry: `wassersteinCost c μ ν = wassersteinCost c ν μ`.  The oscillation
test class `|f x − f y| ≤ c x y` is closed under `f ↦ −f`, so **no symmetry
assumption on `c`** is needed. -/
lemma wassersteinCost_comm {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) :
    wassersteinCost c μ ν = wassersteinCost c ν μ := by
  unfold wassersteinCost
  have hneg : ∀ (f : α → ℝ), (∀ x y, |f x - f y| ≤ c x y) →
      ∀ x y, |(-f) x - (-f) y| ≤ c x y := by
    intro f hf x y
    simp only [Pi.neg_apply]
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    exact hf x y
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    refine le_iSup_of_le (-f) (le_iSup_of_le (hneg f hf) (le_of_eq ?_))
    simp only [Pi.neg_apply, integral_neg]
    congr 1; ring
  · refine iSup_le fun f => iSup_le fun hf => ?_
    refine le_iSup_of_le (-f) (le_iSup_of_le (hneg f hf) (le_of_eq ?_))
    simp only [Pi.neg_apply, integral_neg]
    congr 1; ring

lemma wasserstein1_comm {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : wasserstein1 μ ν = wasserstein1 ν μ :=
  wassersteinCost_comm (fun x y => dist x y) μ ν

/-- Triangle inequality: `wassersteinCost c μ τ ≤ wassersteinCost c μ ν +
wassersteinCost c ν τ`.  **No triangle assumption on `c`** — the inequality is
the test-function integral decomposition (the same `f` is valid for all three
costs `wassersteinCost c · ·`). -/
lemma wassersteinCost_triangle {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν τ : Measure α) :
    wassersteinCost c μ τ ≤ wassersteinCost c μ ν + wassersteinCost c ν τ := by
  unfold wassersteinCost
  refine iSup_le fun f => iSup_le fun hf => ?_
  have hsplit : ∫ x, f x ∂μ - ∫ x, f x ∂τ =
      (∫ x, f x ∂μ - ∫ x, f x ∂ν) + (∫ x, f x ∂ν - ∫ x, f x ∂τ) := by ring
  rw [hsplit]
  calc ENNReal.ofReal _
      ≤ ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
          + ENNReal.ofReal (∫ x, f x ∂ν - ∫ x, f x ∂τ) :=
        ENNReal.ofReal_add_le
    _ ≤ (⨆ (g : α → ℝ) (_ : ∀ x y, |g x - g y| ≤ c x y),
            ENNReal.ofReal (∫ x, g x ∂μ - ∫ x, g x ∂ν))
        + (⨆ (g : α → ℝ) (_ : ∀ x y, |g x - g y| ≤ c x y),
            ENNReal.ofReal (∫ x, g x ∂ν - ∫ x, g x ∂τ)) := by
        gcongr
        · exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
        · exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)

lemma wasserstein1_triangle {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν τ : Measure α) :
    wasserstein1 μ τ ≤ wasserstein1 μ ν + wasserstein1 ν τ :=
  wassersteinCost_triangle (fun x y => dist x y) μ ν τ

/-- Quantitative finite-moment bound for `wasserstein1`: the W₁ distance is
bounded by the sum of the two measures' first moments.

This refines `wasserstein1_lt_top_of_finite_moment` (which only states ≠⊤)
by providing the explicit upper bound `∫‖y‖dμ + ∫‖y‖dν`.  Used by the sup-W₁
pseudodistance on `VlasovMeasureCurve`s to derive finiteness from the
uniform first-moment bound. -/
lemma wasserstein1_le_moments_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y => ‖y‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    wasserstein1 μ ν ≤ ENNReal.ofReal (∫ y, ‖y‖ ∂μ + ∫ y, ‖y‖ ∂ν) := by
  -- Same shape of proof as `wasserstein1_lt_top_of_finite_moment`, but
  -- producing the bound `ofReal M` itself instead of the consequent `< ⊤`.
  rw [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  have hψ_bound : ∀ y, |φ y - φ 0| ≤ ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    exact h_lip
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_μ : AEStronglyMeasurable φ μ := hφ_cont.aestronglyMeasurable
  have hφ_meas_ν : AEStronglyMeasurable φ ν := hφ_cont.aestronglyMeasurable
  have h_bound_abs : ∀ y, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith [hψ_bound y]
      _ = |φ 0| + ‖y‖ := by ring
  have h_dom_μ : Integrable (fun y => |φ 0| + ‖y‖) μ :=
    (integrable_const _).add hμ
  have h_dom_ν : Integrable (fun y => |φ 0| + ‖y‖) ν :=
    (integrable_const _).add hν
  have hφ_int_μ : Integrable φ μ :=
    h_dom_μ.mono hφ_meas_μ (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  have hφ_int_ν : Integrable φ ν :=
    h_dom_ν.mono hφ_meas_ν (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  have h_int_μ_const : ∫ _ : E, φ 0 ∂μ = φ 0 := by
    simp [integral_const, measure_univ]
  have h_int_ν_const : ∫ _ : E, φ 0 ∂ν = φ 0 := by
    simp [integral_const, measure_univ]
  have h_int_μ_sub : ∫ y, (φ y - φ 0) ∂μ = ∫ y, φ y ∂μ - φ 0 := by
    rw [integral_sub hφ_int_μ (integrable_const _), h_int_μ_const]
  have h_int_ν_sub : ∫ y, (φ y - φ 0) ∂ν = ∫ y, φ y ∂ν - φ 0 := by
    rw [integral_sub hφ_int_ν (integrable_const _), h_int_ν_const]
  have h_diff_eq : ∫ y, φ y ∂μ - ∫ y, φ y ∂ν =
      ∫ y, (φ y - φ 0) ∂μ - ∫ y, (φ y - φ 0) ∂ν := by
    rw [h_int_μ_sub, h_int_ν_sub]; ring
  rw [h_diff_eq]
  have hψ_int_μ : Integrable (fun y => φ y - φ 0) μ :=
    hφ_int_μ.sub (integrable_const _)
  have hψ_int_ν : Integrable (fun y => φ y - φ 0) ν :=
    hφ_int_ν.sub (integrable_const _)
  have h_bound_μ : ∫ y, (φ y - φ 0) ∂μ ≤ ∫ y, ‖y‖ ∂μ := by
    calc ∫ y, (φ y - φ 0) ∂μ
        ≤ ∫ y, |φ y - φ 0| ∂μ :=
          integral_mono_ae hψ_int_μ hψ_int_μ.abs
            (Filter.Eventually.of_forall fun _ => le_abs_self _)
      _ ≤ ∫ y, ‖y‖ ∂μ :=
          integral_mono_ae hψ_int_μ.abs hμ (Filter.Eventually.of_forall hψ_bound)
  have h_bound_ν : -∫ y, (φ y - φ 0) ∂ν ≤ ∫ y, ‖y‖ ∂ν := by
    rw [← integral_neg]
    calc ∫ y, -(φ y - φ 0) ∂ν
        ≤ ∫ y, |φ y - φ 0| ∂ν :=
          integral_mono_ae hψ_int_ν.neg hψ_int_ν.abs
            (Filter.Eventually.of_forall fun y => neg_le_abs _)
      _ ≤ ∫ y, ‖y‖ ∂ν :=
          integral_mono_ae hψ_int_ν.abs hν (Filter.Eventually.of_forall hψ_bound)
  linarith

/-- **Cost-generic non-expansion under Lipschitz pushforward** (O2 generalization,
front-loaded for the W̄ migration, 2026-06-04).

If `T : α → β` is `L`-Lipschitz **with respect to the costs**
(`c_β (T x) (T y) ≤ L · c_α x y`) and `c_β` is dominated by the metric on `β`
(`c_β x y ≤ dist x y`, which makes every `c_β`-oscillation test function
1-Lipschitz, hence continuous and measurable — what `integral_map` needs), then
pushforward by `T` is `L`-non-expansive in `wassersteinCost`:
`wassersteinCost c_β (T_# μ) (T_# ν) ≤ L · wassersteinCost c_α μ ν`.

`wasserstein1_le_of_lipschitz_map` (`c = dist`, below) and the W̄ analog
(`c = fun x y => min (dist x y) 1`, see the sanity `example` below) are
instances.  This is the single substantive piece of the O2 cost-parameterization
that O2-minimal deferred to the W̄ step; landing it validates the W̄-additivity
claim (the property lemmas instantiate at `min(dist,1)`). -/
lemma wassersteinCost_le_of_lipschitz_map
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β] [PseudoMetricSpace β] [OpensMeasurableSpace β]
    (c_α : α → α → ℝ) (c_β : β → β → ℝ)
    (hc_β_le : ∀ x y, c_β x y ≤ dist x y)
    (T : α → β) (L : NNReal)
    (hT_cost : ∀ x y, c_β (T x) (T y) ≤ (L : ℝ) * c_α x y)
    (hT_meas : Measurable T)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinCost c_β (Measure.map T μ) (Measure.map T ν) ≤
      (L : ENNReal) * wassersteinCost c_α μ ν := by
  unfold wassersteinCost
  refine iSup_le fun g => iSup_le fun hg => ?_
  -- `c_β`-oscillation + `c_β ≤ dist` ⇒ `g` is 1-Lipschitz ⇒ continuous ⇒ measurable.
  have hg_lip : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact le_trans (hg x y) (hc_β_le x y)
  have hg_meas : Measurable g := hg_lip.continuous.measurable
  rw [integral_map hT_meas.aemeasurable hg_meas.aestronglyMeasurable,
      integral_map hT_meas.aemeasurable hg_meas.aestronglyMeasurable]
  -- `|g(Tx) - g(Ty)| ≤ c_β(Tx,Ty) ≤ L·c_α x y`.
  have h_gT_osc : ∀ x y : α, |g (T x) - g (T y)| ≤ (L : ℝ) * c_α x y :=
    fun x y => le_trans (hg (T x) (T y)) (hT_cost x y)
  by_cases hL : L = 0
  · -- L = 0: `g ∘ T` is constant (oscillation ≤ 0), so the integral difference is 0.
    have hα_nonempty : Nonempty α := by
      by_contra h
      rw [not_nonempty_iff] at h
      have : μ Set.univ = 0 := by
        rw [Set.eq_empty_of_isEmpty (Set.univ : Set α)]; exact measure_empty
      rw [measure_univ] at this; exact one_ne_zero this
    obtain ⟨x₀⟩ := hα_nonempty
    have h_gT_const : ∀ x : α, g (T x) = g (T x₀) := by
      intro x
      have h0 : |g (T x) - g (T x₀)| ≤ 0 := by
        have := h_gT_osc x x₀; rw [hL, NNReal.coe_zero, zero_mul] at this; exact this
      have : g (T x) - g (T x₀) = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
      linarith
    rw [funext h_gT_const]
    simp [integral_const, measureReal_def, measure_univ, sub_self, ENNReal.ofReal_zero]
  · -- L > 0: `h := (g ∘ T)/L` has `c_α`-oscillation; rescale.
    have hL_pos : (0 : ℝ) < (L : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL)
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    set h : α → ℝ := fun x => g (T x) / (L : ℝ) with h_def
    have h_osc : ∀ x y, |h x - h y| ≤ c_α x y := by
      intro x y
      have h_eq : |h x - h y| = |g (T x) - g (T y)| / (L : ℝ) := by
        simp only [h_def, ← sub_div, abs_div, abs_of_pos hL_pos]
      rw [h_eq, div_le_iff₀ hL_pos]
      calc |g (T x) - g (T y)| ≤ (L : ℝ) * c_α x y := h_gT_osc x y
        _ = c_α x y * (L : ℝ) := mul_comm _ _
    have h_int_factor : ∀ (κ : Measure α), ∫ x, g (T x) ∂κ = (L : ℝ) * ∫ x, h x ∂κ := by
      intro κ; simp_rw [h_def]; rw [integral_div, mul_div_cancel₀ _ hL_ne]
    have h_diff_factor : ∫ x, g (T x) ∂μ - ∫ x, g (T x) ∂ν =
        (L : ℝ) * (∫ x, h x ∂μ - ∫ x, h x ∂ν) := by
      rw [h_int_factor μ, h_int_factor ν]; ring
    rw [h_diff_factor, ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    exact le_iSup_of_le h (le_iSup_of_le h_osc le_rfl)

/-- **W₁ non-expansion under Lipschitz pushforward** — the `c = dist` instance of
`wassersteinCost_le_of_lipschitz_map`. -/
lemma wasserstein1_le_of_lipschitz_map
    {α β : Type*}
    [MeasurableSpace α] [PseudoMetricSpace α]
    [MeasurableSpace β] [PseudoMetricSpace β] [OpensMeasurableSpace β]
    (T : α → β) (L : NNReal) (hT : LipschitzWith L T) (hT_meas : Measurable T)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wasserstein1 (Measure.map T μ) (Measure.map T ν) ≤
      (L : ENNReal) * wasserstein1 μ ν :=
  wassersteinCost_le_of_lipschitz_map (fun x y => dist x y) (fun x y => dist x y)
    (fun _ _ => le_refl _) T L (fun x y => hT.dist_le_mul x y) hT_meas μ ν

/-- **W̄-additivity sanity check** (the instantiation O2-minimal could not run —
there was no `c`-generic lemma to instantiate).  The truncated cost
`min(dist, 1)` satisfies both hypotheses of `wassersteinCost_le_of_lipschitz_map`
(`min(dist,1) ≤ dist`; and for 1-Lipschitz `T`,
`min(dist(Tx,Ty),1) ≤ min(dist x y, 1)`), so the property lemma drops in at
`c := fun x y => min (dist x y) 1`.  This validates that the W̄ migration is the
additive instantiation the plan claims. -/
example {α β : Type*}
    [MeasurableSpace α] [PseudoMetricSpace α]
    [MeasurableSpace β] [PseudoMetricSpace β] [OpensMeasurableSpace β]
    (T : α → β) (hT : LipschitzWith 1 T) (hT_meas : Measurable T)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinCost (fun x y => min (dist x y) 1) (Measure.map T μ) (Measure.map T ν) ≤
      (1 : ENNReal) * wassersteinCost (fun x y => min (dist x y) 1) μ ν :=
  wassersteinCost_le_of_lipschitz_map _ _ (fun x y => min_le_left _ _) T 1
    (fun x y => by
      rw [NNReal.coe_one, one_mul]
      refine min_le_min ?_ (le_refl 1)
      have := hT.dist_le_mul x y; rwa [NNReal.coe_one, one_mul] at this)
    hT_meas μ ν

/-- **KR-dual lower bound for `wasserstein1`** (the fourth property of the
W₁-property API, banked as a property lemma for forward-looking
close discipline per planning-notes commit `9b70ecb`).

For any 1-Lipschitz `f : α → ℝ` and any measures μ, ν on a pseudo-metric
measurable space, the (positive part of the) integral difference is a
lower bound on `W₁(μ, ν)`:
  `ENNReal.ofReal (∫ f dμ - ∫ f dν) ≤ wasserstein1 μ ν`.

This is the "easy direction" of the Kantorovich-Rubinstein dual
characterization — it is built into the definition `wasserstein1 :=
⨆ f hf, ENNReal.ofReal (∫ f dμ - ∫ f dν)` and follows by `le_iSup`.

**The unfold is appropriate here**: this lemma IS the property-API
exposure of `wasserstein1`'s dual structure.  The forward-looking
discipline ("let `wasserstein1` touch proofs only through abstract
properties") applies to *consumers* of W₁; property lemmas like this
one ARE the abstraction layer and unfold to establish the
property-level interface.  W̄-survivor automatically: when W̄ replaces
`wasserstein1`, this lemma's proof gets re-derived against W̄'s
concrete form (the KR-dual lower bound is generic across cost
formulations).

**Application** (sketch): chained with `f → -f` 1-Lipschitz, gives the
"W₁=0 → ∫f dμ = ∫f dν for 1-Lipschitz f" reduction at the entry to
the separation lemma.

**Cost-generic** (W̄-additivity): stated below for `wassersteinCost c` with `f`
of `c`-oscillation, no hypothesis on `c`; `wasserstein1_dual_lower_bound` is the
`c = dist` corollary. -/
lemma wassersteinCost_dual_lower_bound
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) (f : α → ℝ) (hf : ∀ x y, |f x - f y| ≤ c x y) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wassersteinCost c μ ν := by
  unfold wassersteinCost
  exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)

lemma wasserstein1_dual_lower_bound
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) (f : α → ℝ) (hf : LipschitzWith 1 f) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wasserstein1 μ ν :=
  wassersteinCost_dual_lower_bound (fun x y => dist x y) μ ν f
    ((lipschitzWith_one_iff_oscillation f).mp hf)

/-- **W̄-additivity across the remaining property layer** (gate-1 completion,
2026-06-04).  The cost-generic `_self`/`_comm`/`_triangle`/`_dual_lower_bound`
carry no hypothesis on `c`, so each instantiates at the truncated cost
`min(dist, 1)` unconditionally — in particular `_triangle` needs **no** triangle
inequality on `c` (the inequality is the test-function decomposition).  Together
with `wassersteinCost_le_of_lipschitz_map`'s sanity check, this validates
W̄-additivity for the full property layer. -/
example {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν τ : Measure α) (f : α → ℝ) (hf : ∀ x y, |f x - f y| ≤ min (dist x y) 1) :
    wassersteinCost (fun x y => min (dist x y) 1) μ μ = 0 ∧
    wassersteinCost (fun x y => min (dist x y) 1) μ ν =
      wassersteinCost (fun x y => min (dist x y) 1) ν μ ∧
    wassersteinCost (fun x y => min (dist x y) 1) μ τ ≤
      wassersteinCost (fun x y => min (dist x y) 1) μ ν +
        wassersteinCost (fun x y => min (dist x y) 1) ν τ ∧
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤
      wassersteinCost (fun x y => min (dist x y) 1) μ ν :=
  ⟨wassersteinCost_self _ μ, wassersteinCost_comm _ μ ν,
   wassersteinCost_triangle _ μ ν τ, wassersteinCost_dual_lower_bound _ μ ν f hf⟩

/-- **Mathlib-TODO (pure measure theory + functional analysis):
bounded-continuous integral equality from 1-Lipschitz integral equality
on first-moment-integrable probability measures over Polish normed
spaces.**

For probability measures μ, ν on a normed-AddCommGroup space `α` with
the Borel σ-algebra, both having finite first moments, if
`∫ f dμ = ∫ f dν` for every 1-Lipschitz function `f : α → ℝ` (with
appropriate integrability), then the same equality holds for every
bounded continuous function `f : α →ᵇ ℝ`.

**Proof idea (sketch — substantive Bucket-1 Mathlib gap)**:
1. For bounded-Lipschitz `g` with Lipschitz constant `L > 0`,
   `g / L` is 1-Lipschitz, so equality of integrals at scale `L`
   follows from the 1-Lipschitz hypothesis.
2. For BC `φ`, approximate by bounded-Lipschitz functions in
   `L¹(μ + ν)` via truncation + Lipschitz mollification:
   * Truncation: replace `φ` with `φ · χ_R` where `χ_R` is a Lipschitz
     bump supported on a ball of radius `R + 1`; the tail
     `μ({|y| > R}) + ν({|y| > R}) → 0` as `R → ∞` (Markov + finite
     first moments).
   * Lipschitz mollification: on a Polish normed space, BC functions
     can be uniformly approximated on bounded sets by Lipschitz
     functions (Stone-Weierstrass-flavored density of bounded-Lipschitz
     in BC under the appropriate uniformity).
3. Combining truncation + mollification + the 1-Lipschitz hypothesis
   gives `|∫ φ dμ - ∫ φ dν| ≤ ε` for any ε > 0, hence equality.

**Bucket-1 PR scope**: standard measure theory + functional analysis.
Same family as `MathlibTODO_bcNarrowFromSmoothCompactNarrow`
(Basic.lean L1794) — both are BC-extension-from-smaller-class results,
operating on different sub-classes (smooth-CS for narrow continuity
along curves vs 1-Lipschitz for integral equality on static measures).

**Banked for forward-looking close discipline**: the separation lemma
`wasserstein1_eq_zero_iff_measure_eq` consumes this as its W̄-survivor
middle step.  When W̄ arrives, this placeholder doesn't change (its
hypothesis is a 1-Lipschitz integral equality, not a W₁ fact); only
the *feeder* changes (W̄=0 → 1-Lipschitz equality replacing W₁=0 →
1-Lipschitz equality), which is a one-line `wasserstein1_dual_lower_bound`
analogue for W̄. -/
theorem MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment
    {α : Type*}
    [MeasurableSpace α] [NormedAddCommGroup α] [BorelSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (_hμ_int : Integrable (fun y : α => ‖y‖) μ)
    (_hν_int : Integrable (fun y : α => ‖y‖) ν)
    (_h_1lip : ∀ (f : α → ℝ), LipschitzWith 1 f →
               Integrable f μ → Integrable f ν →
               ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    ∀ (f : BoundedContinuousFunction α ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  sorry

/-- **Separation lemma for `wasserstein1`** (Stage 2b part 4, 2026-05-31).

For probability measures μ, ν on a Polish normed space with finite
first moments, `W₁(μ, ν) = 0` iff `μ = ν`.

**Property-only proof per forward-looking close discipline** (planning-
notes commit `9b70ecb`).  `wasserstein1` enters the proof body
exclusively through banked property lemmas:
* `wasserstein1_self` (trivial direction).
* `wasserstein1_dual_lower_bound` (W₁=0 → 1-Lipschitz integral
  equality).

The substantive middle (1-Lipschitz equality → BC equality) is
banked as the named pure-FA placeholder
`MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment` (above).
The final step (BC equality → μ = ν) routes through Mathlib's
`ext_of_forall_integral_eq_of_IsFiniteMeasure`
(`HasOuterApproxClosed.lean` L268).

**No `simp [wasserstein1]` or `unfold wasserstein1` anywhere in the
body** — `wasserstein1` enters only via the property API and the
hypothesis `h_w1_zero : wasserstein1 μ ν = 0`.  W̄-survivor by
construction: when W̄ replaces `wasserstein1`, the only changes are
the property-lemma proofs (mechanical re-derivation); this lemma's
body composes against the abstract property API and recompiles. -/
lemma wasserstein1_eq_zero_iff_measure_eq
    {α : Type*}
    [MeasurableSpace α] [NormedAddCommGroup α] [BorelSpace α]
    [HasOuterApproxClosed α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_int : Integrable (fun y : α => ‖y‖) μ)
    (hν_int : Integrable (fun y : α => ‖y‖) ν) :
    wasserstein1 μ ν = 0 ↔ μ = ν := by
  constructor
  · -- Forward (substantive): W₁=0 → μ=ν.
    intro h_w1_zero
    -- Step 1 (property-only via `wasserstein1_dual_lower_bound`):
    -- W₁=0 → ∫f dμ = ∫f dν for every integrable 1-Lipschitz f.
    have h_1lip_eq : ∀ (f : α → ℝ), LipschitzWith 1 f →
                     Integrable f μ → Integrable f ν →
                     ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
      intro f hf _hf_int_μ _hf_int_ν
      -- Apply the property at f and -f; combine.
      have h_pos : ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wasserstein1 μ ν :=
        wasserstein1_dual_lower_bound μ ν f hf
      have hf_neg : LipschitzWith 1 (-f) := by
        simpa using hf.neg
      have h_neg : ENNReal.ofReal (∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν) ≤ wasserstein1 μ ν :=
        wasserstein1_dual_lower_bound μ ν (-f) hf_neg
      rw [h_w1_zero] at h_pos h_neg
      -- ENNReal.ofReal ≤ 0 (in ENNReal) iff = 0 iff the real argument is ≤ 0.
      have h_pos_eq : ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) = 0 :=
        le_antisymm h_pos (zero_le _)
      have h_neg_eq : ENNReal.ofReal (∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν) = 0 :=
        le_antisymm h_neg (zero_le _)
      have h_diff_pos : ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ 0 :=
        (ENNReal.ofReal_eq_zero).mp h_pos_eq
      have h_diff_neg : ∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν ≤ 0 :=
        (ENNReal.ofReal_eq_zero).mp h_neg_eq
      -- ∫(-f) dμ - ∫(-f) dν = -(∫f dμ - ∫f dν).
      have h_neg_int : ∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν =
          -(∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
        simp only [Pi.neg_apply, integral_neg]; ring
      rw [h_neg_int] at h_diff_neg
      linarith
    -- Step 2 (placeholder, W̄-survivor): 1-Lipschitz integral equality → BC integral
    -- equality.  See `MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment` above.
    have h_bc_eq : ∀ (f : BoundedContinuousFunction α ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν :=
      MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment μ ν hμ_int hν_int h_1lip_eq
    -- Step 3 (Mathlib `ext_of_forall_integral_eq_of_IsFiniteMeasure`): BC equality → μ=ν.
    exact ext_of_forall_integral_eq_of_IsFiniteMeasure h_bc_eq
  · -- Backward (trivial): μ=ν → W₁=0, via the property `wasserstein1_self`.
    intro h_eq
    subst h_eq
    exact wasserstein1_self μ

/-- **Mathlib-TODO: completeness of `(𝒫_1(PhysSpace d), W₁)` for Polish spaces.**

A Cauchy sequence in W₁ with a uniform first-moment bound has a W₁-limit
in `𝒫_1`.  The proof routes through Prokhorov + tightness from the moment
bound + narrow-to-W₁ upgrade under moment control.  Mathlib's
narrow-tightness machinery for Polish spaces is not stable at time of
writing; lifted to a placeholder until upstream catches up.

**Used by**: Stage 4 of the well-posedness plan to lift the Picard
iteration's Cauchy sequence (derived from the `Phi_supW1_contraction`
contraction estimate) to a W₁-limit in the curve space.  The resulting
limit is a fixed point of the Picard iteration, which yields a
self-consistent characteristic flow + Vlasov solution on `[0, T₀]`.

**Architectural rationale** (per plan's Stage 4 decision): treating this
as a named placeholder is consistent with the project's strategic
discipline.  The four existing `MathlibTODO_*` placeholders made the same
trade — known-doable Mathlib-OT gap, deferred to a separate focused
session, with the API in place so downstream consumers compose cleanly.
Closure routes through Prokhorov + narrow-tightness for Polish spaces;
substantial Mathlib-OT effort, treated as separate from the project's
critical-path closure.

**Sorry-count impact**: +1 (placeholder body) — planned per the plan's
Stage 4 sorry-count trajectory `5 → 6`. -/
theorem MathlibTODO_cauchyW1_hasNarrowLimit {d : ℕ} [NeZero d]
    (ν : ℕ → Measure (PhysSpace d)) [∀ n, IsProbabilityMeasure (ν n)]
    (M : ℝ) (hMom : ∀ n, ∫ y, ‖y‖ ∂(ν n) ≤ M)
    (h_yint : ∀ n, Integrable (fun y : PhysSpace d => ‖y‖) (ν n))
    -- Cauchy hypothesis in ENNReal form (per M-series design principle:
    -- ENNReal-valued algebraic arguments stay in ENNReal; project to ℝ
    -- via `.toReal` only at the boundary or not at all).
    (hCauchy : ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
                 wasserstein1 (ν m) (ν n) < ε) :
    ∃ μ : Measure (PhysSpace d), IsProbabilityMeasure μ ∧
      Integrable (fun y : PhysSpace d => ‖y‖) μ ∧
      -- Moment-preservation: the bound `M` passes to the limit by
      -- lower-semicontinuity of `∫ ‖·‖ ∂·` under W₁-convergence.  Standard
      -- consequence of W₁-convergence + uniform moment control; included
      -- in the placeholder's conclusion so downstream consumers
      -- (`picard_iterate_bundlesAs_VlasovMeasureCurve`) can re-use the
      -- same moment bound for the limit's `VlasovMeasureCurve` packaging.
      ∫ y, ‖y‖ ∂μ ≤ M ∧
      -- Conclusion also in ENNReal form; downstream consumers project
      -- to ℝ when matching `VlasovMeasureCurve.hW1Cont`'s `.toReal` interface.
      Filter.Tendsto (fun n => wasserstein1 (ν n) μ)
        Filter.atTop (nhds 0) := by
  sorry

/-! Decomposed by sorry-decomposer.
    See `formalize/plans/dobrushin.json`. -/

/-! Decomposed by sorry-decomposer.
    See `formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`. -/

/-!
## Note on the remaining sorries in this cascade

`convolveLipschitz_KR_le`, `convolveLipschitz_inner_bound`, the parent
`MathlibTODO_convolveLipschitzEstimate`, and (downstream) the
`wassersteinGronwallCoupling_ofReal_le` + parent
`MathlibTODO_wassersteinGronwallCoupling` all conclude in `.toReal`
of an ENNReal expression involving `wasserstein1 ρ σ`.  The
inequality is FALSE without a finiteness hypothesis on
`wasserstein1 ρ σ`, because `(⊤ : ℝ≥0∞).toReal = 0` collapses any
positive LHS bound by a `wasserstein1` term.

To close these sorries constructively, we'd need either
  (a) thread `wasserstein1 ρ σ ≠ ⊤` as a hypothesis through the
      cascade and derive it at the dobrushin call site from
      `HasFiniteFirstMoment` via a `wasserstein1_lt_top_of_finite_moment`
      lemma (provable but ~30-50 lines of measure-theoretic
      plumbing); or
  (b) restate the cascade in ENNReal form (no `.toReal`), where the
      bound holds trivially when `wasserstein1 = ⊤`.

Either is a structural change beyond the scope of the current
cleanup pass, so the cascade stays decomposed-with-sorries: each
helper has a clear constructive sketch in its docstring, and the
plan JSON records the textbook proof structure.  The remaining
`MathlibTODO_*` placeholders (`W1ContOn`, `derivBound`) are the
genuine PDE/coupling-theory gaps and are blocked on Mathlib OT
infrastructure (full KR duality, characteristic flow theory for
measure-valued ODEs).  See `formalize/DESIGN.md` for the bigger
picture.
-/


/-- For fixed `x : PhysSpace d` and `v : PhysSpace d`, the function
`y ↦ @inner ℝ (PhysSpace d) _ (gradW (x - y)) v` is LipschitzWith `(L * ‖v‖₊)`.
Proof: the map `y ↦ gradW (x - y)` is L-Lipschitz (composition of the L-Lipschitz `gradW`
with the 1-Lipschitz subtraction `y ↦ x - y`), and `w ↦ ⟨w, v⟩` is `‖v‖₊`-Lipschitz
(bounded linear map with operator norm `‖v‖`); compose via `LipschitzWith.comp`. -/
lemma convolveLipschitz_inner_lipschitz
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (x v : PhysSpace d) :
    LipschitzWith (L * ‖v‖₊) (fun y : PhysSpace d =>
      @inner ℝ (PhysSpace d) _ (gradW (x - y)) v) := by
  -- Step 1: y ↦ x - y is 1-Lipschitz (direct check via dist)
  have h_sub : LipschitzWith 1 (fun y : PhysSpace d => x - y) := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
        sub_sub_sub_cancel_left, norm_sub_rev]
  -- Step 2: gradW ∘ (x - ·) is L-Lipschitz (since L * 1 = L)
  have h_gW : LipschitzWith L (fun y : PhysSpace d => gradW (x - y)) := by
    simpa using hL.comp h_sub
  -- Step 3: w ↦ ⟨w, v⟩ is ‖v‖₊-Lipschitz by Cauchy-Schwarz
  have h_inner_v : LipschitzWith ‖v‖₊
      (fun w : PhysSpace d => @inner ℝ (PhysSpace d) _ w v) := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [Real.dist_eq, ← inner_sub_left, dist_eq_norm]
    calc |@inner ℝ (PhysSpace d) _ (a - b) v|
        ≤ ‖a - b‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = (‖v‖₊ : ℝ) * ‖a - b‖ := by rw [mul_comm]; rfl
  -- Step 4: compose (Lipschitz constant is ‖v‖₊ * L; rewrite to L * ‖v‖₊)
  have h_comp := h_inner_v.comp h_gW
  rwa [mul_comm] at h_comp

/-- For any 1-Lipschitz function `φ : PhysSpace d → ℝ`, the integral difference
`∫ φ dρ − ∫ φ dσ ≤ (wasserstein1 ρ σ).toReal`.
This follows directly from the Kantorovich–Rubinstein definition of `wasserstein1` as the
supremum of integral differences over 1-Lipschitz test functions, together with
`ENNReal.toReal_iSup` and `ENNReal.ofReal_toReal` to convert between ENNReal and ℝ. -/
lemma convolveLipschitz_KR_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (ρ σ : Measure α) (φ : α → ℝ) (hφ : LipschitzWith 1 φ)
    (hW : wasserstein1 ρ σ ≠ ⊤) :
    ∫ y, φ y ∂ρ - ∫ y, φ y ∂σ ≤ (wasserstein1 ρ σ).toReal := by
  -- The KR-dual lower bound (property-only): ENNReal.ofReal (∫φdρ − ∫φdσ) ≤ W₁.
  have h_sup : ENNReal.ofReal (∫ y, φ y ∂ρ - ∫ y, φ y ∂σ) ≤ wasserstein1 ρ σ :=
    wasserstein1_dual_lower_bound ρ σ φ hφ
  -- Convert to .toReal preserving the inequality.
  by_cases h_pos : 0 ≤ ∫ y, φ y ∂ρ - ∫ y, φ y ∂σ
  · -- positive case: ENNReal.ofReal x .toReal = x
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hW).mpr h_sup
    rwa [ENNReal.toReal_ofReal h_pos] at this
  · -- negative case: LHS < 0 ≤ wasserstein1.toReal
    push_neg at h_pos
    exact h_pos.le.trans ENNReal.toReal_nonneg

/-- For any `v : PhysSpace d` with `‖v‖ ≤ 1`, the real inner product
`⟨(∇W∗ρ)(x) − (∇W∗σ)(x), v⟩` is bounded by `(L : ℝ) * (wasserstein1 ρ σ).toReal`.
Proof: unfold `convolveFunctionMeasure` to expose `∫ gradW(x−y) dρ` and `∫ gradW(x−y) dσ`;
commute the inner product `⟨·, v⟩` (a continuous linear map) through each integral via
`ContinuousLinearMap.integral_comp_comm`; then the integrand function
`y ↦ ⟨gradW(x−y), v⟩` has Lipschitz constant `L * ‖v‖` ≤ `L` (from `convolveLipschitz_inner_lipschitz`),
so `(1/L) * (that integrand)` is 1-Lipschitz and `convolveLipschitz_KR_le` closes the estimate. -/
lemma convolveLipschitz_inner_bound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : Measure (PhysSpace d))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (x : PhysSpace d)
    (hW : wasserstein1 ρ σ ≠ ⊤)
    (hρ_int : Integrable (fun y => gradW (x - y)) ρ)
    (hσ_int : Integrable (fun y => gradW (x - y)) σ) :
    ∀ v : PhysSpace d, ‖v‖ ≤ 1 →
      @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW ρ x -
        convolveFunctionMeasure gradW σ x) v ≤
        (L : ℝ) * (wasserstein1 ρ σ).toReal := by
  intro v hv
  unfold convolveFunctionMeasure
  -- Case 1: v = 0 — inner with 0 is 0, RHS ≥ 0.
  by_cases hv_zero : v = 0
  · subst hv_zero
    rw [inner_zero_right]
    exact mul_nonneg L.coe_nonneg ENNReal.toReal_nonneg
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_zero
  -- Case 2: L = 0 — gradW is constant, and probability measures both have mass 1,
  -- so the two convolution integrals are equal, the difference is 0, the inner is 0.
  by_cases hL_zero : L = 0
  · have hgW_const : ∀ y, gradW (x - y) = gradW x := fun y => by
      have h := hL.dist_le_mul (x - y) x
      rw [hL_zero, NNReal.coe_zero, zero_mul] at h
      have h0 : dist (gradW (x - y)) (gradW x) = 0 := le_antisymm h dist_nonneg
      exact dist_eq_zero.mp h0
    have h_fun_eq : (fun y => gradW (x - y)) = (fun _ : PhysSpace d => gradW x) :=
      funext hgW_const
    have hF : ∫ y, gradW (x - y) ∂ρ = gradW x := by
      rw [h_fun_eq, integral_const]; simp
    have hG : ∫ y, gradW (x - y) ∂σ = gradW x := by
      rw [h_fun_eq, integral_const]; simp
    rw [hF, hG, sub_self, inner_zero_left]
    rw [hL_zero, NNReal.coe_zero, zero_mul]
  -- Case 3: L > 0 and v ≠ 0 — main KR rescaling argument.
  have hL_pos : (0 : ℝ) < L := lt_of_le_of_ne L.coe_nonneg (fun h =>
    hL_zero (NNReal.coe_eq_zero.mp h.symm))
  have hc_pos : (0 : ℝ) < (L : ℝ) * ‖v‖ := mul_pos hL_pos hv_pos
  -- Distribute inner across subtraction
  rw [inner_sub_left]
  -- Swap inner with integral on each side (via integral_inner + real_inner_comm)
  have h_swap_ρ : @inner ℝ (PhysSpace d) _ (∫ y, gradW (x - y) ∂ρ) v =
                  ∫ y, @inner ℝ (PhysSpace d) _ (gradW (x - y)) v ∂ρ := by
    rw [real_inner_comm, ← integral_inner hρ_int v]
    simp_rw [real_inner_comm v]
  have h_swap_σ : @inner ℝ (PhysSpace d) _ (∫ y, gradW (x - y) ∂σ) v =
                  ∫ y, @inner ℝ (PhysSpace d) _ (gradW (x - y)) v ∂σ := by
    rw [real_inner_comm, ← integral_inner hσ_int v]
    simp_rw [real_inner_comm v]
  rw [h_swap_ρ, h_swap_σ]
  -- Now goal: ∫ψ dρ − ∫ψ dσ ≤ L · W₁.toReal, with ψ(y) := ⟪gradW(x-y), v⟫_ℝ.
  set ψ : PhysSpace d → ℝ := fun y => @inner ℝ (PhysSpace d) _ (gradW (x - y)) v
    with hψ_def
  have hψ_lip : LipschitzWith (L * ‖v‖₊) ψ :=
    convolveLipschitz_inner_lipschitz gradW L hL x v
  -- Rescale ψ by c := L · ‖v‖ to get 1-Lipschitz φ.
  set c : ℝ := (L : ℝ) * ‖v‖ with hc_def
  set φ : PhysSpace d → ℝ := fun y => ψ y / c with hφ_def
  -- Coerce: ((L * ‖v‖₊ : ℝ≥0) : ℝ) = c
  have h_coe : ((L * ‖v‖₊ : NNReal) : ℝ) = c := by
    simp [hc_def, NNReal.coe_mul]
  -- φ is 1-Lipschitz: bound dist (φ a) (φ b).
  have hφ_lip : LipschitzWith 1 φ := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [NNReal.coe_one, one_mul]
    have hψ_d : dist (ψ a) (ψ b) ≤ c * dist a b := by
      have := hψ_lip.dist_le_mul a b
      rwa [h_coe] at this
    -- dist (ψ a / c) (ψ b / c) = dist (ψ a) (ψ b) / c   (c > 0)
    have h_dist_div : dist (φ a) (φ b) = dist (ψ a) (ψ b) / c := by
      simp [hφ_def, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hc_pos]
    rw [h_dist_div, div_le_iff₀ hc_pos]
    linarith
  -- Apply KR easy direction to the rescaled φ.
  have h_kr : ∫ y, φ y ∂ρ - ∫ y, φ y ∂σ ≤ (wasserstein1 ρ σ).toReal :=
    convolveLipschitz_KR_le ρ σ φ hφ_lip hW
  -- ∫φ = ∫ψ / c  (Bochner integral commutes with scalar division)
  have h_int_φ_ρ : ∫ y, φ y ∂ρ = (∫ y, ψ y ∂ρ) / c := by
    simp_rw [hφ_def, div_eq_mul_inv]
    rw [integral_mul_const]
  have h_int_φ_σ : ∫ y, φ y ∂σ = (∫ y, ψ y ∂σ) / c := by
    simp_rw [hφ_def, div_eq_mul_inv]
    rw [integral_mul_const]
  rw [h_int_φ_ρ, h_int_φ_σ, ← sub_div, div_le_iff₀ hc_pos] at h_kr
  -- h_kr : ∫ψ dρ − ∫ψ dσ ≤ W₁.toReal * c
  -- Goal:  ∫ψ dρ − ∫ψ dσ ≤ L * W₁.toReal
  -- Bridge: c * W₁ = L * ‖v‖ * W₁ ≤ L * W₁  (since ‖v‖ ≤ 1, W₁ ≥ 0)
  have hW_nonneg : 0 ≤ (wasserstein1 ρ σ).toReal := ENNReal.toReal_nonneg
  have h_chain : (wasserstein1 ρ σ).toReal * c ≤ (L : ℝ) * (wasserstein1 ρ σ).toReal := by
    rw [hc_def]
    calc (wasserstein1 ρ σ).toReal * ((L : ℝ) * ‖v‖)
        = (L : ℝ) * ((wasserstein1 ρ σ).toReal * ‖v‖) := by ring
      _ ≤ (L : ℝ) * ((wasserstein1 ρ σ).toReal * 1) := by
          gcongr
      _ = (L : ℝ) * (wasserstein1 ρ σ).toReal := by ring
  linarith

/-- For `z : PhysSpace d` and `C : ℝ`, if every unit vector `v` (with `‖v‖ ≤ 1`) satisfies
`@inner ℝ (PhysSpace d) _ z v ≤ C`, then `‖z‖ ≤ C`.
Proof: in the `z = 0` case, `‖0‖ = 0 ≤ C` (from `C ≥ ⟨0, 0⟩ = 0`); in the `z ≠ 0` case,
take `v = z / ‖z‖` (which satisfies `‖v‖ = 1`); then
`‖z‖ = ⟨z, z/‖z‖⟩ = ⟨z, v⟩ ≤ C` by hypothesis via `real_inner_self_eq_norm_mul_norm`. -/
lemma convolveLipschitz_norm_le_of_inner_forall
    {d : ℕ} [NeZero d]
    (z : PhysSpace d) (C : ℝ)
    (h : ∀ v : PhysSpace d, ‖v‖ ≤ 1 → @inner ℝ (PhysSpace d) _ z v ≤ C) :
    ‖z‖ ≤ C := by
  by_cases hz : z = 0
  · -- z = 0 case: ‖0‖ = 0 ≤ C follows from h 0 (which gives ⟨0, 0⟩ = 0 ≤ C).
    rw [hz, norm_zero]
    have h0 := h 0 (by simp)
    simpa using h0
  · -- z ≠ 0 case: take v = z/‖z‖, which is a unit vector.
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set v : PhysSpace d := (‖z‖⁻¹) • z with hv_def
    have hv_norm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hz_pos), inv_mul_cancel₀ hz_pos.ne']
    -- ⟨z, v⟩ = ‖z‖⁻¹ * ⟨z, z⟩ = ‖z‖⁻¹ * ‖z‖² = ‖z‖
    have h_inner : @inner ℝ (PhysSpace d) _ z v = ‖z‖ := by
      rw [hv_def, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
      field_simp
    rw [← h_inner]
    exact h v hv_norm.le

-- Mathlib gap: pointwise Lipschitz estimate for the convolution ∇W * ρ.
-- Requires Wasserstein-1 Kantorovich–Rubinstein duality, which is not yet
-- in Mathlib's stable API for general metric spaces.
theorem MathlibTODO_convolveLipschitzEstimate
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : Measure (PhysSpace d))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (x : PhysSpace d)
    (hW : wasserstein1 ρ σ ≠ ⊤)
    (hρ_int : Integrable (fun y => gradW (x - y)) ρ)
    (hσ_int : Integrable (fun y => gradW (x - y)) σ) :
    ‖convolveFunctionMeasure gradW ρ x - convolveFunctionMeasure gradW σ x‖ ≤
      (L : ℝ) * (wasserstein1 ρ σ).toReal := by
  -- Compose: from convolveLipschitz_inner_bound (for all unit v, ⟨z, v⟩ ≤ M)
  --          and convolveLipschitz_norm_le_of_inner_forall (then ‖z‖ ≤ M).
  exact convolveLipschitz_norm_le_of_inner_forall
    (convolveFunctionMeasure gradW ρ x - convolveFunctionMeasure gradW σ x)
    ((L : ℝ) * (wasserstein1 ρ σ).toReal)
    (convolveLipschitz_inner_bound gradW L hL ρ σ x hW hρ_int hσ_int)

/-! Decomposed by sorry-decomposer.
    See `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`. -/

/-! Decomposed by sorry-decomposer.
    See `formalize/plans/MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json`. -/

/-! Decomposed by sorry-decomposer.
    See `formalize/plans/MathlibTODO_W1ContOn_lscNarrow.json`. -/

-- Removed (closure-plan Sorry 1, 2026-05-31):
--   `w1_lscNarrow_integralContOn_lip` (the sorry'd non-`_lag` version)
--   + downstream chain `w1_lscNarrow_diff_contOn` + `w1_lscNarrow_summand_lscOn`.
-- The chain was sorry-decomposer scaffolding for `MathlibTODO_W1ContOn_lscNarrow`.
-- Since the load-bearing sub-lemma is unprovable without DiPerna-Lions
-- superposition (out of scope), the chain has been removed and
-- `MathlibTODO_W1ContOn_lscNarrow` is now a direct sorry placeholder per the
-- MathlibTODO-only-state cleanup arc.
-- The `_lag` variant `w1_lscNarrow_integralContOn_lip_lag` (which IS proved
-- via the pushforward equation) is preserved below as banked infrastructure.

/-- **`_lag` variant of `w1_lscNarrow_integralContOn_lip`** — uses the
enriched `IsLagrangianVlasovSolution` predicate instead of bare
`IsVlasovSolution`.

The enrichment makes the proof structurally clean: by the pushforward
equation `f t = Measure.map (charX t, charV t) (f 0)` and `integral_map`,
`∫ φ d(f t) = ∫ (φ ∘ (charX t, charV t)) d(f 0)`.  Continuity in `t` then
reduces to dominated convergence on the *fixed* measure `f 0`, with
pointwise continuity from the flow's `HasDerivAt` and an integrable
dominator from `HasFiniteFirstMoment (f 0)` + a flow-growth bound.

The mollification approach (which couldn't close due to non-uniform-in-t
first moments) is bypassed entirely.

This `_lag` variant exists alongside the original (which remains sorry'd)
for opt-in consumers that have access to the characteristic flow witness. -/
lemma w1_lscNarrow_integralContOn_lip_lag
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d))
    (hf_lag : IsLagrangianVlasovSolution gradW f)
    (hf_prob_0 : HasFiniteFirstMoment (f 0))
    (T : ℝ) (hT : 0 ≤ T)
    -- Flow-growth prerequisites: imported from `flow_distance_growth_bound`.
    -- Eventual callers (e.g. `vlasovWellPosedness`) will derive these from
    -- `HasFiniteFirstMoment (f 0)` + `LipschitzWith gradW` via a bootstrap
    -- Gronwall on the first moment of the spatial marginal.
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T,
      ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f t)))
    (h_conv_int : ∀ t (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (f t)))
    [∀ t, IsProbabilityMeasure (spatialMarginal (f t))]
    (φ : PhaseSpace d → ℝ)
    (hφ_lip : LipschitzWith 1 φ) :
    ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T) := by
  -- Step 1: Destructure IsLagrangianVlasovSolution
  obtain ⟨_, charX, charV, hflow, hpush, hflow_meas⟩ := hf_lag
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  -- Step 2: Rewrite ∫ φ d(f t) = ∫ (φ ∘ (charX t, charV t)) d(f 0)
  have h_rw : ∀ t, ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by
    intro t
    rw [hpush t]
    exact integral_map (hflow_meas t) hφ_lip.continuous.measurable.aestronglyMeasurable
  -- Step 3: Prove growth bound inline (replicate flow_distance_growth_bound)
  set ρ := fun t => spatialMarginal (f t) with hρ_def
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Convolution bound: ‖(∇W ∗ ρ_s)(x)‖ ≤ ε₀ + L * ‖x‖
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
        simp only [sub_add_cancel] at this; linarith
      linarith
    calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
          integral_mono (h_conv_int s x).norm h_bnd_int (fun y => h_pt y)
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
                  have hρs : ρ s = spatialMarginal (f s) := rfl
                  haveI : IsProbabilityMeasure (ρ s) := hρs ▸ inferInstance
                  have h_y_int_ρ : Integrable (fun y => ‖y‖) (ρ s) := hρs ▸ h_y_int s hs
                  rw [integral_add (integrable_const _) h_y_int_ρ, integral_const]
                  simp [measureReal_def]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
          simp only [hε₀_def]
          linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- Growth bound: ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) for t ∈ Icc 0 T
  set C_T := gronwallBound 1 K ε₀ T with hC_T_def
  have hC_T_nn : 0 ≤ C_T := by
    have hmono := gronwallBound_mono (by norm_num : (0:ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  have h_flow_bound : ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
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
      h_f_cont h_deriv h_init h_bound t ht
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
  -- Step 4: Apply continuousOn_of_dominated
  rw [show (fun t => ∫ z, φ z ∂(f t)) = (fun t => ∫ z, φ (charX t z, charV t z) ∂(f 0)) from
    funext h_rw]
  apply continuousOn_of_dominated (bound := fun z => ‖φ 0‖ + C_T * (‖z‖ + 1))
  · -- AEStronglyMeasurable
    intro t _
    exact hφ_lip.continuous.measurable.aestronglyMeasurable.comp_aemeasurable (hflow_meas t)
  · -- Uniform bound
    intro t ht
    apply Filter.Eventually.of_forall
    intro z
    have h_lip_bound : ‖φ (charX t z, charV t z)‖ ≤ ‖φ 0‖ + ‖(charX t z, charV t z)‖ := by
      have hd := hφ_lip.dist_le_mul (charX t z, charV t z) 0
      simp only [dist_eq_norm, NNReal.coe_one, one_mul, sub_zero] at hd
      have htri : ‖φ (charX t z, charV t z)‖ ≤ ‖φ (charX t z, charV t z) - φ 0‖ + ‖φ 0‖ := by
        have := norm_add_le (φ (charX t z, charV t z) - φ 0) (φ 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    linarith [h_flow_bound t ht z]
  · -- Integrable dominator
    haveI : IsProbabilityMeasure (f 0) := hf_prob_0.1
    have h_int_norm : Integrable (fun z : PhaseSpace d => ‖z‖) (f 0) := hf_prob_0.2
    have h_int_1 : Integrable (fun _ : PhaseSpace d => (1 : ℝ)) (f 0) :=
      integrable_const 1
    have h_int_norm1 : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) (f 0) :=
      h_int_norm.add h_int_1
    exact (integrable_const ‖φ 0‖).add (h_int_norm1.const_mul C_T)
  · -- Pointwise continuity
    apply Filter.Eventually.of_forall
    intro z
    apply ContinuousOn.comp hφ_lip.continuous.continuousOn
    · exact continuousOn_of_forall_continuousAt fun s _ =>
        (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
    · exact fun _ _ => Set.mem_univ _

-- Removed (closure-plan Sorry 1, 2026-05-31):
--   `w1_lscNarrow_diff_contOn` (depended on the removed
--   `w1_lscNarrow_integralContOn_lip`).
--   `w1_lscNarrow_summand_lscOn` (depended on the removed `_diff_contOn`).
-- See the removal comment above `w1_lscNarrow_integralContOn_lip_lag` for
-- the closure-plan rationale.  `MathlibTODO_W1ContOn_lscNarrow` below now
-- has a direct sorry body instead of composing through the removed chain.

/-- Given per-1-Lipschitz LSC of each summand `t ↦ ENNReal.ofReal(∫φd(f t) - ∫φd(g t))`,
the Wasserstein-1 distance `wasserstein1 (f t) (g t) = ⨆ φ (_ : LipschitzWith 1 φ), …`
is LowerSemicontinuousOn `Set.Icc 0 T` as a double supremum of LSC functions
via `lowerSemicontinuousOn_iSup` applied twice. -/
lemma w1_lscNarrow_of_summands
    {d : ℕ} [NeZero d]
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ)
    (h_summands : ∀ (φ : PhaseSpace d → ℝ) (_hφ : LipschitzWith 1 φ),
        LowerSemicontinuousOn
          (fun t => ENNReal.ofReal (∫ z, φ z ∂(f t) - ∫ z, φ z ∂(g t)))
          (Set.Icc 0 T)) :
    LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  exact lowerSemicontinuousOn_biSup (fun φ hφ => h_summands φ hφ)

/-- **Mathlib-TODO (pure functional-analytic): W₁ is lower semicontinuous
along pairs of narrowly continuous probability-measure curves with uniform
first-moment bound.**

**⚑ STATUS UNCERTAIN 2026-06-03 — STRUCTURE UNCERTAIN, CLOSE UNBUILT; external-
vs-in-project not resolved.**  The
close needs BC→1-Lipschitz narrow-continuity under the moment bound (Mathlib's
`lowerSemicontinuousOn_biSup` is the engine, but its summands need *unbounded*
1-Lipschitz narrow continuity, while the hypotheses only deliver it for *bounded*
φ).  This may be buildable in-project via a moment-controlled truncation, OR
genuinely external — NOT confidently a Mathlib gap.  Least certain of the
deferred set; resolve by checking whether a moment-truncation upgrades BC- to
1-Lipschitz-narrow-continuity.

If `f, g : ℝ → Measure α` are two measure curves on a Polish space `α`,
both narrowly continuous (∫g dμ_t continuous in t for every bounded
continuous g) and with uniform first-moment integrability on [0, T], then
`t ↦ wasserstein1 (f t) (g t)` is lower semicontinuous on [0, T].

Standard Villani-style result for W₁: lower semicontinuity along narrow
convergence (Villani, *Optimal Transport*, Theorem 5.10).  Pure
functional-analytic; no Vlasov-specific instantiation.

**Bucket-1 PR scope**: Villani-standard OT lemma.  Same family as
`MathlibTODO_cauchyW1_hasNarrowLimit`.

**Decomposed from `MathlibTODO_W1ContOn_lscNarrow`** (Phase 1.5, 2026-05-31).
The Vlasov-specific composition lives below as `w1ContOn_lscNarrow_via_pureFA`. -/
theorem MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves
    {d : ℕ} [NeZero d]
    (f g : ℝ → Measure (PhaseSpace d))
    [∀ t, IsProbabilityMeasure (f t)] [∀ t, IsProbabilityMeasure (g t)]
    (T : ℝ) (_hT : 0 ≤ T)
    (_hf_narrow : ∀ (φ : PhaseSpace d → ℝ), Continuous φ →
      Bornology.IsBounded (Set.range φ) →
      ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T))
    (_hg_narrow : ∀ (φ : PhaseSpace d → ℝ), Continuous φ →
      Bornology.IsBounded (Set.range φ) →
      ContinuousOn (fun t => ∫ z, φ z ∂(g t)) (Set.Icc 0 T))
    (_hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖z‖) (f t))
    (_hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖z‖) (g t)) :
    LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  sorry

/-- For a Vlasov solution f satisfying IsVlasovSolution gradW f and any smooth
compactly-supported test function φ with ContDiff ℝ ⊤ φ and HasCompactSupport φ,
the map t ↦ ∫ z, φ z ∂(f t) is continuous on ℝ. Proof: IsVlasovSolution provides
HasDerivAt (fun s => ∫ φ ∂(f s)) (derivative value) t at every t via WeakEvolutionEq;
HasDerivAt.continuousAt then gives ContinuousAt, and assembling over all t gives Continuous.

**Location note**: hoisted above `MathlibTODO_bcNarrowFromSmoothCompactNarrow` and
`w1ContOn_lscNarrow_via_pureFA` (Phase 3 Session 3, 2026-05-31) so the latter
can consume this lemma without forward-reference. -/
lemma W1ContOn_integralContAt
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    Continuous (fun t => ∫ z, φ z ∂(f t)) := by
  -- IsVlasovSolution specialised to this φ gives WeakEvolutionEq.
  have h_weak : WeakEvolutionEq gradW f φ gradXφ gradVφ (fun _ => 0) :=
    hf φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
  -- WeakEvolutionEq unfolds to `∀ t, HasDerivAt (fun s => ∫ φ ∂f s) _ t`.
  -- HasDerivAt at every point implies Continuous via HasDerivAt.continuousAt.
  rw [continuous_iff_continuousAt]
  intro t
  exact (h_weak t).continuousAt

/-- **Mathlib-TODO (pure functional-analytic): narrow continuity for bounded
continuous test functions follows from narrow continuity for smooth
compactly-supported test functions, given uniform first-moment control.**

If `f : ℝ → Measure α` is a probability-measure curve on a Polish space
`α` such that `t ↦ ∫ φ ∂(f t)` is continuous on `[0, T]` for every smooth
compactly-supported `φ`, and the first moments `∫ ‖z‖ ∂(f t)` are
uniformly integrable on `[0, T]`, then the same continuity holds for every
bounded continuous test function `φ`.

**Proof idea (standard Polish probability theory)**:
1. For ε > 0 and any bounded continuous φ with `‖φ‖_∞ < ∞`, pick R large
   enough that `∫_{|z| > R} ‖φ‖_∞ d(f t) ≤ ‖φ‖_∞ · M/R < ε/3` for all
   t ∈ [0, T] (Markov + uniform first-moment bound `M`).
2. Mollify φ with a compact-support smooth cutoff `χ_R` (supp χ_R ⊂
   closed ball of radius R+1, χ_R ≡ 1 on closed ball R, 0 ≤ χ_R ≤ 1) AND
   smooth-mollify the result to get a smooth-CS approximation `φ_R,ε`
   with `‖φ - φ_R,ε‖_∞ ≤ ε/3` on the support of χ_R.
3. The triangle inequality plus step (1)'s tail estimate plus the
   smooth-CS continuity of `t ↦ ∫ φ_R,ε ∂(f t)` gives the conclusion.

**Bucket-1 PR scope**: standard Polish probability theory (Portmanteau /
narrow convergence machinery already in Mathlib for `ProbabilityMeasure`;
this lemma packages the extension from CS to BC against the
`IsProbabilityMeasure`-on-`Measure` formulation used in the project).
Same family as `MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves`
above.

**Decomposed from `w1ContOn_lscNarrow_via_pureFA`** (Phase 3, 2026-05-31):
the previously substantive Vlasov-composition body collapses to a clean
composition of pure-FA placeholders once this BC-extension step is
separately named.  See `w1ContOn_lscNarrow_via_pureFA` below for the
consumer. -/
theorem MathlibTODO_bcNarrowFromSmoothCompactNarrow
    {d : ℕ} [NeZero d]
    (f : ℝ → Measure (PhaseSpace d))
    [∀ t, IsProbabilityMeasure (f t)]
    (T : ℝ) (_hT : 0 ≤ T)
    (_h_mom : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖z‖) (f t))
    (_h_smooth_narrow : ∀ (φ : PhaseSpace d → ℝ),
      ContDiff ℝ ⊤ φ → HasCompactSupport φ →
      ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T)) :
    ∀ (φ : PhaseSpace d → ℝ), Continuous φ →
      Bornology.IsBounded (Set.range φ) →
      ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T) := by
  sorry

/-- **Project-internal composition (Phase 1.5 decomposition target,
substantively closed in Phase 3 Session 3, 2026-05-31)**: W₁ LSC for two
Vlasov solutions, derived from the pure-FA placeholders by composition.

**Composition body** (closed via API-lock pattern with new pure-FA
sub-placeholder `MathlibTODO_bcNarrowFromSmoothCompactNarrow`):

1. Extract `IsProbabilityMeasure` instances from `HasFiniteFirstMoment`.
2. Derive smooth-compactly-supported narrow continuity for f, g via the
   project's `W1ContOn_integralContAt` (which routes through
   `IsVlasovSolution`'s `WeakEvolutionEq`).
3. Extend smooth-CS narrow continuity to bounded continuous via the
   pure-FA `MathlibTODO_bcNarrowFromSmoothCompactNarrow` (the new
   Phase 3 sub-placeholder, captures standard Polish probability theory).
4. Apply the pure-FA `MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves`.

**Net effect on open work**: the BC-extension step is decomposed into a
clearly-named pure-FA sub-placeholder (`MathlibTODO_bcNarrowFromSmoothCompactNarrow`)
rather than absorbed into this composition's body.  Declaration sorry
count unchanged; structural visibility improved (the Vlasov composition
is now a clean orchestration, and the actual deferred mathematical work
is named explicitly).

**In-project consumer**: `MathlibTODO_wassersteinGronwallCoupling_W1ContOn`
(Basic.lean L1830). -/
theorem w1ContOn_lscNarrow_via_pureFA
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  -- (a) IsProbabilityMeasure instances from HasFiniteFirstMoment
  haveI : ∀ t, IsProbabilityMeasure (f t) := fun t => (hf_prob t).1
  haveI : ∀ t, IsProbabilityMeasure (g t) := fun t => (hg_prob t).1
  -- (b) Smooth-CS narrow continuity from IsVlasovSolution via W1ContOn_integralContAt
  have h_smooth_f : ∀ (φ : PhaseSpace d → ℝ),
      ContDiff ℝ ⊤ φ → HasCompactSupport φ →
      ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T) := by
    intro φ hφ_smooth hφ_compact
    have hcont : Continuous (fun t => ∫ z, φ z ∂(f t)) :=
      W1ContOn_integralContAt gradW f hf φ hφ_smooth hφ_compact
        (fun z => gradient (fun x => φ (x, z.2)) z.1)
        (fun z => gradient (fun v => φ (z.1, v)) z.2)
        (fun _ => rfl) (fun _ => rfl)
    exact hcont.continuousOn
  have h_smooth_g : ∀ (φ : PhaseSpace d → ℝ),
      ContDiff ℝ ⊤ φ → HasCompactSupport φ →
      ContinuousOn (fun t => ∫ z, φ z ∂(g t)) (Set.Icc 0 T) := by
    intro φ hφ_smooth hφ_compact
    have hcont : Continuous (fun t => ∫ z, φ z ∂(g t)) :=
      W1ContOn_integralContAt gradW g hg φ hφ_smooth hφ_compact
        (fun z => gradient (fun x => φ (x, z.2)) z.1)
        (fun z => gradient (fun v => φ (z.1, v)) z.2)
        (fun _ => rfl) (fun _ => rfl)
    exact hcont.continuousOn
  -- (c) Extend smooth-CS narrow continuity to BC via the pure-FA sub-placeholder
  have h_mom_f : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖z‖) (f t) :=
    fun t _ => (hf_prob t).2
  have h_mom_g : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖z‖) (g t) :=
    fun t _ => (hg_prob t).2
  have h_narrow_f : ∀ (φ : PhaseSpace d → ℝ), Continuous φ →
      Bornology.IsBounded (Set.range φ) →
      ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T) :=
    MathlibTODO_bcNarrowFromSmoothCompactNarrow f T hT h_mom_f h_smooth_f
  have h_narrow_g : ∀ (φ : PhaseSpace d → ℝ), Continuous φ →
      Bornology.IsBounded (Set.range φ) →
      ContinuousOn (fun t => ∫ z, φ z ∂(g t)) (Set.Icc 0 T) :=
    MathlibTODO_bcNarrowFromSmoothCompactNarrow g T hT h_mom_g h_smooth_g
  -- (d) Apply the pure-FA LSC placeholder
  exact MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves
    f g T hT h_narrow_f h_narrow_g h_mom_f h_mom_g

/-- **Mathlib-TODO (pure functional-analytic): W₁ is upper semicontinuous
along Lagrangian-pushforward flows of Lipschitz vector fields.**

**⚑ RECLASSIFIED 2026-06-03 — STRUCTURE VERIFIED IN-PROJECT, CLOSE UNBUILT (NOT
EXTERNAL).**  A leaf-read of the consumer (`w1ContOn_uscNarrow_via_pureFA`)
verified it passes the full Lagrangian-pushforward surface (`hpush_f/g`,
`haem_f/g`, `hΦ_f/g`, `hf_mom/g`).  That STRUCTURE positions it to close from
PROVEN project tools (the `h_cont_g`/Route-2 pattern) — a *plausible* close path:
build a joint-flow coupling-integral `ContinuousOn` helper via
`wasserstein1_lagrangian_pushforward_bound` + `integral_map` + Gronwall-growth
DCT + a USC-from-tight-upper-bound step.  **But the close is NOT BUILT** — that
path is a fresh characterization with an unbounded tail (could be ~200 or ~1200
lines, like `h_cont_g`).  Status: *structure present, closeability plausible-not-
established*.  The `MathlibTODO_` prefix is retained only to avoid consumer-rename
churn — this is OWED IN-PROJECT WORK, not a Mathlib gap.

If `f, g : ℝ → Measure α` are measure curves such that each is the
pushforward `(Φ_? t)_# (f? 0)` of its initial datum under a flow `Φ_?`
generated by a Lipschitz vector field `b_?`, then `t ↦ W₁(f t, g t)` is
upper semicontinuous.  Standard characteristic-flow coupling argument:
the joint coupling `π_t := (Φ_f t, Φ_g t)_# π_0` (where π_0 is any
coupling of f 0, g 0) satisfies `W₁(f t, g t) ≤ ∫ ‖x - y‖ dπ_t`; the
RHS is continuous in t by DCT + Lipschitz flow bounds, giving USC.

**Bucket-2 PR scope** (per design doc): requires characteristic-flow
coupling infrastructure not yet in Mathlib stable API.  Decomposed from
`MathlibTODO_W1ContOn_uscNarrow` (Phase 1.5, Session 3, 2026-05-31).

The hypothesis surface uses Option B (Lagrangian pushforward) per the
user-authorized Session 3 design choice.  The Vlasov-specific
composition lives below as `w1ContOn_uscNarrow_via_pureFA`. -/
theorem MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows
    {d : ℕ} [NeZero d]
    (b_f b_g : ℝ → PhaseSpace d → PhaseSpace d)
    (L : NNReal)
    (_hL_f : ∀ t, LipschitzWith L (b_f t))
    (_hL_g : ∀ t, LipschitzWith L (b_g t))
    (Φ_f Φ_g : ℝ → PhaseSpace d → PhaseSpace d)
    (_hΦ_f : ∀ z t, HasDerivAt (fun s => Φ_f s z) (b_f t (Φ_f t z)) t)
    (_hΦ_g : ∀ z t, HasDerivAt (fun s => Φ_g s z) (b_g t (Φ_g t z)) t)
    (f g : ℝ → Measure (PhaseSpace d))
    [∀ t, IsProbabilityMeasure (f t)] [∀ t, IsProbabilityMeasure (g t)]
    (_hf_push : ∀ t, f t = Measure.map (Φ_f t) (f 0))
    (_hg_push : ∀ t, g t = Measure.map (Φ_g t) (g 0))
    (_hf_aem : ∀ t, AEMeasurable (Φ_f t) (f 0))
    (_hg_aem : ∀ t, AEMeasurable (Φ_g t) (g 0))
    (_hf_mom : ∀ t, Integrable (fun z : PhaseSpace d => ‖z‖) (f t))
    (_hg_mom : ∀ t, Integrable (fun z : PhaseSpace d => ‖z‖) (g t))
    (T : ℝ) (_hT : 0 ≤ T) :
    UpperSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  sorry

-- `w1ContOn_uscNarrow_via_pureFA` (formerly here) **relocated to
-- `Vlasov/OT/CharacteristicFlow.lean` §10** (Phase 4 Path A Stage 2a,
-- 2026-05-31) so its Stage 2b substantive close can compose against
-- `convolveFunctionMeasure_lipschitz_in_x` and other flow infrastructure.

/-- For Vlasov solutions f, g with HasFiniteFirstMoment at each time t, the
Wasserstein-1 distance wasserstein1 (f t) (g t) is strictly less than ⊤ (i.e. finite)
for every t. Proof: unfold HasFiniteFirstMoment to extract IsProbabilityMeasure and
Integrable (norm) witnesses, then apply wasserstein1_lt_top_of_finite_moment. -/
lemma W1ContOn_lt_top
    {d : ℕ} [NeZero d]
    (f g : ℝ → Measure (PhaseSpace d))
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∀ t : ℝ, wasserstein1 (f t) (g t) < ⊤ := by
  intro t
  obtain ⟨hf_prob_t, hf_int_t⟩ := hf_prob t
  obtain ⟨hg_prob_t, hg_int_t⟩ := hg_prob t
  haveI : IsProbabilityMeasure (f t) := hf_prob_t
  haveI : IsProbabilityMeasure (g t) := hg_prob_t
  exact wasserstein1_lt_top_of_finite_moment (f t) (g t) hf_int_t hg_int_t

/-- Given lower semicontinuity, upper semicontinuity, and pointwise finiteness of
t ↦ wasserstein1 (f t) (g t) on Set.Icc 0 T, conclude that
t ↦ (wasserstein1 (f t) (g t)).toReal is ContinuousOn Set.Icc 0 T.
Proof: continuousOn_iff_lower_upperSemicontinuousOn gives ContinuousOn for the ENNReal map;
then compose with ENNReal.continuousOn_toReal (which is continuous on {a | a ≠ ⊤}) using
ContinuousOn.comp, with the range-subset condition provided by h_lt_top. -/
lemma W1ContOn_toRealContOn
    {d : ℕ} [NeZero d]
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 ≤ T)
    (h_lt_top : ∀ t : ℝ, wasserstein1 (f t) (g t) < ⊤)
    (h_lsc : LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T))
    (h_usc : UpperSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T)) :
    ContinuousOn (fun t => (wasserstein1 (f t) (g t)).toReal) (Set.Icc 0 T) := by
  -- LSC + USC = ContinuousOn (ENNReal-valued)
  have h_cont_enn : ContinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) :=
    continuousOn_iff_lower_upperSemicontinuousOn.mpr ⟨h_lsc, h_usc⟩
  -- ENNReal.toReal is ContinuousOn {a | a ≠ ⊤}; range of wasserstein1 stays there.
  have h_maps_to : Set.MapsTo (fun t => wasserstein1 (f t) (g t))
      (Set.Icc 0 T) {a : ENNReal | a ≠ ⊤} := fun t _ => (h_lt_top t).ne
  exact ENNReal.continuousOn_toReal.comp h_cont_enn h_maps_to

-- `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (formerly here)
-- **relocated to `Vlasov/OT/CharacteristicFlow.lean` §10** (Phase 4 Path A
-- Stage 2a, 2026-05-31) since it now consumes item 5 (also relocated).
-- The helpers it calls (`W1ContOn_lt_top`, `W1ContOn_toRealContOn`,
-- `W1ContOn_integralContAt`, `w1ContOn_lscNarrow_via_pureFA`) stay in
-- Basic.lean — CharFlow imports Basic, so the calls compose.

/-- **Mathlib-TODO (pure functional-analytic): localized right-derivative
liminf Gronwall bound for W₁ between two Lagrangian-pushforward measure
flows under Lipschitz vector fields on `[0, T]`, with a bound on the
difference of the vector fields linear in W₁(f, g).**

For measure flows `f, g : ℝ → Measure α`, each `(Φ_? t)_#`-generated by
flows of Lipschitz vector fields on `[0, T]`, the W₁ distance between
them satisfies a Gronwall-style right-derivative liminf bound on
`[0, T]` provided `‖b_f t x - b_g t x‖` is bounded by `L · W₁(f t, g t)`
(the standard self-coupling estimate from the Vlasov context) on
`t ∈ [0, T]`.

**Stage 2b part 5 (2026-05-31)**: this is the primary `_On`-localized
form, replacing the prior universal-t variant
`MathlibTODO_w1RightDerivBoundAlongLagrangianFlows`.  The localized form
is *strictly more general* than the universal one (it requires less
— hypotheses only on `[0, T]` rather than universally) for the same
conclusion (right-deriv bound on `Set.Ico 0 T`).  Anyone with universal
hypotheses can pass `fun t _ => h_univ t` to satisfy the windowed
form.  Banking the localized form as primary collapses the two-
placeholder situation into one: one fact, one Mathlib-PR target.
(Avoiding the `LocalSmallness`-style fusion-by-duplication caught
prophylactically per user 2026-05-31.)

Standard Wasserstein-coupling-Gronwall result (Villani Ch. 7,
Ambrosio-Gigli-Savaré).  Pure functional-analytic; underlying
mathematics is the characteristic-flow coupling argument that bounds
W₁ via the joint flow.

**Bucket-2 PR scope** (per design doc): requires characteristic-flow
coupling infrastructure.  Decomposed from
`MathlibTODO_wassersteinGronwallCoupling_derivBound` (Phase 1.5,
Session 3, 2026-05-31); now in its localized form per Stage 2b part 5.
Hypothesis surface uses Option B (Lagrangian pushforward).

**In-project consumers**:
* `wassersteinGronwallCoupling_derivBound_via_pureFA` (CharFlow §10 L9503;
  item 6, post-Stage-2b-part-2): the existing consumer, re-pointed at
  the `_On` form via trivial restriction of its universal hypotheses.
* `dobrushin_uniqueness_On`'s body (CharFlow §9.6, Stage 2b part 5
  target): the new consumer that genuinely needs the `_On` form
  because its inputs come from `IsLagrangianVlasovSolutionOn`. -/
theorem MathlibTODO_w1RightDerivBoundAlongLagrangianFlowsOn
    {d : ℕ} [NeZero d]
    (b_f b_g : ℝ → PhaseSpace d → PhaseSpace d)
    (L : NNReal)
    (T : ℝ) (_hT : 0 ≤ T)
    -- Localized Lipschitz: only on `[0, T]`.
    (_hL_f : ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzWith L (b_f t))
    (_hL_g : ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzWith L (b_g t))
    (Φ_f Φ_g : ℝ → PhaseSpace d → PhaseSpace d)
    -- HasDerivAt on `Ioo 0 T` (interior of the window).
    (_hΦ_f : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => Φ_f s z) (b_f t (Φ_f t z)) t)
    (_hΦ_g : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => Φ_g s z) (b_g t (Φ_g t z)) t)
    (f g : ℝ → Measure (PhaseSpace d))
    -- Probability: localized to `[0, T]` (weakened from universal `[∀ t, …]`
    -- instances, Stage 2b part 5, 2026-05-31 — the universal form was an
    -- over-strong leftover, unsatisfiable by the window solution class whose
    -- consumer `wassersteinGronwallCoupling_derivBound_via_pureFA_On` only has
    -- probability on `[0, T]`).
    (_hf_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (f t))
    (_hg_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (g t))
    -- Pushforward, AEMeasurable, moment: localized to `[0, T]`.
    (_hf_push : ∀ t ∈ Set.Icc (0 : ℝ) T, f t = Measure.map (Φ_f t) (f 0))
    (_hg_push : ∀ t ∈ Set.Icc (0 : ℝ) T, g t = Measure.map (Φ_g t) (g 0))
    (_hf_aem : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Φ_f t) (f 0))
    (_hg_aem : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Φ_g t) (g 0))
    (_hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖z‖) (f t))
    (_hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖z‖) (g t))
    -- Vector-field difference bound: localized to `[0, T]`.
    (_h_diff_bound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      ‖b_f t x - b_g t x‖ ≤ (L : ℝ) * (wasserstein1 (f t) (g t)).toReal)
    (C : ℝ) (_hC : 0 < C) (_hCL : (L : ℝ) ≤ C) :
    ∀ s ∈ Set.Ico 0 T,
      ∀ r : ℝ, C * (wasserstein1 (f s) (g s)).toReal < r →
        ∃ᶠ z in nhdsWithin s (Set.Ioi s),
          (z - s)⁻¹ * ((wasserstein1 (f z) (g z)).toReal -
            (wasserstein1 (f s) (g s)).toReal) < r := by
  sorry

-- `wassersteinGronwallCoupling_derivBound_via_pureFA` (formerly here)
-- **relocated to `Vlasov/OT/CharacteristicFlow.lean` §10** (Phase 4 Path A
-- Stage 2a, 2026-05-31) so its Stage 2b substantive close can use
-- `convolveFunctionMeasure_lipschitz_in_x` for the Vlasov-vector-field
-- Lipschitz proof.

/-- For a continuous function h : ℝ → ℝ on [0, T] with h(0) ≤ δ and with
right-derivative liminf bounded by C * h(s) for all s ∈ [0, T),
Gronwall's inequality gives h(t) ≤ δ * Real.exp(C * t) for all t ∈ [0, T].
This wraps Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` with ε = 0
and then simplifies via `gronwallBound_ε0`. -/
lemma wassersteinGronwallCoupling_gronwall_le
    (h : ℝ → ℝ) (δ C T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn h (Set.Icc 0 T))
    (hinit : h 0 ≤ δ)
    (hderiv : ∀ s ∈ Set.Ico 0 T, ∀ r : ℝ, C * h s < r →
        ∃ᶠ z in nhdsWithin s (Set.Ioi s), (z - s)⁻¹ * (h z - h s) < r) :
    ∀ t ∈ Set.Icc 0 T, h t ≤ δ * Real.exp (C * t) := by
  intro t ht
  have key := le_gronwallBound_of_liminf_deriv_right_le
    (f := h) (f' := fun s => C * h s)
    (δ := δ) (K := C) (ε := 0) (a := 0) (b := T)
    hcont hderiv hinit (fun _ _ => by linarith) t ht
  rwa [sub_zero, gronwallBound_ε0] at key

/-- **Scalar mild-form Gronwall** (integrated-Dobrushin collapse, `M→0` core,
2026-06-03): a continuous nonnegative `Q` satisfying the *integral* inequality
`Q t ≤ q0 + K · ∫₀ᵗ Q` on `[0, T]` obeys `Q t ≤ q0 · exp (K t)`.

This is the mild-form companion to `wassersteinGronwallCoupling_gronwall_le`
(which takes the Dini/right-derivative form).  The integrated coupling-Gronwall
bound produces `Q(t) = ∫‖Φ_f t · − Φ_g t ·‖ dπ₀` in the *integral* form (via
per-trajectory FTC + Tonelli on a nonnegative integrand), sidestepping the
reverse-Fatou difference-quotient interchange.  Proof: apply Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le` to the C¹ primitive
`G t = q0 + K · ∫₀ᵗ Q` (with `G' t = K · Q t ≤ K · G t` since `Q ≤ G`), then
`Q ≤ G`. -/
lemma gronwall_mild_le (Q : ℝ → ℝ) (q0 K T : ℝ) (hK : 0 ≤ K) (hq0 : 0 ≤ q0)
    (hQcont : Continuous Q) (hQnn : ∀ t, 0 ≤ Q t)
    (hmild : ∀ t ∈ Set.Icc 0 T, Q t ≤ q0 + K * ∫ s in (0:ℝ)..t, Q s) :
    ∀ t ∈ Set.Icc 0 T, Q t ≤ q0 * Real.exp (K * t) := by
  set G : ℝ → ℝ := fun t => q0 + K * ∫ s in (0:ℝ)..t, Q s with hGdef
  have hG_deriv : ∀ t, HasDerivAt G (K * Q t) t := by
    intro t
    have hftc : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, Q s) (Q t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hQcont.intervalIntegrable 0 t)
        (hQcont.stronglyMeasurableAtFilter _ _) hQcont.continuousAt
    exact (hftc.const_mul K).const_add q0
  have hG_cont : Continuous G :=
    continuous_iff_continuousAt.mpr fun t => (hG_deriv t).continuousAt
  have hG_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ G t := by
    intro t ht
    have hint : 0 ≤ ∫ s in (0:ℝ)..t, Q s :=
      intervalIntegral.integral_nonneg ht.1 (fun s _ => hQnn s)
    show 0 ≤ q0 + K * ∫ s in (0:ℝ)..t, Q s
    positivity
  have hG0 : G 0 = q0 := by simp [hGdef]
  intro t ht
  have hgb := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := G) (a := 0) (b := T) hG_cont.continuousOn
    (fun s _ => (hG_deriv s).hasDerivWithinAt)
    (show ‖G 0‖ ≤ q0 by rw [hG0, Real.norm_eq_abs, abs_of_nonneg hq0])
    (fun s hs => by
      have hsI : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.le⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (hQnn s)),
          Real.norm_eq_abs, abs_of_nonneg (hG_nonneg s hsI), add_zero]
      have hQG : Q s ≤ G s := hmild s hsI
      nlinarith [hQnn s, hG_nonneg s hsI])
    t ht
  rw [sub_zero, gronwallBound_ε0, Real.norm_eq_abs, abs_of_nonneg (hG_nonneg t ht)] at hgb
  exact le_trans (hmild t ht) hgb

-- `wassersteinGronwallCoupling_real_bound` (formerly here) **relocated to
-- `Vlasov/OT/CharacteristicFlow.lean` §10** (Phase 4 Path A Stage 2a,
-- 2026-05-31).  Calls the now-CharFlow-resident W1ContOn and item 6,
-- plus the still-in-Basic `wassersteinGronwallCoupling_gronwall_le`
-- helper.

/-- For reals δ ≥ 0 and C > 0 and t ≥ 0, if r ≤ δ * Real.exp(C * t) then
ENNReal.ofReal r ≤ ENNReal.ofReal (Real.exp (C * t)) * ENNReal.ofReal δ.
Uses ENNReal.ofReal_mul and mul_comm to reorder the product. -/
lemma wassersteinGronwallCoupling_ennreal_mul_comm
    (δ : ℝ) (hδ : 0 ≤ δ) (C t : ℝ) :
    ENNReal.ofReal (δ * Real.exp (C * t)) =
      ENNReal.ofReal (Real.exp (C * t)) * ENNReal.ofReal δ := by
  rw [ENNReal.ofReal_mul hδ, mul_comm]

-- `wassersteinGronwallCoupling_ofReal_le` (formerly here) **relocated to
-- `Vlasov/OT/CharacteristicFlow.lean` §10** (Phase 4 Path A Stage 2a,
-- 2026-05-31).  Calls the relocated `wassersteinGronwallCoupling_real_bound`.

-- `MathlibTODO_wassersteinGronwallCoupling` (formerly here) **relocated to
-- `Vlasov/OT/CharacteristicFlow.lean` §10** (Phase 4 Path A Stage 2a,
-- 2026-05-31).  Thin wrapper around the relocated
-- `wassersteinGronwallCoupling_ofReal_le`.

/-- For any NNReal L, the value C = max((L : ℝ), 1) satisfies 0 < C and
the strengthened bound `((max 1 L : NNReal) : ℝ) ≤ C`.

**Strengthened conclusion (Phase 4 Stage 2b part 2, 2026-05-31, per M1
discipline)**: the natural-home object the math actually produces is
`max 1 L` (the joint Lipschitz constant of the Vlasov phase-space
vector field).  Carrying `((max 1 L : NNReal) : ℝ) ≤ C` as a single
fact rather than splitting it into `(L : ℝ) ≤ C` + `1 ≤ C` avoids the
structure-projection-boundary smell M1 flags.

The previous weaker conclusion `(L : ℝ) ≤ C` is recoverable from the
new one via `(L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) ≤ C` (the `le_max_right`
direction on NNReal-max, then coercion).  Consumers needing only the
weaker form derive it locally. -/
lemma dobrushin_C_choice (L : NNReal) :
    ∃ C : ℝ, 0 < C ∧ ((max 1 L : NNReal) : ℝ) ≤ C := by
  refine ⟨max (L : ℝ) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · -- ((max 1 L : NNReal) : ℝ) = max 1 (L : ℝ) = max (L : ℝ) 1 = C
    rw [NNReal.coe_max, NNReal.coe_one, max_comm]

/-- If gradW is L-Lipschitz, then for any x : PhysSpace d and any two measures ρ, σ
on PhysSpace d, ‖(∇W*ρ)(x) − (∇W*σ)(x)‖ ≤ L · W₁(ρ,σ).toReal.
This is the key estimate: the convolution ∇W * ρ is Lipschitz in ρ with respect to
the Wasserstein-1 distance, via Kantorovich–Rubinstein duality.
TODO(mathlib): depends on `MathlibTODO_convolveLipschitzEstimate` Mathlib gap. -/
lemma convolveDiff_norm_le
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : Measure (PhysSpace d))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (x : PhysSpace d)
    (hW : wasserstein1 ρ σ ≠ ⊤)
    (hρ_int : Integrable (fun y => gradW (x - y)) ρ)
    (hσ_int : Integrable (fun y => gradW (x - y)) σ) :
    ‖convolveFunctionMeasure gradW ρ x - convolveFunctionMeasure gradW σ x‖ ≤
      (L : ℝ) * (wasserstein1 ρ σ).toReal :=
  MathlibTODO_convolveLipschitzEstimate gradW L hL ρ σ x hW hρ_int hσ_int

/-- For C > 0 and 0 ≤ s ≤ t, we have
ENNReal.ofReal (Real.exp (C * s)) ≤ ENNReal.ofReal (Real.exp (C * t)).
This is the monotonicity of the exponential bound in time. -/
lemma wasserstein1_ofReal_exp_monotone
    (C : ℝ) (hC : 0 < C) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ENNReal.ofReal (Real.exp (C * s)) ≤ ENNReal.ofReal (Real.exp (C * t)) := by
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hC.le)

-- `dobrushin_ennreal_bound`, `dobrushin_package_exists`, and `dobrushin`
-- (the .tex thm:dobrushin marquee) **relocated to
-- `Vlasov/OT/CharacteristicFlow.lean` §10** (Phase 4 Path A Stage 2a,
-- 2026-05-31).  The marquee theorem `dobrushin` follows its chain
-- (items 5/6 + W1ContOn + Gronwall lift + ennreal bound) to CharFlow so
-- the substantive close paths can compose against flow infrastructure.
-- The Basic-resident `meanFieldLimit` (below) consumes the Dobrushin
-- estimate as a hypothesis (`hDobrushin : ∀ N, DobrushinStabilityEstimate
-- ...`) rather than calling `dobrushin` directly, so this relocation
-- doesn't ripple to `meanFieldLimit`'s signature.

-- ---------------------------------------------------------------------------
-- §12  Equation (Dobrushin stability estimate)   (tex: eq:dobrushin)
-- ---------------------------------------------------------------------------

/-- (tex: eq:dobrushin)
The exponential Wasserstein-1 stability estimate for Vlasov solutions
(the content of Theorem thm:dobrushin):

  W_1(f_t, g_t) ≤ e^{C·t} · W_1(f_0, g_0),   for all t ≥ 0.

This `Prop`-valued definition packages the statement as a reusable predicate.
-/
def DobrushinStabilityEstimate
    (f g : ℝ → Measure (PhaseSpace d))
    (C : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    wasserstein1 (f t) (g t) ≤
      ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0)

-- ---------------------------------------------------------------------------
-- §13  Corollary (Mean-field limit)   (tex: cor:mfl)
-- ---------------------------------------------------------------------------

/-- (tex: cor:mfl)
Mean-field limit theorem.

Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) and let (X^N, V^N) be the N-particle Newton
trajectories.  Write μ_0^N for the initial empirical measure of (X^N(0),
V^N(0)).  If μ_0^N → f_0 in W_1 as N → ∞ then, under Assumption ass:W and
the Dobrushin estimate, for every T > 0,

  sup_{t ∈ [0,T]} W_1(μ_t^N, f_t) ≤ e^{C·T} · W_1(μ_0^N, f_0)  →  0,  as N → ∞.

f_t is the unique Vlasov solution with initial datum f_0 (Theorem thm:vlasov-wp).
The .tex names the initial data `(X_0^N, V_0^N)`; here we identify them with
`X N 0` and `V N 0` rather than introducing redundant `X₀, V₀` parameters
that would need a separate hypothesis to link them to the trajectory.
-/
theorem meanFieldLimit
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    -- the Vlasov solution with initial datum f₀
    (f₀ : Measure (PhaseSpace d)) (hf₀ : HasFiniteFirstMoment f₀)
    (f : ℝ → Measure (PhaseSpace d))
    (hf_sol : IsLagrangianVlasovSolution gradW f)
    (hf_init : f 0 = f₀)
    -- N-particle Newton trajectories; initial data is `(X N 0, V N 0)`.
    (X V : (N : ℕ) → ℝ → Fin N → PhysSpace d)
    (hSol : ∀ (N : ℕ), IsNewtonSolution N gradW (X N) (V N))
    -- initial empirical measures converge to f₀ in W_1
    (hInit : Filter.Tendsto
      (fun N : ℕ => wasserstein1 (empiricalMeasure N (X N 0) (V N 0)) f₀)
      Filter.atTop (nhds 0))
    -- the Dobrushin constant C from Theorem thm:dobrushin
    (C : ℝ) (hC : 0 < C)
    (hDobrushin : ∀ (N : ℕ), DobrushinStabilityEstimate
      (empiricalMeasureCurve N (X N) (V N)) f C)
    (T : ℝ) (hT : 0 < T) :
    Filter.Tendsto
      (fun N : ℕ => ⨆ t ∈ Set.Icc 0 T,
        wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t))
      Filter.atTop (nhds 0) := by
  -- Skeleton from sorry-prover; finished manually.
  -- (1) hsup_bound: for each N, the sup over t ∈ [0,T] is bounded by
  --     exp(C·T) · W_1(μ_0^N, f_0).  Uses hDobrushin pointwise then
  --     monotonicity of exp to lift `t` to the upper endpoint T.
  have hsup_bound : ∀ N : ℕ,
      ⨆ t ∈ Set.Icc 0 T, wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t) ≤
        ENNReal.ofReal (Real.exp (C * T)) *
          wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
    intro N
    apply iSup_le; intro t
    apply iSup_le; intro ht
    calc wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t)
        ≤ ENNReal.ofReal (Real.exp (C * t)) *
            wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) :=
          hDobrushin N t ht.1
      _ ≤ ENNReal.ofReal (Real.exp (C * T)) *
            wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
          apply mul_le_mul_of_nonneg_right _ (zero_le _)
          apply ENNReal.ofReal_le_ofReal
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (le_of_lt hC))
  -- (2) hUpper: the upper-bound sequence tends to 0.  Apply
  --     ENNReal.Tendsto.const_mul to hInit; the witness for `a ≠ ∞` is
  --     `ENNReal.ofReal_ne_top`.  Rewrite empiricalMeasureCurve at t=0
  --     to expose hInit's empiricalMeasure form, and use hf_init to
  --     align f 0 with f₀.
  have hUpper : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Real.exp (C * T)) *
        wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0))
      Filter.atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (C * T)))
      hInit (Or.inr ENNReal.ofReal_ne_top)
    simpa [empiricalMeasureCurve, hf_init, mul_zero] using h
  -- (3) Squeeze: 0 ≤ sup ≤ upper-bound → 0.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun _ => zero_le _) hsup_bound

end Vlasov
