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

/-- (tex: thm:vlasov-wp)
Existence and uniqueness for the Vlasov equation.

Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) be a probability measure with finite first moment.
Under Assumption ass:W, there exists a unique narrowly continuous curve
t ↦ f_t ∈ 𝒫_1(ℝ^d × ℝ^d) satisfying eq:vlasov in the distributional sense
with f_{t=0} = f_0.
-/
theorem vlasovWellPosedness
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
  * `vlasovWellPosedness` (currently sorry'd) will produce
    `IsLagrangianVlasovSolution` when its Banach fixed-point existence
    half is proved — the construction explicitly builds the flow.

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

/-- Wasserstein-1 distance between two measures on a (pseudo)metric space,
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
noncomputable def wasserstein1 {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ENNReal :=
  ⨆ (f : α → ℝ) (_ : LipschitzWith 1 f),
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)

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
  -- By definition, ENNReal.ofReal (∫φdρ − ∫φdσ) ≤ wasserstein1 ρ σ.
  have h_sup : ENNReal.ofReal (∫ y, φ y ∂ρ - ∫ y, φ y ∂σ) ≤ wasserstein1 ρ σ := by
    refine le_iSup₂ (α := ENNReal) (f := fun f _ =>
      ENNReal.ofReal (∫ x, f x ∂ρ - ∫ x, f x ∂σ)) φ hφ
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

/-- For any 1-Lipschitz function φ : PhaseSpace d → ℝ and a Vlasov solution f whose
measure curve has HasFiniteFirstMoment at each time t, the map t ↦ ∫ z, φ z ∂(f t)
is continuous on Set.Icc 0 T.

Technical heart of the lscNarrow decomposition: approximate φ by compactly-supported
smooth functions via ContDiffBump mollifiers, apply W1ContOn_integralContAt to each
approximant, then pass to the limit via MeasureTheory.tendsto_integral_of_dominated_convergence
with the integrable dominator ‖z‖ supplied by HasFiniteFirstMoment. -/
lemma w1_lscNarrow_integralContOn_lip
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (T : ℝ) (hT : 0 ≤ T)
    (φ : PhaseSpace d → ℝ)
    (hφ_lip : LipschitzWith 1 φ) :
    ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T) := by
  sorry

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
    (f : ℝ → Measure (PhaseSpace d))
    (hf_lag : IsLagrangianVlasovSolution gradW f)
    (hf_prob_0 : HasFiniteFirstMoment (f 0))
    (T : ℝ) (hT : 0 ≤ T)
    (φ : PhaseSpace d → ℝ)
    (hφ_lip : LipschitzWith 1 φ) :
    ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T) := by
  sorry

/-- For any 1-Lipschitz function φ, the map t ↦ ∫ φ d(f t) - ∫ φ d(g t) is
ContinuousOn Set.Icc 0 T, as the difference of two applications of
w1_lscNarrow_integralContOn_lip (one for f, one for g). -/
lemma w1_lscNarrow_diff_contOn
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T)
    (φ : PhaseSpace d → ℝ)
    (hφ_lip : LipschitzWith 1 φ) :
    ContinuousOn (fun t => ∫ z, φ z ∂(f t) - ∫ z, φ z ∂(g t)) (Set.Icc 0 T) := by
  exact (w1_lscNarrow_integralContOn_lip gradW f hf hf_prob T hT φ hφ_lip).sub
        (w1_lscNarrow_integralContOn_lip gradW g hg hg_prob T hT φ hφ_lip)

/-- For any 1-Lipschitz function φ, the map t ↦ ENNReal.ofReal (∫ φ d(f t) - ∫ φ d(g t))
is LowerSemicontinuousOn Set.Icc 0 T: it is continuous (since ENNReal.ofReal is continuous
and the inner map is continuous by w1_lscNarrow_diff_contOn), and continuous implies LSC
via ContinuousOn.lowerSemicontinuousOn. -/
lemma w1_lscNarrow_summand_lscOn
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T)
    (φ : PhaseSpace d → ℝ)
    (hφ_lip : LipschitzWith 1 φ) :
    LowerSemicontinuousOn
      (fun t => ENNReal.ofReal (∫ z, φ z ∂(f t) - ∫ z, φ z ∂(g t)))
      (Set.Icc 0 T) :=
  (ENNReal.continuous_ofReal.comp_continuousOn'
    (w1_lscNarrow_diff_contOn gradW f g hf hg hf_prob hg_prob T hT φ hφ_lip)).lowerSemicontinuousOn

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
  unfold wasserstein1
  exact lowerSemicontinuousOn_biSup (fun φ hφ => h_summands φ hφ)

-- Mathlib gap A: W₁ is lower semicontinuous under narrow convergence of measure curves.
-- Requires KR duality for non-compactly-supported Lipschitz test functions;
-- not available in Mathlib's stable OT/measure-valued-ODE API.
theorem MathlibTODO_W1ContOn_lscNarrow
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) :=
  -- Compose: per-φ LSC of the summand (H3) → LSC of the double sup (H4).
  w1_lscNarrow_of_summands f g T
    (fun φ hφ_lip =>
      w1_lscNarrow_summand_lscOn gradW f g hf hg hf_prob hg_prob T hT φ hφ_lip)

-- Mathlib gap B: W₁ is upper semicontinuous along Vlasov solution curves.
-- Requires characteristic flow coupling argument and W₁ triangle inequality under pushforward;
-- neither is in Mathlib's stable API for measure-valued ODEs.
theorem MathlibTODO_W1ContOn_uscNarrow
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    UpperSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  sorry

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

/-- For a Vlasov solution f satisfying IsVlasovSolution gradW f and any smooth
compactly-supported test function φ with ContDiff ℝ ⊤ φ and HasCompactSupport φ,
the map t ↦ ∫ z, φ z ∂(f t) is continuous on ℝ. Proof: IsVlasovSolution provides
HasDerivAt (fun s => ∫ φ ∂(f s)) (derivative value) t at every t via WeakEvolutionEq;
HasDerivAt.continuousAt then gives ContinuousAt, and assembling over all t gives Continuous. -/
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

-- Sub-axiom 1 of MathlibTODO_wassersteinGronwallCoupling (decomposed above):
-- Narrow continuity of Wasserstein-1 distance along Vlasov solution curves.
theorem MathlibTODO_wassersteinGronwallCoupling_W1ContOn
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun t => (wasserstein1 (f t) (g t)).toReal) (Set.Icc 0 T) := by
  -- Step 1: pointwise finiteness from HasFiniteFirstMoment
  have h_finite : ∀ t, wasserstein1 (f t) (g t) < ⊤ :=
    W1ContOn_lt_top f g hf_prob hg_prob
  -- Step 2: narrow continuity of integral-against-test-function for f and g
  -- (W1ContOn_integralContAt; feeds into the LSC argument below)
  have h_int_cont_f : ∀ (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ ⊤ φ)
      (hc : HasCompactSupport φ) (gXφ gVφ : PhaseSpace d → PhysSpace d)
      (hgXφ : ∀ z, gXφ z = gradient (fun x => φ (x, z.2)) z.1)
      (hgVφ : ∀ z, gVφ z = gradient (fun v => φ (z.1, v)) z.2),
      Continuous (fun t => ∫ z, φ z ∂(f t)) :=
    fun φ hφ hc gXφ gVφ hgXφ hgVφ =>
      W1ContOn_integralContAt gradW f hf φ hφ hc gXφ gVφ hgXφ hgVφ
  -- Step 3: W₁ is LSC along these Vlasov flows (Mathlib gap MathlibTODO_W1ContOn_lscNarrow)
  have h_lsc : LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) :=
    MathlibTODO_W1ContOn_lscNarrow gradW f g hf hg hf_prob hg_prob T hT
  -- Step 4: W₁ is USC along these Vlasov flows (Mathlib gap MathlibTODO_W1ContOn_uscNarrow)
  have h_usc : UpperSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) :=
    MathlibTODO_W1ContOn_uscNarrow gradW L hL f g hf hg hf_prob hg_prob T hT
  -- Step 5: assemble via W1ContOn_toRealContOn (close this sorry to finish)
  have h_goal := W1ContOn_toRealContOn f g T hT h_finite h_lsc h_usc
  exact h_goal

-- Sub-axiom 2 of MathlibTODO_wassersteinGronwallCoupling:
-- Right-derivative Gronwall bound for the Wasserstein-1 coupling.
-- Requires: characteristic flow coupling argument (pairing ODE solutions via common
-- initial label) + W₁ triangle inequality under measure pushforward.
-- Neither the measure-valued Picard theorem nor the W₁ pushforward contraction
-- is in Mathlib's stable API.
theorem MathlibTODO_wassersteinGronwallCoupling_derivBound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : (L : ℝ) ≤ C)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ s ∈ Set.Ico 0 T,
      ∀ r : ℝ, C * (wasserstein1 (f s) (g s)).toReal < r →
        ∃ᶠ z in nhdsWithin s (Set.Ioi s),
          (z - s)⁻¹ * ((wasserstein1 (f z) (g z)).toReal -
            (wasserstein1 (f s) (g s)).toReal) < r := by
  sorry

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
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : (L : ℝ) ≤ C)
    (t : ℝ) (ht : 0 ≤ t) :
    (wasserstein1 (f t) (g t)).toReal ≤
      (wasserstein1 (f 0) (g 0)).toReal * Real.exp (C * t) := by
  have key := wassersteinGronwallCoupling_gronwall_le
    (fun s => (wasserstein1 (f s) (g s)).toReal)
    (wasserstein1 (f 0) (g 0)).toReal C t ht
    (MathlibTODO_wassersteinGronwallCoupling_W1ContOn
      gradW L hL f g hf hg hf_prob hg_prob t ht)
    (le_refl _)
    (MathlibTODO_wassersteinGronwallCoupling_derivBound
      gradW L hL f g hf hg hf_prob hg_prob C hC hCL t ht)
  exact key t (Set.right_mem_Icc.mpr ht)

/-- For reals δ ≥ 0 and C > 0 and t ≥ 0, if r ≤ δ * Real.exp(C * t) then
ENNReal.ofReal r ≤ ENNReal.ofReal (Real.exp (C * t)) * ENNReal.ofReal δ.
Uses ENNReal.ofReal_mul and mul_comm to reorder the product. -/
lemma wassersteinGronwallCoupling_ennreal_mul_comm
    (δ : ℝ) (hδ : 0 ≤ δ) (C t : ℝ) :
    ENNReal.ofReal (δ * Real.exp (C * t)) =
      ENNReal.ofReal (Real.exp (C * t)) * ENNReal.ofReal δ := by
  rw [ENNReal.ofReal_mul hδ, mul_comm]

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
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : (L : ℝ) ≤ C)
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
-- The proof scaffold uses the sub-axioms and the four helper lemmas above.
theorem MathlibTODO_wassersteinGronwallCoupling
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : (L : ℝ) ≤ C)
    (t : ℝ) (ht : 0 ≤ t)
    (hW_t : wasserstein1 (f t) (g t) ≠ ⊤) :
    wasserstein1 (f t) (g t) ≤
      ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) :=
  wassersteinGronwallCoupling_ofReal_le gradW L hL f g hf hg hf_prob hg_prob C hC hCL t ht hW_t

/-- For any NNReal L, the value C = max((L : ℝ), 1) satisfies 0 < C and (L : ℝ) ≤ C.
This provides the Dobrushin constant independently of whether L = 0. -/
lemma dobrushin_C_choice (L : NNReal) :
    ∃ C : ℝ, 0 < C ∧ (L : ℝ) ≤ C := by
  refine ⟨max (L : ℝ) 1, ?_, le_max_left _ _⟩
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

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

/-- Given MathlibTODO_wassersteinGronwallCoupling and C = max(L,1) > 0 with (L : ℝ) ≤ C,
for any two Vlasov solutions f and g, for all t ≥ 0 we have
wasserstein1 (f t) (g t) ≤ ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0).
Depends on dobrushin_C_choice (for the constant C) and convolveDiff_norm_le (for the
Lipschitz estimate used in the Gronwall argument via MathlibTODO_wassersteinGronwallCoupling).
TODO(mathlib): depends on `MathlibTODO_wassersteinGronwallCoupling` Mathlib gap. -/
lemma dobrushin_ennreal_bound
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t))
    (C : ℝ) (hC : 0 < C) (hCL : (L : ℝ) ≤ C) :
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
Depends on dobrushin_C_choice and dobrushin_ennreal_bound. -/
lemma dobrushin_package_exists
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
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
-/
theorem dobrushin
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    -- L is the Lipschitz constant of ∇W from Assumption ass:W
    (L : NNReal) (hL : LipschitzWith L gradW)
    -- f and g are two Vlasov solutions
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsVlasovSolution gradW f)
    (hg : IsVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
  -- close via dobrushin_package_exists, which composes dobrushin_C_choice
  -- and dobrushin_ennreal_bound (which itself invokes MathlibTODO_wassersteinGronwallCoupling)
  exact dobrushin_package_exists W gradW hgradW L hL f g hf hg hf_prob hg_prob

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
    (hf_sol : IsVlasovSolution gradW f)
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
