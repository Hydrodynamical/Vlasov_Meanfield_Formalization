## 2026-05-27 · vlasov_traj_chain_rule

**Result:** success
**Iterations:** 6/8
**Sorry count:** 2 → 1 (in CharacteristicFlow.lean)
**Pre-flight (§3.5):** dropped 0 hints; validated 0 sketch lemmas (no plan); rejected 0 in-loop citations

### Final proof (on success)
```lean
  have hpair : HasDerivAt (fun s => (charX s z, charV s z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) t :=
    (hX_deriv t z).prodMk (hV_deriv t z)
  have hFDeriv : HasFDerivAt φ (fderiv ℝ φ (charX t z, charV t z)) (charX t z, charV t z) :=
    (hφ_smooth.differentiable (by simp) _).hasFDerivAt
  have hchain : HasDerivAt (fun s => φ (charX s z, charV s z))
      ((fderiv ℝ φ (charX t z, charV t z))
        (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z)))) t :=
    hFDeriv.comp_hasDerivAt t hpair
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
      exact ((hdiffφ.hasFDerivAt).comp z₀.1 (hasFDerivAt_prodMk_left z₀.1 z₀.2)).fderiv
    have hfderiv_V : fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      exact ((hdiffφ.hasFDerivAt).comp z₀.2 (hasFDerivAt_prodMk_right z₀.1 z₀.2)).fderiv
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
```

### Lookup trail
- `HasDerivAt.prodMk` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean:51`
- `HasFDerivAt.comp_hasDerivAt` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:389`
- `hasFDerivAt_prodMk_left` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:74`
- `hasFDerivAt_prodMk_right` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:79`
- `ContinuousLinearMap.inl_apply` / `inr_apply` — `.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:69,73`
- `inner_gradient_left` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:270`
- `real_inner_comm` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:59`
- `inner_neg_left` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:231`
- `ContDiff.differentiable` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1129`
- `DifferentiableAt.prodMk` — `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:90`

### What didn't work
- iteration 1 (skeleton): `ContDiff.differentiable` wanted `⊤ ≠ 0` not `1 ≤ ⊤` — fixed with `by simp`
- iteration 2 (full hval attempt): wrong `rw` order; `← hgradXφ z₀` before `← inner_gradient_left` failed since gradient not in goal yet
- iteration 3: `differentiableAt_const.prodMk` syntax — needed `(differentiableAt_const z₀.2)` with explicit argument; `differentiableAt_const` without argument is a function
- iteration 4: `rw [← heq, ← hgradXφ z₀]; rfl` — `← heq` failed because `(F.comp inl) a` ≠ `F (inl a)` syntactically (definitional equality not enough for `rw`)
- iteration 5: fixed by `have hstep : F (inl a) = fderiv ℝ (fun x => φ(x, z₀.2)) z₀.1 a := by rw [hfderiv_X]; rfl` — the `rfl` closes because `comp_apply` is `rfl`; then correct `rw` order `← inner_gradient_left` then `← hgradXφ` works
- iteration 5 (inner_neg_left): `simp only [inner_neg_left]` made no progress because `b` was a `set`-introduced variable, not yet unfolded; fixed with `show b = -(convolve...) from rfl`
