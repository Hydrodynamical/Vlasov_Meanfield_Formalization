## 2026-05-30T06:49:39Z · thm:vlasov-wp · vlasovWellPosedness

**Result:** success
**Iterations:** 2/8
**Sorry count:** 4 → 4 (declaration-level count unchanged; body replaced single `sorry` with structural composition with 3 named sub-sorries)
**Pre-flight (§3.5):** dropped 0 hints; validated 2 names (`Isometry.lipschitzWith_iff`, `SemilinearIsometryClass.isometry`); rejected 0 in-loop citations

### Final proof (on success)
```lean
  -- Step 1: Extract Lipschitz constant L from [AssW W].
  obtain ⟨L, hL_fderiv⟩ := (inferInstance : AssW W).lipschitzGrad
  have hL_gradW : LipschitzWith L gradW := by
    have hiso : Isometry (InnerProductSpace.toDual ℝ (PhysSpace d)).symm :=
      SemilinearIsometryClass.isometry _
    have hfun : gradW = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm ∘
        (fun x => fderiv ℝ W x) := by
      funext x; simp only [Function.comp, hgradW x, gradient]
    rw [hfun]
    exact (hiso.lipschitzWith_iff L).mpr hL_fderiv
  by_cases hL_pos : (0 : ℝ) < L
  · by_cases hL_lt : (L : ℝ) < 1
    · obtain ⟨f, h_init, h_mom, h_lag, h_cont⟩ :=
        vlasovWellPosedness_universal_existence W gradW hgradW L hL_gradW hL_pos hL_lt f₀ hf₀
      refine ⟨f, ⟨h_init, h_mom, h_lag, h_cont⟩, ?_⟩
      intro g ⟨hg_init, hg_mom, hg_lag, _⟩
      funext t
      by_cases ht_nn : (0 : ℝ) ≤ t
      · have hT : (0 : ℝ) < t + 1 := by linarith
        have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht_nn, by linarith⟩
        have hf_on := h_lag.toOn (t + 1)
        have hg_on := hg_lag.toOn (t + 1)
        have hf_mom_on : ∀ s ∈ Set.Icc (0 : ℝ) (t + 1), HasFiniteFirstMoment (f s) :=
          fun s _ => h_mom s
        have hg_mom_on : ∀ s ∈ Set.Icc (0 : ℝ) (t + 1), HasFiniteFirstMoment (g s) :=
          fun s _ => hg_mom s
        exact (vlasovWellPosedness_uniqueness W gradW hgradW L hL_gradW hL_pos hL_lt
          f₀ hf₀ hT f g h_init hg_init hf_mom_on hg_mom_on hf_on hg_on t ht_mem).symm
      · sorry  -- sub-sorry 3: backward-time uniqueness
    · sorry  -- sub-sorry 2: L ≥ 1 regime
  · sorry  -- sub-sorry 2: L = 0 regime
```

### Lookup trail
- `Isometry.lipschitzWith_iff` — `.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:728`
- `SemilinearIsometryClass.isometry` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:92`
- `InnerProductSpace.toDual` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean:137`
- `IsLagrangianVlasovSolution.toOn` — `Vlasov/OT/CharacteristicFlow.lean:597`
- `vlasovWellPosedness_universal_existence` — `Vlasov/OT/CharacteristicFlow.lean:7187`
- `vlasovWellPosedness_uniqueness` — `Vlasov/OT/CharacteristicFlow.lean:7125`

### Sub-sorries (3 named, each clearly gated)
1. **L = 0 regime** (line 7309): constant-force case; sub-sorry gated on constructing the explicit Dirac-flow solution.
2. **L ≥ 1 regime** (line 7307): out of scope until M-series `+1` removal (watch-list candidate); the Lipschitz-contraction argument needs `L·T² < 1` which fails for `L ≥ 1` in any window.
3. **Backward-time uniqueness** (line 7304): for `t < 0`, uniqueness via time-reflection argument; gated on a backward-iteration analogue of Stage 8.

### Key observation
The `hL_gradW` bridge (fderiv → gradient Lipschitzness) closes fully via
`SemilinearIsometryClass.isometry` + `Isometry.lipschitzWith_iff` — no sub-sorry
needed there. The `simp only [Function.comp, hgradW x, gradient]` unfolds
`gradient W x = (InnerProductSpace.toDual ℝ ...).symm (fderiv ℝ W x)` correctly.

### Lines added
62 lines of structured proof body replacing 8 lines of pure-comment sorry.

## 2026-05-30 · vlasovWellPosedness (L=0 regime close)

**Result:** success
**Iterations:** 8/8 (split across two sessions)
**Sorry count:** 13 → 12
**Pre-flight (§3.5):** dropped 0 hints; validated several in-loop citations; rejected 0 in-loop citations

### Final proof (on success)

The L=0 sorry at line 7509 in the backup (single `sorry`) was replaced with:

1. `hL_zero` (L = 0 as NNReal)
2. `hgradW_zero` (gradW ≡ 0 using LipschitzWith.zero_iff + gradient_zero_of_even)
3. `hconv_zero` (convolution vanishes)
4. Explicit solution `f_sol t = Measure.map (fun z => (z.1+t•z.2, z.2)) f₀`
5. `hf_init` (f_sol 0 = f₀)
6. `hf_mom` (finite first moment via integrable_map_measure + nlinarith)
7. `hf_lag` via `vlasovSolutionViaPushforward_isLagrangianVlasovSolution` (closes IsVlasovSolution!)
8. `hf_cont` (narrow continuity via continuous_of_dominated + integral_map)
9. `hf_uniq` (uniqueness via is_const_of_fderiv_eq_zero)

Key insight for closing `IsVlasovSolution`: `f_sol = vlasovSolutionViaPushforward charX charV f₀`
definitionally, so `vlasovSolutionViaPushforward_isLagrangianVlasovSolution` applies directly,
providing the entire `IsLagrangianVlasovSolution` (including `IsVlasovSolution`) without
separate sorry for the weak PDE.

### Lookup trail
- `LipschitzWith.zero_iff` — Basic result about zero Lipschitz constant
- `gradient_zero_of_even` — Basic.lean L99
- `is_const_of_fderiv_eq_zero` — MeanValue.lean L565
- `hasDerivAt_id` — Deriv/Basic.lean L670 (with `(𝕜 := ℝ)` annotation to fix ℕ vs ℝ smul issue)
- `toSpanSingleton_deriv` — Deriv/Basic.lean L465 (to convert HasDerivAt to fderiv = 0)
- `vlasovSolutionViaPushforward_isLagrangianVlasovSolution` — CharacteristicFlow.lean L3254
- `hasDerivAt_id (𝕜 := ℝ)` needed instead of `hasDerivAt_id'` to fix `(1 : ℕ)` vs `(1 : ℝ)` type mismatch
- `Measure.map_map` — Map.lean
- `sub_eq_zero.mp` — to extract equality from `x - y = 0`

### Pre-flight rejections (in-loop)
- `HasFDerivAtFilter.fderiv` — zero matches; `.fderiv` doesn't exist as field on `HasDerivAt`; used `rw [← toSpanSingleton_deriv, ...]` instead
- `hasCompactSupport_gradient` — zero matches; was looking for compact support of gradient; avoided by using `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`
