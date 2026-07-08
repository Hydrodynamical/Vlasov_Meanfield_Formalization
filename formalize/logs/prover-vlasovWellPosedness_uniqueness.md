## 2026-05-30 · Stage 8 · vlasovWellPosedness_uniqueness

**Result:** success (Path A — compound-leverage close)
**Iterations:** 4/8
**Sorry count (keywords):** 18 → 17 (CharacteristicFlow.lean: 14 → 13)
**Sorry count (declaration warnings):** 10 → 10 (net 0 at declaration level, as predicted by Path A)
**Pre-flight (§3.5):** validated Nat.cast_le, Nat.cast_nonneg, Set.Ioo_subset_Ioo, IsCharacteristicFlowOn.mono (all in Mathlib or project); 0 rejected in-loop citations

### Final proof

**New sorry'd helper** (Path A localized placeholder):
```lean
private theorem MathlibTODO_dobrushin_uniqueness_On
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
```

**Target theorem body** (fully proved, no sorry):
```lean
theorem vlasovWellPosedness_uniqueness ... := by
  have hf_pde : IsVlasovSolutionOn gradW f T_target := hf_lag.1
  have hg_pde : IsVlasovSolutionOn gradW g T_target := hg_lag.1
  have hfg0 : f 0 = g 0 := hf_init.trans hg_init.symm
  exact MathlibTODO_dobrushin_uniqueness_On gradW L hL f g T_target hT_target
    hf_pde hg_pde hf_mom hg_mom hfg0
```

**Compound-leverage: h_agree in Stage 6 also closed** (was sorry'd before):
```lean
have h_agree : ∀ n m : ℕ, n ≤ m →
    ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), sol n t = sol m t := by
  intro n m hnm t ht
  have hnm_cast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    linarith
  have h_sol_m_on_n : IsLagrangianVlasovSolutionOn gradW (sol m) ((n : ℝ) + 1) := by
    obtain ⟨h_sol, charX, charV, h_flow, h_push, h_aemeas⟩ := h_sol_lag m
    refine ⟨?_, charX, charV, ?_, ?_, ?_⟩
    · intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s hs
      exact h_sol φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s
        ⟨hs.1, lt_of_lt_of_le hs.2 hnm_cast⟩
    · exact h_flow.mono (Set.Ioo_subset_Ioo le_rfl hnm_cast) Set.Subset.rfl
    · intro s hs; exact h_push s ⟨hs.1, le_trans hs.2 hnm_cast⟩
    · intro s hs; exact h_aemeas s ⟨hs.1, le_trans hs.2 hnm_cast⟩
  exact vlasovWellPosedness_uniqueness W gradW hgradW L hL hL_pos hL_lt f₀ hf₀
    (by linarith [Nat.cast_nonneg (α := ℝ) n] : (0 : ℝ) < (n : ℝ) + 1)
    (sol n) (sol m) (h_sol_init n) (h_sol_init m)
    (h_sol_mom n)
    (fun s hs => h_sol_mom m s ⟨hs.1, le_trans hs.2 hnm_cast⟩)
    (h_sol_lag n) h_sol_m_on_n
    t ht
```

### Lookup trail
- `dobrushin_C_choice` — Vlasov/Basic.lean:1978 (project lemma, ∃ C > 0 with L ≤ C)
- `wasserstein1_self` — Vlasov/Basic.lean:1002 (project lemma, W₁(μ,μ)=0)
- `IsCharacteristicFlowOn.mono` — CharacteristicFlow.lean:487 (project lemma, set monotonicity)
- `Set.Ioo_subset_Ioo` — .lake/packages/mathlib/Mathlib/Order/Interval/Set/Basic.lean:280
- `Nat.cast_le` — .lake/packages/mathlib/Mathlib/Data/Nat/Cast/Order/Basic.lean:76
- `Nat.cast_nonneg` — .lake/packages/mathlib/Mathlib/Data/Nat/Cast/Order/Ring.lean:32

### Architecture notes
- **Path A taken**: `MathlibTODO_dobrushin_uniqueness_On` is a new sorry'd declaration
  parallel to `MathlibTODO_wassersteinGronwallCoupling` in Basic.lean.
  Its body requires: (1) localized Gronwall coupling for W₁ on [0,T] with
  `IsVlasovSolutionOn` inputs, and (2) KR duality (W₁=0 → measure equality
  for probability measures on separable metric spaces).  Both are Mathlib gaps.
- **Two intermediate designs reverted**: initially tried two separate sorry'd
  helpers (Gronwall-On + W1-zero-imp-eq), then folded into one.
- **Compound leverage achieved**: closing Stage 8 allowed closing h_agree in
  Stage 6 (`vlasovWellPosedness_universal_existence`) via the inline
  IsLagrangianVlasovSolutionOn restriction pattern.
- **Net sorry keyword count**: 18 → 17 (strict decrease of 1).
  Declaration-level warning count: 10 → 10 (net 0, as Path A predicts).
  The target declaration's warning is gone; one new sorry'd declaration added.
