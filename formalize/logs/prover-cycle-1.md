## 2026-05-23T00:00:00Z · wasserstein1 (thm:dobrushin, eq:dobrushin, cor:mfl auxiliary) · `wasserstein1`

**Result:** success
**Iterations:** 5/8
**Sorry count:** 6 → 5

---

### Decision to skip first recommendation

The top recommendation was `weakEvolutionEmpiricalMeasure` (prop:weak, line 163). After careful analysis and 4 failed iteration attempts, the theorem was found to be **mathematically false as stated** for the following reason:

The conclusion is `HasDerivAt (fun s => ∫ φ dμ_s^N) (∫ ... ∂μ_t + R_N t) t ∧ |R_N t| ≤ bound`. Here `R_N : ℝ → ℝ` is a **free parameter** (universally quantified). Since `HasDerivAt` has a unique derivative, the first conjunct uniquely forces `R_N t = actual_derivative − ∫ ... ∂μ_t`. For a different choice of `R_N`, the first conjunct would be false. Therefore, both conjuncts cannot simultaneously hold for **all** `R_N`. The correct statement should existentially quantify `R_N`.

Concrete attempts in iterations 1–4:
- Iteration 1: Tried `constructor` + `simp_rw [hint]` to reduce to finite sum, but `ring` failed on the integral simplification and `conv_lhs` failed on `HasDerivAt`.
- Iteration 2: Reverted to `sorry` after recognizing quantification issue.
- Iteration 3: Tried `refine ⟨?_, ?_⟩` with `integral_smul_measure` + `integral_finset_sum_measure` approach; encountered `No goals to be solved` error and missing `integrable_of_isCompact_support` field.
- Iteration 4: Confirmed the theorem is false for general `R_N` (verified unique-derivative argument); reverted all changes.

Since the first recommendation is blocked (theorem false for arbitrary R_N), proceeded to the second recommendation: discharge the `wasserstein1` sorry.

---

### Target sorry discharged: `wasserstein1`

The `wasserstein1` definition had body `sorry`. Replaced with the **Kantorovich–Rubinstein dual formula** for the Wasserstein-1 distance:

```
W₁(μ, ν) = sup { ∫ f dμ − ∫ f dν | f : 1-Lipschitz }
```

### Final proof (definition body)
```lean
noncomputable def wasserstein1 {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ℝ :=
  -- Kantorovich–Rubinstein dual formula for the Wasserstein-1 distance:
  --   W₁(μ, ν) = sup { ∫ f dμ − ∫ f dν | f : 1-Lipschitz }
  ⨆ (f : α → ℝ) (_ : LipschitzWith 1 f), ∫ x, f x ∂μ - ∫ x, f x ∂ν
```

### Lookup trail
- `LipschitzWith` — `/Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/.lake/packages/mathlib/Mathlib/Topology/Algebra/Order/LiminfLimsup.lean` (used throughout Mathlib)
- `MeasureTheory.integral` (Bochner integral) — used in the subtraction
- `iSup` (conditional supremum over `ℝ`) — `Mathlib.Order.ConditionallyCompleteLattice.Basic`

### What didn't work on weakEvolutionEmpiricalMeasure
- Iteration 1: `integral_finset_sum_measure` lemma + `ring` failed: `ring_nf made no progress on goal`
- Iteration 2: Reverted; recognized the fundamental obstruction
- Iteration 3: `integral_smul_measure` + `integral_finset_sum_measure` had wrong integrability API; `conv_lhs` tactic failed on `HasDerivAt`
- Iteration 4: Confirmed theorem is mathematically false for arbitrary `R_N`

**Root cause of weakEvolutionEmpiricalMeasure failure:** The theorem universally quantifies over `R_N : ℝ → ℝ` but requires `HasDerivAt` (unique derivative) to hold for the given value. For two different choices of `R_N`, the two values `R_N t` differ, but the derivative of `fun s => ∫ φ dμ_s^N` at `t` is unique. Hence the first conjunct can be true for at most one value of `R_N t`, making the theorem false for general `R_N`. The statement should have `R_N` existentially quantified.

**Wished-for Mathlib API:**
- `MeasureTheory.Measure.wasserstein` — a library-native Wasserstein-p distance with the Kantorovich–Rubinstein duality theorem and stability estimates

## 2026-05-23T00:00:00 · most-tractable selection · meanFieldLimit

**Result:** failure
**Iterations:** 2/8
**Sorry count:** 5 → 5 (no change; file reverted)

### Candidate scoring (most-tractable mode)

All 5 open sorries were evaluated:

| Sorry | Score notes |
|-------|-------------|
| `weakEvolutionEmpiricalMeasure` | Very large statement; requires HasDerivAt on integral of empirical measure, full chain-rule computation under finite sum. Not tractable in 8 iterations. |
| `empiricalMeasureSolvesVlasov` | Blocked on `weakEvolutionEmpiricalMeasure` (which is sorry). Would invoke that sorry in the proof body, so cannot discharge. |
| `vlasovWellPosedness` | Requires Picard iteration in measure space; no Mathlib API. Not tractable. |
| `dobrushin` | Requires Gronwall inequality + Wasserstein metric theory not in Mathlib. Not tractable. |
| `meanFieldLimit` | Has `hDobrushin` as a hypothesis (Dobrushin stability), so does not depend on `dobrushin` being proved. Strategy: bound sup via hDobrushin, squeeze to 0 via hInit. **Selected as most tractable.** |

### Proof skeleton attempted

The `hbound` have-block successfully proved (iteration 2):

```lean
have hbound : ∀ N : ℕ,
    ⨆ t ∈ Set.Icc 0 T, wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t) ≤
    ENNReal.ofReal (Real.exp (C * T)) *
      wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
  intro N; apply iSup_le; intro t; apply iSup_le; intro ht
  calc wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t)
      ≤ ENNReal.ofReal (Real.exp (C * t)) *
          wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) :=
        hDobrushin N t ht.1
    _ ≤ ENNReal.ofReal (Real.exp (C * T)) *
          wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
        apply mul_le_mul_of_nonneg_right _ (zero_le _)
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp_of_le
        exact mul_le_mul_of_nonneg_left ht.2 (le_of_lt hC)
```

### What didn't work

- **Iteration 1:** Used `ENNReal.mul_le_mul_right'` (nonexistent); fixed to `mul_le_mul_of_nonneg_right`.
- **Iteration 2:** `hbound` proved. Completing the proof requires showing
  `wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) → 0`,
  which equals `wasserstein1 (empiricalMeasure N (X N 0) (V N 0)) f₀`.
  But `hInit` gives `wasserstein1 (empiricalMeasure N (X₀ N) (V₀ N)) f₀ → 0`.
  The theorem statement has no hypothesis linking `X N 0` to `X₀ N` — a gap in the theorem's hypothesis list.

**Root cause of failure:** `meanFieldLimit` is missing the initial-condition hypothesis `∀ N i, X N 0 i = X₀ N i ∧ V N 0 i = V₀ N i`. Without it, `hInit` and `hbound` cannot be combined.

**Wished-for fix:** Add hypothesis `hInitLink : ∀ N, X N 0 = X₀ N ∧ V N 0 = V₀ N` to the theorem, then the proof closes in ~3 more iterations via ENNReal scalar multiplication continuity and the squeeze theorem.
## 2026-05-23T00:00:00 · cor:mfl · meanFieldLimit

**Result:** failure
**Iterations:** 8/8
**Sorry count:** 5 → 5 (unchanged)

### Score breakdown (most-tractable selection)

| Candidate | Score | Reason |
|---|---|---|
| `weakEvolutionEmpiricalMeasure` | 2/10 | Large, requires differentiating integral of Dirac sums |
| `empiricalMeasureSolvesVlasov` | 1/10 | Blocked on weakEvolutionEmpiricalMeasure |
| `vlasovWellPosedness` | 1/10 | No Mathlib path; deep existence/uniqueness |
| `dobrushin` | 3/10 | Gronwall + incomplete Wasserstein API |
| `meanFieldLimit` | 6/10 | Key estimate given as hypothesis `hDobrushin`; just need squeeze |

Selected `meanFieldLimit` because the Dobrushin stability bound is given directly as hypothesis `hDobrushin : ∀ N, DobrushinStabilityEstimate (...) f C`, so the proof reduces to: bound the sup by `exp(C*T) * W1(μ_0^N, f₀)`, then send to 0 using `hInit`.

### Final proof attempt (failed)

The skeleton was:
1. Prove `hsup_bound`: for each `N`, `⨆ t ∈ Icc 0 T, W1(μ_t^N, f_t) ≤ exp(C*T) * W1(μ_0^N, f₀)`.
   - Use `iSup_le` twice, apply `hDobrushin N t ht.1`, then monotonicity of `exp` and rewrite `empiricalMeasureCurve N _ 0 = empiricalMeasure N _ f₀`.
2. Prove `hUpper`: `fun N => exp(C*T) * W1(μ_0^N, f₀)` tends to 0.
   - Use `ENNReal.Tendsto.const_mul` applied to `hInit`.
3. Conclude by `tendsto_of_tendsto_of_tendsto_of_le_of_le`.

`hsup_bound` was proved successfully in iteration 6. The failure point was `hUpper` in iteration 8:

### What didn't work
- iteration 1: skeleton with inner `sorry` for `hUpper` — `tendsto_of_tendsto_of_tendsto_of_le_of_le` expected reversed le order
- iteration 2: fixed order; wrong `Filter.Tendsto.const_mul` (not the ENNReal namespace version) 
- iteration 3: `gcongr` split produced `t ≤ T` goal that wasn't discharged; also wrong `const_mul`
- iteration 4: tried `mul_le_mul_of_nonneg_left ht.2 hC.le` → got `t ≤ T` sub-goal from `gcongr` split
- iteration 5: rewrote calc chain more explicitly; `ENNReal.mul_le_mul_right'` doesn't exist; `f 0` vs `f₀` mismatch
- iteration 6: used `hf_init ▸ hD` to fix `f 0/f₀`, used `mul_le_mul_of_nonneg_right`; `hsup_bound` succeeded. `ENNReal.Tendsto.const_mul` type-inference fails
- iteration 7: tried explicit `(a := ...)` annotation; `Or.inr ENNReal.ofReal_ne_top` syntax issue — `⊢ ℝ` error on the `have`
- iteration 8: tried `Or.inl (by positivity)` for `0 ≠ 0` (wrong — the limit is 0, so `b ≠ 0` is false); got "failed to prove nonzeroness"

**Wished-for Mathlib API:**
- `ENNReal.Tendsto.const_mul` with better argument inference when the limit is `0` (the `Or.inr` condition `a ≠ ∞` should suffice but type inference fails to pick `a` from context)
- Alternatively `Filter.Tendsto.const_mul_ennreal_ne_top : Tendsto f l (nhds b) → a ≠ ⊤ → Tendsto (fun x => a * f x) l (nhds (a * b))`

**Root cause:** Lean could not infer the implicit constant `a` in `ENNReal.Tendsto.const_mul`; explicit annotation `(a := ENNReal.ofReal (Real.exp (C * T)))` triggered positivity on the wrong `Or` branch. One more iteration could likely fix this by using `Or.inr (ENNReal.ofReal_ne_top (x := Real.exp (C * T)))` but the cap was reached.
