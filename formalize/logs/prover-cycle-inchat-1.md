## 2026-05-24T00:00:00Z · diagonalCorrection_bound · Vlasov.diagonalCorrection_bound

**Result:** failure
**Iterations:** 8/8
**Sorry count:** 7 → 7 (no change; file reverted)

### Selection rationale (Mode B: most-tractable)

Plan-aware lookup fired. Plan file: `formalize/plans/weakEvolutionEmpiricalMeasure.json`.

Candidate scores:
- `diagonalCorrection_bound` — difficulty 1 → score 5 (highest; deps on `diagonalCorrection_eq` but bound body is standalone)
- `diagonalCorrection_eq` — difficulty 2 → score 4
- `hasDerivAt_phi_along_trajectory` — difficulty 3 → score 3
- `hasDerivAt_empiricalIntegral_sum` — difficulty 3 → score 3
- residual_glue — difficulty estimated 4 (has tactic_sketch but deps on sorry'd helpers)

Selected `diagonalCorrection_bound` as highest score.

### What didn't work

- **Iteration 1**: Tried `abs_sum_le_sum_abs` — not in scope (needed `Finset.abs_sum_le_sum_abs`). Error: unknown identifier.
- **Iteration 2**: Fixed to `Finset.abs_sum_le_sum_abs` — compile error persisted (still had the original sorry).
- **Iteration 3**: Both identifiers correct, build green with scaffolding sorry. Partial proof:
  - `abs_mul` + `abs_of_pos` to split the absolute value
  - `Finset.abs_sum_le_sum_abs` for triangle inequality
  - `abs_real_inner_le_norm` for Cauchy-Schwarz on each term
  Now needed: `1/N² * Σ ‖gradW 0‖*‖gradVφ(zᵢ)‖ ≤ 1/N * ⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖`
- **Iteration 4**: Added `mul_le_mul_of_nonneg_left` + `Finset.sum_le_card_nsmul` + `by_cases BddAbove` skeleton. Errors: `rw [Real.iSup_mul_of_nonneg]` failed (pattern mismatch — goal already had iSup in RHS form), and `positivity` failed on `≤ 0` subgoal in unbounded case.
- **Iteration 5**: Tried `le_ciSup_of_le ?_ 0` + `le_ciSup ?_ _` for `hterm`. Error: type mismatch — `le_ciSup` returns `f c ≤ iSup f` but elaboration failed to match the pattern without explicit `BddAbove` hypothesis.
- **Iteration 6**: Full `by_cases` on both `BddAbove` flags. Errors showed that in unbounded case, `simp [ciSup_of_not_bddAbove]` leads to `⊢ LHS ≤ 0` but `LHS ≥ 0`, so the subgoal is FALSE.
- **Iteration 7**: Tried `Nat.cast_smul_eq_nsmul` rewrite — failed (pattern not found after prior rewrites).
- **Iteration 8**: Multiple errors; fundamental blocker identified.

### Root cause of failure

The lemma `diagonalCorrection_bound` as stated is **unprovable in Lean 4/Mathlib** without additional `BddAbove` hypotheses. The key issues:

1. `le_ciSup (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f` requires `BddAbove`.
2. In Lean's `ConditionallyCompleteLinearOrder ℝ`, `⨆ x, f x = sSup ∅ = 0` when `¬BddAbove (range f)`.
3. Therefore when `gradW` or `gradVφ` is unbounded, the RHS `(1/N) * ⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖ = 0`, while the LHS `|(1/N²) * Σ ⟨gradW 0, gradVφ(zᵢ)⟩| ≥ 0` cannot be shown to be `≤ 0` in general.
4. Mathlib only provides the "downward" lemma `Real.iSup_le` (working without `BddAbove`) and `Real.iSup_nonneg`, but no unconditional "upward" `le_iSup` for `ℝ`.

### Wished-for Mathlib API

- A lemma `Real.le_iSup_of_le (c : ι) (h : a ≤ f c) : a ≤ ⨆ i, f i` that works without `BddAbove` — possible if `f c ≥ 0` and one uses `sSup_nonneg'`. However this would require `a ≤ 0 ∨ BddAbove (range f)` and is thus only provable when `BddAbove` holds or `a ≤ 0`.

### Recommended fix

Add `BddAbove` hypotheses to `diagonalCorrection_bound`:
```lean
lemma diagonalCorrection_bound ... 
    (hbW : BddAbove (Set.range (‖gradW ·‖)))
    (hbV : BddAbove (Set.range (fun z => ‖gradVφ z‖))) : ...
```
Then the proof follows straightforwardly using `le_ciSup hbW` and `le_ciSup hbV`.

### Lookup trail

- `Finset.abs_sum_le_sum_abs` — `.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:287`
- `abs_real_inner_le_norm` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:467`
- `le_ciSup` — `.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean:143` (requires `BddAbove`)
- `Real.iSup_nonneg` — `.lake/packages/mathlib/Mathlib/Data/Real/Archimedean.lean:298`
- `Real.iSup_mul_of_nonneg` — `.lake/packages/mathlib/Mathlib/Data/Real/Pointwise.lean:127`
- `ciSup_of_not_bddAbove` — `.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:421`
- `Real.sSup_empty` — `.lake/packages/mathlib/Mathlib/Data/Real/Archimedean.lean:168` (= 0)
- `Finset.sum_le_card_nsmul` — `.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:214`
