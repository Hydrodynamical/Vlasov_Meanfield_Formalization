## 2026-05-30T00:00:00 · Stage6 · vlasovWellPosedness_universal_existence

**Result:** success (structural close — body laid out; 3 internal sub-sub-sorries remain)
**Iterations:** 2/8
**Sorry count:** 3 → 3 (declaration-level count unchanged; internal structure changed from 1 flat sorry to 3 targeted sub-sub-sorries)
**Pre-flight (§3.5):** dropped 0 hints; validated 0 sketch lemmas; rejected 0 in-loop citations

### Final proof (structured body)

The single `sorry` in the theorem body was replaced with a 66-line structured proof:

1. **Step 1**: `h_fwd_exists` — for each `n : ℕ`, invokes `vlasovWellPosedness_forward` with `T_target = (n : ℝ) + 1` to get a per-window solution.
2. **Step 2**: `Classical.choose` extracts canonical per-n solutions `sol n`, with `h_sol_init`, `h_sol_mom`, `h_sol_lag` recording their properties.
3. **Step 3**: `h_agree` — sub-sub-sorry (A): overlap agreement via Stage 8 uniqueness.
4. **Step 4**: defines `f t := if 0 ≤ t then sol ⌈t⌉₊ t else f₀`.
5. **Step 5**: proves the four conjuncts:
   - Conjunct 1 (`f 0 = f₀`): CLOSED by `simp [h_sol_init 0]`.
   - Conjunct 2 (`∀ t, HasFiniteFirstMoment (f t)`): CLOSED by case split on `0 ≤ t`; forward case uses `h_sol_mom (⌈t⌉₊)` + `le_ceil`.
   - Conjunct 3 (`IsLagrangianVlasovSolution`): sub-sub-sorry (B) — requires gluing per-window `IsLagrangianVlasovSolutionOn` to universal form across all windows; backward time is a genuine scope boundary.
   - Conjunct 4 (narrow continuity): sub-sub-sorry (C) — DCT using moment bound; backward time constant.

### Sub-sub-sorries listed

- **(A) `h_agree`** (1 sorry): overlap agreement `sol n t = sol m t` for `t ∈ [0, n+1]`, `n ≤ m`. Requires `vlasovWellPosedness_uniqueness` (Stage 8, sorry'd body) applied after restricting `sol m`'s `IsLagrangianVlasovSolutionOn` from `(m:ℝ)+1` to `(n:ℝ)+1`.
- **(B) IsLagrangianVlasovSolution conjunct** (1 sorry): universal-in-`t` Vlasov solution from per-window solutions. Forward time: glue `IsVlasovSolutionOn` + `IsCharacteristicFlowOn` from per-n windows into universal `IsVlasovSolution` + `IsCharacteristicFlow`. Backward time: `t < 0` path uses `f t := f₀`, which doesn't satisfy the Vlasov PDE or the flow ODE (genuine scope boundary).
- **(C) Narrow continuity** (1 sorry): `t ↦ ∫ g df_t` continuous for bounded continuous `g`. Forward: DCT using moment bound from `h_sol_mom`; backward: `f t = f₀` constant. Gluing at `t = 0` requires continuity argument.

### What's closed without sorry

- Construction of the universal `f` via ceiling-indexed `sol` family.
- `f 0 = f₀` (closed substantively).
- `∀ t ≥ 0, HasFiniteFirstMoment (f t)` (closed by `h_sol_mom` + `le_ceil`).
- `∀ t < 0, HasFiniteFirstMoment (f t)` (closed since `f t = f₀ = hf₀`).

### Build status

Build succeeds (`lake build Vlasov.OT.CharacteristicFlow` exits 0). No new errors. The three sorry warnings at CharacteristicFlow.lean:7213, 7275, 7382 are unchanged in count; the 7275 sorry is now structurally richer (65 lines of proof infrastructure instead of 1 flat `sorry`).

### Lookup trail

- `vlasovWellPosedness_forward` — `CharacteristicFlow.lean:7047`
- `vlasovWellPosedness_uniqueness` — `CharacteristicFlow.lean:7213`
- `Classical.choose` / `Classical.choose_spec` — Lean 4 built-in
- `Nat.le_ceil` — `Mathlib/Algebra/Order/Floor/Semiring.lean:179` (as bare `le_ceil`)
- `le_trans` — Lean 4 built-in
