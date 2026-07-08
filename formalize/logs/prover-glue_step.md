## 2026-05-30 · vlasovWellPosedness_glue_step · Stage 5 glue step

**Result:** success (per user task spec; 8 sub-sub-sorries inside body, structural layout complete)
**Iterations:** 2/8
**Sorry count:** 10 → 10 (declaration still uses sorry through internal sub-sorries; user task explicitly permitted sub-sub-sorries with done criterion = build success + structural layout)
**Pre-flight (§3.5):** dropped 0 hint(s); validated 1 sketch lemma (Set.right_mem_Icc); rejected 0 in-loop citation(s)

### Final proof (structural layout)
```lean
  -- Step 1: invoke vlasovWellPosedness_local on f_prev T to get g on [0, T_0]
  have h_prev_T_mom : HasFiniteFirstMoment (f_prev T) :=
    h_prev_mom T (Set.right_mem_Icc.mpr hT_pos.le)
  obtain ⟨g, hg_init, hg_mom, hg_lag⟩ :=
    vlasovWellPosedness_local W gradW hgradW L hL
      (f_prev T) h_prev_T_mom hT_0_pos hT_0_small
  -- Step 2: define the glued solution piecewise
  let f_next : ℝ → Measure (PhaseSpace d) :=
    fun t => if t ≤ T then f_prev t else g (t - T)
  -- Step 3: four conjuncts
  refine ⟨f_next, ?_, ?_, ?_, ?_⟩
  -- Conjunct (i): agreement on [0,T] — 2 lines, closed
  -- Conjunct (ii): f_next 0 = f₀ — 2 lines, closed
  -- Conjunct (iii): HasFiniteFirstMoment on [0,T+T_0] — 8 lines, closed
  -- Conjunct (iv): IsLagrangianVlasovSolutionOn — structural + 8 sub-sorries
```

### Lookup trail
- `Set.right_mem_Icc` — `.lake/packages/mathlib/Mathlib/Order/Interval/Finset/Basic.lean:133`

### Sub-sub-sorries (8 total, all inside vlasovWellPosedness_glue_step)
1. L7078: `IsVlasovSolutionOn gradW f_next (T + T_0)` — PDE gluing at boundary t=T requires continuity argument
2. L7098: `HasDerivAt charX_next` for t ≤ T in IsCharacteristicFlowOn — needs boundary case t=T
3. L7102: `HasDerivAt charX_next` for t > T — needs shift composition with h_g_flow
4. L7108: `HasDerivAt charV_next` for t ≤ T — same as #2
5. L7110: `HasDerivAt charV_next` for t > T — same as #3
6. L7125: pushforward equation for t ≤ T — needs `f_next 0 = f_prev 0` + heq composition
7. L7130: pushforward for t > T — needs flow composition through T
8. L7147: AEMeasurability for s > T — needs composition of AEMeasurable maps

### What closed fully (no sorry)
- Conjuncts (i), (ii), (iii): all closed inline
- IsCharacteristicFlowOn initial condition clause (charX_next 0 = z.1, charV_next 0 = z.2)
- AEMeasurability for s ≤ T (uses h_prev_aemeas with f_next 0 = f_prev 0 rewrite)

### Notes
- The boundary t=T for IsVlasovSolutionOn and IsCharacteristicFlowOn (HasDerivAt) is the load-bearing difficulty: both pieces give Ioo 0 T and Ioo T (T+T_0), not covering T itself
- The pushforward for t > T requires flow composition: f_next 0 → f_prev T → g(t-T), while charX_next threads through charX_p(T,z) as the "initial condition" for charX_g
- Suggested next session: attack sub-sorries #2/#3/#4/#5 first (all have the same structure: boundary + shift)
## 2026-05-30 · vlasovWellPosedness_glue_step sub-sub-sorries

**Result:** partial success — 5 of 8 sub-sub-sorries closed substantively; 3 remain as structural debt (t = T boundary)

**Iterations:** 8/8

**Sorry count:** 21 → 16 (5 fewer)

**Pre-flight (§3.5):** validated 5 Mathlib names (AEMeasurable.map_map_of_aemeasurable, HasDerivAt.congr_of_eventuallyEq, HasDerivAt.scomp_of_eq, eventually_gt_nhds, eventually_lt_nhds); rejected 2 in-loop citations (Measure.map_map_of_aemeasurable → AEMeasurable.map_map_of_aemeasurable; 𝓝 → nhds)

### What was closed

1. **L7125** (pushforward t ≤ T): `simp only [if_pos hT_pos.le]; exact heq` — trivial once the if-expression for `f_next 0` is simplified.

2. **L7147** (AEMeasurability s > T): Used `AEMeasurable.comp_aemeasurable` with `h_g_aemeas (s-T)` (rewritten via `hg_init` + `h_prev_push T`) composed with `h_prev_aemeas T`.

3. **L7130** (pushforward t > T): Three rewrites `h_g_push`, `hg_init`, `h_prev_push T` collapse to `Measure.map (comp) (f_prev 0)`, then `AEMeasurable.map_map_of_aemeasurable` + `rfl`.

4. **L7102** (charX HasDerivAt t > T): `HasDerivAt.scomp_of_eq t h_g_deriv h_sub rfl` + `simpa [Function.comp, one_smul]` for beta reduction + `congr_of_eventuallyEq` using `eventually_gt_nhds`.

5. **L7110** (charV HasDerivAt t > T): Same chain rule approach; used `congrArg spatialMarginal h_fnext_t.symm` rewritten into `h_chain` to match `f_next t` with `g (t-T)`.

6. **t < T strict interior of charX HasDerivAt**: `congr_of_eventuallyEq` using `eventually_lt_nhds ht_lt`.

7. **t < T strict interior of charV HasDerivAt**: Same, plus `simp only [h_eq_marg]` to match `spatialMarginal (f_prev t)` with `spatialMarginal (f_next t)`.

8. **IsVlasovSolutionOn t < T**: `HasDerivAt.congr_of_eventuallyEq` applied to the integral function.

9. **IsVlasovSolutionOn t > T**: Chain rule via `HasDerivAt.comp_of_eq t h_g_deriv h_sub rfl` + `simpa [Function.comp, mul_one]`.

### Remaining 3 sorries (structural debt)

All three occur at `t = T` (the exact gluing boundary):

1. **IsVlasovSolutionOn t = T**: `HasDerivAt` of `∫ φ ∂f_next s` at s = T requires one-sided derivatives from both `h_prev_vlasov` and `h_g_vlasov` to agree and combine. These functions only have `HasDerivAt` on the OPEN intervals `Ioo 0 T` and `Ioo 0 T_0` respectively; the boundary point T itself is excluded. Needs Friction-5-style boundary regularity theorem.

2. **charX HasDerivAt t = T**: `HasDerivAt (piecewise charX_p / charX_g) (charV_p T z) T`. Both pieces are continuous at T (charX_g 0 pt = charX_p T z by initial condition), but HasDerivAt requires agreement of one-sided limits of the difference quotient. Left derivative = charV_p T z from h_prev_flow; right derivative should equal charV_g 0 pt = charV_p T z. Needs combining left/right HasDerivAt.

3. **charV HasDerivAt t = T**: Same structural issue for the velocity component.

### Technical notes

- `HasDerivAt.scomp_of_eq` has an explicit `(x)` argument (from the section variable `variable ... (x)` in Mathlib's Deriv/Comp.lean). Must call as `HasDerivAt.scomp_of_eq t hg hh rfl` not `hg.scomp_of_eq hh rfl`.
- After `scomp_of_eq`, the result has `(g ∘ h)` not beta-reduced; need `simpa [Function.comp]` to get `fun s => g (h s)`.
- `spatialMarginal (f_prev t)` appears as `(fun t => spatialMarginal (f_prev t)) t` in goals (not beta-reduced); use `simp only [eq_marg]` to substitute, not `rw [eq_marg]`.
- For charX goals, `congr_of_eventuallyEq` takes `h₁ : f₁ =ᶠ f` (f₁ is the new function, f is the original). Do NOT use `.symm` — the direction is correct as written.

### Pre-flight rejections (in-loop)
- `Measure.map_map_of_aemeasurable` — zero matches in Mathlib; correct name is `AEMeasurable.map_map_of_aemeasurable` (inside `namespace AEMeasurable` in AEMeasurable.lean)
- `𝓝` — unknown identifier in this file's scope; use `nhds` (ASCII) instead

## 2026-05-30 · vlasovWellPosedness_glue_step · t=T boundary surgery (cases b, c, vii)

**Result:** failure — 8/8 iterations exhausted; conjunct (vii) edit introduced `subst ht_eq` (Unknown identifier `T` errors) instead of `rw [ht_eq]`; reverted to checkpoint losing cases (b) and (c) fixes

**Iterations:** 8/8

**Sorry count:** 10 → 10 (no change; reverted)

**Pre-flight (§3.5):** validated: `HasDerivWithinAt.union`, `HasDerivWithinAt.hasDerivAt`, `Icc_union_Icc_eq_Icc`, `HasDerivWithinAt.scomp_of_eq`, `HasDerivWithinAt.congr_of_eventuallyEq_of_mem`, `eventually_nhdsWithin_of_forall`, `HasDerivWithinAt.mono_of_mem_nhdsWithin`, `mem_nhdsWithin_of_mem_nhds`, `nhdsWithin_Icc_eq_nhdsGE`, `nhdsWithin_Icc_eq_nhdsLE`, `Icc_mem_nhdsGE`, `Icc_mem_nhdsLE`; rejected 0 in-loop citations

### What was closed (but lost to revert)

**Case (b): charX_next HasDerivAt at t=T** — Proof used `HasDerivWithinAt.union` combining:
- Left side (Icc 0 T): `h_prev_boundary.1` rewritten via `congr_of_eventuallyEq_of_mem` and `eventually_nhdsWithin_of_forall (fun s hs => if_pos hs.2)`
- Right side (Icc T (T+T_0)): `hg_boundary.1` + `hg_init_cond.2` to align value at 0, then chain rule `HasDerivWithinAt.scomp_of_eq` for s ↦ s-T, then `congr_of_eventuallyEq_of_mem` for the if-expression
- Union then converted to `Icc 0 (T+T_0)` via `Icc_union_Icc_eq_Icc`, then `hasDerivAt` via `Icc_mem_nhds`

**Case (c): charV_next HasDerivAt at t=T** — Same structure as (b), with `.2` half of boundary hypotheses, plus:
- `rw [show g 0 = f_prev T from hg_init, show charX_g 0 (...) = charX_prev T z from h_ic.1] at h_raw_R` to align convolution argument
- Goal rewritten via `rw [show spatialMarginal (f_next T) = spatialMarginal (f_prev T) from congrArg spatialMarginal h_fT]`

**Key errors encountered and fixed during (b)/(c)**:
- `Filter.eventually_nhdsWithin_of_forall` — no `Filter.` prefix needed (lives at top level)
- `congr_of_eventuallyEq_of_mem` arg order: `refine h_raw_L.congr_of_eventuallyEq_of_mem ?_ h_T_mem` (membership is second arg)
- `Icc_mem_nhds_iff` conflicts — use `Icc_mem_nhds (by linarith) (by linarith)` directly
- `simp only [h_ic.1, hg_init]` at let-binding z' — use explicit `rw [show ...]` instead

### What didn't work

**Iteration 8 (conjunct vii)**: Used `subst ht_eq` for `ht_eq : t = T` which eliminated `T` not `t`, producing "Unknown identifier `T`" at every subsequent mention. Should have used `rw [ht_eq]` (same fix as documented in earlier iterations for cases (b)/(c)).

**Case (a): IsVlasovSolutionOn at t=T** — Structurally blocked. `IsVlasovSolutionOn` delivers `HasDerivAt (∫ φ ∂f_next s) D(t) t` only for `t ∈ Ioo 0 T`. Extending to `t = T` requires continuity of the derivative map, which depends on the Lagrangian chain rule that is sorry'd throughout the project (Stage C). Cannot be closed without new infrastructure.

### Wished-for Mathlib API

- A boundary-regularity version of `HasDerivWithinAt.union` that works from two one-sided `HasDerivAt` statements on `Ioo` intervals, not requiring `HasDerivWithinAt` on the closed interval (would simplify the Ioo→Icc lifting step needed for case (a))

### Sketch for future session (cases b, c, vii)

The (b) and (c) proofs are known-correct (validated by build in this session before context exhaustion). The conjunct (vii) proof needs the same union trick but producing `HasDerivWithinAt` on `Icc 0 (T+T_0)` rather than `HasDerivAt`. Key: always use `rw [ht_eq]` not `subst ht_eq` when `ht_eq : t = T`. For interior points (t < T or T < t < T+T_0), use `HasDerivAt.hasDerivWithinAt`. For the left endpoint t=0, use `mono_of_mem_nhdsWithin` with `nhdsWithin_Icc_eq_nhdsGE`. For the right endpoint t=T+T_0, use `mono_of_mem_nhdsWithin` with `nhdsWithin_Icc_eq_nhdsLE`.
