# Formalization coverage report

Generated: 2026-05-25
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 8 (lines 784, 917, 926, 938, 949, 968, 997, 1017 — see Sorry inventory below)
- Other warnings: 18 (unused section vars, unused simp args, unused variables — cosmetic only)
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` (line 41) | present-proved |
| eq:newton | equation | `IsNewtonSolution` (line 60) | present-proved |
| ass:W | assumption | `class AssW` (line 80) | present-proved |
| def:empirical | definition | `empiricalMeasure`, `empiricalMeasureCurve` (lines 174, 197) | present-proved |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` (line 557) | present-proved |
| eq:weak-eq | equation | `WeakEvolutionEq` (line 674) | present-proved |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` (line 698) | present-proved |
| eq:vlasov | equation | `IsVlasovSolution` (line 755) | present-proved |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` (line 784) | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` (lines 822, 837, 846) | present-proved |
| thm:dobrushin | theorem | `dobrushin` (line 997) | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` (line 1031) | present-proved |
| cor:mfl | corollary | `meanFieldLimit` (line 1057) | present-proved |

Status key: `present-proved` = no sorry; `present-with-sorry` = declaration exists but
body contains sorry (directly or via decomposed helpers); `present-stubbed` = declaration
present but entire body is a single `sorry` with no structure; `missing` = no corresponding
Lean declaration found.

Summary: **13/13 outline items present** (11 present-proved, 2 present-with-sorry, 0 missing).

## Sorry inventory

### `Vlasov.dobrushin` (tex: thm:dobrushin, decomposed)

Plan: `formalize/plans/dobrushin.json`

Two Mathlib-gap axioms underpin this decomposition:
- `MathlibTODO_convolveLipschitzEstimate` (line 886) — Kantorovich–Rubinstein pointwise Lipschitz estimate for convolution against measures; not yet in Mathlib's stable API.
- `MathlibTODO_wassersteinGronwallCoupling` (line 900) — Gronwall-based exponential W₁ growth bound via characteristic-flow coupling; requires measure-valued ODE existence + Wasserstein-1 triangle inequality under pushforward, neither in Mathlib's stable API.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|-----------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 917 | 2 | 4 | (none) | sorry |
| 2 | `convolveDiff_norm_le` | 926 | 4 | 2 | (none) | sorry |
| 3 | `wasserstein1_ofReal_exp_monotone` | 938 | 1 | 5 | (none) | sorry |
| 4 | `dobrushin_ennreal_bound` | 949 | 4 | 2 | dobrushin_C_choice, convolveDiff_norm_le | sorry |
| 5 | `dobrushin_package_exists` | 968 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | sorry |

`Score = 6 − Difficulty`. The residual glue (below) gets a fixed Score = 4.

Residual glue: line 1017 (branch `main body of dobrushin; residual sorry to be closed once
dobrushin_package_exists is proved`); Score 4; composes [dobrushin_C_choice,
dobrushin_ennreal_bound, dobrushin_package_exists]. tactic_sketch present in plan.

---

### `Vlasov.weakEvolutionEmpiricalMeasure` (tex: prop:weak, decomposed)

Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

All helpers proved — no sorries remain in this decomposed cascade.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|-----------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | proved |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 372 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 412 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 490 | 2 | 4 | (none) | proved |

Residual glue: line 619 (branch `HasDerivAt (first ?_ branch of the refine combinator)`);
composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. Status: **proved**.
The entire weakEvolutionEmpiricalMeasure cascade is now fully proved — zero sorries.

---

### Non-decomposed sorries

| Line | Enclosing declaration | Tex label | Notes |
|------|-----------------------|-----------|-------|
| 784 | `vlasovWellPosedness` | thm:vlasov-wp | Entire body is a single `sorry`; well-posedness of the Vlasov equation requires Mathlib API for measure-valued ODEs that does not yet exist. |

## Recommended next steps

### Decomposed parent: `dobrushin` helpers (ordered by tractability)

1. **Discharge `wasserstein1_ofReal_exp_monotone` (difficulty 1, Score 5; no deps).**
   This is a one-line monotonicity fact about real exponentials lifted to ENNReal.
   The plan's `proof_sketch` gives an almost-complete proof:
   `apply ENNReal.ofReal_le_ofReal; exact Real.exp_le_exp.mpr
   (mul_le_mul_of_nonneg_left hst (le_of_lt hC))`.
   Mathlib hints: `ENNReal.ofReal_le_ofReal`, `Real.exp_le_exp`,
   `mul_le_mul_of_nonneg_left`. Expected to close in one build cycle.

2. **Discharge the residual glue at line 1017 (Score 4) — has machine-executable
   `tactic_sketch` in the plan.** Once `dobrushin_package_exists` is proved, the
   residual reduces to unwrapping `obtain ⟨C, hC, hbound⟩` and applying `exact
   ⟨C, hC, hbound⟩`. The prover's fast path may close it immediately.
   Tactic sketch from plan:
   `obtain ⟨C, hC, hbound⟩ :=
     dobrushin_package_exists W gradW hgradW L hL f g hf hg hf_prob hg_prob;
   exact ⟨C, hC, hbound⟩`.

3. **Discharge `dobrushin_C_choice` (difficulty 2, Score 4; no deps).**
   Prove `∃ C : ℝ, 0 < C ∧ (L : ℝ) ≤ C` for any `L : NNReal` by taking
   `C = max((L : ℝ), 1)`. Mathlib hints: `le_max_right`, `le_max_left`,
   `lt_max_of_lt_right`, `NNReal.coe_nonneg`.

4. **Discharge `dobrushin_package_exists` (difficulty 2, Score 4; depends on
   dobrushin_C_choice, dobrushin_ennreal_bound — independent attack order applies).**
   Pure packaging: obtain the constant from `dobrushin_C_choice` and the bound from
   `dobrushin_ennreal_bound`, then close the existential. Mathlib hints:
   `le_max_right`, `le_max_left`, `lt_max_of_lt_right`.
   Plan's proof_sketch: `obtain ⟨C, hC, hCL⟩ := dobrushin_C_choice L; exact ⟨C, hC,
   dobrushin_ennreal_bound W gradW hgradW L hL f g hf hg hf_prob hg_prob C hC hCL⟩`.

5. **Discharge `convolveDiff_norm_le` (difficulty 4, Score 2; no deps;
   depends on `MathlibTODO_convolveLipschitzEstimate` axiom).**
   The body invokes the axiom directly. Once the axiom is accepted as a boundary,
   the proof is `exact MathlibTODO_convolveLipschitzEstimate gradW L hL ρ σ x`.
   Mathlib hints: `MeasureTheory.norm_integral_le_integral_norm`,
   `LipschitzWith.dist_le_mul`, `ENNReal.ofReal_le_ofReal`.
   NOTE: this sorry can only be fully discharged (axiom-free) once Mathlib adds
   Kantorovich–Rubinstein duality for general metric spaces. It is currently blocked
   by the `MathlibTODO_convolveLipschitzEstimate` gap.

6. **Discharge `dobrushin_ennreal_bound` (difficulty 4, Score 2; depends on
   dobrushin_C_choice, convolveDiff_norm_le — independent attack order applies).**
   The body delegates to `MathlibTODO_wassersteinGronwallCoupling`. Mathlib hints:
   `ENNReal.ofReal_mul`, `ENNReal.ofReal_le_ofReal`, `iSup_le`, `le_iSup`.
   NOTE: this sorry is blocked by `MathlibTODO_wassersteinGronwallCoupling` (the
   Gronwall estimate for measure-valued ODEs), which requires Mathlib API that does
   not yet exist. It is the deepest Mathlib gap in the project.

### Non-decomposed sorry

7. **`vlasovWellPosedness` (thm:vlasov-wp, line 784) — entire body is a single
   `sorry`; no decomposition plan exists yet.**
   This requires Mathlib API for existence and uniqueness of measure-valued ODEs
   (the Vlasov equation as a fixed-point problem on a curve of measures), which is
   not in Mathlib's current stable API. Recommended approach: either (a) axiomatize
   it as a `MathlibTODO_vlasovWellPosedness` axiom in the same style as the Dobrushin
   gap axioms, or (b) run the sorry-decomposer on this theorem to identify tractable
   sub-goals (characteristic flow existence via Picard iteration, uniqueness via
   Gronwall). Blocking dependencies: measure-valued ODE Picard iteration, narrow
   topology compactness. This is the second major Mathlib gap.
