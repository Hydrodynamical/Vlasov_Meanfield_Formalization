# Formalization coverage report

Generated: 2026-05-25
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status
- Result: success
- Sorry warnings: 12
- Other warnings: 17
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` | present |
| eq:newton | equation | `IsNewtonSolution` | present |
| ass:W | assumption | `class AssW` | present |
| def:empirical | definition | `empiricalMeasure`, `empiricalMeasureCurve`, `empiricalMeasure_isProbabilityMeasure` | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present |
| eq:weak-eq | equation | `WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

Status values: `present` = no sorry; `present-with-sorry` = declaration exists but uses sorry (directly or via helper decomposition); `commented-out` = explicitly skipped with TODO comment; `missing` = no corresponding declaration found.

Summary: 13/13 items present (11 fully proved or sorry-free, 2 present-with-sorry, 0 missing).

---

## Sorry inventory

### `Vlasov.weakEvolutionEmpiricalMeasure` (`prop:weak`, decomposed)
Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

All helpers in this decomposition are **proved** (no sorry warnings on any helper line). The residual glue (line 619) is also proved. The parent theorem `weakEvolutionEmpiricalMeasure` itself carries no sorry warning in the build output. This entire cascade is complete.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | proved |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 372 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 412 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 490 | 2 | 4 | (none) | proved |

Residual glue: line 619 (branch `HasDerivAt (first ?_ branch of the refine combinator)`); Score 4; composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. tactic_sketch present in plan. Status: **proved**.

---

### `Vlasov.MathlibTODO_wassersteinGronwallCoupling` (no tex-label, decomposed)
Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

This theorem (originally an axiom, now expressed as a theorem) bridges the Mathlib gap for the Gronwall-based Wasserstein-1 growth estimate. It depends on two sub-axioms (`MathlibTODO_wassersteinGronwallCoupling_W1ContOn` and `MathlibTODO_wassersteinGronwallCoupling_derivBound`) that formalise properties not yet in Mathlib's stable API.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_gronwall_le` | 942 | 2 | 4 | (none) | sorry |
| 2 | `wassersteinGronwallCoupling_real_bound` | 957 | 3 | 3 | wassersteinGronwallCoupling_gronwall_le | sorry |
| 3 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 975 | 1 | 5 | (none) | sorry |
| 4 | `wassersteinGronwallCoupling_ofReal_le` | 986 | 2 | 4 | wassersteinGronwallCoupling_real_bound, wassersteinGronwallCoupling_ennreal_mul_comm | sorry |

`Score = 6 − Difficulty` for helpers; the residual glue row gets a fixed `Score = 4`.

Residual glue: line 1003 (branch `main body of MathlibTODO_wassersteinGronwallCoupling`); Score 4; composes [wassersteinGronwallCoupling_ofReal_le]. tactic_sketch: `exact wassersteinGronwallCoupling_ofReal_le ...`. Status: **sorry**.

Sub-axioms (Mathlib gaps, not provable without new Mathlib API):
- `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 902): narrow continuity of W₁ along Vlasov flows.
- `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 920): right-derivative Gronwall bound via characteristic flow coupling.

---

### `Vlasov.dobrushin` (`thm:dobrushin`, decomposed)
Plan: `formalize/plans/dobrushin.json`

The Dobrushin stability theorem. Depends on `MathlibTODO_wassersteinGronwallCoupling` (above) and on the Mathlib-gap axiom `MathlibTODO_convolveLipschitzEstimate`.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 1023 | 2 | 4 | (none) | sorry |
| 2 | `convolveDiff_norm_le` | 1032 | 4 | 2 | (none) | sorry |
| 3 | `wasserstein1_ofReal_exp_monotone` | 1044 | 1 | 5 | (none) | sorry |
| 4 | `dobrushin_ennreal_bound` | 1055 | 4 | 2 | dobrushin_C_choice, convolveDiff_norm_le | sorry |
| 5 | `dobrushin_package_exists` | 1074 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | sorry |

`Score = 6 − Difficulty` for helpers.

Residual glue: line 1103 (branch `main body of dobrushin`); Score 4; composes [dobrushin_C_choice, dobrushin_ennreal_bound, dobrushin_package_exists]. tactic_sketch: `obtain ⟨C, hC, hbound⟩ := dobrushin_package_exists ...; exact ⟨C, hC, hbound⟩`. Status: **sorry**.

Mathlib-gap axioms (not provable without new Mathlib API):
- `MathlibTODO_convolveLipschitzEstimate` (line 886): pointwise Lipschitz estimate for ∇W * ρ via Kantorovich–Rubinstein duality.

---

### Non-decomposed sorries

| Declaration | Line | Tex label | Note |
|-------------|------|-----------|------|
| `vlasovWellPosedness` | 784 | thm:vlasov-wp | Standalone sorry; full existence+uniqueness for Vlasov PDE. Depends on Mathlib-gap items (measure-valued Picard theory). |

---

## Recommended next steps

### Decomposed parents: `MathlibTODO_wassersteinGronwallCoupling` helpers (ordered by tractability)

1. **Discharge `wassersteinGronwallCoupling_ennreal_mul_comm` (difficulty 1, Score 5; no deps).** The statement is `ENNReal.ofReal (δ * exp(C * t)) = ENNReal.ofReal (exp(C * t)) * ENNReal.ofReal δ`. Direct application of `ENNReal.ofReal_mul` (requires `exp_pos` for the nonnegativity side condition) followed by `mul_comm`. The plan's tactic sketch `rw [mul_comm δ ..., ENNReal.ofReal_mul ...]` should close this in one build cycle. Mathlib hints: `ENNReal.ofReal_mul`, `mul_comm`, `Real.exp_pos`.

2. **Discharge `wassersteinGronwallCoupling_gronwall_le` (difficulty 2, Score 4; no deps).** This wraps Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` with ε = 0 and uses `gronwallBound_ε0`, `gronwallBound_x0`. The plan calls it a "clean wrapper"; the sub-axioms `_W1ContOn` and `_derivBound` are assumed — so the Gronwall wrapper itself should be a straightforward API exercise once the statement is checked against `Mathlib.Analysis.ODE.Gronwall`. Mathlib hints: `le_gronwallBound_of_liminf_deriv_right_le`, `gronwallBound_ε0`, `gronwallBound_x0`.

3. **Discharge `dobrushin_C_choice` (difficulty 2, Score 4; no deps).** Prove `∃ C : ℝ, 0 < C ∧ (L : ℝ) ≤ C` for any `L : NNReal`. The witness is `C = max((L : ℝ), 1)`. Order lemmas `le_max_left`, `lt_max_of_lt_right`, `NNReal.coe_nonneg` suffice. Mathlib hints: `le_max_right`, `le_max_left`, `lt_max_of_lt_right`, `NNReal.coe_nonneg`.

4. **Discharge `dobrushin_package_exists` (difficulty 2, Score 4; depends on dobrushin_C_choice, dobrushin_ennreal_bound).** The plan tactic sketch (`obtain ⟨C, hC, hCL⟩ := dobrushin_C_choice L; exact ⟨C, hC, dobrushin_ennreal_bound ...⟩`) will close this once its two deps are proved. Independent-attack-order applies: can be attempted now with `dobrushin_C_choice` and `dobrushin_ennreal_bound` sorried. Mathlib hints: `le_max_right`, `le_max_left`.

5. **Discharge `wassersteinGronwallCoupling_ofReal_le` (difficulty 2, Score 4; depends on wassersteinGronwallCoupling_real_bound, wassersteinGronwallCoupling_ennreal_mul_comm).** Once item 1 above (ennreal_mul_comm) and item 6 below (real_bound) are proved, this lifts the bound to ENNReal via `ENNReal.ofReal_le_ofReal` and `ENNReal.ofReal_toReal_le`. Independent-attack-order applies. Mathlib hints: `ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_toReal_le`, `mul_le_mul_of_nonneg_left`.

6. **Discharge `wassersteinGronwallCoupling_real_bound` (difficulty 3, Score 3; depends on wassersteinGronwallCoupling_gronwall_le).** Applies the Gronwall wrapper to the sub-axiom-provided continuity and derivative-bound hypotheses. Once `wassersteinGronwallCoupling_gronwall_le` is proved, the body is `exact wassersteinGronwallCoupling_gronwall_le ... (MathlibTODO_..._W1ContOn ...) (MathlibTODO_..._derivBound ...)`. Independent-attack-order applies. Mathlib hints: `le_gronwallBound_of_liminf_deriv_right_le`, `gronwallBound_ε0`.

7. **Discharge `convolveDiff_norm_le` (difficulty 4, Score 2; no deps, but depends on Mathlib gap axiom `MathlibTODO_convolveLipschitzEstimate`).** The statement directly follows from the axiom; the proof is a one-liner `exact MathlibTODO_convolveLipschitzEstimate gradW L hL ρ σ x`. Mathlib hints: `MeasureTheory.norm_integral_le_integral_norm`, `LipschitzWith.dist_le_mul`.

8. **Discharge `dobrushin_ennreal_bound` (difficulty 4, Score 2; depends on dobrushin_C_choice, convolveDiff_norm_le).** Invokes `MathlibTODO_wassersteinGronwallCoupling` (the coupled Gronwall result) with the C-choice constant. Once dobrushin_C_choice and the Gronwall theorem are proved, this wraps them into the universal `∀ t ≥ 0` bound. Mathlib hints: `ENNReal.ofReal_mul`, `ENNReal.ofReal_le_ofReal`, `iSup_le`, `le_iSup`.

### Residual-glue items (Score 4 each, machine-executable tactic sketches in plans)

After the helper cascade above is complete, close the two residual-glue items:

- **`MathlibTODO_wassersteinGronwallCoupling` residual glue (line 1003):** tactic sketch `exact wassersteinGronwallCoupling_ofReal_le gradW L hL f g hf hg hf_prob hg_prob C hC hCL t ht` — single-line once `wassersteinGronwallCoupling_ofReal_le` is proved.

- **`dobrushin` residual glue (line 1103):** tactic sketch `obtain ⟨C, hC, hbound⟩ := dobrushin_package_exists W gradW hgradW L hL f g hf hg hf_prob hg_prob; exact ⟨C, hC, hbound⟩` — single-line once `dobrushin_package_exists` is proved.

### Non-decomposed sorry

- **`vlasovWellPosedness` (line 784, thm:vlasov-wp):** Full existence and uniqueness for the Vlasov PDE. This is the most mathematically substantial gap. It requires measure-valued Picard theory (global flow of a Lipschitz vector field on a space of measures) and unique continuation — neither is in Mathlib's stable API. Recommend deferring this until `MeasureTheory.MeasureValuedODE` or equivalent is contributed to Mathlib upstream. As a shorter-term path, one could state a `sorry`-backed axiom `MathlibTODO_vlasovWellPosedness` mirroring the Dobrushin-gap pattern, to make the downstream dependency structure explicit.

