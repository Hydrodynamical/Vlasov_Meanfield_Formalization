# Formalization coverage report

Generated: 2026-05-25
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status
- Result: success
- Sorry warnings: 11
- Other warnings: 18
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` | present |
| eq:newton | equation | `IsNewtonSolution` | present |
| ass:W | assumption | `class AssW` | present |
| def:empirical | definition | `empiricalMeasure`, `empiricalMeasure_isProbabilityMeasure`, `empiricalMeasureCurve` | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present |
| eq:weak-eq | equation | `WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

Status values: `present` (no sorry), `present-with-sorry` (sorry in body or helpers),
`present-stubbed` (axiom placeholder), `commented-out`, `missing`.

**Note on status:**
- `eq:HN`, `eq:newton`, `ass:W`, `def:empirical`, `eq:weak-eq`, `cor:empirical-vlasov`,
  `eq:vlasov`, `eq:char`, `eq:dobrushin`, `cor:mfl`: fully proved, no sorries.
- `prop:weak` (`weakEvolutionEmpiricalMeasure`): the theorem itself and all its helper
  decomposition are fully proved (cascade completed 2026-05-24). Status: `present`.
- `thm:vlasov-wp` (`vlasovWellPosedness`): body is a single `sorry` at line 784.
  Status: `present-with-sorry`.
- `thm:dobrushin` (`dobrushin`): residual glue sorry at line 1103; five helpers still
  sorried; two Mathlib-gap axioms (`MathlibTODO_convolveLipschitzEstimate`,
  `MathlibTODO_wassersteinGronwallCoupling_*`). Status: `present-with-sorry`.

---

## Sorry inventory

### `weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)
Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

**All helpers and residual glue are proved. Cascade is COMPLETE.**

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | proved |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 372 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 412 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 490 | 2 | 4 | (none) | proved |

`Score = 6 − Difficulty` for helpers; residual glue gets Score = 4.

Residual glue: line 619 (branch `HasDerivAt first ?_ branch`); Score 4;
composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. Tactic sketch present in plan.
Status: **proved**.

---

### `MathlibTODO_wassersteinGronwallCoupling` (no tex-label, decomposed)
Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

Promoted from `axiom` to `theorem`; backed by two sub-axioms:
- `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 902, axiom)
- `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 920, axiom)

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_gronwall_le` | 942 | 2 | 4 | (none) | sorry |
| 2 | `wassersteinGronwallCoupling_real_bound` | 957 | 3 | 3 | wassersteinGronwallCoupling_gronwall_le | sorry |
| 3 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 975 | 1 | 5 | (none) | proved |
| 4 | `wassersteinGronwallCoupling_ofReal_le` | 986 | 2 | 4 | wassersteinGronwallCoupling_real_bound, wassersteinGronwallCoupling_ennreal_mul_comm | sorry |

`Score = 6 − Difficulty`.

Residual glue: line 1003 (branch `main body of MathlibTODO_wassersteinGronwallCoupling`);
Score 4; composes [wassersteinGronwallCoupling_ofReal_le]. Tactic sketch present in plan.
Status: **sorry**.

---

### `dobrushin` (thm:dobrushin, decomposed)
Plan: `formalize/plans/dobrushin.json`

Backed by one Mathlib-gap axiom:
- `MathlibTODO_convolveLipschitzEstimate` (line 886, axiom — Kantorovich–Rubinstein duality)
- Indirectly backed by `MathlibTODO_wassersteinGronwallCoupling` (line 1003, theorem — itself
  backed by two more sub-axioms)

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 1023 | 2 | 4 | (none) | sorry |
| 2 | `convolveDiff_norm_le` | 1032 | 4 | 2 | (none) | sorry |
| 3 | `wasserstein1_ofReal_exp_monotone` | 1044 | 1 | 5 | (none) | sorry |
| 4 | `dobrushin_ennreal_bound` | 1055 | 4 | 2 | dobrushin_C_choice, convolveDiff_norm_le | sorry |
| 5 | `dobrushin_package_exists` | 1074 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | sorry |

`Score = 6 − Difficulty`.

Residual glue: line 1103 (branch `main body of dobrushin`); Score 4;
composes [dobrushin_C_choice, dobrushin_ennreal_bound, dobrushin_package_exists].
Tactic sketch present in plan. Status: **sorry**.

---

### Non-decomposed sorries (flat table)

| Enclosing declaration | Line | Tex label | Notes |
|-----------------------|------|-----------|-------|
| `vlasovWellPosedness` | 784 | thm:vlasov-wp | Entire proof body is a single `sorry`; requires Mathlib API for measure-valued PDE well-posedness (Picard iteration on `𝒫_1`) |

---

## Recommended next steps

### For decomposed parents

#### `MathlibTODO_wassersteinGronwallCoupling` helpers (ranked by tractability)

1. Discharge `wassersteinGronwallCoupling_ennreal_mul_comm` (difficulty 1, Score 5; no deps;
   already **proved** — no action needed).

2. Discharge `wassersteinGronwallCoupling_gronwall_le` (difficulty 2, Score 4; no deps;
   has a machine-executable `tactic_sketch`-style path via
   `le_gronwallBound_of_liminf_deriv_right_le` + `gronwallBound_ε0` + `gronwallBound_x0`
   in Mathlib. This is a clean wrapper with ε = 0 — the prover's fast path may close
   it in one build cycle. Hints: `le_gronwallBound_of_liminf_deriv_right_le`,
   `gronwallBound_ε0`, `gronwallBound_x0`).

3. Discharge `wassersteinGronwallCoupling_ofReal_le` (difficulty 2, Score 4; depends on
   `wassersteinGronwallCoupling_real_bound` and `wassersteinGronwallCoupling_ennreal_mul_comm` —
   independent attack-order applies since Lean treats sorry'd names as opaque references.
   Hints: `ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_toReal_le`,
   `mul_le_mul_of_nonneg_left`).

4. Discharge `wassersteinGronwallCoupling_real_bound` (difficulty 3, Score 3; depends on
   `wassersteinGronwallCoupling_gronwall_le` — independent attack-order applies. Requires
   composing the Gronwall wrapper with the two sub-axioms for continuity and derivative bound.
   Hints: `le_gronwallBound_of_liminf_deriv_right_le`, `gronwallBound_ε0`).

5. Discharge the `MathlibTODO_wassersteinGronwallCoupling` residual glue at line 1003
   (Score 4; `tactic_sketch` in plan: `exact wassersteinGronwallCoupling_ofReal_le gradW L hL
   f g hf hg hf_prob hg_prob C hC hCL t ht` — should close once helper 4 above is proved).

#### `dobrushin` helpers (ranked by tractability)

1. Discharge `wasserstein1_ofReal_exp_monotone` (difficulty 1, Score 5; no deps;
   hints: `ENNReal.ofReal_le_ofReal`, `Real.exp_le_exp`, `mul_le_mul_of_nonneg_left`.
   Plan provides a proof sketch: `apply ENNReal.ofReal_le_ofReal; exact Real.exp_le_exp.mpr
   (mul_le_mul_of_nonneg_left hst (le_of_lt hC))`).

2. Discharge `dobrushin_C_choice` (difficulty 2, Score 4; no deps;
   hints: `le_max_right`, `le_max_left`, `lt_max_of_lt_right`, `NNReal.coe_nonneg`.
   This is a pure order-lemma exercise on `max((L : ℝ), 1)`).

3. Discharge `dobrushin_package_exists` (difficulty 2, Score 4; depends on `dobrushin_C_choice`
   and `dobrushin_ennreal_bound` — independent attack-order applies. Plan sketch:
   `obtain ⟨C, hC, hCL⟩ := dobrushin_C_choice L; exact ⟨C, hC,
   dobrushin_ennreal_bound W gradW hgradW L hL f g hf hg hf_prob hg_prob C hC hCL⟩`).

4. Discharge the `dobrushin` residual glue at line 1103 (Score 4; `tactic_sketch` in plan:
   `obtain ⟨C, hC, hbound⟩ := dobrushin_package_exists ...; exact ⟨C, hC, hbound⟩`).

5. Discharge `dobrushin_ennreal_bound` (difficulty 4, Score 2; depends on `dobrushin_C_choice`,
   `convolveDiff_norm_le` — independent attack-order applies. Requires invoking
   `MathlibTODO_wassersteinGronwallCoupling` (already a theorem, backed by sub-axioms).
   Hints: `ENNReal.ofReal_mul`, `ENNReal.ofReal_le_ofReal`, `iSup_le`, `le_iSup`).

6. Discharge `convolveDiff_norm_le` (difficulty 4, Score 2; no deps; but depends on Mathlib
   gap axiom `MathlibTODO_convolveLipschitzEstimate` (Kantorovich–Rubinstein duality for
   general metric spaces). This is blocked on upstream Mathlib development.
   Hints: `MeasureTheory.norm_integral_le_integral_norm`, `LipschitzWith.dist_le_mul`,
   `ENNReal.ofReal_le_ofReal`).

### For non-decomposed sorries

- `vlasovWellPosedness` (thm:vlasov-wp, line 784): This requires Picard iteration for
  measure-valued PDEs on `𝒫_1(ℝ^d × ℝ^d)`, yielding a unique narrowly continuous solution
  curve. Blocked on Mathlib API: `MeasureTheory.ProbabilityMeasure` doesn't yet have a
  general existence-uniqueness theorem for Vlasov-type measure-valued ODEs. Recommend
  introducing this as a `MathlibTODO_vlasovWellPosedness` axiom and tracking separately,
  analogous to the pattern used for `MathlibTODO_convolveLipschitzEstimate`.

### Mathlib gap axioms — upstream tracking

The following axioms represent genuine Mathlib gaps that require upstream contributions:

- `MathlibTODO_convolveLipschitzEstimate` (line 886): Kantorovich–Rubinstein duality for
  Wasserstein-1 on general metric spaces. Needed for `convolveDiff_norm_le`.

- `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 902): Continuity of
  `t ↦ W₁(f_t, g_t)` along narrowly-continuous Vlasov solution curves.

- `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 920): Differential inequality
  `d/dt W₁(f_t, g_t) ≤ C · W₁(f_t, g_t)` via characteristic flow coupling.

These three axioms are the core Dobrushin estimate ingredients not yet available in Mathlib's
stable API. All other sorries in the file can be closed once these are available.

---

**Summary:** 13/13 outline items present; 10/13 items fully proved (no sorry);
3 items present-with-sorry (thm:vlasov-wp, thm:dobrushin, and transitively
MathlibTODO_wassersteinGronwallCoupling). Build: success.
