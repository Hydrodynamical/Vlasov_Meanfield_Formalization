# Formalization coverage report

Generated: 2026-05-26
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 18
- Other warnings: 14 (unused section variables, unused simp args, unused variables, long line)
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` | present |
| eq:newton | equation | `IsNewtonSolution` | present |
| ass:W | assumption | `class AssW` | present |
| def:empirical | definition | `empiricalMeasure`, `empiricalMeasureCurve`, `empiricalMeasure_isProbabilityMeasure` | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present-with-sorry |
| eq:weak-eq | equation | `WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

**Summary: 13/13 outline items present. 0 missing.**

Notes:
- `prop:weak` (`weakEvolutionEmpiricalMeasure`) is fully proved; the sorry warnings at lines 891–945 belong to a nested decomposition of a Mathlib-gap helper (`MathlibTODO_convolveLipschitzEstimate`) that is invoked deep in its dependency chain. The theorem itself (line 557) does not appear in the sorry list.
- `thm:vlasov-wp` (`vlasovWellPosedness`) carries a direct top-level sorry at line 784.
- `thm:dobrushin` (`dobrushin`) carries a residual-glue sorry at line 1165; all helpers are sorry'd due to Mathlib gaps.
- `cor:mfl` (`meanFieldLimit`) is fully proved (no sorry warning on it), delegating to the Dobrushin estimate as a hypothesis.

## Sorry inventory

### `MathlibTODO_convolveLipschitzEstimate` (Mathlib gap, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`

This parent has no `tex_label` (it is an infrastructure theorem bridging Wasserstein-1 duality
to the convolution-Lipschitz estimate needed by `dobrushin`).

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `convolveLipschitz_inner_lipschitz` | 891 | 3 | 3 | (none) | sorry |
| 2 | `convolveLipschitz_KR_le` | 905 | 2 | 4 | (none) | sorry |
| 3 | `convolveLipschitz_inner_bound` | 918 | 3 | 3 | convolveLipschitz_inner_lipschitz, convolveLipschitz_KR_le | sorry |
| 4 | `convolveLipschitz_norm_le_of_inner_forall` | 935 | 2 | 4 | (none) | sorry |

Residual glue: line 945 (branch `main body of MathlibTODO_convolveLipschitzEstimate`); Score 4;
composes [convolveLipschitz_inner_bound, convolveLipschitz_norm_le_of_inner_forall]. tactic_sketch present in plan.

---

### `MathlibTODO_wassersteinGronwallCoupling` (Mathlib gap, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

This parent has no `tex_label` (it is an infrastructure theorem providing the Gronwall-based
Wasserstein coupling estimate that backs `dobrushin`).

Sub-axioms (not in sorry list as standalone declarations; sorried inside the helpers that invoke them):
- `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 962) — sorry
- `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 981) — sorry

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 1037 | 1 | 5 | (none) | proved |
| 2 | `wassersteinGronwallCoupling_gronwall_le` | 1004 | 2 | 4 | (none) | sorry |
| 3 | `wassersteinGronwallCoupling_ofReal_le` | 1048 | 2 | 4 | wassersteinGronwallCoupling_real_bound, wassersteinGronwallCoupling_ennreal_mul_comm | sorry |
| 4 | `wassersteinGronwallCoupling_real_bound` | 1019 | 3 | 3 | wassersteinGronwallCoupling_gronwall_le | sorry |

Residual glue: line 1065 (branch `main body of MathlibTODO_wassersteinGronwallCoupling; delegate to wassersteinGronwallCoupling_ofReal_le`); Score 4;
composes [wassersteinGronwallCoupling_ofReal_le]. tactic_sketch present in plan.

---

### `dobrushin` (tex: thm:dobrushin, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/dobrushin.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wasserstein1_ofReal_exp_monotone` | 1106 | 1 | 5 | (none) | sorry |
| 2 | `dobrushin_C_choice` | 1085 | 2 | 4 | (none) | sorry |
| 3 | `dobrushin_package_exists` | 1136 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | sorry |
| 4 | `convolveDiff_norm_le` | 1094 | 4 | 2 | (none) | sorry |
| 5 | `dobrushin_ennreal_bound` | 1117 | 4 | 2 | dobrushin_C_choice, convolveDiff_norm_le | sorry |

Residual glue: line 1165 (branch `main body of dobrushin; residual sorry to be closed once dobrushin_package_exists is proved`); Score 4;
composes [dobrushin_C_choice, dobrushin_ennreal_bound, dobrushin_package_exists]. tactic_sketch present in plan.

---

### `weakEvolutionEmpiricalMeasure` (tex: prop:weak, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/weakEvolutionEmpiricalMeasure.json`

All helpers and the residual glue are PROVED (no sorry warnings on any of their lines).

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | proved |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 372 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 412 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 490 | 2 | 4 | (none) | proved |

Residual glue: line 619 (branch `HasDerivAt (first ?_ branch of the refine combinator)`); Score 4;
composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. tactic_sketch present in plan. Status: proved.

---

### Non-decomposed sorries (flat table)

| Line | Declaration | Tex label | Notes |
|------|-------------|-----------|-------|
| 784 | `vlasovWellPosedness` | thm:vlasov-wp | Top-level sorry; existence+uniqueness for Vlasov requires measure-valued PDE theory not yet in Mathlib |

## Recommended next steps

### For `MathlibTODO_convolveLipschitzEstimate` (decomposed)

1. Discharge the residual glue at line 945 (Score 4) — has machine-executable `tactic_sketch`
   (`exact convolveLipschitz_norm_le_of_inner_forall ...` citing `convolveLipschitz_inner_bound`);
   the prover's fast path may close it in one build cycle once the two helpers it depends on are proved.

2. Discharge `convolveLipschitz_KR_le` (difficulty 2, Score 4; no deps;
   hints: `le_iSup₂`, `ENNReal.ofReal_le_ofReal`, `ENNReal.toReal_iSup`, `ENNReal.ofReal_toReal`).
   Unfold `wasserstein1` as the KR supremum and use `le_iSup` to bound the specific 1-Lipschitz
   test function's integral difference.

3. Discharge `convolveLipschitz_norm_le_of_inner_forall` (difficulty 2, Score 4; no deps;
   hints: `real_inner_self_eq_norm_mul_norm`, `real_inner_le_norm`, `abs_real_inner_le_norm`,
   `norm_nonneg`). In `z = 0`: trivial; in `z ≠ 0`: take `v = z / ‖z‖`, use
   `real_inner_self_eq_norm_mul_norm` to equate `‖z‖` with `⟨z, z/‖z‖⟩`.

4. Discharge `convolveLipschitz_inner_lipschitz` (difficulty 3, Score 3; no deps;
   hints: `LipschitzWith.comp`, `lipschitzWith_of_opNorm_le`, `ContinuousLinearMap.integral_comp_comm`,
   `real_inner_smul_left`). Compose the L-Lipschitz `y ↦ gradW(x−y)` with the `‖v‖₊`-Lipschitz
   `w ↦ ⟨w, v⟩` via `LipschitzWith.comp`.

5. Discharge `convolveLipschitz_inner_bound` (difficulty 3, Score 3; depends on
   `convolveLipschitz_inner_lipschitz`, `convolveLipschitz_KR_le` — independent attack-order applies;
   hints: `ContinuousLinearMap.integral_comp_comm`, `integral_sub`, `norm_integral_le_integral_norm`,
   `real_inner_le_norm`). Commute the inner product `⟨·, v⟩` through the integral difference, then
   rescale the integrand to 1-Lipschitz and apply `convolveLipschitz_KR_le`.

### For `MathlibTODO_wassersteinGronwallCoupling` (decomposed)

Note: `wassersteinGronwallCoupling_ennreal_mul_comm` is already proved (Score 5, skip).

1. Discharge the residual glue at line 1065 (Score 4) — has machine-executable `tactic_sketch`
   (`exact wassersteinGronwallCoupling_ofReal_le gradW L hL f g hf hg hf_prob hg_prob C hC hCL t ht`);
   one build cycle once `wassersteinGronwallCoupling_ofReal_le` is proved.

2. Discharge `wassersteinGronwallCoupling_gronwall_le` (difficulty 2, Score 4; no deps;
   hints: `le_gronwallBound_of_liminf_deriv_right_le`, `gronwallBound_ε0`, `gronwallBound_x0`).
   Set `ε = 0` in Mathlib's Gronwall lemma and simplify.

3. Discharge `wassersteinGronwallCoupling_ofReal_le` (difficulty 2, Score 4; depends on
   `wassersteinGronwallCoupling_real_bound`, `wassersteinGronwallCoupling_ennreal_mul_comm` —
   independent attack-order applies; hints: `ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_toReal_le`,
   `mul_le_mul_of_nonneg_left`). Lift the real-valued bound to ENNReal via `ENNReal.ofReal_toReal_le`.

4. Discharge `wassersteinGronwallCoupling_real_bound` (difficulty 3, Score 3; depends on
   `wassersteinGronwallCoupling_gronwall_le`; hints: `le_gronwallBound_of_liminf_deriv_right_le`,
   `gronwallBound_ε0`). Apply the Gronwall wrapper with `h = fun t => (wasserstein1 (f t) (g t)).toReal`,
   feeding in the two sub-axioms `W1ContOn` and `derivBound` for continuity and derivative bound.

   Note: the two sub-axioms `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 962) and
   `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 981) are themselves sorry'd and
   represent genuine Mathlib gaps (narrow continuity of Wasserstein-1 along measure-valued ODEs,
   and the coupling-based derivative bound). These require external Mathlib development or
   custom axiom acceptance.

### For `dobrushin` (tex: thm:dobrushin, decomposed)

1. Discharge the residual glue at line 1165 (Score 4) — has machine-executable `tactic_sketch`
   (`obtain ⟨C, hC, hbound⟩ := dobrushin_package_exists ...; exact ⟨C, hC, hbound⟩`);
   closes in one build cycle once `dobrushin_package_exists` is proved.

2. Discharge `wasserstein1_ofReal_exp_monotone` (difficulty 1, Score 5; no deps;
   hints: `ENNReal.ofReal_le_ofReal`, `Real.exp_le_exp`, `mul_le_mul_of_nonneg_left`).
   Direct chain: `C * s ≤ C * t` (from `hC > 0` and `s ≤ t`), then `exp` is monotone,
   then `ENNReal.ofReal_le_ofReal`.

3. Discharge `dobrushin_C_choice` (difficulty 2, Score 4; no deps;
   hints: `le_max_right`, `le_max_left`, `lt_max_of_lt_right`, `NNReal.coe_nonneg`).
   Take `C = max((L : ℝ), 1)`; `0 < C` follows from `lt_max_of_lt_right (by norm_num)`;
   `(L : ℝ) ≤ C` from `le_max_left`.

4. Discharge `dobrushin_package_exists` (difficulty 2, Score 4; depends on `dobrushin_C_choice`,
   `dobrushin_ennreal_bound` — independent attack-order applies;
   hints: `le_max_right`, `le_max_left`, `lt_max_of_lt_right`). Obtain `C` from
   `dobrushin_C_choice L`, then use `dobrushin_ennreal_bound` for the bound.

5. Discharge `convolveDiff_norm_le` (difficulty 4, Score 2; no deps;
   hints: `MeasureTheory.norm_integral_le_integral_norm`, `LipschitzWith.dist_le_mul`,
   `ENNReal.ofReal_le_ofReal`). This delegates to `MathlibTODO_convolveLipschitzEstimate`
   (which must itself be proved first).

6. Discharge `dobrushin_ennreal_bound` (difficulty 4, Score 2; depends on `dobrushin_C_choice`,
   `convolveDiff_norm_le`; hints: `ENNReal.ofReal_mul`, `ENNReal.ofReal_le_ofReal`, `iSup_le`,
   `le_iSup`). Apply `MathlibTODO_wassersteinGronwallCoupling` (which must itself be proved first).

### For the non-decomposed sorry

- `vlasovWellPosedness` (thm:vlasov-wp, line 784): This requires existence and uniqueness for the
  nonlinear Vlasov equation in the measure-valued sense. This is a substantial Mathlib gap:
  it needs a Picard–Lindelöf theorem for measure-valued ODEs with Lipschitz right-hand side
  (in Wasserstein topology). Recommended approach: introduce as an explicit `MathlibTODO_*`
  theorem and decompose, or accept as an axiom pending Mathlib development of measure-valued
  ODE theory. The most tractable near-term step is to state the well-posedness as an axiom
  and document the dependency chain, similar to the treatment of
  `MathlibTODO_wassersteinGronwallCoupling`.
