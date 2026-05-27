# Formalization coverage report

Generated: 2026-05-27T03:36:42Z
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status
- Result: success
- Sorry warnings: 6
  - Line 784: `vlasovWellPosedness` (thm:vlasov-wp)
  - Line 1233: `MathlibTODO_W1ContOn_lscNarrow`
  - Line 1248: `MathlibTODO_W1ContOn_uscNarrow`
  - Line 1283: `W1ContOn_integralContAt`
  - Line 1303: `W1ContOn_toRealContOn`
  - Line 1354: `MathlibTODO_wassersteinGronwallCoupling_derivBound`
- Other warnings: 22 (unused variables, unused simp args, style)
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

Status values: `present` (no sorry in declaration body), `present-with-sorry` (declaration body contains sorry or depends on sorry'd helpers), `present-stubbed` (declaration exists but is a bare sorry), `commented-out`, `missing`.

Notes:
- `thm:dobrushin` (`dobrushin`) delegates entirely to `dobrushin_package_exists`, which itself calls `dobrushin_ennreal_bound`, which invokes `MathlibTODO_wassersteinGronwallCoupling`; the chain is clean Lean but the Gronwall and coupling sub-axioms (`MathlibTODO_wassersteinGronwallCoupling_derivBound`) remain sorry'd.
- `cor:mfl` (`meanFieldLimit`) is a fully proved theorem; its sorry-free status is conditional on the correctness of the Dobrushin bound it takes as a hypothesis.
- `thm:vlasov-wp` (`vlasovWellPosedness`) is a bare `sorry` at line 800; it is the only outline theorem with no decomposition plan.

---

## Sorry inventory

### Decomposed parents

#### `weakEvolutionEmpiricalMeasure` (prop:weak, decomposed)
Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

All helpers are proved (no sorry warning on any helper line). The parent body at
line 557 is clean. The residual glue block (line 619) is also clean.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | proved |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 372 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 412 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 490 | 2 | 4 | (none) | proved |

Residual glue: line 619 (branch `HasDerivAt first ?_ branch`); Score 4; composes
`hasDerivAt_empiricalIntegral_sum`, `diagonalCorrection_eq`. Tactic sketch present
in plan. Status: **proved**.

This decomposed parent is **fully closed**. No outstanding sorries.

---

#### `MathlibTODO_convolveLipschitzEstimate` (no tex label, decomposed)
Plan: `formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`

All helpers are at confirmed lines (plan listed `-1` for pre-existence lines, but
grep shows them at lines 1016, 1048, 1073, 1179 respectively). No sorry warnings
on any of these lines. The parent body at line 1205 is clean (delegates via
`convolveLipschitz_norm_le_of_inner_forall`).

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `convolveLipschitz_inner_lipschitz` | 1016 | 3 | 3 | (none) | proved |
| 2 | `convolveLipschitz_KR_le` | 1048 | 2 | 4 | (none) | proved |
| 3 | `convolveLipschitz_inner_bound` | 1073 | 3 | 3 | inner_lipschitz, KR_le | proved |
| 4 | `convolveLipschitz_norm_le_of_inner_forall` | 1179 | 2 | 4 | (none) | proved |

Residual glue: parent body at line 1205 (branch `main body`). Status: **proved**.

This decomposed parent is **fully closed**. No outstanding sorries.

---

#### `dobrushin` (thm:dobrushin, decomposed)
Plan: `formalize/plans/dobrushin.json`

The plan lists lines relative to an older file path (`Vlasov/Basic.lean`); actual
lines in the current file are determined by build warnings and grep.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 1495 | 2 | 4 | (none) | proved |
| 2 | `convolveDiff_norm_le` | 1505 | 4 | 2 | MathlibTODO_convolveLipschitzEstimate | proved |
| 3 | `wasserstein1_ofReal_exp_monotone` | 1521 | 1 | 5 | (none) | proved |
| 4 | `dobrushin_ennreal_bound` | 1533 | 4 | 2 | dobrushin_C_choice, convolveDiff_norm_le | proved (but calls MathlibTODO_wassersteinGronwallCoupling, itself sorry-backed) |
| 5 | `dobrushin_package_exists` | 1559 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | proved (transitively sorry-backed) |

Residual glue: `dobrushin` at line 1590 delegates entirely to `dobrushin_package_exists`.
Status: **proved** (but transitively sorry-backed via `MathlibTODO_wassersteinGronwallCoupling`).

---

#### `MathlibTODO_wassersteinGronwallCoupling` (no tex label, decomposed)
Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

The parent at line 1477 delegates to `wassersteinGronwallCoupling_ofReal_le`.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_gronwall_le` | 1377 | 2 | 4 | (none) | proved |
| 2 | `wassersteinGronwallCoupling_real_bound` | 1397 | 3 | 3 | gronwall_le, W1ContOn (sorry), derivBound (sorry) | proved structure, sorry-backed |
| 3 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 1423 | 1 | 5 | (none) | proved |
| 4 | `wassersteinGronwallCoupling_ofReal_le` | 1434 | 2 | 4 | real_bound, ennreal_mul_comm | proved structure, sorry-backed |

Sub-axioms (genuine Mathlib gaps, always sorry'd by design):
- `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (used by `wassersteinGronwallCoupling_real_bound`): no sorry warning because its body is a composed proof — it calls `W1ContOn_toRealContOn` which is sorry'd at line 1303.
- `MathlibTODO_wassersteinGronwallCoupling_derivBound` at line 1354: **sorry** (build warning line 1354).

Residual glue: parent `MathlibTODO_wassersteinGronwallCoupling` at line 1477 delegates to `wassersteinGronwallCoupling_ofReal_le`. Status: proved structure, sorry-backed.

---

#### `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (no tex label, decomposed)
Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `W1ContOn_lt_top` | 1265 | 2 | 4 | (none) | proved |
| 2 | `W1ContOn_integralContAt` | 1283 | 3 | 3 | (none) | **sorry** (line 1283) |
| 3 | `W1ContOn_toRealContOn` | 1303 | 2 | 4 | W1ContOn_lt_top, lscNarrow (sorry), uscNarrow (sorry) | **sorry** (line 1303) |

Sub-axioms (genuine Mathlib gaps):
- `MathlibTODO_W1ContOn_lscNarrow` at line 1233: **sorry** (build warning line 1233).
- `MathlibTODO_W1ContOn_uscNarrow` at line 1248: **sorry** (build warning line 1248).

The parent `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` at line 1315 delegates
to `W1ContOn_toRealContOn` (line 1303), which is sorry'd.

---

### Non-decomposed sorries (flat table)

| Declaration | Line | Tex label | Note |
|-------------|------|-----------|------|
| `vlasovWellPosedness` | 784 | thm:vlasov-wp | Bare `sorry`; no decomposition plan. Genuine PDE well-posedness gap. |
| `MathlibTODO_W1ContOn_lscNarrow` | 1233 | — | Mathlib gap: LSC of W₁ under narrow convergence; needs full KR duality. |
| `MathlibTODO_W1ContOn_uscNarrow` | 1248 | — | Mathlib gap: USC of W₁ along Vlasov flows; needs characteristic flow theory. |
| `W1ContOn_integralContAt` | 1283 | — | Helper: continuity of `t ↦ ∫ φ d(f t)` for Vlasov solutions. Should be provable from `HasDerivAt.continuousAt`. |
| `W1ContOn_toRealContOn` | 1303 | — | Helper: LSC+USC+finiteness → ContinuousOn of `.toReal` composition. |
| `MathlibTODO_wassersteinGronwallCoupling_derivBound` | 1354 | — | Mathlib gap: right-derivative Gronwall bound; needs measure-valued ODE coupling. |

---

## Recommended next steps

### Decomposed-parent recommendations

The two open decomposed parents are `MathlibTODO_wassersteinGronwallCoupling_W1ContOn`
(3 sorries: lscNarrow, uscNarrow, W1ContOn_integralContAt, W1ContOn_toRealContOn) and
`MathlibTODO_wassersteinGronwallCoupling` (1 sorry: derivBound).

Ordered by ascending difficulty (Score = 6 − difficulty; residual glue at effective
difficulty 2 / Score 4 ranks ahead of difficulty-2 helpers):

1. **Discharge `W1ContOn_integralContAt` (difficulty 3, Score 3; no deps)**
   This helper derives continuity of `t ↦ ∫ φ d(f t)` from `IsVlasovSolution`'s
   `HasDerivAt`. The route is: `IsVlasovSolution` provides `HasDerivAt (fun s => ∫φ∂(f s)) _ t`
   for every `t`; `HasDerivAt.continuousAt` then gives `ContinuousAt`, and
   `continuous_iff_continuousAt` assembles `Continuous`. This is structurally clean and
   does not depend on any Mathlib gap.
   Hints: `HasDerivAt.continuousAt`, `continuousAt_iff_continuousOn`, `continuous_iff_continuousAt`.

2. **Discharge `W1ContOn_toRealContOn` (difficulty 2, Score 4; depends on
   lscNarrow, uscNarrow — independent attack-order)**
   This helper assembles `ContinuousOn` of `t ↦ (wasserstein1 (f t) (g t)).toReal`
   from LSC + USC + finiteness. The key tactic is
   `ENNReal.continuousOn_toReal.comp (continuousOn_of_forall_lsc_usc ...)` or working
   directly with `ContinuousOn.mono`. `lscNarrow` and `uscNarrow` are Mathlib-gap
   axioms that can be treated as opaque hypotheses at this level — the goal here is
   purely the composition step.
   Hints: `continuousOn_iff_lower_upperSemicontinuousOn`, `ENNReal.continuousOn_toReal`,
   `ContinuousOn.comp`, `LowerSemicontinuousOn.continuousOn_of_upperSemicontinuousOn`.

3. **Discharge `MathlibTODO_wassersteinGronwallCoupling_derivBound` (difficulty
   unrated — genuine Mathlib gap, bare sorry at line 1354)**
   This is the characteristic-flow coupling estimate. It requires:
   (a) the measure-valued Picard theorem for the mean-field ODE (not in Mathlib),
   (b) W₁ triangle inequality under measure pushforward (not in Mathlib's stable OT API).
   This sorry is blocked on upstream Mathlib infrastructure. A placeholder axiom is
   the appropriate treatment until Mathlib's `MeasureTheory.Measure.wasserstein`
   API stabilises.

4. **The `MathlibTODO_W1ContOn_lscNarrow` and `MathlibTODO_W1ContOn_uscNarrow`
   sorries (lines 1233, 1248)** are similarly blocked on KR duality and characteristic
   flow theory respectively.

### Non-decomposed sorry recommendation

5. **`vlasovWellPosedness` (thm:vlasov-wp, bare sorry at line 784)**
   No decomposition plan exists. The statement is: given `f₀` with finite first moment
   and `[AssW W]`, there exists a unique narrowly continuous Vlasov solution with `f 0 = f₀`.
   This is Theorem 1.4 in Dobrushin (1979) / Braun-Hepp (1977), and its Lean proof
   requires: the Picard-Lindelöf theorem applied to the measure-valued ODE (not in Mathlib),
   plus uniqueness from the Dobrushin stability estimate (`dobrushin`, which is available).
   Recommended action: submit a decomposition plan to sorry-decomposer splitting the
   existence part (Picard iteration on probability measures) from the uniqueness part
   (apply `dobrushin` to two solutions with same initial data to get W₁ ≡ 0).
   The uniqueness half is immediately provable from `dobrushin`; the existence half
   is a genuine Mathlib gap.

