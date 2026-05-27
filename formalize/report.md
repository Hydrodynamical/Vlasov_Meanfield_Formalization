# Formalization coverage report

Generated: 2026-05-26
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 7
- Other warnings: 28
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` | present |
| eq:newton | equation | `IsNewtonSolution` | present |
| ass:W | assumption | `class AssW` + `gradient_zero_of_even` (helper) | present |
| def:empirical | definition | `empiricalMeasure` + `empiricalMeasure_isProbabilityMeasure` + `empiricalMeasureCurve` | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` | present |
| eq:weak-eq | equation | `WeakEvolutionEq` (Prop-valued def) | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `IsVlasovSolution` (Prop-valued def) | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow` + `IsCharacteristicFlowSelfConsistent` + `vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `dobrushin` | present-with-sorry (via `MathlibTODO_wassersteinGronwallCoupling`) |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` (Prop-valued def) | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

Status values used: `present` (no sorry in declaration chain), `present-with-sorry` (declaration exists but contains or transitively depends on a sorry).

**Summary: 13/13 outline items present. 2 items carry sorry (thm:vlasov-wp, thm:dobrushin). 11 items fully sorry-free.**

---

## Sorry inventory

### `Vlasov.vlasovWellPosedness` (tex: thm:vlasov-wp, non-decomposed)

Line 784 (inside the theorem body). No decomposition plan. Existential well-posedness for the Vlasov PDE requires a full measure-valued Picard–Lindelof theorem and uniqueness argument that is not in Mathlib's stable API.

| Declaration | Line | Status |
|-------------|------|--------|
| `vlasovWellPosedness` | 784 | sorry |

---

### `Vlasov.MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (tex: none, decomposed)

Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json`

The parent is the W1 continuity sub-axiom needed by the Gronwall cascade. It is decomposed into three helpers plus two Mathlib-gap sub-axioms (LSC and USC of W1 along Vlasov flows). The plan records line numbers as -1 for helpers (lines were not finalised at decomposition time); actual Lean lines are noted from the file.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `W1ContOn_lt_top` | 1265 | 2 | 4 | (none) | proved |
| 2 | `W1ContOn_integralContAt` | 1283 | 3 | 3 | (none) | sorry |
| 3 | `W1ContOn_toRealContOn` | 1303 | 2 | 4 | W1ContOn_lt_top, MathlibTODO_W1ContOn_lscNarrow, MathlibTODO_W1ContOn_uscNarrow | sorry |
| Glue sub-axiom A | `MathlibTODO_W1ContOn_lscNarrow` | 1233 | — | — | — | sorry (Mathlib gap) |
| Glue sub-axiom B | `MathlibTODO_W1ContOn_uscNarrow` | 1248 | — | — | — | sorry (Mathlib gap) |

`Score = 6 − Difficulty` for helpers.

Residual glue: line 1346 (branch `main body of MathlibTODO_wassersteinGronwallCoupling_W1ContOn`); Score 4; composes [W1ContOn_lt_top, W1ContOn_toRealContOn, MathlibTODO_W1ContOn_lscNarrow, MathlibTODO_W1ContOn_uscNarrow]. tactic_sketch present in plan:
```
exact W1ContOn_toRealContOn gradW L hL f g hf hg hf_prob hg_prob T hT
```

**Note on sorry lines 1233 and 1248**: `MathlibTODO_W1ContOn_lscNarrow` and `MathlibTODO_W1ContOn_uscNarrow` are Mathlib gap theorems (LSC/USC of W1 under narrow convergence). These represent genuine missing Mathlib infrastructure (KR duality for non-compactly-supported test functions, characteristic flow coupling). They are not helpers in the standard decomposition sense—they cannot be discharged without new Mathlib API.

---

### `Vlasov.MathlibTODO_wassersteinGronwallCoupling_derivBound` (tex: none, non-decomposed)

Line 1354 (inside the theorem body). The right-derivative Gronwall bound for the Wasserstein-1 coupling. Requires the characteristic flow coupling argument and the W1 triangle inequality under measure pushforward—neither is in Mathlib's stable API for measure-valued ODEs. No decomposition plan.

| Declaration | Line | Status |
|-------------|------|--------|
| `MathlibTODO_wassersteinGronwallCoupling_derivBound` | 1354 | sorry (Mathlib gap) |

---

### `Vlasov.MathlibTODO_wassersteinGronwallCoupling` (tex: none, decomposed via plan)

Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

This parent is proved by delegation to `wassersteinGronwallCoupling_ofReal_le`, which itself depends on `wassersteinGronwallCoupling_real_bound`, which in turn depends on the two sub-axioms `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` and `MathlibTODO_wassersteinGronwallCoupling_derivBound`. The parent theorem body at line 1477 is already closed (it merely calls `wassersteinGronwallCoupling_ofReal_le`); the remaining sorries in this cascade are in the sub-axioms listed above.

Helpers recorded in the plan with their current status (derived from sorry warnings):

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_gronwall_le` | 1377 | 2 | 4 | (none) | proved |
| 2 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 1423 | 1 | 5 | (none) | proved |
| 3 | `wassersteinGronwallCoupling_real_bound` | 1397 | 3 | 3 | wassersteinGronwallCoupling_gronwall_le | proved |
| 4 | `wassersteinGronwallCoupling_ofReal_le` | 1434 | 2 | 4 | wassersteinGronwallCoupling_real_bound, wassersteinGronwallCoupling_ennreal_mul_comm | proved |

All four helpers in the `MathlibTODO_wassersteinGronwallCoupling` decomposition plan are proved. The residual sorry in this cascade traces to `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 1315) and `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1354), which are the genuine Mathlib gaps.

---

### `Vlasov.dobrushin` (tex: thm:dobrushin, decomposed)

Plan: `formalize/plans/dobrushin.json`

The parent is closed (line 1590 calls `dobrushin_package_exists` directly). The plan records a slightly different file path (pre-refactor); lines are resolved from the current file.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 1495 | 2 | 4 | (none) | proved |
| 2 | `wasserstein1_ofReal_exp_monotone` | 1521 | 1 | 5 | (none) | proved |
| 3 | `dobrushin_ennreal_bound` | 1533 | 4 | 2 | dobrushin_C_choice, convolveDiff_norm_le | proved (delegates to MathlibTODO_wassersteinGronwallCoupling) |
| 4 | `dobrushin_package_exists` | 1559 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | proved |
| 5 | `convolveDiff_norm_le` | 1505 | — | — | MathlibTODO_convolveLipschitzEstimate | proved (wrapper over MathlibTODO) |

All dobrushin-plan helpers are proved. The parent `dobrushin` body (line 1590) is also proved. The `sorry` in this cascade traces entirely to `MathlibTODO_wassersteinGronwallCoupling` (and its sub-axioms), not to the dobrushin helpers themselves.

---

### `Vlasov.weakEvolutionEmpiricalMeasure` (tex: prop:weak, decomposed)

Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | proved |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 372 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 412 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 490 | 2 | 4 | (none) | proved |

Residual glue: line 619 (branch `HasDerivAt first ?_ branch`); Score 4; composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. tactic_sketch present in plan. **Status: proved** (no sorry warning at line 619; the parent `weakEvolutionEmpiricalMeasure` has no sorry warning).

All helpers proved. Parent theorem `weakEvolutionEmpiricalMeasure` is fully proved.

---

### `Vlasov.MathlibTODO_convolveLipschitzEstimate` (tex: none, decomposed)

Plan: `formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`

The plan records lines as -1 (pre-insertion); actual lines resolved from the file.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `convolveLipschitz_KR_le` | 1048 | 2 | 4 | (none) | proved |
| 2 | `convolveLipschitz_norm_le_of_inner_forall` | 1179 | 2 | 4 | (none) | proved |
| 3 | `convolveLipschitz_inner_lipschitz` | 1016 | 3 | 3 | (none) | proved |
| 4 | `convolveLipschitz_inner_bound` | 1073 | 3 | 3 | convolveLipschitz_inner_lipschitz, convolveLipschitz_KR_le | proved |

Residual glue: parent body at line 1205 (`MathlibTODO_convolveLipschitzEstimate`). **Status: proved** (no sorry warning). The parent is closed by calling `convolveLipschitz_norm_le_of_inner_forall` + `convolveLipschitz_inner_bound`.

All helpers proved. `MathlibTODO_convolveLipschitzEstimate` is fully proved despite the `MathlibTODO_` name.

---

### Flat sorry table (non-decomposed, Mathlib-gap sorries)

| Line | Declaration | Nature |
|------|-------------|--------|
| 784 | `vlasovWellPosedness` | Standalone sorry; Vlasov PDE well-posedness (measure-valued Picard, uniqueness) not in Mathlib |
| 1233 | `MathlibTODO_W1ContOn_lscNarrow` | Mathlib gap: LSC of W1 under narrow convergence (KR duality for non-compactly-supported Lip functions) |
| 1248 | `MathlibTODO_W1ContOn_uscNarrow` | Mathlib gap: USC of W1 along Vlasov flows (characteristic flow coupling + W1 pushforward contraction) |
| 1283 | `W1ContOn_integralContAt` | Helper sorry: t-continuity of integral of test fn against Vlasov solution |
| 1303 | `W1ContOn_toRealContOn` | Helper sorry: assembling LSC+USC+finiteness into ContinuousOn of toReal composition |
| 1315 | `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | Composite sorry: residual glue of W1ContOn decomposition, blocked on sub-axioms 1233, 1248, 1283, 1303 |
| 1354 | `MathlibTODO_wassersteinGronwallCoupling_derivBound` | Mathlib gap: right-derivative Gronwall bound via characteristic flow coupling |

---

## Recommended next steps

### Decomposed parents with open helpers

**W1ContOn cascade** (`MathlibTODO_wassersteinGronwallCoupling_W1ContOn`): two helpers remain open. Ordered by ascending difficulty (tractability-first), with leaf-first tie-breaking:

1. Discharge `W1ContOn_integralContAt` (difficulty 3, Score 3; no deps; line 1283).
   Mathematical content: given `IsVlasovSolution gradW f`, which provides `HasDerivAt (fun s => ∫ φ ∂(f s)) (derivative) t` for all t, conclude `Continuous (fun t => ∫ φ ∂(f t))` by assembling `HasDerivAt.continuousAt` pointwise into `continuous_iff_continuousAt`.
   Mathlib hints: `HasDerivAt.continuousAt`, `ContinuousAt.continuousOn`, `continuous_iff_continuousAt`.

2. Discharge `W1ContOn_toRealContOn` (difficulty 2, Score 4; depends on `W1ContOn_lt_top` [proved], `MathlibTODO_W1ContOn_lscNarrow` [Mathlib gap], `MathlibTODO_W1ContOn_uscNarrow` [Mathlib gap]; line 1303).
   This helper is blocked on the two Mathlib-gap sub-axioms below. Attack-order is independent (Lean treats sorried names as opaque), but the proof will only be meaningful once those gaps are filled.
   Mathlib hints: `continuousOn_iff_lower_upperSemicontinuousOn`, `ENNReal.continuousOn_toReal`, `ContinuousOn.comp`.

3. Discharge residual glue at line 1346 (Score 4); has machine-executable `tactic_sketch` in the plan:
   ```
   exact W1ContOn_toRealContOn gradW L hL f g hf hg hf_prob hg_prob T hT
   ```
   This is the fast-path close once `W1ContOn_toRealContOn` is proved.

### Non-decomposed Mathlib-gap sorries

The following are genuine Mathlib gaps. They cannot be discharged by tactic manipulation alone; they require either upstream Mathlib additions or structural reformulation of the statement.

4. **`MathlibTODO_W1ContOn_lscNarrow`** (line 1233). LSC of Wasserstein-1 under narrow convergence of the measure argument. Mathlib's `MeasureTheory.Measure.restrict`-based optimal transport infrastructure does not yet expose KR duality for unbounded (non-compactly-supported) 1-Lipschitz test functions. Suggested path: reformulate using Mathlib's `MeasureTheory.Measure.FiniteWasserstein` if/when it reaches stable API, or use compactly-supported approximation + monotone convergence.

5. **`MathlibTODO_W1ContOn_uscNarrow`** (line 1248). USC of Wasserstein-1 along Vlasov solution curves. Requires the characteristic flow coupling argument (pairing two Vlasov solutions via a common label ODE and estimating the cost of the resulting coupling plan) and the W1 triangle inequality under pushforward. Neither the measure-valued Picard theorem nor the W1 pushforward contraction is in Mathlib's stable API.

6. **`MathlibTODO_wassersteinGronwallCoupling_derivBound`** (line 1354). Right-derivative Gronwall bound for the Wasserstein-1 coupling. Companion to `MathlibTODO_W1ContOn_uscNarrow`; shares the same missing Mathlib API (measure-valued ODE Picard theory + W1 pushforward triangle inequality). Both 5 and 6 will be unblocked by the same upstream additions.

7. **`vlasovWellPosedness`** (line 784). Existence and uniqueness for the Vlasov PDE. Requires a full infinite-dimensional Picard–Lindelof theorem for the McKean–Vlasov equation in the space of probability measures, plus a uniqueness argument. This is the most structurally complex outstanding sorry and will require the same infrastructure as 5 and 6, plus additional uniqueness arguments. It is lowest priority given that `dobrushin` and `meanFieldLimit` are already proved using separate hypotheses.
