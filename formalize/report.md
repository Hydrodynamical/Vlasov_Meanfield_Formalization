# Formalization coverage report

Generated: 2026-05-26
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 4
- Other warnings: 28
- Errors: 0

The 4 sorry warnings are at:
- Line 784: `vlasovWellPosedness` (tex: thm:vlasov-wp)
- Line 1073: `convolveLipschitz_inner_bound` (helper of MathlibTODO_convolveLipschitzEstimate)
- Line 1140: `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (sub-axiom)
- Line 1159: `MathlibTODO_wassersteinGronwallCoupling_derivBound` (sub-axiom)

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
| thm:dobrushin | theorem | `dobrushin` | present |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `meanFieldLimit` | present |

Status values: `present` (proved, no sorry), `present-with-sorry`, `present-stubbed`, `commented-out`, `missing`.

Notes:
- `thm:dobrushin` (`dobrushin`) itself closes via `dobrushin_package_exists` which
  internally invokes `MathlibTODO_wassersteinGronwallCoupling`; the latter
  terminates via two `sorry`-backed sub-axioms. The theorem declaration contains
  no `sorry` at the top level; the sorry cascade is buried in the helper graph.
  See the sorry inventory below.
- `meanFieldLimit` is fully proved (no sorry): it relies on `DobrushinStabilityEstimate`
  as a parameter rather than calling the `dobrushin` proof chain internally.
- All 13 outline items have at least a named Lean declaration. No outline item is
  `missing` or `commented-out`.

## Sorry inventory

### `MathlibTODO_convolveLipschitzEstimate` (no tex-label, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`

This parent has line -1 entries in the plan (helpers not yet placed in the file).
The helpers `convolveLipschitz_inner_lipschitz`, `convolveLipschitz_norm_le_of_inner_forall`
appear in the file (lines 1016 and 1091) as proved lemmas; they are not in the plan's
helper list with positive line numbers. The one sorry-bearing helper that IS in the file is
`convolveLipschitz_inner_bound` (line 1073). `convolveLipschitz_KR_le` (line 1048) is proved.

The parent theorem `MathlibTODO_convolveLipschitzEstimate` (line 1117) is itself proved
(delegates to `convolveLipschitz_norm_le_of_inner_forall` citing `convolveLipschitz_inner_bound`).
The build's sorry warning at line 1073 is entirely within `convolveLipschitz_inner_bound`.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | convolveLipschitz_inner_lipschitz | 1016 | 3 | 3 | (none) | proved |
| 2 | convolveLipschitz_KR_le | 1048 | 2 | 4 | (none) | proved |
| 3 | convolveLipschitz_inner_bound | 1073 | 3 | 3 | inner_lipschitz, KR_le | sorry |
| 4 | convolveLipschitz_norm_le_of_inner_forall | 1091 | 2 | 4 | (none) | proved |

`Score = 6 − Difficulty`.

Residual glue: line -1 (not placed in file); has `tactic_sketch` in plan.
Parent `MathlibTODO_convolveLipschitzEstimate` (line 1117): proved (delegates to helpers).

---

### `MathlibTODO_wassersteinGronwallCoupling` (no tex-label, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

Sub-axioms (genuine Mathlib gaps, blocked on OT infrastructure):
- `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 1140): **sorry**
- `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1159): **sorry**

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | wassersteinGronwallCoupling_gronwall_le | 1182 | 2 | 4 | (none) | proved |
| 2 | wassersteinGronwallCoupling_real_bound | 1202 | 3 | 3 | gronwall_le (+ sub-axioms W1ContOn, derivBound) | proved (sorry-backed) |
| 3 | wassersteinGronwallCoupling_ennreal_mul_comm | 1228 | 1 | 5 | (none) | proved |
| 4 | wassersteinGronwallCoupling_ofReal_le | 1239 | 2 | 4 | real_bound, ennreal_mul_comm | proved (sorry-backed) |

`Score = 6 − Difficulty`.

Residual glue: line 1282 (parent `MathlibTODO_wassersteinGronwallCoupling` body); delegates to
`wassersteinGronwallCoupling_ofReal_le`. Status: proved (no sorry at the parent's line).
The sorry warnings at lines 1140 and 1159 are entirely inside the two sub-axioms; the helper
chain (`real_bound` → `ofReal_le`) composes them successfully.

---

### `weakEvolutionEmpiricalMeasure` (tex: prop:weak, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/weakEvolutionEmpiricalMeasure.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | empiricalMeasure_integral_eq | 226 | 1 | 5 | (none) | proved |
| 2 | hasDerivAt_phi_along_trajectory | 251 | 1 | 5 | (none) | proved |
| 3 | hasDerivAt_empiricalIntegral_sum | 305 | 3 | 3 | 1, 2 | proved |
| 4 | convolveFunctionMeasure_empiricalSpatial_eq | 372 | 3 | 3 | (none) | proved |
| 5 | diagonalCorrection_eq | 412 | 1 | 5 | 4 | proved |
| 6 | diagonalCorrection_bound | 490 | 2 | 4 | (none) | proved |

`Score = 6 − Difficulty`.

Residual glue: line 619 (branch `HasDerivAt` first `?_` branch of parent `refine`);
composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]; `tactic_sketch` present in plan.
Status: proved (no sorry warning at line 619 or parent line 557).

All 6 helpers and the residual glue are **proved**. `weakEvolutionEmpiricalMeasure` is clean.

---

### `dobrushin` (tex: thm:dobrushin, decomposed)

Plan: `/Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/plans/dobrushin.json`

Note: the plan file records file path as `Vlasov/Basic.lean` (the pre-rename path);
the current file is `Vlasov/Vlasov/Basic.lean`. Line numbers below are from the current file
by inspection.

Sub-axioms (genuine Mathlib gaps):
- `MathlibTODO_convolveLipschitzEstimate` (line 1117): theorem proved, backed by `convolveLipschitz_inner_bound` (sorry)
- `MathlibTODO_wassersteinGronwallCoupling` (line 1282): proved, backed by two sorry sub-axioms

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | dobrushin_C_choice | 1300 | 2 | 4 | (none) | proved |
| 2 | convolveDiff_norm_le | 1310 | 4 | 2 | MathlibTODO_convolveLipschitzEstimate | proved (sorry-backed) |
| 3 | wasserstein1_ofReal_exp_monotone | 1323 | 1 | 5 | (none) | proved |
| 4 | dobrushin_ennreal_bound | 1335 | 4 | 2 | dobrushin_C_choice, convolveDiff_norm_le, MathlibTODO_wassersteinGronwallCoupling | proved (sorry-backed) |
| 5 | dobrushin_package_exists | 1361 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | proved (sorry-backed) |

`Score = 6 − Difficulty`.

Residual glue: line 1392 (parent `dobrushin` body); composes [dobrushin_package_exists].
`tactic_sketch` present in plan. Status: proved (no sorry at line 1392).

`dobrushin` itself is proved; the sorry cascade is isolated within two `MathlibTODO_*` placeholders.

---

### Non-decomposed sorries (flat table)

| Line | Enclosing declaration | Tex label | Notes |
|------|-----------------------|-----------|-------|
| 784 | `vlasovWellPosedness` | thm:vlasov-wp | Single top-level sorry; the existence-and-uniqueness theorem for Vlasov is a known Mathlib gap |
| 1073 | `convolveLipschitz_inner_bound` | (none — helper of MathlibTODO_convolveLipschitzEstimate) | Key inner-product-versus-KR-dual estimate; see decomposed section above |
| 1140 | `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | (none — sub-axiom) | Narrow continuity of W₁ along Vlasov flows; requires Mathlib measure-ODE API |
| 1159 | `MathlibTODO_wassersteinGronwallCoupling_derivBound` | (none — sub-axiom) | Differential inequality for W₁; requires characteristic flow coupling + pushforward contraction |

## Recommended next steps

### Decomposed parent: `MathlibTODO_convolveLipschitzEstimate`

The only open helper is `convolveLipschitz_inner_bound` (difficulty 3, Score 3). All other helpers
in this cluster are proved. Closing this one sorry would make the entire `MathlibTODO_convolveLipschitzEstimate`
cascade sorry-free (it already delegates correctly to the helper).

1. **Discharge `convolveLipschitz_inner_bound` (line 1073, difficulty 3, Score 3; no deps).**
   The goal is: for any `v : PhysSpace d` with `‖v‖ ≤ 1`,
   `⟨(∇W∗ρ)(x) − (∇W∗σ)(x), v⟩ ≤ L * (wasserstein1 ρ σ).toReal`.
   Strategy: unfold `convolveFunctionMeasure` to expose `∫ gradW(x−y) dρ` and `∫ gradW(x−y) dσ`;
   commute `⟨·, v⟩` (a CLM) through each integral via `ContinuousLinearMap.integral_comp_comm`;
   the integrand `y ↦ ⟨gradW(x−y), v⟩` is `LipschitzWith (L * ‖v‖₊)` by
   `convolveLipschitz_inner_lipschitz` (already proved); since `‖v‖ ≤ 1` this is
   `LipschitzWith L`-or-less, so rescale by `L⁻¹` to get a 1-Lipschitz function and apply
   `convolveLipschitz_KR_le` (already proved, at line 1048).
   Hints: `ContinuousLinearMap.integral_comp_comm`, `integral_sub`, `norm_integral_le_integral_norm`,
   `real_inner_le_norm`, `convolveLipschitz_inner_lipschitz`, `convolveLipschitz_KR_le`.

### Decomposed parent: `MathlibTODO_wassersteinGronwallCoupling`

The two open sorries (`W1ContOn` and `derivBound`) are classified as genuine Mathlib gaps:
they require narrow continuity of Wasserstein-1 along measure-valued ODE flows, and the
characteristic flow coupling argument + W₁ triangle inequality under pushforward. Neither is
in Mathlib's stable API. These are the deepest unresolved blockers.

2. **Discharge `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 1140, difficulty 2, Score 4).**
   States that `t ↦ (wasserstein1 (f t) (g t)).toReal` is `ContinuousOn [0, T]` for two Vlasov
   solutions `f, g`. This is a consequence of narrow continuity of Vlasov solutions (itself a
   `HasFiniteFirstMoment`-type corollary) and continuity of Wasserstein distance under narrow
   convergence. Hints from the Gronwall plan: `le_gronwallBound_of_liminf_deriv_right_le`,
   `gronwallBound_ε0`, `gronwallBound_x0`. Mathlib's `MeasureTheory.ProbabilityMeasure`
   API and `NNReal.tendsto_coe_iff` are relevant entry points.

3. **Discharge `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1159, difficulty 3, Score 3).**
   States the liminf right-derivative bound: `C * W₁(f_s, g_s) < r ⟹ ∃ᶠ z ...` for the
   Gronwall wrapper. This requires the characteristic flow coupling argument — pairing particles
   of `f` and `g` via the same initial label — plus the `MathlibTODO_convolveLipschitzEstimate`
   estimate (which will be fully proved once step 1 is closed). Hints: `LipschitzWith.dist_le_mul`,
   `ENNReal.ofReal_le_ofReal`, `iSup_le`, `le_iSup`.

### Non-decomposed sorry: `vlasovWellPosedness`

4. **Discharge `vlasovWellPosedness` (line 784, single sorry, tex: thm:vlasov-wp).**
   This is the existence-and-uniqueness theorem for the Vlasov equation. It requires a
   fixed-point / Picard iteration for the characteristic mean-field ODE at the measure level,
   which depends on compactness and narrowly-continuous measure-valued ODE theory — not yet
   in Mathlib. The recommended approach is decomposition via sorry-decomposer: extract
   (a) a fixed-point iteration helper, (b) uniqueness via Dobrushin stability (already proved
   as `dobrushin`), and (c) a narrow-continuity assertion. The `dobrushin` chain can serve as
   the uniqueness component. Consider filing a decomposition plan JSON for this theorem.

### Priority order summary

| Priority | Target | Score | Rationale |
|----------|--------|-------|-----------|
| 1 | `convolveLipschitz_inner_bound` (line 1073) | 3 | Closes the entire `MathlibTODO_convolveLipschitzEstimate` cascade; no Mathlib gaps, pure functional-analysis tactics |
| 2 | `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 1140) | 4 | Lower difficulty but requires ODE continuity API; unblocks `derivBound` |
| 3 | `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1159) | 3 | Deepest gap; benefits from step 1 being closed first |
| 4 | `vlasovWellPosedness` (line 784) | — | Largest scope; recommend decomposition plan first |
