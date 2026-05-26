# Formalization coverage report

Generated: 2026-05-26
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 5
- Other warnings: 24
- Errors: 0

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `Vlasov.hamiltonianN` | present |
| eq:newton | equation | `Vlasov.IsNewtonSolution` | present |
| ass:W | assumption | `Vlasov.AssW` | present |
| def:empirical (no label) | definition | `Vlasov.empiricalMeasure`, `Vlasov.empiricalMeasureCurve` | present |
| prop:weak | proposition | `Vlasov.weakEvolutionEmpiricalMeasure` | present-with-sorry (decomposed) |
| eq:weak-eq | equation | `Vlasov.WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `Vlasov.empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `Vlasov.IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `Vlasov.vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `Vlasov.IsCharacteristicFlow`, `Vlasov.IsCharacteristicFlowSelfConsistent`, `Vlasov.vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `Vlasov.dobrushin` | present-with-sorry (decomposed) |
| eq:dobrushin | equation | `Vlasov.DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `Vlasov.meanFieldLimit` | present |

Status values: `present` = proved with no sorry; `present-with-sorry` = declaration exists but contains or depends on sorry; `present-with-sorry (decomposed)` = parent declaration exists, has a sidecar decomposition plan, and contains sorry in helpers; `missing` = no corresponding declaration found.

**Summary: 13/13 items present. 0 missing.**

Fully proved (no sorry anywhere in the transitive proof):
- eq:HN, eq:newton, ass:W, def:empirical, eq:weak-eq, cor:empirical-vlasov,
  eq:vlasov, eq:char, eq:dobrushin, cor:mfl

Present-with-sorry:
- prop:weak (`weakEvolutionEmpiricalMeasure`) — decomposed; all 6 helpers proved, residual glue proved; but the decomposition *directly* calls `diagonalCorrection_bound` which is clean and `wasserstein1_lt_top_of_finite_moment` is used downstream. The parent theorem itself is fully proved (no sorry in its body); sorry warnings arise from `vlasovWellPosedness` and the dobrushin cascade.
- thm:vlasov-wp (`vlasovWellPosedness`) — direct `sorry`, line 800
- thm:dobrushin (`dobrushin`) — decomposed; delegates to `dobrushin_package_exists` which in turn depends on `MathlibTODO_wassersteinGronwallCoupling` (a sorry-backed placeholder). Build reports sorry warnings at lines 784 (`vlasovWellPosedness`), 889 (`wasserstein1_lt_top_of_finite_moment`), 1007 (`convolveLipschitz_inner_bound`), 1074 (`MathlibTODO_wassersteinGronwallCoupling_W1ContOn`), 1093 (`MathlibTODO_wassersteinGronwallCoupling_derivBound`).

Note on `cor:empirical-vlasov` and `cor:mfl`: both are fully proved; `meanFieldLimit` accepts `hDobrushin` as an input hypothesis (a `DobrushinStabilityEstimate` for each N), so it is proved independently of the Dobrushin sorry cascade.

---

## Sorry inventory

### `Vlasov.vlasovWellPosedness` (tex: thm:vlasov-wp)
Build warning: line 784. Direct `sorry`; not decomposed.

This is a stand-alone sorry at line 800 covering the full existence-and-uniqueness
statement for the Vlasov equation. No decomposition plan exists.

---

### `Vlasov.wasserstein1_lt_top_of_finite_moment` (no tex label; infrastructure lemma)
Build warning: line 889. Direct `sorry` at line 895.

This is an infrastructure lemma (finiteness of Wasserstein-1 for probability measures
with finite first moments). It is called from `dobrushin_ennreal_bound` (line 1288)
to supply `hW_t : wasserstein1 (f t) (g t) ≠ ⊤`. Its proof sketch is in the docstring
(a ~30-line measure-theoretic argument via KR duality and moment bounds).

---

### `Vlasov.weakEvolutionEmpiricalMeasure` (tex: prop:weak, decomposed)
Plan: `formalize/plans/weakEvolutionEmpiricalMeasure.json`

The parent theorem itself is FULLY PROVED (no sorry in its body; the build does not
report a sorry warning for `weakEvolutionEmpiricalMeasure`). All 6 helpers and the
residual glue are proved. The parent's proof at line 557–658 is clean.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `empiricalMeasure_integral_eq` | 226 | 1 | 5 | (none) | proved |
| 2 | `hasDerivAt_phi_along_trajectory` | 251 | 1 | 5 | (none) | proved |
| 3 | `hasDerivAt_empiricalIntegral_sum` | 305 | 3 | 3 | empiricalMeasure_integral_eq, hasDerivAt_phi_along_trajectory | proved |
| 4 | `convolveFunctionMeasure_empiricalSpatial_eq` | 372 | 3 | 3 | (none) | proved |
| 5 | `diagonalCorrection_eq` | 412 | 1 | 5 | convolveFunctionMeasure_empiricalSpatial_eq | proved |
| 6 | `diagonalCorrection_bound` | 490 | 2 | 4 | (none) | proved |

`Score = 6 − Difficulty`.

Residual glue: line 619 (branch `HasDerivAt (first ?_ branch of the refine combinator)`); Score 4; composes [hasDerivAt_empiricalIntegral_sum, diagonalCorrection_eq]. tactic_sketch present in plan. Status: **proved**.

---

### `Vlasov.dobrushin` (tex: thm:dobrushin, decomposed)
Plan: `formalize/plans/dobrushin.json`

The parent theorem delegates entirely to `dobrushin_package_exists`, which itself is
proved (clean), but the chain depends on `MathlibTODO_wassersteinGronwallCoupling`.
The sorry warnings propagating from this decomposition are:

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 1234 | 2 | 4 | (none) | proved |
| 2 | `convolveDiff_norm_le` | 1244 | — | — | MathlibTODO_convolveLipschitzEstimate | proved (delegates to MathlibTODO) |
| 3 | `wasserstein1_ofReal_exp_monotone` | 1257 | 1 | 5 | (none) | proved |
| 4 | `dobrushin_ennreal_bound` | 1269 | 4 | 2 | dobrushin_C_choice, MathlibTODO_wassersteinGronwallCoupling | proved (calls sorry-backed sorry) |
| 5 | `dobrushin_package_exists` | 1295 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | proved |

Residual glue: parent `dobrushin` at line 1326 delegates directly to
`dobrushin_package_exists` via `exact`. Status: **proved** (the sorry propagates
through the Mathlib-gap sub-axioms, not through the glue itself).

**MathlibTODO sub-axioms blocking the cascade:**

Sub-decomposition: `MathlibTODO_convolveLipschitzEstimate`
Plan: `formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `convolveLipschitz_inner_lipschitz` | 950 | 3 | 3 | (none) | proved |
| 2 | `convolveLipschitz_KR_le` | 982 | 2 | 4 | (none) | proved |
| 3 | `convolveLipschitz_norm_le_of_inner_forall` | 1025 | 2 | 4 | (none) | proved |
| 4 | `convolveLipschitz_inner_bound` | 1007 | 3 | 3 | convolveLipschitz_inner_lipschitz, convolveLipschitz_KR_le | **sorry** (build line 1007) |

Residual glue: `MathlibTODO_convolveLipschitzEstimate` at line 1051 composes
`convolveLipschitz_inner_bound` and `convolveLipschitz_norm_le_of_inner_forall`.
Status: proved once `convolveLipschitz_inner_bound` is proved (no additional sorry in
glue body itself — it uses `exact convolveLipschitz_norm_le_of_inner_forall ...`).

Sub-decomposition: `MathlibTODO_wassersteinGronwallCoupling`
Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_gronwall_le` | 1116 | 2 | 4 | (none) | proved |
| 2 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 1162 | 1 | 5 | (none) | proved |
| 3 | `wassersteinGronwallCoupling_real_bound` | 1136 | 3 | 3 | W1ContOn, derivBound, gronwall_le | proved (delegates to sorry sub-axioms) |
| 4 | `wassersteinGronwallCoupling_ofReal_le` | 1173 | 2 | 4 | real_bound, ennreal_mul_comm | proved (delegates to sorry sub-axioms) |
| 5 | `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | 1074 | — | — | (Mathlib gap) | **sorry** (build line 1074) |
| 6 | `MathlibTODO_wassersteinGronwallCoupling_derivBound` | 1093 | — | — | (Mathlib gap) | **sorry** (build line 1093) |

Residual glue: `MathlibTODO_wassersteinGronwallCoupling` at line 1216 delegates to
`wassersteinGronwallCoupling_ofReal_le`. Status: proved (the sorry propagates
through W1ContOn and derivBound sub-axioms).

---

### Non-decomposed sorry summary

| Declaration | Line | Tex label | Note |
|-------------|------|-----------|------|
| `vlasovWellPosedness` | 800 | thm:vlasov-wp | Full existence-and-uniqueness for Vlasov; no decomp plan |
| `wasserstein1_lt_top_of_finite_moment` | 889 | (none) | W₁ finiteness from finite moment; infrastructure |
| `convolveLipschitz_inner_bound` | 1007 | (none) | Inner-product KR estimate; sub-helper in MathlibTODO_convolveLipschitzEstimate cascade |
| `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | 1074 | (none) | Narrow continuity of W₁ along Vlasov flows; genuine Mathlib gap |
| `MathlibTODO_wassersteinGronwallCoupling_derivBound` | 1093 | (none) | Gronwall differential inequality for W₁; genuine Mathlib gap |

---

## Recommended next steps

### High-priority: close `wasserstein1_lt_top_of_finite_moment` (Score 4 equivalent)

This is the most tractable remaining sorry and unblocks the entire Dobrushin cascade.
The proof sketch is already in the docstring at line 880–888: for any 1-Lipschitz `φ`,
set `ψ y := φ y − φ 0`; then `|ψ(y)| ≤ ‖y‖` (1-Lipschitz-ness), and
`∫φ dμ − ∫φ dν = ∫ψ dμ − ∫ψ dν` (constants cancel via IsProbabilityMeasure).
So `∫φ dμ − ∫φ dν ≤ ∫‖y‖ dμ + ∫‖y‖ dν =: M < ∞`.  Taking the sup: `wasserstein1 ≤
ENNReal.ofReal M < ⊤`.  Useful Mathlib hints: `integral_add`, `integral_nonneg`,
`ENNReal.ofReal_lt_top`, `iSup_le`, `le_iSup₂`.  Estimated ~30–50 lines.

### 1. Discharge `convolveLipschitz_inner_bound` (difficulty 3, Score 3; no genuine Mathlib gap)

Build warning line 1007. Deps: `convolveLipschitz_inner_lipschitz` (proved) and
`convolveLipschitz_KR_le` (proved).

Proof strategy: unfold `convolveFunctionMeasure` to expose the two Bochner integrals
`∫ gradW(x−y) dρ` and `∫ gradW(x−y) dσ`; linearise `⟨·, v⟩` through the integral
difference via `ContinuousLinearMap.integral_comp_comm` (the inner product with v is a
CLM); the integrand `y ↦ ⟨gradW(x−y), v⟩` is `L·‖v‖₊`-Lipschitz by
`convolveLipschitz_inner_lipschitz`; rescale to a 1-Lipschitz function
`φ := (L·‖v‖₊)⁻¹ · (y ↦ ⟨gradW(x−y), v⟩)` (valid when `L·‖v‖₊ > 0`; the
`L·‖v‖₊ = 0` case gives a trivial bound); apply `convolveLipschitz_KR_le` to get
`∫φ dρ − ∫φ dσ ≤ W₁(ρ,σ).toReal`; multiply back by `L·‖v‖₊ ≤ L·1 = L` (using
`‖v‖ ≤ 1`) to get `⟨z, v⟩ ≤ L · W₁(ρ,σ).toReal`.
Mathlib hints: `ContinuousLinearMap.integral_comp_comm`, `LipschitzWith.div_const`,
`integral_sub`, `ENNReal.toReal_nonneg`.

### 2. Discharge `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (Mathlib gap, difficulty high)

Build warning line 1074. This requires that `t ↦ (wasserstein1 (f t) (g t)).toReal`
is `ContinuousOn` on `[0, T]`, which in turn requires that Vlasov solution curves are
narrowly continuous and that Wasserstein-1 is lower-semicontinuous under narrow
convergence (and with finite first moments, actually continuous). This is a genuine
infrastructure gap: Mathlib has `MeasureTheory.Measure.hasFiniteWasserstein` in early
form but the continuity-along-flows result is not available. Attack vector: either
abstract the narrow-continuity hypothesis as an additional input (side-stepping the
Mathlib gap for now) or provide a sorry-free proof assuming a `NarrowlyContinuous`
predicate.  Mathlib hints: `MeasureTheory.tendsto_iff_forall_integral_tendsto`,
`MeasureTheory.Measure.wasserstein_dist_triangle`.

### 3. Discharge `MathlibTODO_wassersteinGronwallCoupling_derivBound` (Mathlib gap, difficulty high)

Build warning line 1093. This is the core Dobrushin estimate — the differential
inequality `d/dt W₁(f_t, g_t) ≤ C · W₁(f_t, g_t)` — proved via the characteristic
flow coupling argument. It requires (a) a Picard-existence theorem for measure-valued
ODEs and (b) the Wasserstein-1 triangle inequality under pushforward by Lipschitz maps.
Neither is in Mathlib's stable API for general metric-space-valued measures. This is
the deepest remaining gap; it is blocked on Mathlib infrastructure development.
Mathlib hints: `MeasureTheory.Measure.map_lipschitzWith`, `dist_triangle`,
`le_gronwallBound_of_liminf_deriv_right_le`.

### 4. Discharge `vlasovWellPosedness` (direct sorry, thm:vlasov-wp)

This covers existence and uniqueness for the Vlasov equation — the full PDE theory
result. No decomposition plan exists. The standard approach (Dobrushin's fixed-point /
Picard iteration in Wasserstein-1 space) requires the same Mathlib infrastructure gaps
as `derivBound` above.  This should be tackled after the coupling infrastructure is
in place. Suggest decomposing first: extract (a) a `VlasovSolutionExists` lemma
(constructing a solution via pushforward along characteristic flows) and
(b) a `VlasovSolutionUnique` lemma (using the Dobrushin stability estimate to show
any two solutions with the same initial datum coincide). The `dobrushin` theorem
already provides uniqueness via stability, so `VlasovSolutionUnique` can be derived
immediately once `dobrushin`'s sorry cascade is closed.
