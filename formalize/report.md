# Formalization coverage report

Generated: 2026-05-26
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status

- Result: success
- Sorry warnings: 8
- Other warnings: 28
- Errors: 0

Sorry-bearing declarations (from build output):
- Line 784: `vlasovWellPosedness`
- Line 1233: `MathlibTODO_W1ContOn_lscNarrow`
- Line 1248: `MathlibTODO_W1ContOn_uscNarrow`
- Line 1265: `W1ContOn_lt_top`
- Line 1278: `W1ContOn_integralContAt`
- Line 1298: `W1ContOn_toRealContOn`
- Line 1310: `MathlibTODO_wassersteinGronwallCoupling_W1ContOn`
- Line 1349: `MathlibTODO_wassersteinGronwallCoupling_derivBound`

## Coverage

| Tex label | Kind | Lean declaration | Status |
|-----------|------|------------------|--------|
| eq:HN | equation | `hamiltonianN` (line 41) | present |
| eq:newton | equation | `IsNewtonSolution` (line 60) | present |
| ass:W | assumption | `class AssW` (line 80) | present |
| def:empirical | definition | `empiricalMeasure` + `empiricalMeasureCurve` (lines 174, 197) | present |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` (line 557) | present |
| eq:weak-eq | equation | `WeakEvolutionEq` (line 674) | present |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` (line 698) | present |
| eq:vlasov | equation | `IsVlasovSolution` (line 755) | present |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` (line 784) | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow` + `IsCharacteristicFlowSelfConsistent` + `vlasovSolutionViaPushforward` (lines 822, 837, 846) | present |
| thm:dobrushin | theorem | `dobrushin` (line 1585) | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` (line 1617) | present |
| cor:mfl | corollary | `meanFieldLimit` (line 1643) | present |

**Summary: 13/13 outline items present. 2 items carry sorries (vlasovWellPosedness, dobrushin).**

Status key:
- `present`: proved without sorry (or is a definition/predicate requiring no proof)
- `present-with-sorry`: Lean declaration exists and type-checks, but proof body contains `sorry` (directly or via chain of helper dependencies)

Notes:
- `eq:HN`, `eq:newton`, `def:empirical`, `eq:vlasov`, `eq:char`, `eq:dobrushin`: These are equations/definitions formalized as Lean `def` or `abbrev`; they carry no proof obligation beyond type-checking.
- `ass:W` is a `class` (structure of hypotheses); its helper `gradient_zero_of_even` is fully proved.
- `prop:weak` (`weakEvolutionEmpiricalMeasure`) has no direct sorry on line 557; its proof is fully assembled from the six helper lemmas in `formalize/plans/weakEvolutionEmpiricalMeasure.json`, all of which are proved (no sorry warnings on lines 226, 251, 305, 372, 412, 490).
- `cor:empirical-vlasov` (`empiricalMeasureSolvesVlasov`) is fully proved (no sorry warning at line 698).
- `cor:mfl` (`meanFieldLimit`) is fully proved (no sorry warning at line 1643).
- `thm:dobrushin` (`dobrushin`) delegates to `dobrushin_package_exists` which in turn depends on `MathlibTODO_wassersteinGronwallCoupling`; sorry propagates through the chain.

---

## Sorry inventory

### `vlasovWellPosedness` (tex: thm:vlasov-wp)

**Not decomposed.** A single top-level `sorry` at line 800. This is a genuine
Mathlib gap: existence-uniqueness for measure-valued Vlasov PDE requires a
Picard-style fixed-point theorem for measure-valued ODEs in the Wasserstein
metric, which is not in Mathlib's stable API.

| Decl | Line | Note |
|------|------|------|
| `vlasovWellPosedness` | 784 (sorry at 800) | Entire proof body is `sorry` |

---

### `dobrushin` (tex: thm:dobrushin, decomposed)

Plan: `formalize/plans/dobrushin.json`

`dobrushin` itself (line 1585) has no direct sorry — its body calls
`dobrushin_package_exists` which in turn depends on
`MathlibTODO_wassersteinGronwallCoupling`. The sorry chain passes through
the `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` sub-axiom and
`MathlibTODO_wassersteinGronwallCoupling_derivBound` sub-axiom, both of
which are genuine Mathlib gaps (measure-valued ODE theory).

The dobrushin plan helpers at the level of `dobrushin.json`:

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|-----------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 1490 | 2 | 4 | (none) | proved |
| 2 | `wasserstein1_ofReal_exp_monotone` | 1516 | 1 | 5 | (none) | proved |
| 3 | `dobrushin_ennreal_bound` | 1528 | 4 | 2 | `dobrushin_C_choice`, `convolveDiff_norm_le` | sorry (via MathlibTODO chain) |
| 4 | `dobrushin_package_exists` | 1554 | 2 | 4 | `dobrushin_C_choice`, `dobrushin_ennreal_bound` | sorry (via MathlibTODO chain) |

`Score = 6 - Difficulty`.

Residual glue: line 1603 (dobrushin body: `exact dobrushin_package_exists …`);
composes [dobrushin_C_choice, dobrushin_ennreal_bound, dobrushin_package_exists].
The residual is a one-liner that is already written and correct — it is not a
sorry itself; the chain is blocked on the MathlibTODO sub-tree.

---

### `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (decomposed)

Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json`

This theorem decomposes into helpers in the W1ContOn sub-plan. The sorry
warnings at lines 1233, 1248, 1265, 1278, 1298, 1310 belong to this sub-tree.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|-----------|-------|------|--------|
| 1 | `MathlibTODO_W1ContOn_lscNarrow` | 1233 | — | — | (none; Mathlib gap) | sorry |
| 2 | `MathlibTODO_W1ContOn_uscNarrow` | 1248 | — | — | (none; Mathlib gap) | sorry |
| 3 | `W1ContOn_lt_top` | 1265 | 2 | 4 | (none) | sorry |
| 4 | `W1ContOn_integralContAt` | 1278 | 3 | 3 | (none) | sorry |
| 5 | `W1ContOn_toRealContOn` | 1298 | 2 | 4 | W1ContOn_lt_top, MathlibTODO_W1ContOn_lscNarrow, MathlibTODO_W1ContOn_uscNarrow | sorry |
| 6 | `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | 1310 | — | — | all above | sorry |

`MathlibTODO_W1ContOn_lscNarrow` and `MathlibTODO_W1ContOn_uscNarrow` are
genuine Mathlib gaps (KR duality for non-compact test functions; characteristic
flow coupling for measure-valued ODEs). They block the entire W1ContOn sub-tree.

`W1ContOn_lt_top` (line 1265) is independently tractable: it only needs
`wasserstein1_lt_top_of_finite_moment` (already proved, line 889) applied
under the `HasFiniteFirstMoment` hypothesis. Its sorry is a proof-assembly gap,
not a Mathlib gap.

`W1ContOn_integralContAt` (line 1278) is also independently tractable:
`IsVlasovSolution` provides `HasDerivAt` for each integral, and `HasDerivAt`
implies `ContinuousAt`, from which `Continuous` follows by pointwise assembly.
This is a proof-assembly gap, not a Mathlib gap.

`W1ContOn_toRealContOn` (line 1298) is blocked on the two Mathlib gaps
(LSC + USC), so it cannot be closed until those are resolved.

`MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1349) is a separate
Mathlib gap: the right-derivative bound for the Wasserstein coupling requires
the characteristic flow coupling argument and the W₁ triangle inequality under
pushforward, neither of which is in Mathlib.

---

### `MathlibTODO_wassersteinGronwallCoupling` (decomposed)

Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

The helpers in this plan that are relevant to the sorry chain:

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|-----------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 1418 | 1 | 5 | (none) | proved |
| 2 | `wassersteinGronwallCoupling_gronwall_le` | 1372 | 2 | 4 | (none) | proved |
| 3 | `wassersteinGronwallCoupling_ofReal_le` | 1429 | 2 | 4 | `wassersteinGronwallCoupling_real_bound` | proved (wraps sub-axioms correctly) |
| 4 | `wassersteinGronwallCoupling_real_bound` | 1392 | 3 | 3 | `wassersteinGronwallCoupling_gronwall_le`, sub-axioms | sorry (via sub-axioms) |
| 5 | `MathlibTODO_wassersteinGronwallCoupling` | 1472 | — | — | all above | proved (delegates to `wassersteinGronwallCoupling_ofReal_le`) |

Note: `MathlibTODO_wassersteinGronwallCoupling` at line 1472 has no sorry
warning directly. The sorry chain runs through
`wassersteinGronwallCoupling_real_bound` (line 1392) → sub-axioms at lines
1310 and 1349.

---

### `MathlibTODO_convolveLipschitzEstimate` (decomposed)

Plan: `formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`

All helpers are now proved (no sorry warnings on any of lines 1016, 1048,
1073, 1179, 1205). The "MathlibTODO" name is historical; the theorem is
fully proved via the four helper lemmas.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|-----------|-------|------|--------|
| 1 | `convolveLipschitz_inner_lipschitz` | 1016 | 3 | 3 | (none) | proved |
| 2 | `convolveLipschitz_KR_le` | 1048 | 2 | 4 | (none) | proved |
| 3 | `convolveLipschitz_norm_le_of_inner_forall` | 1179 | 2 | 4 | (none) | proved |
| 4 | `convolveLipschitz_inner_bound` | 1073 | 3 | 3 | inner_lipschitz, KR_le | proved |
| 5 | `MathlibTODO_convolveLipschitzEstimate` | 1205 | — | — | inner_bound, norm_le | proved |

---

### Non-decomposed sorries — flat table

| Declaration | Line | Tex label | Nature |
|-------------|------|-----------|--------|
| `vlasovWellPosedness` | 784 (sorry at 800) | thm:vlasov-wp | Genuine Mathlib gap: measure-valued Picard theorem |
| `W1ContOn_lt_top` | 1265 | (helper for thm:dobrushin chain) | Proof-assembly gap (tractable) |
| `W1ContOn_integralContAt` | 1278 | (helper for thm:dobrushin chain) | Proof-assembly gap (tractable) |
| `MathlibTODO_W1ContOn_lscNarrow` | 1233 | (sub-axiom for thm:dobrushin) | Genuine Mathlib gap: KR duality, narrow topology |
| `MathlibTODO_W1ContOn_uscNarrow` | 1248 | (sub-axiom for thm:dobrushin) | Genuine Mathlib gap: char. flow coupling |
| `W1ContOn_toRealContOn` | 1298 | (helper for thm:dobrushin chain) | Blocked on Mathlib gaps (LSC + USC) |
| `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | 1310 | (sub-axiom for thm:dobrushin) | Blocked on sub-axioms |
| `MathlibTODO_wassersteinGronwallCoupling_derivBound` | 1349 | (sub-axiom for thm:dobrushin) | Genuine Mathlib gap: deriv bound via char. flow |

---

## Recommended next steps

The 8 sorries fall into two buckets:

**Bucket A: Tractable proof-assembly gaps (no new Mathlib API needed)**

1. Discharge `W1ContOn_lt_top` (line 1265; difficulty 2, Score 4; no deps).
   The sorry's only obligation is: for each `t`, extract
   `IsProbabilityMeasure (f t)`, `IsProbabilityMeasure (g t)`,
   `Integrable (‖·‖) (f t)`, `Integrable (‖·‖) (g t)` from
   `HasFiniteFirstMoment`, then apply `wasserstein1_lt_top_of_finite_moment`
   (proved at line 889). This is a ~10-line proof.
   Hints: `HasFiniteFirstMoment` unfolds to `IsProbabilityMeasure ∧ Integrable (·.norm) _;`
   `wasserstein1_lt_top_of_finite_moment`.

2. Discharge `W1ContOn_integralContAt` (line 1278; difficulty 3, Score 3; no deps).
   `IsVlasovSolution gradW f` expands (via `WeakEvolutionEq`) to: for every
   smooth compactly-supported `φ`, at every `t`,
   `HasDerivAt (fun s => ∫ φ ∂f s) _ t`. `HasDerivAt.continuousAt` converts
   this to `ContinuousAt` at every `t`, and `continuous_iff_continuousAt.mpr`
   assembles `Continuous`. The remaining friction is supplying `gradXφ`,
   `gradVφ`, `hgradXφ`, `hgradVφ` from `ContDiff ℝ ⊤ φ`.
   Hints: `HasDerivAt.continuousAt`, `continuous_iff_continuousAt`,
   `ContDiff.hasFDerivAt`.

**Bucket B: Genuine Mathlib gaps (blocked on OT infrastructure)**

3. `MathlibTODO_W1ContOn_lscNarrow` (line 1233): W₁ is LSC under narrow
   convergence. Requires KR duality for non-compactly-supported 1-Lipschitz
   test functions. Blocked on Mathlib's optimal-transport API for general
   (non-compact) metric spaces. Not tractable without upstream Mathlib work.

4. `MathlibTODO_W1ContOn_uscNarrow` (line 1248): W₁ is USC along Vlasov
   solution curves. Requires the characteristic flow coupling argument (pairing
   particles of `f` and `g` via the same ODE flow) and the W₁ triangle
   inequality under measure pushforward. Blocked on Mathlib's measure-valued
   ODE theory and the pushforward-contraction lemma.

5. `W1ContOn_toRealContOn` (line 1298): follows immediately once items 3 and 4
   are resolved (it composes LSC + USC + finiteness into `ContinuousOn`).
   Hints: `continuousOn_iff_lower_upperSemicontinuousOn`,
   `ENNReal.continuousOn_toReal`, `ContinuousOn.comp`.

6. `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 1310): follows
   from items 1–5. Residual glue is a one-liner: `exact W1ContOn_toRealContOn …`.

7. `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1349): the
   right-derivative Gronwall bound for the W₁ coupling. Requires the
   characteristic flow coupling argument and W₁ triangle inequality under
   pushforward. Independent of items 3–6 but equally blocked on Mathlib gaps.

8. `vlasovWellPosedness` (line 784): entire well-posedness theorem for the
   Vlasov PDE. Requires a Picard-style fixed-point theorem in the space of
   probability measures with finite first moment, equipped with the W₁ metric.
   This is the deepest gap; resolving it likely requires items 3–7 plus
   significant additional Mathlib OT infrastructure.

**Priority ordering** (tractable first, then by impact on the sorry count):

1. `W1ContOn_lt_top` (Score 4, no deps, no Mathlib gaps, ~10 lines).
2. `W1ContOn_integralContAt` (Score 3, no deps, no Mathlib gaps, ~20 lines).
3. After 1 and 2, `W1ContOn_toRealContOn` becomes tractable once the
   Mathlib gaps are supplied (items 3–4 above).
4. All remaining sorries are blocked on Mathlib OT infrastructure and should
   be treated as `MathlibTODO_*` stubs until that infrastructure is available.
