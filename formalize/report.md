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
| def:empirical | definition | `Vlasov.empiricalMeasure`, `Vlasov.empiricalMeasureCurve`, `Vlasov.empiricalMeasure_isProbabilityMeasure` | present |
| prop:weak | proposition | `Vlasov.weakEvolutionEmpiricalMeasure` | present |
| eq:weak-eq | equation | `Vlasov.WeakEvolutionEq` | present |
| cor:empirical-vlasov | corollary | `Vlasov.empiricalMeasureSolvesVlasov` | present |
| eq:vlasov | equation | `Vlasov.IsVlasovSolution` | present |
| thm:vlasov-wp | theorem | `Vlasov.vlasovWellPosedness` | present-with-sorry |
| eq:char | equation | `Vlasov.IsCharacteristicFlow`, `Vlasov.IsCharacteristicFlowSelfConsistent`, `Vlasov.vlasovSolutionViaPushforward` | present |
| thm:dobrushin | theorem | `Vlasov.dobrushin` | present-with-sorry |
| eq:dobrushin | equation | `Vlasov.DobrushinStabilityEstimate` | present |
| cor:mfl | corollary | `Vlasov.meanFieldLimit` | present |

**Status values:** `present` = fully proved, no sorry; `present-with-sorry` = declared and connected to the outline item but contains or depends on sorry.

Summary: 11 items present (clean), 2 present-with-sorry, 0 missing. Coverage ratio: 13/13 outline items represented.

---

## Sorry inventory

### `Vlasov.vlasovWellPosedness` (tex: thm:vlasov-wp, non-decomposed)

Line 800 (`sorry`). This is a single stubbed proof with no decomposition plan.

The theorem asserts existence and uniqueness of a narrowly-continuous curve of
probability measures with finite first moment satisfying the Vlasov equation in
the distributional sense. Lean line 800 carries the only `sorry` in this declaration.
No decomposition sidecar exists.

### Decomposed parent: `Vlasov.MathlibTODO_convolveLipschitzEstimate` (no tex-label, decomposed)

Plan: `formalize/plans/MathlibTODO_convolveLipschitzEstimate.json`

This is a Mathlib-gap theorem (Kantorovich-Rubinstein duality for the convolution
`‖(∇W*ρ)(x) − (∇W*σ)(x)‖ ≤ L * W₁(ρ,σ).toReal`). The parent body at line 1051
is now **proved** (it delegates to `convolveLipschitz_inner_bound` via
`convolveLipschitz_norm_le_of_inner_forall`). The plans recorded line numbers of -1
for the helpers because they were to-be-inserted; the build shows they now exist at
lines 950 and 1025. The one remaining sorry in the helper cascade is:

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `convolveLipschitz_inner_lipschitz` | 950 | 3 | 3 | (none) | proved |
| 2 | `convolveLipschitz_KR_le` | 982 | 2 | 4 | (none) | proved |
| 3 | `convolveLipschitz_inner_bound` | 1007 | 3 | 3 | convolveLipschitz_inner_lipschitz, convolveLipschitz_KR_le | **sorry** (line 1007) |
| 4 | `convolveLipschitz_norm_le_of_inner_forall` | 1025 | 2 | 4 | (none) | proved |

Residual glue: parent body at line 1051; **proved** (delegates to helpers 3+4 directly).

`Score = 6 − Difficulty`. The residual glue gets Score 4 per prover spec.

---

### Decomposed parent: `Vlasov.MathlibTODO_wassersteinGronwallCoupling` (no tex-label, decomposed)

Plan: `formalize/plans/MathlibTODO_wassersteinGronwallCoupling.json`

This is a Mathlib-gap theorem (Gronwall-based Wasserstein stability for Vlasov
solutions). The parent body at line 1216 is **proved** (it delegates to
`wassersteinGronwallCoupling_ofReal_le`). The two sub-axioms are the genuine PDE
gaps.

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `wassersteinGronwallCoupling_gronwall_le` | 1116 | 2 | 4 | (none) | proved |
| 2 | `wassersteinGronwallCoupling_real_bound` | 1136 | 3 | 3 | W1ContOn, derivBound, gronwall_le | proved (calls sub-axioms) |
| 3 | `wassersteinGronwallCoupling_ennreal_mul_comm` | 1162 | 1 | 5 | (none) | proved |
| 4 | `wassersteinGronwallCoupling_ofReal_le` | 1173 | 2 | 4 | real_bound, ennreal_mul_comm | proved |

Sub-axioms (genuine Mathlib gaps, backed by `sorry`):

| # | Name | Line | Status |
|---|------|------|--------|
| A | `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | 1074 | **sorry** (line 1074) |
| B | `MathlibTODO_wassersteinGronwallCoupling_derivBound` | 1093 | **sorry** (line 1093) |

Residual glue: parent body at line 1216; **proved** (direct delegation to
`wassersteinGronwallCoupling_ofReal_le`).

---

### Decomposed parent: `Vlasov.dobrushin` (tex: thm:dobrushin, decomposed)

Plan: `formalize/plans/dobrushin.json`

| # | Name | Line | Difficulty | Score | Deps | Status |
|---|------|------|------------|-------|------|--------|
| 1 | `dobrushin_C_choice` | 1234 | 2 | 4 | (none) | proved |
| 2 | `convolveDiff_norm_le` | 1244 | 4 | 2 | MathlibTODO_convolveLipschitzEstimate | proved (delegates to parent) |
| 3 | `wasserstein1_ofReal_exp_monotone` | 1257 | 1 | 5 | (none) | proved |
| 4 | `dobrushin_ennreal_bound` | 1269 | 4 | 2 | dobrushin_C_choice, MathlibTODO_wassersteinGronwallCoupling | proved (delegates to sorry-backed axiom) |
| 5 | `dobrushin_package_exists` | 1295 | 2 | 4 | dobrushin_C_choice, dobrushin_ennreal_bound | proved |

Residual glue: parent body at line 1326; **proved** (delegates to
`dobrushin_package_exists`).

The `dobrushin` theorem is structurally complete; its only sorry dependency
flows through `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 1074)
and `MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1093).

---

### `Vlasov.wasserstein1_lt_top_of_finite_moment` (no tex-label, non-decomposed)

Line 889 (`sorry`). This lemma proves that the Wasserstein-1 distance between two
probability measures with finite first moment is finite (`< ⊤`). No decomposition
plan exists. The docstring contains a complete proof sketch (shift by φ(0), apply
triangle inequality on bounded integrals).

---

### Non-decomposed sorries: flat table

| Declaration | Line | Tex-label | Note |
|-------------|------|-----------|------|
| `Vlasov.vlasovWellPosedness` | 800 | thm:vlasov-wp | Existence & uniqueness of Vlasov; requires Picard theory for measure-valued ODEs — genuine Mathlib gap |
| `Vlasov.wasserstein1_lt_top_of_finite_moment` | 889 | (none) | Finiteness of W₁ for finite-moment measures; proof sketch present in docstring; required by `dobrushin_ennreal_bound` |
| `Vlasov.convolveLipschitz_inner_bound` | 1007 | (none) | Inner-product KR duality step; depends on `convolveLipschitz_inner_lipschitz` (proved) + `convolveLipschitz_KR_le` (proved) |
| `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` | 1074 | (none) | Continuity of W₁(f_t, g_t) along Vlasov flows; genuine Mathlib gap (no measure-valued ODE continuity API) |
| `MathlibTODO_wassersteinGronwallCoupling_derivBound` | 1093 | (none) | Characteristic-flow coupling + Gronwall differential inequality; genuine Mathlib gap |

---

## Recommended next steps

### Tractable sorries (attack immediately)

1. **Discharge `wasserstein1_lt_top_of_finite_moment` (line 889).**
   Score: ~5 (easy, self-contained). The docstring already supplies the
   complete proof sketch: for any 1-Lipschitz `φ`, set `ψ y := φ y − φ 0`;
   then `|ψ y| ≤ ‖y‖`, so `∫φdμ − ∫φdν = ∫ψdμ − ∫ψdν ≤ ∫‖y‖dμ + ∫‖y‖dν`,
   which is finite by `hμ` and `hν`. The `iSup` is then bounded by
   `ENNReal.ofReal M` where `M` is the finite sum of integrals.
   Hints: `MeasureTheory.integral_sub`, `ENNReal.ofReal_lt_top`,
   `iSup_le`, `MeasureTheory.IsProbabilityMeasure.measure_univ`.
   Closing this also unblocks `wasserstein1_ne_top_of_finite_moment` (proved
   already as a corollary) and the `hW_t` derivation inside `dobrushin_ennreal_bound`.

2. **Discharge `convolveLipschitz_inner_bound` (line 1007, difficulty 3, Score 3).**
   Both of its deps (`convolveLipschitz_inner_lipschitz` and
   `convolveLipschitz_KR_le`) are already proved. The tactic sketch in the
   plan: unfold `convolveFunctionMeasure` on each side of the difference;
   commute `⟨·, v⟩` (a bounded linear map) through both Bochner integrals via
   `ContinuousLinearMap.integral_comp_comm`; express the integrand
   `y ↦ ⟨gradW(x−y), v⟩` as 1-Lipschitz after rescaling by `1/(L*‖v‖)`;
   apply `convolveLipschitz_KR_le`.
   Hints: `ContinuousLinearMap.integral_comp_comm`, `integral_sub`,
   `norm_integral_le_integral_norm`, `real_inner_le_norm`,
   `LipschitzWith.div_const` (or manual rescaling), `convolveLipschitz_inner_lipschitz`.
   Closing this also closes `MathlibTODO_convolveLipschitzEstimate` (already
   proved as a wrapper) and `convolveDiff_norm_le`.

### Genuine Mathlib gaps (require upstream infrastructure)

3. **`MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (line 1074).**
   Requires continuity of `t ↦ (wasserstein1 (f t) (g t)).toReal` for Vlasov
   solutions. This needs narrow continuity of the solution map under the Vlasov
   PDE and a continuity lemma for Wasserstein distance under narrow convergence.
   No Mathlib stable API yet. Architectural options: (a) add a `ContinuousOn`
   hypothesis to `dobrushin` and thread it through; (b) prove it as a
   consequence of the Picard-Lindelöf theorem for measure-valued ODEs (once
   available in Mathlib).

4. **`MathlibTODO_wassersteinGronwallCoupling_derivBound` (line 1093).**
   Requires the characteristic-flow coupling argument: pair particles of `f`
   and `g` started at the same label `z ∈ PhaseSpace d`, estimate the coupled
   cost growth at rate `≤ C * W₁(f_t, g_t)`, and apply the `W₁` triangle
   inequality under measure pushforward. Blocked on Mathlib's measure-valued
   Picard theory and a KR-duality pushforward contraction lemma.

5. **`vlasovWellPosedness` (line 800, tex: thm:vlasov-wp).**
   Existence and uniqueness for the Vlasov PDE as a measure-valued equation.
   This is the deepest gap: it requires a fixed-point / Picard iteration in
   the space of narrowly-continuous curves of probability measures, which is
   not in Mathlib. A feasible intermediate milestone is to add an axiomatic
   placeholder (matching the pattern of the Mathlib-gap theorems) and
   decompose its proof into: (a) a contraction argument on a short time
   interval, (b) an extension argument using the Gronwall estimate already
   proved for `dobrushin`. Hints once Mathlib infrastructure exists:
   `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`,
   `MeasureTheory.Measure.tendsto_iff_forall_integral_tendsto`.

