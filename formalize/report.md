# Formalization coverage report

Generated: 2026-05-23
Source outline: /Users/jkmiller/Documents/Claude/Projects/Vlasov/formalize/structure.md
Lean file: /Users/jkmiller/Documents/Claude/Projects/Vlasov/Vlasov/Vlasov/Basic.lean

## Build status
- Result: success
- Sorry warnings: 5
- Other warnings: 0
- Errors: 0

Sorry locations (from compiler output):
```
warning: Vlasov/Basic.lean:239:8: declaration uses `sorry`   -- weakEvolutionEmpiricalMeasure
warning: Vlasov/Basic.lean:309:8: declaration uses `sorry`   -- empiricalMeasureSolvesVlasov
warning: Vlasov/Basic.lean:372:8: declaration uses `sorry`   -- vlasovWellPosedness
warning: Vlasov/Basic.lean:481:8: declaration uses `sorry`   -- dobrushin
warning: Vlasov/Basic.lean:537:8: declaration uses `sorry`   -- meanFieldLimit
```

## Coverage

| Tex label | Kind | Lean declaration | Status |
|---|---|---|---|
| eq:HN | equation | `hamiltonianN` (line 41) | present-stubbed |
| eq:newton | equation | `IsNewtonSolution` (line 60) | present-stubbed |
| ass:W | assumption | `class AssW` (line 80) + `gradient_zero_of_even` (line 99, proved) | present-stubbed |
| def:empirical | definition | `empiricalMeasure` (line 174), `empiricalMeasure_isProbabilityMeasure` (line 185, proved), `empiricalMeasureCurve` (line 197) | present-stubbed |
| prop:weak | proposition | `weakEvolutionEmpiricalMeasure` (line 239) | present-with-sorry |
| eq:weak-eq | equation | `WeakEvolutionEq` (line 285) | present-stubbed |
| cor:empirical-vlasov | corollary | `empiricalMeasureSolvesVlasov` (line 309) | present-with-sorry |
| eq:vlasov | equation | `IsVlasovSolution` (line 343) | present-stubbed |
| thm:vlasov-wp | theorem | `vlasovWellPosedness` (line 372) | present-with-sorry |
| eq:char | equation | `IsCharacteristicFlow` (line 410), `IsCharacteristicFlowSelfConsistent` (line 425), `vlasovSolutionViaPushforward` (line 434) | present-stubbed |
| thm:dobrushin | theorem | `dobrushin` (line 481) | present-with-sorry |
| eq:dobrushin | equation | `DobrushinStabilityEstimate` (line 511) | present-stubbed |
| cor:mfl | corollary | `meanFieldLimit` (line 537) | present-with-sorry |

Status key:
- `present-stubbed`: declaration is fully stated (or fully proved); no `sorry` inside it.
- `present-with-sorry`: declaration is stated correctly but its proof body is `sorry`.
- `commented-out`: not applicable here — no items are commented out.
- `missing`: not applicable here — all 13 outline items have a corresponding declaration.

Notes on `present-stubbed` items:
- `eq:HN`, `eq:newton`, `eq:weak-eq`, `eq:vlasov`, `eq:dobrushin` are equations/definitions; they carry no proof obligation beyond well-typedness.
- `ass:W` (`class AssW`) is a typeclass with no proof body. The associated helper lemma `gradient_zero_of_even` is fully proved (no sorry).
- `def:empirical`: `empiricalMeasure` and `empiricalMeasureCurve` are computable definitions with full bodies. `empiricalMeasure_isProbabilityMeasure` is fully proved.
- `eq:char`: all three declarations (`IsCharacteristicFlow`, `IsCharacteristicFlowSelfConsistent`, `vlasovSolutionViaPushforward`) are fully defined.

## Sorry inventory

| Line | Enclosing declaration | Tex label |
|---|---|---|
| 269 | `weakEvolutionEmpiricalMeasure` | prop:weak |
| 323 | `empiricalMeasureSolvesVlasov` | cor:empirical-vlasov |
| 388 | `vlasovWellPosedness` | thm:vlasov-wp |
| 497 | `dobrushin` | thm:dobrushin |
| 563 | `meanFieldLimit` | cor:mfl |

Each is a single `sorry` terminating the entire proof body; none are partial-proof sorries.

## Recommended next steps

### 1. Highest-value declarations to prove next (most tractable first)

1. **`weakEvolutionEmpiricalMeasure` (prop:weak, line 239).**
   This is the central calculation. The sum-of-Diracs structure of `empiricalMeasure` means
   every integral `∫ φ d(empiricalMeasureCurve N X V t)` reduces to a finite sum
   `(1/N) Σ_i φ(X t i, V t i)`. Differentiating under the sum then applies the chain rule
   with `HasDerivAt` — both are available in Mathlib. The main subgoals are:
   (a) `HasDerivAt` of `fun t => ∫ z, φ z ∂(empiricalMeasureCurve N X V t)`, which reduces
       to `HasDerivAt (fun t => (1/N) Σ_i φ(X t i, V t i))` via `integral_smul_measure` and
       `integral_finset_sum`;
   (b) the chain rule on `fun t => φ(X t i, V t i)` via `HasFDerivAt.comp`; and
   (c) expanding `fderiv ℝ φ` in terms of `gradXφ` and `gradVφ` (inner products).
   The diagonal remainder term isolates to `−(1/N²) Σ_i gradW 0 · gradVφ(xᵢ, vᵢ)`,
   making the bound straightforward. This proof does not require Wasserstein theory.

2. **`empiricalMeasureSolvesVlasov` (cor:empirical-vlasov, line 309).**
   Given a proof of `weakEvolutionEmpiricalMeasure`, this corollary is nearly one line:
   apply `weakEvolutionEmpiricalMeasure`, then use `gradient_zero_of_even` (already proved)
   to show the remainder `r = 0`. The `WeakEvolutionEq` wrapper unfolds immediately.

3. **`dobrushin` (thm:dobrushin, line 481).**
   The key estimate `‖convolveFunctionMeasure gradW ρ x − convolveFunctionMeasure gradW σ x‖`
   `≤ L · wasserstein1 ρ σ` is a duality argument (Kantorovich–Rubinstein); once that lemma
   is isolated, a `gronwall`-style argument closes the bound. Mathlib has `Gronwall` in
   `Mathlib.Analysis.ODE.Gronwall`. This is more involved than prop:weak but does not depend
   on well-posedness.

### 2. Missing Mathlib API that would unblock the rest

- **Differentiation through a finite measure integral parameterised by time.**
  `MeasureTheory.integral_hasDerivAt_right` handles differentiation under an integral for
  a fixed sigma-finite measure, but differentiating `fun t => ∫ φ d(μ t)` where `μ t` itself
  varies requires a custom argument. A lemma of the form
  `HasDerivAt (fun t => ∫ f d(μ t)) (∫ Df d(μ t)) t` when `μ t` is a weighted sum of
  Diracs is not yet in Mathlib. Needed for: prop:weak.

- **Wasserstein-1 distance API for finite measures on ℝ^d.**
  `MeasureTheory.ProbabilityMeasure.FiniteWasserstein` exists but its Kantorovich–Rubinstein
  dual formula (`wasserstein1 μ ν = sup {∫ f dμ − ∫ f dν | Lip f ≤ 1}`) has not been
  proved in full generality in current Mathlib (as of early 2026). The local `wasserstein1`
  definition in the file is the correct dual formula, but connecting it to any metric-space
  properties (triangle inequality, joint lower semicontinuity) will require hand-rolling
  several lemmas. Needed for: thm:dobrushin, cor:mfl.

- **Gronwall inequality for ENNReal-valued quantities.**
  `Mathlib.Analysis.ODE.Gronwall` provides `gronwall_bound` for real-valued integrals.
  The Dobrushin argument produces an estimate on `wasserstein1 (f t) (g t) : ENNReal`;
  one needs to coerce to `ℝ` (valid when measures have finite first moment) and apply
  `gronwall_bound`. The coercion lemma `ENNReal.toReal_le_toReal` with a finiteness side
  condition is present but the combination is not packaged. Needed for: thm:dobrushin.

- **Existence and uniqueness of ODE solutions with measure-valued right-hand side.**
  `vlasovWellPosedness` (thm:vlasov-wp) depends on a fixed-point / Picard iteration in
  the space of probability measures. Mathlib's `ODE.solution_eq_zero` and
  `ContDiff.exists_forall_hasDerivAt` cover finite-dimensional smooth ODEs, but the
  self-consistent measure-valued fixed-point argument is not in Mathlib. This is the
  hardest gap. Needed for: thm:vlasov-wp, cor:mfl.
