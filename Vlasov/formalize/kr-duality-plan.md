# Phase B build plan — Kantorovich–Rubinstein duality (the shrunk Foundation B)

The project's single external sorry, post the Phase A.0 shrink (`656e9b9`).

## Goal

Prove `foundationB_coupling_le_dual` (`Vlasov/OT/Coupling.lean:274`):
```
wassersteinCost_coupling c μ ν ≤ wassersteinCost c μ ν
```
for probability measures `μ, ν` with finite first moment (`Integrable (dist · x₀)`),
`c` a continuous pseudometric.  This is the **hard direction** of KR duality
(`coupling-inf ≤ dual-sup`).  The easy direction (`≥`, weak duality) is
`wasserstein1_le_wasserstein1_coupling` (proved, B-free).

Definitions:
- dual: `wassersteinCost c μ ν = ⨆ (f) (_ : ∀ x y, |f x − f y| ≤ c x y),
  ENNReal.ofReal (∫ f ∂μ − ∫ f ∂ν)` (`Basic.lean:900`).
- coupling: `wassersteinCost_coupling c μ ν = ⨅ (π) (_ : IsCoupling π μ ν),
  ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π` (`Coupling.lean:235`).

## Phase A status (done)

- **A.0** (`656e9b9`): shrank B from attainment + strong duality + equality to
  this inequality alone.  The consumer (`dobrushin`, via `wasserstein1_eq_coupling`)
  needs only `coupling ≤ dual`; attainment dropped.  Deleted
  `foundationB_optimal_coupling_exists` + the callerless
  `wasserstein1_optimal_coupling_exists`.
- **A.1 verdict**: genuine from-scratch OT build — NO Mathlib scaffolding
  (no `Kantorovich`/`Wasserstein`/`OptimalTransport`; no Fenchel–Rockafellar /
  minimax / Sion; the Lévy–Prokhorov metric is weak-convergence, ≠ transport
  duality).  ~250–500 lines.  User decision: **build it** (B-first holds on
  clean-baseline / risk-isolation / don't-restate-twice).

## Route: DISCRETE APPROXIMATION + LIMIT (Route 1, selected)

~70% Mathlib coverage; preferred over Hahn–Banach (Route 2, ~450–850 lines,
needs a signed-measure space + cost-sublinear functional from scratch).

Proof idea (Villani Thm 1.3 flavour): prove the inequality for finitely-supported
measures (finite LP duality), then transfer to general `μ, ν` by approximating
each with a finitely-supported measure joined by an explicit low-cost coupling,
using finite first moment to control the tail.  Phrase the transfer with
**explicit couplings**, NOT W₁-self-reference (avoids circularity).

## Mathlib inventory (verified present this session)

- **Birkhoff–von Neumann**: `doublyStochastic_eq_convexHull_permMatrix`,
  `exists_eq_sum_perm_of_mem_doublyStochastic`, `convex_doublyStochastic`,
  `mem_doublyStochastic_iff_sum` (`Analysis/Convex/Birkhoff.lean`,
  `…/DoublyStochasticMatrix.lean`).
- **Tonelli/Fubini**: `lintegral_prod` (`MeasureTheory/Measure/Prod.lean`).
- **DCT**: `tendsto_integral_of_dominated_convergence`,
  `tendsto_lintegral_filter_of_dominated_convergence`
  (`MeasureTheory/Integral/DominatedConvergence.lean`).
- **Weak convergence / Portmanteau**: `FiniteMeasure` weak topology,
  `…tendsto_iff_forall_integral_tendsto`, `MeasureTheory/Measure/Portmanteau.lean`.
- **Simple-function / partition approximation**: `SimpleFunc.approxOn`
  (`…/SimpleFuncDenseLp.lean`); `SeparableSpace.exists_measurable_partition_diam_le`
  (`LevyProkhorovMetric.lean:551` — partition into small-diameter pieces, the
  approximation workhorse).
- **In-project, reusable**: `IsCoupling`, `IsCoupling.map`,
  `wasserstein1_le_wasserstein1_coupling` (easy direction),
  `wasserstein1_pushforward_le_iInf`, `wassersteinCost_triangle` (dual-side
  triangle), the moment lemmas.
- **GAPS to build**: finite LP/transport duality (no Hall / max-flow in Mathlib —
  via Birkhoff vertices + a finite dual-potential construction); the
  coupling-side triangle inequality (gluing couplings through a common middle);
  the limiting glue.

## Skeleton (helpers to API-lock — sorry-decomposer, then close each)

1. **`kr_duality_finite_support`** — the finite-support core: `coupling-inf ≤
   dual-sup` for finitely-supported `μ', ν'`.  Finite LP duality; Birkhoff gives
   the coupling polytope's vertices are permutation-like, the dual potential is
   built finite-dimensionally.  THE hard core; size first at implementation.
2. **`exists_finite_support_coupling_approx`** — ∀ ε>0, ∃ finitely-supported `μ'`
   and an explicit coupling `γ` of `(μ, μ')` with `∫⁻ c dγ ≤ ε`.  Construction:
   partition a large compact into small-diameter cells
   (`exists_measurable_partition_diam_le`), push `μ` to cell representatives; the
   tail outside the compact is controlled by finite first moment (Markov).
3. **`wassersteinCost_coupling_triangle`** — coupling-side triangle:
   `coupling-inf(μ,ν) ≤ coupling-inf(μ,μ') + coupling-inf(μ',ν') +
   coupling-inf(ν',ν)`, by gluing couplings through common middles (disintegration
   / `Measure.prod` + the marginal-matching middle).
4. **`wassersteinCost_le_dual_approx_stable`** — dual-side stability:
   `dual-sup(μ',ν') ≤ dual-sup(μ,ν) + (cost γ_μ) + (cost γ_ν)`.  For a c-admissible
   `f`, `∫f dμ' − ∫f dμ = ∫(f(x')−f(x)) dγ_μ ≤ ∫ c dγ_μ` (f is c-Lipschitz), so the
   approximation error is bounded by the coupling costs from helper 2.
5. **Assembly** in `foundationB_coupling_le_dual`: pick ε; get `μ',ν'` + couplings
   (h2); `coupling-inf(μ,ν) ≤ coupling-inf(μ',ν') + 2ε` (h3 + h2);
   `coupling-inf(μ',ν') ≤ dual-sup(μ',ν')` (h1, finite); `dual-sup(μ',ν') ≤
   dual-sup(μ,ν) + 2ε` (h4); chain, then `ε → 0` (`ENNReal.le_of_forall_pos_le_add`).

Exact signatures + the finite-duality sub-route to be fixed with build feedback at
implementation.  Watch the ENNReal `⨅`/`⨆` plumbing and the ε→0 in ENNReal.

## Cadence / discipline

- Implementation session opens against this doc (P6 brief-driven execution).
- Lay the skeleton with `sorry-decomposer` (parent assembled + building, helpers
  sorried — P4 API-lock); then close each helper with `sorry-prover` / manual over
  subsequent sessions; certify B-freeness / axiom footprint myself (P10).
- Property-only where possible; the helpers genuinely `unfold` the coupling/dual
  defs (they ARE the duality), which is expected for this lemma.
- On the last helper closing: `#print axioms vlasovWellPosedness` AND `dobrushin`
  both `[propext, Classical.choice, Quot.sound]`; project sorry count **0** =
  zero external axioms at L<1 (the Phase B checkpoint).
- Build cwd: `cd …/Vlasov/Vlasov && lake build …`. Local Mathlib at
  `Vlasov/.lake/packages/mathlib/Mathlib/`.
