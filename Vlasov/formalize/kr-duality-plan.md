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

## Skeleton — LAID (commit `6bcb4cd`); actual decl names

Six general-OT helpers in `Coupling.lean`, sorried + marked
`[General OT — reusable / Mathlib-upstreamable]`:
- `wassersteinCost_coupling_comm` — symmetry (clean).
- `wassersteinCost_coupling_triangle` — gluing through a common middle; needs
  `[StandardBorelSpace α]` (disintegration).  **SUBSTANTIVE.**
- `wassersteinCost_coupling_map_le` — graph-coupling bound
  `W_c(μ, map T μ) ≤ ∫⁻ ofReal(c x (T x)) dμ`.
- `exists_finiteRange_map_cost_le` — ∀ε>0, ∃ finite-range `T` with
  `∫⁻ ofReal(c x (T x)) dμ ≤ ofReal ε` (partition by diameter + finite-moment tail).
- `wassersteinCost_coupling_le_dual_of_finiteRange` — finite KR duality core
  (clean: Birkhoff present).
- `wassersteinCost_dual_le_add_map` — dual stability under pushforward.

Parent `foundationB_coupling_le_dual` documents the ε→0 assembly (`comm` +
`triangle`×2 + `map_le` + `le_dual_of_finiteRange` + `dual_le_add_map`, costs
`≤ ε/4`, close with `ENNReal.le_of_forall_pos_le_add`).  Body still `sorry`.

## Difficulty re-ranking (correcting the earlier "finite core is substantive")

The friction in discrete-approx+limit builds lives in the **measure-theoretic
plumbing**, NOT the finite-dimensional convexity core.  Real ranking:
- **HARDEST**: `wassersteinCost_coupling_triangle` (coupling-gluing via
  disintegration) ≈ the **ε→0 assembly** (the limit — ENNReal plumbing +
  bookkeeping).  These are the substantive arcs.
- then `exists_finiteRange_map_cost_le` (approximation + tail).
- then `wassersteinCost_dual_le_add_map`.
- **CLEANEST**: `wassersteinCost_coupling_le_dual_of_finiteRange` (Birkhoff is in
  Mathlib) ≈ `wassersteinCost_coupling_comm`.

**Triangle scaffolding read (banked this session)**: Mathlib HAS disintegration +
composition — `Probability/Kernel/Disintegration/` (`condKernel`,
`eq_condKernel_of_measure_eq_compProd`, `…/StandardBorel.lean`) and
`Probability/Kernel/Composition/MeasureCompProd.lean`
(`compProd : Measure α → Kernel α β → Measure (α × β)`).  The coupling-GLUING
lemma itself is NOT packaged but is assemblable from these — so the triangle is a
**moderate build on Mathlib scaffolding**, not a from-scratch disintegration.
Still the largest helper.

## Cadence / discipline (assembly-wiring session — carry-forward)

1. **WIRE THE PARENT FIRST — that is the real API-lock.**  Before closing ANY
   helper, wire `foundationB_coupling_le_dual`'s body to call the six sorried
   helpers and get it **green modulo the six**.  The current state is *designed,
   not locked*: a prose assembly can hide a gap (a missing 7th fact, an `osc ≤ c`
   threading issue, ε-bookkeeping) that only surfaces when you write the actual
   `calc`.  Wiring proves the decomposition is sound before effort sinks into
   helpers.  Requires threading `[StandardBorelSpace α]` (for the triangle)
   through `foundationB_coupling_le_dual` + `wasserstein1_eq_coupling`; consumers
   instantiate at the Polish `PhaseSpace d` so it resolves — confirm the CharFlow
   chain (incl. `dobrushin`) stays green.
2. **CLOSE CLEAN-FIRST** to bank progress: `comm`, `le_dual_of_finiteRange`
   (Birkhoff), `dual_le_add_map`; then `map_le`, `exists_finiteRange_…`.  Then the
   real arcs: `triangle` (gluing via Mathlib disintegration) and the ε→0 assembly
   (folded into the wiring).
3. Certify (P10): on the last helper, `#print axioms vlasovWellPosedness` AND
   `dobrushin` both `[propext, Classical.choice, Quot.sound]`; project sorry count
   **0** = zero external axioms at L<1 (Phase B checkpoint).
4. Build cwd: `cd …/Vlasov/Vlasov && lake build …`. Local Mathlib at
   `Vlasov/.lake/packages/mathlib/Mathlib/`.
