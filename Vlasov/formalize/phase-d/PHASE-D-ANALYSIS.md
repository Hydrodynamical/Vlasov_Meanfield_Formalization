# Phase D — dependency graph + OT/Vlasov separation verdict + target structure

**Status: diagnostic complete (Steps 1–2). Target structure below is the review gate (Step 3). NO declarations moved yet.**

## The governing invariant (hold absolutely)

The project is at its terminal certified state:
`#print axioms vlasovWellPosedness` and `#print axioms dobrushin` are BOTH
`[propext, Classical.choice, Quot.sound]` — zero external axioms, arbitrary `L`.
Every move must preserve this EXACTLY. Acceptance test for every step:
build green AND `#print axioms` on both marquee theorems unchanged
(no `sorryAx`, no added axiom). A green build with a changed footprint is a
FAILURE. Move-and-verify, never move-and-hope; if a move breaks the build OR the
footprint, revert that move and diagnose — do not patch forward.

## Method (robust instrument, not text-grep)

Declaration-level dependency graph extracted from Lean's own environment via a
meta-program (`formalize/phase-d/depgraph-tool.lean`): for each declaration in
the project modules, `ConstantInfo.type/value?.getUsedConstants` filtered to
project declarations, tagged by defining module. Raw graph (230 decls):
`formalize/phase-d/phase_d_deps.txt`, format `MODTAG|declname|dep_tag:dep,...`.
Re-run after any move with `lake env lean formalize/phase-d/depgraph-tool.lean`
(writes `phase_d_deps.txt` in cwd) to re-verify the graph against the build —
the build is the oracle; grep was used only to cross-reference docstring `[General OT]` markings.

## Module-level DAG (verified — no back-edges)

Current files: `Basic.lean` (75 decls) → `OT/Coupling.lean` (29) →
`OT/CharacteristicFlow.lean` (124); `Vlasov.Mathlib.ODE.PicardLindelof` (2, leaf).
Imports already enforce a one-directional DAG; verified zero forbidden edges:
- COUP → CHARFLOW: **0**
- BASIC → {COUP, CHARFLOW}: **0**
- PICARD → {anything project}: **0**  (pure vendored ODE leaf — upstreamable as-is)

## The OT → Kinetic interface (narrow — 4 names + the bridge)

`CharacteristicFlow` touches the OT layer through exactly 4 declarations:
- `wasserstein1_coupling`        (coupling-based W₁, 4 uses)
- `wasserstein1_pushforward_le_iInf`  (pushforward bound, 1)
- `wasserstein1_eq_coupling`     (**THE BRIDGE** — dual↔coupling identification, 1)
- `IsCoupling`                   (coupling predicate, 1)

Confirms the brief's hypothesis: Kinetic depends on OT only through the
cost/coupling API + the bridge, not OT internals.

## The crux: classifying `Basic.lean` (75 decls)

Coupling's ENTIRE `Basic`-footprint is 5 declarations, ALL pure general-OT
(`wasserstein1`, `wasserstein1_eq_iSup_lipschitz`, `wassersteinCost`,
`wassersteinCost_comm`, `wassersteinCost_triangle`) — zero Vlasov-specific names.

Three-way classification (verified by transitive intra-Basic closure + leakage check):

**Base/Geometry (shared ambient space, 2):** `PhysSpace`, `PhaseSpace`
(`= EuclideanSpace ℝ (Fin d)` and its square). Not Vlasov physics — the ambient
geometry both layers sit on. (`wasserstein1`/`wassersteinCost`/`wassersteinBar`
are GENERIC and do NOT depend on these; only `HasFiniteFirstMoment` does.)

**OT layer (general optimal transport, 27 — upstreamable):**
`wasserstein1` + property lemmas (`_comm _self _triangle _eq_iSup_lipschitz
_dual_lower_bound _le_of_lipschitz_map _eq_zero_iff_measure_eq
_le_liminf_of_narrow _lt_top_of_finite_moment _ne_top_of_finite_moment
_ofReal_exp_monotone _le_moments_sum`); `wassersteinCost` + `_comm _triangle
_self _dual_lower_bound _le_of_lipschitz_map`; `wassersteinBar` (W̄ truncated
metric) + `_comm _self _triangle _dual_lower_bound _le_of_lipschitz_map`;
`HasFiniteFirstMoment`; `lipschitzWith_one_iff_oscillation`;
`MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment` (general polish-space
first-moment helper — reclassified to OT, see leakage below).

**Vlasov/Kinetic (47):** `AssW` (+ generated), `convolveFunctionMeasure`,
`convolveDiff_norm_le`, `convolveLipschitz_*`, `gradient_zero_of_even`,
`IsVlasovSolution`, `IsLagrangianVlasovSolution`, `IsCharacteristicFlow*`,
`IsNewtonSolution`, `WeakEvolutionEq`, `empiricalMeasure*`, `meanFieldLimit`,
`vlasovSolutionViaPushforward`, `hamiltonianN`, `spatialMarginal`,
`DobrushinStabilityEstimate`, `diagonalCorrection_*`, `wassersteinGronwallCoupling_*`,
`w1_lscNarrow_*`, `gronwall_mild_le`, `hasDerivAt_*`, `weakEvolutionEmpiricalMeasure`,
the Vlasov `MathlibTODO_*` (cauchyW1, convolveLipschitzEstimate), …

### Leakage verdict (the load-bearing check)

Transitive closure of the OT set within Basic touches exactly **3** Vlasov-tagged
decls — none a genuine OT→Vlasov-physics dependency:
1. `PhysSpace` ← `HasFiniteFirstMoment`
2. `PhaseSpace` ← `HasFiniteFirstMoment`  → both = shared ambient geometry → **Base layer** (not a leak).
3. `MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment` ← `wasserstein1_eq_zero_iff_measure_eq`
   → general polish-space helper **misclassified** by the name filter → belongs **in the OT layer**.

**Conclusion: the OT layer is cleanly separable.** No OT lemma depends on Vlasov
physics. The only cross-edges are the shared ambient geometry (→ a base layer) and
one misclassified general helper (→ OT).

## Target file structure (REVIEW GATE — derived from the graph)

Linear import stack `Base → OT → Kinetic`, each file a mathematical unit,
declarations in dependency order, `section`-grouped, with a `/-! # … -/` module docstring.

```
Vlasov/
  Base/Geometry.lean        — PhysSpace, PhaseSpace (ambient EuclideanSpace).  [tiny; could fold into OT base]
  OT/
    WassersteinCost.lean    — wassersteinCost (dual cost) + comm/triangle/self/dual_lower/le_of_lipschitz_map
    Wasserstein.lean        — wasserstein1 + all W₁ property lemmas; HasFiniteFirstMoment;
                              lipschitzWith_one_iff_oscillation; the firstMoment polish helper; eq_iSup_lipschitz
    WassersteinBar.lean     — wassersteinBar (W̄ truncated metric) + its lemmas  [optional: fold into Wasserstein.lean]
    Coupling.lean           — IsCoupling, wasserstein1_coupling, gluing, easy direction, triangle, graph bound, finite-range approx
    KantorovichDuality.lean — the Farkas finale: transport polytope + compactness leaves,
                              finiteTransport_dual_eps (separation core), c-transform,
                              finiteRange_transportation_dual, wassersteinCost_coupling_le_dual
    Bridge.lean             — wasserstein1_eq_coupling  (the dual↔coupling seam; consumed by Kinetic)
  Kinetic/
    VectorField.lean        — AssW, convolveFunctionMeasure, convolveLipschitz_*, gradient_zero_of_even
                              (CharFlow Stage A/A.2 + the convolve* / gradient Basic decls)
    Solutions.lean          — IsVlasovSolution(On), IsLagrangianVlasovSolution(On), IsCharacteristicFlow*, the _On predicate family
    CharacteristicFlow.lean — the tight flow: extend_one_window_tight, characteristicFlow_tight, perz, global_smallT,
                              per-window helpers (CharFlow Stage B + per-window helpers)
    LagrangianEulerian.lean — Stage C (pushforward solves weak Vlasov) + SC bundle  [large; may split]
    WellPosedness.lean      — vlasovWellPosedness_forward/_uniqueness/_universal + the marquee vlasovWellPosedness
                              (CharFlow §9/§9.5/§9.6/§9.7/§10)
    Dobrushin.lean          — DobrushinStabilityEstimate, wassersteinGronwallCoupling_*, w1_lscNarrow_*, dobrushin  (CharFlow §10 stability)
    MeanField.lean          — empiricalMeasure*, meanFieldLimit, weakEvolutionEmpiricalMeasure, hamiltonianN  (Basic Vlasov decls)
  Mathlib/ODE/PicardLindelof.lean — unchanged (vendored ODE leaf)
```

Open design questions for review:
- Granularity: WassersteinBar fold into Wasserstein? Base/Geometry fold into the lowest OT file?
- `HasFiniteFirstMoment` is stated over `PhaseSpace` (needs Base); `wasserstein1` is generic — keep `HasFiniteFirstMoment` in OT/Wasserstein (above Base) or push generic and drop the Base dep?
- Kinetic split granularity (Stage C is large; the marquee chain §9–§10 is large).

## Naming (Step 5 — within the OT reorg)

Audit OT layer for campaign-jargon names → Mathlib descriptive-statement convention:
- `foundationB_coupling_le_dual` → `wassersteinCost_coupling_le_dual` (drop "Foundation B").
- `MathlibTODO_*` in the OT layer → mathematical names (they are closed lemmas now, not TODOs).
- `wasserstein1_eq_coupling` already mathematical — keep.
Each rename = refactor: rename + build + footprint-check (a missed call site breaks the build; a wrong one is caught by the footprint).

## Execution plan (Step 4 — after structure review; incremental, footprint-checked)

One mathematical unit per move: move → `lake build` green → `#print axioms`
vlasovWellPosedness + dobrushin both `[propext, Classical.choice, Quot.sound]` →
commit that single move (bisectable) → next. Never batch unverified moves.
Bottom-up (Base first, then OT generic, then Coupling/Duality/Bridge, then Kinetic)
so each new file's imports already exist. Re-run depgraph-tool periodically to
confirm the graph still matches intent.
```
