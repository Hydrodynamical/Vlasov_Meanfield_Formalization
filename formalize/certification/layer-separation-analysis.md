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
meta-program (`formalize/certification/depgraph-tool.lean`): for each declaration in
the project modules, `ConstantInfo.type/value?.getUsedConstants` filtered to
project declarations, tagged by defining module. Raw graph (230 decls):
`formalize/certification/depgraph-deps.txt`, format `MODTAG|declname|dep_tag:dep,...`.
Re-run after any move with `lake env lean formalize/certification/depgraph-tool.lean`
(writes `depgraph-deps.txt` in cwd) to re-verify the graph against the build —
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
    CharacteristicFlow.lean — the tight flow: extend_one_window_tight, characteristicFlow_tight, exists_vlasov_trajectory, global_smallT,
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

## Resume note (status + next-session ordering)

**Done (committed, footprint `[propext, Classical.choice, Quot.sound]` held at each step):**
- `d7df18c` — this diagnostic + graph + tool. Reusable check: `formalize/certification/footprint-check.lean`.
- `ed667c3` — **move 1**: `Base/Geometry.lean` (PhysSpace, PhaseSpace) extracted; Basic imports it.
- `a9c000d` — **move 2**: OT-generic core (`wassersteinCost`/`wasserstein1`/`wassersteinBar` + lemmas +
  firstMoment helper) → `OT/Wasserstein.lean` (imports Mathlib only — fully generic). Basic 2658→2015 lines.
- `6c2cf79` — **move 3 (load-bearing)**: re-pointed `Coupling` `import Vlasov.Basic` → `import Vlasov.OT.Wasserstein`.
  The `Coupling→Basic` edge is GONE. OT layer fully decoupled: `Base/Geometry → OT/Wasserstein → Coupling`,
  Kinetic reaches it only through the 4-name interface. Critical footprint check passed.

**Phase-D-OT (option 3) COMPLETE** — OT layer extracted, decoupled, file-complete, Mathlib-named;
footprint `[propext, Classical.choice, Quot.sound]` held through every move. Commits beyond moves 1–3:
- `7ae814c` — rename `foundationB_coupling_le_dual → wassersteinCost_coupling_le_dual` (OT-internal: sole
  call site was Coupling's own dual-witness wrapper).
- `0bb0c7f` — mop-up: the 3 W₁ stragglers (`eq_zero_iff`, `le_liminf_of_narrow`, `ofReal_exp_monotone`) →
  `OT/Wasserstein.lean`; **no `wasserstein1` lemma defs remain in Basic**. `HasFiniteFirstMoment` confirmed
  Kinetic-only (consumed only by Basic-Vlasov + CharacteristicFlow, zero OT consumers) → stays in Basic.
- `e9afbaa` — rename `MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment →
  integral_boundedContinuous_eq_of_integral_lipschitz_eq` (proved/closed — verified no live sorry; OT-internal
  AFTER the mop-up moved its consumer `eq_zero_iff` into OT/Wasserstein).

**Jargon audit (full OT public surface — 56 decls across OT/Wasserstein + OT/Coupling): PASS.**
No campaign vocabulary in any declaration name (no `foundationB_`, no closed `MathlibTODO_`, no Stage/Friction).
Every name is descriptive-statement-shape. The bridge `wasserstein1_eq_coupling` correctly kept (crosses the seam).
- PR-prep notes (mild descriptive project-internal shorthand — NOT jargon, NOT rename-now; batch at PR time):
  `lintegral_ofReal_kept_cells_le`, `finiteTransport_dual_eps`, `wassersteinCost_dual_singleMap_le`,
  `measure_compl_biUnion_range_tendsto_zero` — descriptive and acceptable; a Mathlib reviewer might tweak
  `kept_cells`/`_eps` wording at PR time, non-blocking.
- `MathlibTODO_cauchyW1_hasNarrowLimit` — at the time of this audit a sorry'd placeholder; since PROVEN and
  renamed to `exists_wasserstein1_limit_of_cauchy` (Tier-2 names, 2026-06-10). No `MathlibTODO_*` remain.

**Discipline notes (this arc):**
- *Stale-check (→ CLAUDE.md P11)*: move 2's first cut grabbed a dangling docstring (off by 25 lines). The build
  caught it; the chained footprint check was STALE (move-1 oleans, build had failed) — a passing check against a
  failed build is NOT certification. Revert → re-diagnose (L1520) → redo. Re-run the check only after the build
  it certifies succeeds.
- *Authoritative graph over grep*: the straggler self-containment check used `depgraph-deps.txt` (ground-truth
  decl graph), not text-grep — grep over-matched `AssW`/`empirical`/`gradW` in docstring prose; the graph showed
  clean OT-only deps. Trusting the grep would have wrongly blocked a clean move.

## Kinetic split — PLANNED (full 7-file split; refreshed 2026-06-10, NOT started)

**Status.** OT extraction is complete; the Kinetic split was deferred while the codebase was
cleaned — Tier 0 (truthful comments/docstrings), Tier 1 (≤100-codepoint lines, `/-! ## -/`
section headers, Mathlib copyright + LICENSE, linter), Tier 2 (names: the 2 real
`MathlibTODO_*` lemmas + 8 Group-A jargon helpers renamed; 0 `MathlibTODO_*` remain). This
plan is refreshed to current names. Bonus from the cleanup: `CharacteristicFlow.lean` now
carries `/-! ## -/` headers that fall on the partition boundaries, so it is effectively
pre-cut (see the **cut-point map** below).

Kinetic side = Basic (Vlasov decls) + CharacteristicFlow (~13.0k lines, ~111 decls); OT
(Base/Geometry → OT/Wasserstein → OT/Coupling) is below and untouched. Partition is a
bottom-up DAG. Oracles/gates per move: `depgraph-tool.lean` (back-edge oracle —
revert-diagnose-redo on any cycle) → `lake build` green → `footprint-check.lean` (both
marquees `[propext, Classical.choice, Quot.sound]`) → `sorry-scan.lean` (0) →
`reuse-score.lean` (total stays 230) → commit each file.

**Target files (bottom-up; current names):**

1. **`Kinetic/VectorField.lean`** ← AssW, convolveFunctionMeasure, convolveLipschitz_*,
   `norm_convolveFunctionMeasure_sub_le` (was MathlibTODO_convolveLipschitzEstimate),
   convolveDiff_norm_le, gradient_zero_of_even, + the velocity field
   (vlasovVectorField + _lipschitzWith + growth/Gronwall). Imports OT/Wasserstein + Base/Geometry.
2. **`Kinetic/Solutions.lean`** ← IsVlasovSolution(On), IsNewtonSolution,
   IsLagrangianVlasovSolution(On), IsCharacteristicFlow(SelfConsistent)(On), WeakEvolutionEq,
   HasFiniteFirstMoment, vlasovSolutionViaPushforward, the `_On` predicate family. Imports VectorField.
3. **`Kinetic/CharacteristicFlow.lean`** (residual) ← the tight per-window flow:
   exists_vlasov_extend_one_window(_tight), exists_vlasov_characteristicFlow_tight,
   `exists_vlasov_trajectory` (was perz), _global_smallT, the Φ operator + Picard fixed point
   (Phi_*), LocalSmallness_*, supW1On_*, `characteristicFlow_boundary_regularity` (was Stage_1_9_…).
   Imports Solutions + VectorField + Mathlib/ODE/PicardLindelof.
4. **`Kinetic/LagrangianEulerian.lean`** ← Stage C (pushforward solves weak Vlasov) +
   the SC.5–SC.8 bundle. [largest residual; may split in two.] Imports CharacteristicFlow.
5. **`Kinetic/WellPosedness.lean`** ← vlasovWellPosedness_{forward,uniqueness,universal_existence},
   `vlasovWellPosedness_local(_moment/_isLagrangian)` (was _finalAssembly_*),
   `vlasovWellPosedness_glue(_boundary)` (was _glue_step / glue_step_boundary_bundle),
   `dobrushin_uniqueness_On` (the §9.6 private per-window uniqueness helper — see wrinkle),
   and the marquee `vlasovWellPosedness` (§10). Imports LagrangianEulerian.
6. **`Kinetic/Dobrushin.lean`** ← the §10 stability chain: DobrushinStabilityEstimate,
   wassersteinGronwallCoupling_*, `continuousOn_integral_of_isLagrangianVlasovSolution`
   (was w1_lscNarrow_integralContOn_lip_lag), w1_lscNarrow_of_summands, diagonalCorrection_*,
   `exists_wasserstein1_limit_of_cauchy` (was MathlibTODO_cauchyW1…, now proven), and `dobrushin`.
   Imports OT/Coupling (the `wasserstein1_eq_coupling` bridge) + Solutions + CharacteristicFlow.
7. **`Kinetic/MeanField.lean`** ← hamiltonianN, empiricalMeasure*, weakEvolutionEmpiricalMeasure,
   empiricalMeasureSolvesVlasov, meanFieldLimit(_coupling), spatialMarginal, hasDerivAt_empirical*,
   convolveFunctionMeasure_empiricalSpatial_eq. Imports WellPosedness + Dobrushin. Top leaf.

DAG: `VectorField → Solutions → CharacteristicFlow → LagrangianEulerian → WellPosedness → Dobrushin → MeanField`.

**Dependency wrinkle (resolved).** `vlasovWellPosedness_uniqueness` (file 5) calls
`dobrushin_uniqueness_On` (the §9.6 *private* per-window uniqueness), so that helper stays in
WellPosedness — the §10 marquee `dobrushin` stability theorem is the only thing in Dobrushin
(file 6). The depgraph tool flags this as the sole would-be back-edge; keeping the helper in
WellPosedness makes the DAG strictly linear.

**Cut-point map** — current `CharacteristicFlow.lean` `/-! ## -/` headers → target file:

  L48   Vlasov velocity field + Lipschitz             → VectorField
  L117  Flow distance growth (Gronwall)               → VectorField / CharacteristicFlow
  L1162 Characteristic flow existence (Picard)        → CharacteristicFlow
  L1233 Localized `_On` solution predicates           → Solutions
  L1750 Per-window helpers (N-window induction)       → CharacteristicFlow
  L2877 Lagrangian → Eulerian (pushforward → weak PDE)→ LagrangianEulerian
  L3251 LE bundle sub-helpers (SC.5–SC.8)             → LagrangianEulerian
  L4008 "Integration smoke test"                      → drop, or move to a test file
  L4055 Banach fixed-point scaffolding                → CharacteristicFlow
  L4148 Metric-dependent smallness (LocalSmallness_*) → CharacteristicFlow
  L4321 Constant extension past [0,T]                 → CharacteristicFlow
  L4721 The pushforward operator Φ (Phi_*)            → CharacteristicFlow
  L6841 §9 Existence and uniqueness                   → WellPosedness
  L8187 Banked hasDerivAt_of_hasDerivAt_of_ne         → WellPosedness (helper)
  L8261 Variable-T_target continuation                → WellPosedness
  L11082 Uniqueness over …On per window               → WellPosedness (dobrushin_uniqueness_On)
  L12187 Universal-in-t bridge                        → WellPosedness
  L12502 §10 Marquee theorem                          → WellPosedness
  L12853 §10 Dobrushin stability chain                → Dobrushin

Plus the Basic-resident Vlasov decls distribute: AssW/convolve*/gradient → VectorField;
solution predicates → Solutions; empirical*/meanField/hamiltonianN → MeanField;
DobrushinStabilityEstimate/Gronwall/cauchy-limit → Dobrushin. End state: `Basic.lean`
emptied (all Vlasov decls → Kinetic/) → delete, or keep a thin re-export shim.

**Open design questions:** split the large LagrangianEulerian (Stage C) in two? Keep
`HasFiniteFirstMoment` in Solutions or push to OT/Wasserstein? Delete `Basic.lean` or keep a
shim? Drop the "Integration smoke test" or relocate it?

**Effort & caution.** The heaviest structural item — ~15k lines redistributed, ~15–20 moves,
each a CharFlow-class rebuild; a multi-session phase. Develop large body-extractions against
the slow host (L12 scratch trick); boundary-pin per the move-2 lesson (end at the decl's end,
not the next docstring). If any moves are delegated to subagents, apply the edit move-ban +
`agent-edit-guard.sh`; doing the moves directly sidesteps the `.prover-bak` hazard. Orthogonal
to the weak⟺Lagrangian bridge, which slots into Solutions/LagrangianEulerian either way.

**Historical (superseded by the above):**

**Refinement found during move 1:** `wasserstein1`/`wassersteinCost` are GENERIC over
`{α : Type*}` (Basic L900/L922) — the OT *core* does NOT depend on Base/Geometry; only
`HasFiniteFirstMoment` (over `PhaseSpace`) does. So the OT-generic core can sit at the very
bottom (above Mathlib only), with `HasFiniteFirstMoment` one layer up (above Base).

**Next moves, in order (each: create file → move decls from Basic → build → `footprint-check.lean`
shows both marquees `[propext, Classical.choice, Quot.sound]` → commit; revert-on-failure):**
1. Extract the OT-generic core (`wassersteinCost` + lemmas, then `wasserstein1` + lemmas + W̄,
   then `HasFiniteFirstMoment` + the polish firstMoment helper) out of Basic into `OT/`.
   (WassersteinCost before Wasserstein — wasserstein1 uses wassersteinCost.)
2. **THE LOAD-BEARING MOVE — `Coupling` import re-point.** Only AFTER the OT-generic core is fully
   in `OT/`, re-point `Coupling.lean`'s `import Vlasov.Basic` → the new `OT/` files (removing the
   `Coupling → Basic` module edge entirely; Coupling becomes pure OT). The footprint check *after
   this move* is THE critical one — it confirms the marquee still reaches the OT layer through the
   intended 4-name interface (`wasserstein1_coupling`, `wasserstein1_pushforward_le_iInf`,
   `wasserstein1_eq_coupling`, `IsCoupling`) and not through a stale `Basic` path.
3. Renames, kept INSIDE the OT layer so they don't ripple across the seam:
   `foundationB_coupling_le_dual → wassersteinCost_coupling_le_dual`; closed OT `MathlibTODO_*`
   → mathematical names. **Keep `wasserstein1_eq_coupling`** (the bridge — it crosses to Kinetic;
   renaming it would touch the Kinetic call site).
4. (Optional, this phase) split `Coupling.lean` into `Coupling` / `KantorovichDuality` / `Bridge`.

Kinetic (Basic's 47 Vlasov decls + CharacteristicFlow) is LEFT UNTOUCHED this phase (option 3);
reassess the Kinetic split after the OT layer lands clean + renamed.
