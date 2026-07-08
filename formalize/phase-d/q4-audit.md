# Q4 audit — non-redundancy of the self-contained layer $\mathcal{L}_{\mathrm{gen}}$ (Def 3.2)

> **OUTCOME (this audit motivated a redefinition).** Half A below found 11 of the original
> 60 general decls unreachable from a target. In response, $\mathcal{L}_{\mathrm{gen}}$ was
> **redefined to the 49-declaration reachable general core** (the 11 excluded: 6 deferred W̄
> lemmas + 5 superseded). Current authoritative numbers (from `reuse-score.lean` with the
> 49-set): **49/299 ≈ 16%**, S2 back-edges **0**, interface **w = 22** (up from 17 — the 11
> still physically reside in the modules and reference the layer; pruning would re-minimise it,
> deferred). Q4-reachability now passes 49/49 by construction. The audit below describes the
> original 60-set run that produced this finding.

Generated from `reuse-score.lean` — the **same run** that produces `60/299`, `w=17`,
S2 back-edges `=0`. $\mathcal{L}_{\mathrm{gen}}$ is the elaborator's set, not a hand-typed
list: **exactly 60** declarations, all in the four self-contained modules
(`Base.Geometry` 2, `OT.Wasserstein` 27, `OT.Coupling` 29, `Mathlib.ODE.PicardLindelof` 2).

Q4 has two halves of **very different strength**; they are reported separately.

## Verdict table

| Q4 half | Strength of the check | Result |
|---|---|---|
| **A. Reachability** from a target theorem | machine-checked (graph query) | **49/60 reachable; 11 NOT** (listed) |
| **B1. Generality** (no problem-specific decl) | **machine-certified by Q2** | **60/60** library-general; 0 problem-specific; 0 entangled |
| **B2. Non-redundancy** (no Mathlib duplicate) | library search — *evidence, not proof* | **0/60** duplicates found |

### Half A — reachability (graph query; FAILS for 11/60)
Targets = the four axiom-clean marquees `{vlasovWellPosedness, dobrushin, meanFieldLimit,
weak_isLagrangianVlasovSolutionOn}`. Transitive `getUsedConstants` closure: **49/60** general
decls reachable. (Project-wide **223/299** reachable — confirms the query is sound, not an
under-count.) The **11 unreached** are general OT math but not on any current target's proof
path — technically dead-code-relative-to-targets, so Q4-A does *not* cleanly pass:

- **Deferred W̄ truncated-metric regime (6)** — no target uses W̄:
  `wassersteinBar`, `wassersteinBar_comm`, `wassersteinBar_self`, `wassersteinBar_triangle`,
  `wassersteinBar_le_of_lipschitz_map`, `wassersteinBar_dual_lower_bound`
- **W₁/coupling lemmas built but superseded / not wired (5)**:
  `wasserstein1_pushforward_le_iInf` (its "used in dobrushin" docstring is stale — the
  Phase-C refactor superseded it; it survives only via an unreachable orphan helper),
  `wasserstein1_le_of_lipschitz_map`, `wassersteinCost_le_of_lipschitz_map`,
  `wasserstein1_ofReal_exp_monotone`, `IsCoupling.map`

### Half B1 — generality (PASSES; machine-certified by Q2)
All 60 live in the four modules that `ot-standalone` compiles **against Mathlib alone**. A
declaration whose statement mentioned `gradW` / `ρ` / the Vlasov field / the characteristic
flow could not compile there — so **Q2 certifies** that no statement is problem-specific. By
inspection of every name and statement, each files under a general Mathlib namespace
(`MeasureTheory` / `Analysis` / `ODE` / `Topology` / Euclidean geometry):
**0 problem-specific, 0 general-but-entangled.** ("Vlasov"/"dobrushin" appear only in three
*docstring* lines explaining downstream use — never in a statement.)

### Half B2 — non-redundancy (PASSES by search; the weakest half)
- **OT core (54/60):** statements are built from `wasserstein1` / `wassersteinCost` /
  `wassersteinBar` / `IsCoupling` / `transportProperCone` / the dual machinery — definitions
  **absent from Mathlib v4.29.1** (verified, §6.5). A Mathlib lemma cannot restate a statement
  over symbols Mathlib does not define. Non-redundant by construction.
- **Picard–Lindelöf (2/60):** both IPL lemmas are documented in-source as *"Vendored addition,
  absent from the upstream"* — strict extensions of Mathlib's `IsPicardLindelof` existence
  lemmas, adding the confinement conjunct `α x t ∈ closedBall x₀ a`. They prove strictly more;
  non-redundant.
- **Generic helpers (4/60):** `exact?` library search against v4.29.1 found **no single-lemma
  Mathlib proof** for `lipschitzWith_one_iff_oscillation`,
  `lintegral_ofReal_ne_top_of_integrable_nonneg`, `lintegral_ofReal_tail_tendsto_zero`,
  `measure_compl_biUnion_range_tendsto_zero`.
- **`integral_boundedContinuous_eq_of_integral_lipschitz_eq` (1/60):** bespoke
  measure-equality-from-1-Lipschitz-integral-equality; non-redundant by inspection (not
  `exact?`-tested).

> **Limitation (do not round up):** `exact?` finding nothing is *evidence, not proof* — it can
> miss a result phrased differently. This half is **"no duplication found by library search
> against v4.29.1,"** not "certified non-redundant."

## Grouped listing of the 60 (every name in exactly one general-titled group)

Headers carry the generality argument; names are evidence. **`†` = unreachable from a target
(Half A).** No group title mentions Vlasov.

**G1 — Phase-space types (Euclidean geometry) [2]**
`PhysSpace`, `PhaseSpace`

**G2 — Picard–Lindelöf existence with confinement (ODE) [2]**
`IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined`,
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_confined`

**G3 — Wasserstein-1 metric core: KR-dual definition + metric API [13]**
`wasserstein1`, `wasserstein1_comm`, `wasserstein1_self`, `wasserstein1_triangle`,
`wasserstein1_eq_iSup_lipschitz`, `wasserstein1_eq_zero_iff_measure_eq`,
`wasserstein1_le_of_lipschitz_map`†, `wasserstein1_le_liminf_of_narrow`,
`wasserstein1_le_moments_sum`, `wasserstein1_lt_top_of_finite_moment`,
`wasserstein1_ne_top_of_finite_moment`, `wasserstein1_ofReal_exp_monotone`†,
`wasserstein1_dual_lower_bound`

**G4 — Couplings and the primal–dual W₁ identity [7]**
`IsCoupling`, `IsCoupling.map`†, `wasserstein1_coupling`, `wasserstein1_coupling_eq`,
`wasserstein1_eq_coupling`, `wasserstein1_le_wasserstein1_coupling`,
`wasserstein1_pushforward_le_iInf`†

**G5 — Wasserstein transport cost (abstract ground cost) [14]**
`wassersteinCost`, `wassersteinCost_comm`, `wassersteinCost_self`, `wassersteinCost_triangle`,
`wassersteinCost_le_of_lipschitz_map`†, `wassersteinCost_dual_lower_bound`,
`wassersteinCost_dual_le_add_map`, `wassersteinCost_dual_singleMap_le`,
`wassersteinCost_coupling`, `wassersteinCost_coupling_comm`, `wassersteinCost_coupling_triangle`,
`wassersteinCost_coupling_map_le`, `wassersteinCost_coupling_le_dual`,
`wassersteinCost_coupling_le_dual_of_finiteRange`

**G6 — Truncated-metric Wasserstein W̄ (deferred regime) [6]** — all unreachable
`wassersteinBar`†, `wassersteinBar_comm`†, `wassersteinBar_self`†, `wassersteinBar_triangle`†,
`wassersteinBar_le_of_lipschitz_map`†, `wassersteinBar_dual_lower_bound`†

**G7 — Finite Kantorovich–Rubinstein duality (Farkas route) [7]**
`finiteTransport_dual_eps`, `finiteTransport_dual_eps_plan`, `finiteRange_transportation_dual`,
`cTransform_dual_witness`, `transportProperCone`, `isClosed_transport_cone`,
`exists_transport_min`

**G8 — Finite-range transport approximation and compactness [7]**
`exists_coupling_glue`, `finiteRange_approxMap_measurable`, `exists_finiteRange_map_cost_le`,
`lintegral_ofReal_kept_cells_le`, `lintegral_ofReal_ne_top_of_integrable_nonneg`,
`lintegral_ofReal_tail_tendsto_zero`, `measure_compl_biUnion_range_tendsto_zero`

**G9 — Generic measure-theory / analysis helpers [2]**
`integral_boundedContinuous_eq_of_integral_lipschitz_eq`, `lipschitzWith_one_iff_oscillation`

Total: 2+2+13+7+14+6+7+7+2 = **60**.
