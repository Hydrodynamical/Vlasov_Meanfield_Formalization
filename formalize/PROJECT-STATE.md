# Vlasov formalization — project state snapshot

**Snapshot date**: 2026-05-31, post-Phase-3 (cleanup document, Phase B).

This document captures the project's research-artifact state at the
Phase 3 endpoint, before the Phase 4 architectural swing.  Intended
audience: the next strategic session, and Mathlib PR-drafting work.

For the structural codebase reference, see `formalize/codebase-outline.md`.
For session-by-session planning history, see `formalize/planning-notes.md`.
For the original design choices, see `formalize/DESIGN.md`.

---

## 1. Headline state

* **Marquee theorem**: `vlasovWellPosedness` (in
  `Vlasov/OT/CharacteristicFlow.lean`, relocated from Basic.lean) —
  forward-only existence of `IsLagrangianVlasovSolution` for
  `0 < L < 1` Lipschitz regime, with HasFiniteFirstMoment initial data
  on Polish phase space `ℝ^d × ℝ^d`.
* **Sorry count**: 15 declarations using `sorry` (8 pure-FA placeholders
  + 7 project-internal substantive close targets).
* **Closure status**: existence-side of `vlasovWellPosedness` is closed
  modulo 4 of 7 project-internal sub-sub-sorries plus 8 pure-FA
  placeholders.  Uniqueness side requires the deferred
  `dobrushin_uniqueness_On` substantive close (Phase 4).
* **Architectural status**: ready for Phase 4 (Lagrangian-upgrade
  cascade) — the single load-bearing decision that retires Phase 3's
  4 deferred composition lemmas (items 1, 3, 5, 6) plus one residual
  CharFlow-internal sorry.

---

## 2. Sorry inventory

### 2.1 Pure-FA `MathlibTODO_*` placeholders (8 total)

These are the Mathlib-extension targets — Bucket-1 (Villani-standard
single-PR scope) or Bucket-2 (requires characteristic-flow coupling
infrastructure not yet stable in Mathlib).  Closure routes through
Mathlib OT API maturity, not project-internal work.

| # | Name | File:Line | Bucket | Status |
|---|------|-----------|--------|--------|
| 1 | `MathlibTODO_cauchyW1_hasNarrowLimit` | Basic.lean L1148 | 1 | Banked; closure routes through Prokhorov + tightness for Polish spaces |
| 2 | `MathlibTODO_convolveContinuousAtOfNarrowMoment` | Basic.lean L1448 | 1 | Banked; standard convolution-continuity-along-narrow-moment-curves |
| 3 | `MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves` | Basic.lean L1715 | 1 | Banked; Villani 5.10 |
| 4 | `MathlibTODO_bcNarrowFromSmoothCompactNarrow` | Basic.lean L1794 | 1 | **NEW** (Phase 3 Session 3); BC extension from smooth-CS via Portmanteau |
| 5 | `MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows` | Basic.lean L1905 | 2 | Banked; Lagrangian-pushforward USC |
| 6 | `MathlibTODO_w1RightDerivBoundAlongLagrangianFlows` | Basic.lean L2051 | 2 | Banked; W₁ right-deriv Gronwall under Lagrangian flows |
| 7 | `MathlibTODO_lipschitzFlowTrajectoryLipBound` | CharFlow.lean L2674 | 1 | Banked; Lipschitz-flow trajectory `‖φ ∘ flow_t‖` Lip bound |
| 8 | `MathlibTODO_lipschitzFlowAEMeasurable` | CharFlow.lean L6247 | 1 | Banked; AEMeasurability of an ODE flow |

**Bucket-1 ship-ready PR candidates** (subset of above): items 1, 3, 4, 7.
All are Villani-standard single-PR scope, no characteristic-flow
coupling required, no cross-file dependency.

**Bucket-2 PR candidates** (subset of above): items 5, 6.  Both require
characteristic-flow coupling infrastructure; should be deferred to
Mathlib OT API maturity.  Could be scoped as a single PR or split.

**Unclassified**: items 2, 8 — not yet bucketed (await Mathlib survey).

### 2.2 Project-internal sorries (7 total)

These are substantive close targets within the project's existence
proof.  Phase 4 architectural work will retire 4 of these; the
remaining 3 are sub-sub-sorries inside `vlasovWellPosedness_local`
sub-helpers awaiting focused close sessions.

| # | Name | File:Line | Phase | Status |
|---|------|-----------|-------|--------|
| 1 | `w1ContOn_uscNarrow_via_pureFA` | Basic.lean L1939 | 4 | Phase 3 item 5; needs Lagrangian-upgrade or cross-file decomposition |
| 2 | `wassersteinGronwallCoupling_derivBound_via_pureFA` | Basic.lean L2098 | 4 | Phase 3 item 6; same as #1 + Vlasov-vector-field-diff bound |
| 3 | `picardCharFlow_aemeasurable` | CharFlow.lean L6272 | 4 | Phase 3 item 1; needs `IsCharacteristicFlowSelfConsistent` predicate decision (architectural) |
| 4 | `vlasovWellPosedness_local_picard_fixedPointFlow` | CharFlow.lean L6349 | 2-3 | Sub-helper inside marquee local-existence; substantive Picard close |
| 5 | `vlasovWellPosedness_glue_step` | CharFlow.lean L7294 | 2-3 | Sub-helper for gluing local windows; case (b)/(c) closed, case (a) substantive |
| 6 | `dobrushin_uniqueness_On` | CharFlow.lean L8484 | 4 | Phase 3 item 3; depends on item 6 close + W₁-zero characterization |
| 7 | `vlasovWellPosedness_universal_existence` | CharFlow.lean L8578 | 2-3 | Sub-helper assembling universal-in-`t` Lagrangian existence |

**Phase 4 targets**: items 1, 2, 3, 6 (the Lagrangian-upgrade cascade).
**Substantive close pending (non-architectural)**: items 4, 5, 7.

---

## 3. Phase 4 architectural prompt

### 3.1 The Lagrangian-upgrade decision

**Question**: should the project's `IsVlasovSolution`-keyed downstream
chain (`MathlibTODO_wassersteinGronwallCoupling_W1ContOn` →
`MathlibTODO_wassersteinGronwallCoupling` → `dobrushin_ennreal_bound` →
`dobrushin_package_exists` → `dobrushin` → `meanFieldLimit`) be
upgraded to take `IsLagrangianVlasovSolution`?

**Why this is the right unit of decision**:

* Items 1, 3, 5, 6 from Phase 3 all hit the same architectural wall:
  closing them substantively requires Lagrangian flow witnesses, which
  `IsVlasovSolution` doesn't carry but `IsLagrangianVlasovSolution`
  does.
* The 5-6 consumer declarations downstream all currently take
  `IsVlasovSolution`; upgrading the upstream items 1, 3, 5, 6 forces
  the consumer chain to upgrade too.
* The forward-only refactor (M-series sighting in commit `de135c7`)
  already strengthened `vlasovWellPosedness`'s conclusion to
  `IsLagrangianVlasovSolution`.  The consumer chain is the missing
  piece to make this strengthening externally visible.

**Two implementation paths**:

* **Path A — restate consumers**: change each consumer's hypothesis
  from `IsVlasovSolution gradW f` to `IsLagrangianVlasovSolution gradW f`.
  Provides flow witnesses to items 5, 6 directly; closes them via
  composition.  Cascade through 5-6 consumer declarations + 4 Phase 3
  items.  Estimated ~300-500 lines across 2-3 sessions.

* **Path B — DiPerna-Lions superposition placeholder**: add
  `MathlibTODO_superpositionPrinciple_Lagrangian` to bridge
  `IsVlasovSolution → ∃ Φ, ...`.  Doesn't require consumer-chain
  upgrade.  Adds 1 new pure-FA placeholder (Bucket-2 deep, not
  Mathlib-stable).  Closes items 1, 3, 5, 6 via composition.
  Estimated ~150-250 lines, mostly in one session.

**Recommendation**: Path A.  The IsLagrangianVlasovSolution
strengthening already happened at the marquee theorem; the consumer
chain just needs to catch up.  Path B introduces a deep deferred
placeholder (DiPerna-Lions superposition is genuinely out-of-scope
hard) without genuinely reducing project-internal work.  Path A is
mostly mechanical signature restatement.

### 3.2 The four-series discipline recommendation for Phase 4

* **P1 (atom-level signature reading)**: before drafting consumer
  upgrades, read the actual signatures of all 5-6 consumers + their
  call sites.  Verify nothing else breaks under the upgrade.
* **P5 (verification of strategic recommendation)**: this document
  recommends Path A based on the architectural analysis above; P5 says
  verify the recommendation atom-by-atom before committing.  The first
  Phase 4 session should be a discovery commit confirming or refining
  the path.
* **P4 (API-lock pattern)**: each consumer upgrade is its own commit
  candidate.  Phase 4 likely produces 2-3 commits per session.
* **B1 (predicate enrichment over per-site bridging)**: the upgrade IS
  B1 operating at the consumer chain — enriching the predicate the
  chain takes, rather than per-site bridging at each consumer.

---

## 4. Narrative — M-series statement-correction sighting

**Single sighting** of statement-mathematical-content mismatch
(commit `de135c7`, 2026-05-30) — proposed-promoted to M-series after
the trigger condition (2 more sightings) is met.

The marquee theorem `vlasovWellPosedness` was originally stated as
`∃! f : ℝ → Measure (PhaseSpace d), ...` with universal-in-`t`
conjuncts including `t < 0`.  The proof's content (forward Picard
iteration from `t = 0`) only establishes forward-time existence.
The mismatch required ~30 lines of sub-sub-sorried case-split
machinery in the marquee body that wasn't proving anything
mathematical — just bridging the unprovable `t < 0` case.

The refactor restated the marquee to forward-only existence:

```lean
∃ f, f 0 = f₀ ∧
  ∀ t ∈ Ici 0, HasFiniteFirstMoment (f t) ∧
  ∀ T > 0, IsLagrangianVlasovSolutionOn gradW f T
```

This matches Dobrushin 1979's actual claim.  The case-split machinery
disappeared along with the corresponding sub-sub-sorry.  Sorry count
unchanged at the marquee declaration level, but structural content
honesty significantly improved.

**Why this matters for the cleanup document**:

* "Sorry count" is one metric; "statement correctness" is another,
  distinct, axis.
* The forward-only refactor is genuine research-artifact value — it
  surfaced and corrected a misstatement that had been carried for
  multiple sessions.
* Mathlib PRs from this project should adopt the same forward-only
  framing where appropriate (e.g., bucket-1 `MathlibTODO_cauchyW1_hasNarrowLimit`
  is intrinsically forward-only at the limit-existence level).

---

## 5. Process retrospective — the four-series discipline framework

Post-Phase-3 retrospective on the discipline framework's operation.
Detail in `CLAUDE.md`; this section summarizes empirical impact.

### 5.1 L-series (Lean tool / agent-tool lessons)

* **L1-L5** (sorry-prover spec engineering — Hard rules vs workflow
  sub-bullets): post-promotion enforcement empirically worked; the
  grep-validate-before-citing constraint fires reliably when in Hard
  rules.
* **L6** (silent-CLI-hang watchdog): empirically saved ~50-min wall
  clock per rate-limit-exhaustion event; observed firing post-promotion.
* **L7** (inline `?_` placeholders in chained Mathlib-API calls):
  empirically reverted ~85-line Stage 2b proof attempt; re-write with
  named-`have` discipline landed cleanly.
* **L8** (iff-direction at API call sites): 3 sightings across Stage
  2b / Stage 4 Cauchy / Phi_step; broadened framing covers
  `_map_measure` family + `.congr` family + `lt_top_iff_ne_top`
  family.
* **L9** (Lean elaborator treats defeq forms as not-immediately-unifiable):
  5 sightings across Stages 1.8-4; promoted to L-series proper.

### 5.2 P-series (process discipline)

* **P1** (atom-level signature reading): 4+ sightings; empirically the
  cheapest insurance against planned-against-imagined-API repeats.
* **P2** (structural-vs-tactical diagnosis on cascade): 2 sightings;
  the Stage 2 → Stage 1.9 pivot and Stage 4 Path 3 pivot.
* **P3** (cross-session context loading via diagnostic commits): 3
  sightings; explains why two-commit session structures
  (discovery + execution, often paired across sessions) are the
  project's most productive cadence.
* **P4** (API-lock-vs-substantive-proof): 3 sightings; generalizes
  from theorem-level signature lock to composition-body sub-placeholder
  decomposition.  Phase 3 item 4 close used P4 at the proof-body level.
* **P5** (discipline framework's pattern-extrapolation needs atom-level
  verification): 4 sightings in this Phase 3 alone; the self-referential
  application of P1.
* **P6** (brief-driven execution lands cleanly): 2 sightings; the
  positive-pattern companion to P5.

### 5.3 M-series (mathematical structure)

* **M1** (minimize structure-projection boundaries — ENNReal vs ℝ): 3
  sightings; Stage 4 Cauchy / iterated triangle / `picard_iterate_geometric_bound`.

### 5.4 B-series (bridging architecture / structural-fix patterns)

* **B1** (predicate enrichment over per-site bridging): 2 sightings
  (`IsLagrangianVlasovSolution` introduction + `_On`-family). Both
  retired multiple consumer bridges in one architectural move.
* **B2** (boundary regularity at predicate-layer boundaries): 3
  sightings; promoted to B-series.  Demonstrates fractal recursion —
  same surgery shape recurs at multiple architectural layers.
* **B2-anti-prophylaxis** (counter-refinement, commit `c25c8b0`): check
  Mathlib for localized derivative-extension lemmas
  (`FDeriv/Extend.lean`) before committing to B2 surgery.

### 5.5 Watch-list (pre-promotion candidates with 1-2 sightings)

* M-series statement-correction (1 sighting, commit `de135c7`).
* Session-type cadence (2 sightings; P6 captured the positive-execution
  half).
* Cascade-as-signal (1 sighting).
* Local-clamping technique (1-2 sightings).
* Strategic-conversation diagnosis → focused-session execution
  (1 sighting).
* Cumulative-trajectory honesty (2 sightings).
* Additive offsets in smallness constraints are structurally fatal
  (1 sighting).

---

## 6. Mathlib PR drafting recommendations

### 6.1 Bucket-1 single-PR candidates

These are the most ship-ready Mathlib-extension targets.  Each is
self-contained, requires no characteristic-flow coupling, and has a
clearly-scoped Mathlib-standard target.

1. **`MathlibTODO_cauchyW1_hasNarrowLimit`** (Basic.lean L1148):
   Cauchy-in-W₁ sequences with uniform first-moment bound have W₁-limits
   in 𝒫₁ on Polish spaces.  Closure: Prokhorov +
   tightness-from-first-moment + narrow-to-W₁ upgrade.  PR scope:
   ~200-500 lines depending on Prokhorov-for-Polish-spaces stability
   in Mathlib at PR time.

2. **`MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves`** (Basic.lean L1715):
   W₁ is LSC along pairs of narrowly continuous probability-measure
   curves with uniform first-moment bound.  Closure: standard double
   sup of LSC summands.  PR scope: ~100-200 lines.

3. **`MathlibTODO_bcNarrowFromSmoothCompactNarrow`** (Basic.lean L1794):
   BC narrow continuity from smooth-CS narrow continuity, given uniform
   first-moment bound.  Closure: truncation argument + cutoff
   mollification.  PR scope: ~150-250 lines.

4. **`MathlibTODO_lipschitzFlowTrajectoryLipBound`** (CharFlow.lean L2674):
   Lipschitz flow trajectory bound.  Closure: standard Gronwall.  PR
   scope: ~100-200 lines.

**Suggested PR ordering**: 2, 4 first (most self-contained); 3 second
(builds on Mathlib's bounded-continuous-functions API); 1 last (deepest
infrastructure dependency on Mathlib's Prokhorov machinery).

### 6.2 Bucket-2 deferred-to-stability candidates

* `MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows` (Basic.lean L1905)
* `MathlibTODO_w1RightDerivBoundAlongLagrangianFlows` (Basic.lean L2051)

Both require characteristic-flow coupling infrastructure.  Defer to
Mathlib OT API stability for Lagrangian-pushforward / characteristic
flow primitives.  Plausibly a single combined PR (~400-700 lines) once
the prerequisite Mathlib infrastructure exists.

### 6.3 Pending classification

* `MathlibTODO_convolveContinuousAtOfNarrowMoment` (Basic.lean L1448)
* `MathlibTODO_lipschitzFlowAEMeasurable` (CharFlow.lean L6247)

Not yet bucketed.  Mathlib-survey-before-PR work.

---

## 7. Out-of-scope items

These were investigated and confirmed outside the project's closure
arc.

* **DiPerna-Lions superposition principle**: the Eulerian-to-Lagrangian
  direction (i.e., extracting a Lagrangian flow from a weak Eulerian
  solution).  Genuinely hard mathematics; out of scope unless a
  Bucket-2-friendly Mathlib infrastructure becomes available.
* **L ≥ 1 Lipschitz regime**: the marquee `vlasovWellPosedness` is
  stated for `0 < L < 1`.  The `L ≥ 1` regime requires Dobrushin's
  truncated metric W̄ + a `T²`-shape contraction estimate (replacing
  the current `(T+1)²` additive offset).  Out of scope for Phase 4;
  documented as a separate W̄-refactor arc.
* **`MathlibTODO_wasserstein1_coupling_le_wasserstein1`**: KR-hard
  direction.  Orthogonal axis to the project's closure arc.

---

## 8. Phase 4 entry brief

The next focused session should:

1. **Atom-level read** of the consumer chain
   (`MathlibTODO_wassersteinGronwallCoupling_W1ContOn` →
   `MathlibTODO_wassersteinGronwallCoupling` → `dobrushin_*` →
   `meanFieldLimit`).
2. **Per-consumer signature impact analysis**: for each consumer,
   identify whether the upgrade from `IsVlasovSolution` to
   `IsLagrangianVlasovSolution` ripples to its callers.
3. **Decision commit**: Path A vs Path B (per §3.1 above), with the
   atom-level findings as the discriminator.
4. **First execution commit**: upgrade the simplest consumer (likely
   `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` since it's the
   most upstream).

**Sorry trajectory expectation under Path A**: 15 → 11-12 over 2-3
sessions (4 Phase 3 items close + possibly Phase 4 sub-helpers).
Under Path B: 15 → 12 in one session, but the new
`MathlibTODO_superpositionPrinciple_Lagrangian` is a deep Bucket-2+
placeholder (not Mathlib-stable in the foreseeable future).

**Phase 4 endpoint** (under Path A): marquee `vlasovWellPosedness`
becomes the only externally-visible declaration using `sorry` for
substantive Vlasov content (the remaining 4-5 sorries are
sub-sub-sorries inside `vlasovWellPosedness_local` sub-helpers).
Pure-FA placeholders remain at 7-8 (depending on whether Phase 4
adds any).
