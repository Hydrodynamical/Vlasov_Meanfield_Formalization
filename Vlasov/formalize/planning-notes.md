# Planning notes — Phase A endpoint and beyond

Cross-cutting planning artifacts not naturally placed in CLAUDE.md (discipline
framework) or `codebase-outline.md` (generated dependency graph).  Use this
file for: decisions-pending, banked P5 atom-level findings for upcoming
sessions, and Phase B sequencing.

---

## Banked P5 findings for upcoming sessions

### Stage 6 t=0 boundary close — infrastructure shape

**Banked 2026-05-31** (post commit `81c1748`, ahead of the planned Stage 6
session 2 sessions out).

**Sub-sub-sorry**: `CharacteristicFlow.lean` L8572, inside
`vlasovWellPosedness_universal_existence`'s narrow continuity conjunct
(`ContinuousOn (fun t => ∫ z, g z ∂f t) (Set.Ici 0)`), the right-continuity-
at-t=0 case after `rw [← h_eq]`.

**P5 finding: `hasDerivAt_of_hasDerivAt_of_ne_in_nhds` does NOT apply directly**.
Stage 6 t=0 is a `ContinuousWithinAt`-at-endpoint problem (continuity of the
integral function at `t = 0` within `Ici 0`), not a `HasDerivAt`-at-interior
problem.  The helper's signature assumes the point is interior to a
neighborhood where HasDerivAt holds at every nearby ≠ point; t=0 is the LEFT
endpoint of `Ici 0`.

**Applicable close path**: same Mathlib DCT pattern as h_cont_f LEFT/RIGHT
(commits `360813f` + `81c1748`), but applied at the t=0 endpoint:

1. `continuousWithinAt_of_dominated` with constant bound `Cg` (from
   `Bornology.IsBounded (Set.range g)` hypothesis already in scope).
2. AEStronglyMeasurable + bound + integrable_const (standard).
3. Pointwise continuity at t=0 from the right via boundary regularity from
   the per-window `IsLagrangianVlasovSolutionOn` solutions.
4. Bridge `f t = (charX_N t, charV_N t)#(f 0)` for t ∈ Icc 0 N (already
   used in the existing t₀ > 0 branch above the sorry).

**Sub-finding: boundary regularity exposure required**.  Stage 6's
`_universal_existence` body destructures `h_sol_lag N` (L8589) to extract
only basic conjuncts of `IsLagrangianVlasovSolutionOn` (PDE, flow,
pushforward, AEMeasurable).  Boundary regularity from `vlasovWellPosedness_local`'s
output bundle is NOT currently threaded through.

Two options:

* **(a) Enrich** `_universal_existence`'s destructure to extract boundary
  regularity from `vlasovWellPosedness_local`'s output bundle.  Small
  threading change (~30-50 lines) since `vlasovWellPosedness_local` already
  produces the boundary bundle.
* **(b) Inline-derive** boundary continuity from `IsCharacteristicFlowOn`'s
  HasDerivAt-on-Ioo data.  Awkward — `IsCharacteristicFlowOn` provides no
  data at t = 0 directly (Ioo excludes endpoints).

Option (a) is the likely path.

**Estimated total Stage 6 t=0 close**: ~80-100 lines (smaller than h_cont_g
since the DCT pattern is now well-exercised in this arc).

**Cluster retirement contribution**: closes the only remaining sub-sub-sorry
in `vlasovWellPosedness_universal_existence` → Stage 6 declaration retires
(after h_cont_g closes _glue_step).

---

## Phase B sequencing — deliberate decision pending

**Banked 2026-05-31**, decision required before Phase A endpoint arrives
(estimated 3-4 focused sessions out, after h_cont_g + Stage 6 t=0 close +
any residual L≥1 / `MathlibTODO_dobrushin_uniqueness_On` items).

**Question**: post-Phase-A, which of these comes first?

* **Cleanup document phase**: write the project's final research artifact
  documentation — codebase outline regeneration, Mathlib PR drafts for the
  closeable `MathlibTODO_*` placeholders (probably 2-3 of the 4-5
  remaining), the M-series statement-correction narrative (the marquee
  forward-only refactor), the four-series discipline framework summary
  as a process retrospective.
* **W̄ refactor phase**: discharge the `L ≥ 1` regime sub-sub-sorry by
  replacing the per-ball-flow's `(T + 1)²` additive offset with a `T²`-
  shape via Dobrushin's truncated metric W̄.  Removes the `0 < L < 1`
  restriction from `vlasovWellPosedness`'s scope.  Substantively closes
  the marquee for all Lipschitz regimes.

**Decision affects**:

* **Mathlib PR drafting order**: the cleanup phase's PR drafts compose
  against the project's current Mathlib placeholder set.  If W̄ refactor
  reduces placeholder count (e.g., by retiring `MathlibTODO_convolveLipschitzEstimate`
  if its role changes under W̄), the PR drafts shift.
* **Cleanup document's marquee framing**: cleanup-first means the document
  reads "0 < L < 1 regime, with L ≥ 1 as deliberate W̄-refactor-pending
  out-of-scope item."  W̄-first means the document reads "full Lipschitz
  range, complete formalization."
* **Session-cadence over Phase B**: cleanup phase is documentation-heavy
  (lower per-session line count, higher information density), W̄ refactor
  is execution-heavy (~200-400 line sessions per the per-ball-flow surgery
  estimate).  The session-cadence watch-list pattern (P6 + alternation)
  suggests interleaving them rather than running purely sequentially —
  but the *starting* phase matters for project narrative coherence.

**Trade-off shape**:

* **Cleanup-first pros**: ships a complete documentation artifact at the
  earliest moment; cleanup phase is well-suited to current operating mode
  (mostly text + reformulation); allows W̄ refactor to be planned with
  cleanup-phase insight on what's actually used downstream.
* **Cleanup-first cons**: documents an incomplete-Lipschitz-range result;
  W̄ refactor's downstream effects on documentation require a second
  cleanup pass.
* **W̄-first pros**: ships a Lipschitz-complete result; cleanup phase
  documents the final state cleanly without revision.
* **W̄-first cons**: defers documentation by 2-4 sessions; W̄ refactor's
  exact scope is currently uncertain (Mathlib infrastructure for
  W̄ + Dobrushin's truncated estimates is not well-trodden in current
  Mathlib).

**Decision deadline**: the session AFTER h_cont_g lands (i.e., before the
Stage 6 t=0 session), per the user's framing.  At that point Phase A
endpoint is 1-2 sessions away and the post-Phase-A sequencing becomes
load-bearing for the next strategic conversation.

**Decision currently held as**: pending.  No commitment.  Both paths remain
viable.  The strategic conversation should revisit explicitly at the
recommended deadline rather than letting Phase A endpoint arrive with the
sequencing un-decided (which would force an ad-hoc choice).
