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

### h_cont_g path-choice — decision pending

**Banked 2026-05-31** (P5 verification of `MathlibTODO_convolveLipschitzEstimate`
at the planned h_cont_g session's open).

**Sub-sub-sorry**: `CharacteristicFlow.lean` L7559, inside `_glue_step`'s
case (a) close (the last remaining sub-sub-sorry of `_glue_step`'s body
— h_cont_g is the cluster-retirement gate for `_glue_step`).

**P5 finding**: `MathlibTODO_convolveLipschitzEstimate` (Basic.lean L1405)
provides a **W₁-Lipschitz bound on the convolution at a fixed point**:
```
‖convolveFunctionMeasure gradW ρ x - convolveFunctionMeasure gradW σ x‖
    ≤ (L : ℝ) * (wasserstein1 ρ σ).toReal
```
NOT direct continuity-in-time-of-the-measure.  To close h_cont_g via this
placeholder, two additional pieces are needed:

1. **W₁-continuity of `t' ↦ spatialMarginal(f_next t')` at T** — to apply
   the bound's RHS.  Stronger than narrow continuity (which h_cont_f
   proved via DCT on the pushforward equation).  W₁ vs narrow gap requires
   moment-uniformity bridge (Villani-style stability under narrow
   convergence), itself a non-trivial Mathlib gap.
2. **Joint continuity in (μ, x) of `convolveFunctionMeasure`** — for the
   x-side of the integrand argument (`charX_prev t' z`'s variation in t').

**Path options** (decision required before h_cont_g substantive close
attempt):

* **Option A — Direct-DCT via explicit pushforward**.  Express the
  convolution via pushforward: `conv(spatialMarginal(f_next s), x) =
  ∫ z, gradW(x - charX_prev s z) ∂f₀`.  Continuity in s via continuity of
  charX_prev + DCT on f₀.  Bound: `‖gradW(x - charX_prev s z)‖ ≤
  ‖gradW(0)‖ + L * ‖x - charX_prev s z‖` — linear growth in z, NOT
  uniformly bounded.  Requires careful bound via flow-distance-growth-
  bound to dominate.  **Substantive scope**: ~200-300 lines per side
  (LEFT, RIGHT), ~400-600 lines total.  **No new Mathlib placeholder**.

* **Option B — Add `MathlibTODO_convolveContinuousFromNarrowContAndMoment`
  placeholder**.  States the W₁-stability-under-narrow-convergence
  corollary directly: if `t ↦ μ t` is narrowly continuous at t₀ with
  uniform-in-t finite first moment near t₀, and gradW is Lipschitz, then
  `t ↦ convolveFunctionMeasure gradW (μ t) x` is continuous at t₀ for each
  x.  Plus a Joint-continuity version covering the x-side.  **Substantive
  scope**: ~100-200 lines per side using the placeholders.  **+1 (or +2)
  new MathlibTODO declaration(s)** matching project's existing pattern
  (per the four `MathlibTODO_*` placeholders + `MathlibTODO_dobrushin_uniqueness_On`
  + `MathlibTODO_cauchyW1_hasNarrowLimit` existing precedent).

* **Option C — Reformulation avoiding convolution-continuity**.
  Restructure h_cont_g's proof to bypass continuity of the convolution-
  integrand entirely.  E.g., bound the integral DIFFERENCE directly via
  Lipschitz bounds without separating the convolution.  **Substantive
  scope**: unclear — requires invention.  **Risk**: high; possibly stuck
  on the same fundamental gap.

**Trade-offs**:

* **A pros**: no new placeholders; final close is fully substantive in
  the project.  **A cons**: ~400-600 line substantive close session, the
  highest line-count session in the recent arc.  Variance high due to
  flow-distance-growth-bound integration with DCT.
* **B pros**: ~100-200 line close + 1-2 new clearly-deferrable placeholders,
  matches project's MathlibTODO discipline.  Cluster retires `_glue_step`
  declaration (sub-sub-sorry net zero: -1 h_cont_g, +1-2 placeholders, but
  `_glue_step` declaration retires).  **B cons**: adds placeholder(s) to
  the Mathlib-track inventory.
* **C pros**: avoids the W₁ gap entirely.  **C cons**: unknown
  feasibility; not a documented approach.

**Recommendation lean**: Option B.  Matches project's MathlibTODO discipline
(the four abstract placeholders + the two recent additions already
establish the pattern), gives the cleanest cluster retirement (_glue_step
declaration retires, structural debt shifts to a focused leaf placeholder),
and the substantive close composes against well-characterized Mathlib gaps
rather than requiring novel infrastructure.  Decision belongs to user;
documented here for explicit strategic conversation rather than ad-hoc
session execution.

**Decision deadline**: before the h_cont_g session begins.  Per session-
cadence discipline, the strategic conversation needs the option-set
pre-loaded so the session opens as type-(a) execution-mode against a
verified plan rather than type-(b) diagnostic-mode mid-close.

**Decision committed (2026-05-31)**: option B per user authorization.
Placeholder `MathlibTODO_convolveContinuousAtOfNarrowMoment` landed in
commit `a123d63` (Basic.lean L1424+).

**h_cont_g substantive close — scope re-estimate** (post-placeholder
landing, 2026-05-31):

The user's original estimate ("~100-200 lines, bridge-and-compose")
assumed the auxiliary narrow + moment + integrability properties for
`spatialMarginal ∘ f_next` were already in scope or trivially derivable.
They're not — the project's existing infrastructure provides narrow
continuity for the SPECIFIC h_cont_f integrand (compact-support φ), not
the general bounded continuous test functions the placeholder requires
for its narrow-continuity hypothesis.  Plus moment continuity isn't in
scope at all.

**Realistic scope re-estimate**:

* **Sub-helper 1**: narrow continuity of `t ↦ spatialMarginal(f_next t)`
  at T for general bounded continuous test functions.  ~50-80 lines
  (h_cont_f's pattern generalized from compact-support to bounded-range).
* **Sub-helper 2**: moment continuity of `t ↦ ∫ ‖y‖ ∂(spatialMarginal(f_next t))`
  at T.  ~50-80 lines (DCT with flow-distance-growth-bound dominator).
* **Sub-helper 3**: convolution integrability uniformity across t.
  ~30-50 lines (Lipschitz + moment finiteness).
* **h_cont_g main close** composing sub-helpers 1-3 + placeholder + outer
  DCT.  ~100-200 lines per side (LEFT + RIGHT) + union.

**Total realistic**: ~330-540 lines.  Above the user's ~100-200 estimate
by a factor of ~2-3x.  Substantively achievable but requires multi-
commit structuring per P4 API-lock pattern.

**Recommended decomposition** (per P4 discipline for dense composition):

* Commit 1 (this commit's predecessor `a123d63`): placeholder landed.
* Commit 2: sub-helper 1 (narrow continuity for general bounded
  continuous integrands).  ~80 lines.  Single focused close.
* Commit 3: sub-helper 2 (moment continuity).  ~80 lines.  Single focused
  close.
* Commit 4: h_cont_g LEFT substantive close composing sub-helpers + placeholder.
  ~150 lines.  Single focused close.
* Commit 5: h_cont_g RIGHT substantive close mirroring LEFT.  ~150 lines.
* Commit 6: union for h_cont_g → `_glue_step` cluster retirement.
  ~20 lines.

**Session-budget allocation**: 2-3 focused sessions per the per-commit
estimate.  Phase A endpoint shifts from "3-4 focused sessions" to
"4-5 focused sessions" with this revised scope.

**Per session-cadence**: each commit above is a type-(a) execution
session with pre-loaded brief from the preceding commit's residual
structure.  No diagnostic pivots expected since the path is now
characterized end-to-end.

## Phase B sequencing — recommendation registered (2026-05-31, post Phase 1.5)

**User-voiced recommendation (post Phase 1.5)**: **cleanup-document
first**, W̄ refactor as deliberate post-cleanup arc.

**Rationale**:
* Phase 1.5's decomposed inventory (7 pure-FA MathlibTODOs vs project-
  internal compositions vs substantive containers) means cleanup
  document drafting can begin at Phase A endpoint without waiting for
  W̄ refactor.
* W̄ refactor improves the marquee theorem (closes the `L ≥ 1` regime)
  but does NOT change the pure-FA MathlibTODO contribution arc.  The
  cleanup document's strongest external framing — "7 pure-FA placeholders
  characterized as bucket-1 / bucket-2 Mathlib PR units" — is independent
  of W̄ refactor's status.
* Cleanup-first lets the project ship its external artifact at the
  earliest moment.  W̄ refactor follows as deliberate scope expansion
  rather than blocking on the original ~2-3 session estimate.

**Status**: recommendation, not yet committed decision.  Strategic
conversation can revisit at Phase A endpoint.  Default per current
recommendation: cleanup-first.

---

## Phase 3 scope re-estimate — composition lemmas are NOT one-liners (P2 finding, 2026-05-31)

**P2 firing** during attempted Phase 3 execution: atom-level reading of
the 6 Phase 1.5 composition lemmas reveals the "one-liner pattern
expected for most" framing in the brief was overly optimistic.

**Concrete issue** (illustrated with `vlasovTrajectoryLipschitzBound`):
the composition lemma's signature, inherited from the original mixed
MathlibTODO, does NOT carry the hypotheses the pure-FA placeholder
requires:
* Missing: `L : NNReal`, `hL : LipschitzWith L gradW`,
  `[∀ t, IsProbabilityMeasure (ρ t)]`, `h_int : ∀ t x, Integrable
  (fun y => gradW (x - y)) (ρ t)`.
* These are needed by `vlasovVectorField_lipschitzWith` (project's existing
  joint-flow Lipschitz proof, which the composition would compose against).

The original mixed MathlibTODO sorried these away.  The composition can't
just `apply` the pure-FA placeholder; it needs to first GAIN these
hypotheses (via signature restate) or DERIVE them inline (often impossible
when the constants like `L` aren't passed at all).

**Closure-path scope re-estimate per composition**:
* `picardCharFlow_aemeasurable`: needs signature restate to add L, hL,
  IsCharacteristicFlow → joint flow construction.  ~40-60 lines.
* `vlasovTrajectoryLipschitzBound`: similar.  ~40-60 lines.
* `dobrushin_uniqueness_On`: needs Vlasov vector field construction +
  Gronwall integration + W₁-zero characterization.  ~80-120 lines.
* `w1ContOn_lscNarrow_via_pureFA`: needs narrow-continuity extension
  from compact-support to bounded continuous (substantive in itself).
  ~60-100 lines.
* `w1ContOn_uscNarrow_via_pureFA`: needs IsLagrangianVlasovSolution
  upgrade for pushforward extraction.  ~80-100 lines.
* `wassersteinGronwallCoupling_derivBound_via_pureFA`: same as above
  + vector-field-difference bound.  ~100-120 lines.

**Total realistic Phase 3 scope**: ~400-560 lines across 6 commits OR
3-4 focused sessions (multi-commit per session).  NOT a single focused
session as the brief projected.

**Revised Phase 3 plan**:
* Treat each composition lemma as its own focused-session unit
  (or pair of compositions per session for the smaller items 1, 2).
* Items 1, 2 (~40-60 lines each): one combined session.
* Items 4, 5, 6 (~60-120 lines each): one session per item, OR combine
  items 5+6 (similar Lagrangian-pushforward shape).
* Item 3 (dobrushin): possibly its own session due to Gronwall + W₁-zero
  composition.

**Realistic Phase 3 total**: ~3-5 focused sessions.

**Sorry-count trajectory revision**:
* Original projection (brief): 16 → 10-12 in one Phase 3 session.
* Revised: 16 → 10 across 3-5 sessions (each composition closure
  removes 1 sorry from the composition lemma).

**Underlying cause**: Phase 1.5's design committed to making the
compositions Vlasov-specific bridge work with sorry'd bodies, deferring
substantive closure to Phase 2-4.  The brief's "one-liner" framing
assumed the body closures would be trivial — but the bridge work IS the
Vlasov-to-pure-FA hypothesis translation, which is non-trivial.

**Phase 1.5 retrospective sighting**: this is the design-doc projection
operating honestly — the projection said the 6 compositions land "each
close trivially via one-line `apply`" but with atom-level verification
this turns out to need additional hypothesis-threading.  The brief's
"one-liner pattern" was extrapolation from the projection rather than
verified.  P5 caught it (this turn).

**Strategic note**: this doesn't change the Phase A endpoint trajectory
materially.  The total work is still ~6-8 sessions; just the distribution
shifts (Phase 3 grows from 1 to 3-5 sessions; Phase 4 stays the same;
some Phase 2 work folds into Phase 3 as composition closures pull in
hypothesis-design questions).

**Phase 3 next-session brief (revised)**:
* Pick items 1 + 2 (the smallest, similar Lipschitz-flow closures).
* Restate each composition's signature to add the necessary hypotheses
  (`L : NNReal`, `hL : LipschitzWith L gradW`, etc.).
* Update consumers (1-2 per composition) to provide the new hypotheses.
* Substantively close the body via pure-FA + joint-flow construction.
* Target: 2 composition closures in 1 session.

---

## Phase 3 Session 2 outcomes (2026-05-31)

**Item 2 (`vlasovTrajectoryLipschitzBound`) substantively closed**.
Commit `ddf3cd0`.  Sorry trajectory: 16 → 15.  Cascade through 3
declarations + 1 call site (~80 lines including signature restates
through `vlasovSolutionViaPushforward_isVlasovSolution`,
`_isLagrangianVlasovSolution`, and the marquee L=0 case).  Body closed
via 6-line composition: `prodMk` of HasDerivAt clauses +
`vlasovVectorField_lipschitzWith` Lipschitz constant + pure-FA placeholder.

**Item 1 (`picardCharFlow_aemeasurable`) deferred via P2**: atom-level
reading revealed the pure-FA placeholder
`MathlibTODO_lipschitzFlowAEMeasurable` requires `∀ z t, HasDerivAt`
(universal-t), but Vlasov flow from `IsCharacteristicFlowOn` only gives
HasDerivAt on `Set.Ioo 0 T`.  Mismatch.

**Closure paths for item 1**:
* **Option A**: restate pure-FA placeholder to take per-set HasDerivAt
  hypothesis (`∀ z, ∀ t ∈ s, HasDerivAt ...` for some set s).  Requires
  placeholder refinement (not a new placeholder — refining an existing
  Phase 1.5 statement).  Ripples to composition lemma's output if
  consumer needs universal AEMeasurable.
* **Option B**: project composition restated to limit output to
  `∀ s ∈ Set.Icc 0 T, AEMeasurable ...` (matching IsCharacteristicFlowOn's
  domain).  Ripples to `_picard_fixedPointFlow`'s consumer site
  (`h_aemeas_out`) which currently uses `∀ s` universal.
* **Option C**: substantive close via Picard regularity (continuity-in-z
  derivable from Lipschitz vector field + Picard fixed-point).  Avoids
  HasDerivAt-based hypothesis entirely.  ~50-100 lines.

**Decision deferred to next focused session**: Option A appears cleanest
(placeholder refinement matches the standard "ODE on a time domain"
formulation; doesn't require redoing the composition's output type).
Strategic conversation can confirm at next session open.

**Phase 3 progress after this session**:
* Items closed: 2 (item 2).
* Items remaining: 5 (items 1, 3, 4, 5, 6).
* Sorry trajectory: 16 → 15 (-1 this session; estimate -5 more across
  the next 3-4 sessions).

**Next-after-next session brief**:
* Decide on item 1 close path (Option A vs B vs C).
* If Option A: refine `MathlibTODO_lipschitzFlowAEMeasurable` statement;
  close `picardCharFlow_aemeasurable` body.  Estimated ~40 lines.
* If Option B: restate composition output; update consumer; close
  body.  Estimated ~60 lines.
* If Option C: substantive Picard-regularity inline.  Estimated ~80-100
  lines.
* Then proceed to items 3, 4 (or 5, 6 if combined).

---

## Item 1 deeper analysis (2026-05-31, post-Item-2 attempt)

**Atom-level reading update on the consumer cascade**: `_picard_fixedPointFlow`'s
output `h_aemeas_out : ∀ s, AEMeasurable ...` (universal s) is consumed by
`_finalAssembly_isLagrangian`'s body in the
`IsCharacteristicFlowSelfConsistent` step.  The SelfConsistent predicate
quantifies `∀ t, ρ t = Measure.map (charX t) f₀`, which uses `h_aemeas t`
for ALL t (not just Icc 0 T).

**Cascade implications**:
* **Option B (restate composition output)** would require either:
  - Weakening `IsCharacteristicFlowSelfConsistent` to set-restricted form
    (architectural change to a core project predicate).
  - Threading the universal-t AEMeasurable hypothesis from elsewhere
    (where? — IsLagrangianVlasovSolution's AEMeasurable conjunct is also
    set-restricted).
* **Option A (refine pure-FA placeholder)** doesn't help directly — the
  refined placeholder still provides set-restricted conclusion, which
  doesn't satisfy the universal consumer.
* **Option C (substantive Picard regularity inline)** bypasses the
  cascade by constructing AEMeasurable from the project's own
  Stage 1.9 flow construction details, without going through the
  pure-FA placeholder.  ~80-100 lines but doesn't ripple to other
  declarations.

**Revised recommendation**: Option C.  Bypasses the cascade entirely.
The pure-FA `MathlibTODO_lipschitzFlowAEMeasurable` remains in the
Mathlib OT contribution arc as a banked placeholder for other potential
consumers; the in-project AEMeasurable witness routes through
substantive Picard regularity.

**Or**: defer item 1 entirely.  The IsCharacteristicFlowSelfConsistent
universal-t issue is genuinely a deeper architectural question
(arguably the predicate IS overstated and should be weakened to
match the construction's actual domain).  Phase A endpoint trajectory
isn't materially impacted by deferring item 1 — it just means the
`MathlibTODO_lipschitzFlowAEMeasurable` placeholder ships with the
project as a "consumer-pending" placeholder in the Mathlib contribution
arc, while `_picard_fixedPointFlow`'s `h_aemeas_out` remains sorry'd
as a substantive Phase 2-4 close target.

**Decision pending**: Option C vs deferral.  Strategic conversation at
next session open should resolve this.

---

## Phase 3 Session 3 outcomes (2026-05-31)

**User decision on item 1**: Defer to Phase 4 (user message:
"On item 1: Defer Phase 4. Continue.").  Item 1 stays as sorry'd
composition with `_picard_fixedPointFlow`'s `h_aemeas_out` still a
Phase 2-4 close target.

**Item 4 (`w1ContOn_lscNarrow_via_pureFA`) substantively closed via
API-lock decomposition pattern (P4)**.  Sorry trajectory: 15 → 15
(net 0; one body close + one new sub-placeholder).

**Mechanism**: rather than absorbing the smooth-CS → BC narrow-continuity
extension into item 4's body (~60-100 lines of mollifier + truncation
argument requiring Mathlib infrastructure the project doesn't have), the
extension step is decomposed into a new pure-FA sub-placeholder
`MathlibTODO_bcNarrowFromSmoothCompactNarrow` (Bucket-1 Mathlib-extension
scope).  Item 4's body becomes a clean 4-step orchestration:
1. Extract `IsProbabilityMeasure` from `HasFiniteFirstMoment`.
2. Smooth-CS narrow continuity via `W1ContOn_integralContAt` (project's
   existing helper, routes through `IsVlasovSolution.WeakEvolutionEq`).
3. Extend smooth-CS → BC via new `MathlibTODO_bcNarrowFromSmoothCompactNarrow`.
4. Apply pure-FA `MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves`.

**Structural improvement vs sorry-count**: declaration sorry count
unchanged (15 → 15), but the actual deferred mathematical work is now
named explicitly as a Bucket-1 pure-FA target with its own docstring,
proof sketch, and Mathlib-PR scoping.  The Vlasov composition body is
visible as orchestration rather than absorbing-the-difficulty.  This is
the API-lock pattern (P4) operating at the sub-placeholder level: the
composition's interface is closed, the substantive close work is
identified as a distinct, smaller, Bucket-1-correctly-scoped unit.

**Reorder note**: as part of this session, `W1ContOn_integralContAt`
(Basic.lean) was moved from after the LSC/USC placeholders to before
them, so item 4's body can consume it without forward-reference.

**Phase 3 progress after this session**:
* Items closed: 2 (item 2 substantively in Session 2; item 4 via
  API-lock decomposition in this session).
* Items deferred to Phase 4: 1 (item 1).
* Items remaining for Phase 3: 3 (items 3, 5, 6).
* Sorry trajectory: 16 → 15 (Session 2) → 15 (this session; +1 new
  pure-FA sub-placeholder, -1 item 4 body).

**Lessons compounding from this session**:
* **P5** (discipline framework's pattern-extrapolation needs atom-level
  verification): the prior session's brief identified item 4 as the
  "next independent target" but P1 atom-level reading revealed
  substantive close requires ~60-100 lines of mollifier infrastructure.
  Without P5, would have attempted inline close and likely produced a
  P2 cascade or budget overrun.
* **P4** (API-lock-vs-substantive-proof): the API-lock pattern
  generalizes from "theorem-level signature lock + sorry'd body" to
  "composition-body close via sub-placeholder decomposition."  The
  underlying principle is the same: separate interface stabilization
  from substantive proof discharge.
* **B1** (predicate enrichment over per-site bridging) generalizes
  symmetrically: when a composition's body would absorb substantial
  pure-FA infrastructure, decompose by naming the pure-FA step as a
  sub-placeholder.  This is the "extract-an-abstraction" move at the
  proof-body level (vs B1's at the predicate level).

**Next-session brief**:
* Items 5 and 6 share the same shape (both need IsLagrangianVlasovSolution
  upgrade for pushforward extraction; both compose against
  Lagrangian-pushforward pure-FA placeholders).  Same architectural
  question as item 1 (Lagrangian-upgrade through consumer chain).
  Per the item 1 deferral pattern, items 5+6 likely also defer to
  Phase 4 unless a sub-placeholder decomposition similar to item 4 is
  available.
* Item 3 (`dobrushin_uniqueness_On`): depends on item 6's substantive
  close OR on a sub-placeholder decomposition.  Plausibly also defers.
* **Phase 3 endpoint estimate revised**: items 2 + 4 closed (2 of 6);
  items 1, 5, 6 deferred to Phase 4 architectural swing; item 3 deferred
  pending item 6 status.  Realistic Phase 3 endpoint: 2 of 6
  substantively closed via Phase 3 mechanics; 4 of 6 reclassified to
  Phase 4 architectural work.
* Phase B sequencing (cleanup-first) becomes more attractive: the
  Phase 4 architectural swing (Lagrangian-upgrade cascade) is a clear
  load-bearing decision worth documenting before more piecemeal work.

**Phase 3 Session 2 deliverable summary**:
* Item 2 closed substantively (sorry 16 → 15).
* Item 1 atom-level analysis revealed deeper cascade; deferred.
* Net: 1 of 6 compositions closed.

---

## Phase 3 Session 3 — items 5/6 verification (P5 sighting #4)

**P1 atom-level reading on items 5/6's API-lock decomposition feasibility**
(post-item-4-close, same session as the above):

Considered closing items 5/6 via the same API-lock decomposition pattern
that worked for item 4 — add a `MathlibTODO_superpositionPrinciple_Lagrangian`
sub-placeholder for DiPerna-Lions superposition (extract Lagrangian flow
witnesses from `IsVlasovSolution`), then orchestrate via the pure-FA
USC/derivBound placeholders.

**Atom-level reading revealed cross-file infrastructure dependency**:

* The Vlasov phase-space vector field `b(t, z) := (z.2, -convolveFunctionMeasure
  gradW (spatialMarginal (f t)) z.1)` needs to be proved `max(1, L)`-Lipschitz
  to feed `MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows`'s `_hL_f`
  hypothesis.
* The Lipschitz proof routes through `convolveFunctionMeasure_lipschitz_in_x`
  (CharacteristicFlow.lean L75) + `Prod.norm`-style arithmetic for the
  phase-space joint Lipschitz constant.
* `convolveFunctionMeasure_lipschitz_in_x` lives in
  `Vlasov/OT/CharacteristicFlow.lean`, which **imports** Basic.lean.
  Items 5/6 currently live in Basic.lean.

**Three options to bridge the cross-file dependency**:

1. **Move items 5/6 + new placeholder to CharFlow.lean**: significant
   relocation (~100-200 lines), affects the natural placement of the
   placeholder family.
2. **Re-prove `convolveFunctionMeasure_lipschitz_in_x` in Basic.lean**:
   duplicates ~30 lines of proof; creates two-fold maintenance burden.
3. **Defer to Phase 4 architectural swing**: the Lagrangian-upgrade
   cascade is the cleaner architectural decision; both items 5/6
   substantive close paths converge on it.

**Decision**: option 3 (defer).  This matches the next-session brief's
recommendation and avoids per-session piecemeal architectural moves.
The Phase 4 swing will handle items 1, 3, 5, 6 together as a
coordinated Lagrangian-upgrade refactor (or via the API-lock
decomposition pattern executed in the right file structure).

**P5 sighting #4**: pattern-extrapolation said "item 4's API-lock
decomposition pattern should work for items 5/6 too."  Atom-level
verification revealed the cross-file infrastructure dependency that
makes the pattern non-trivially applicable in Basic.lean.  Without
P5, would have attempted the decomposition and hit either (a) cross-
file circular import (option 2 attempted) or (b) ~150-200 line
relocation work mid-session (option 1 attempted).

**Confirms Phase 3 endpoint**: 2 of 6 closed (items 2, 4); 4 of 6
deferred to Phase 4 (items 1, 3, 5, 6).  Phase 3 mechanics have
exhausted the items they can close without architectural commitment.

**Phase B sequencing recommendation strengthened**: cleanup-first
becomes even more attractive.  The Phase 4 architectural swing is
clearly the next strategic decision.  Documenting Phase 1.5 + Phase 3
outcomes + the Phase 4 architectural prompt as a cleanup deliverable
loads the right context for the Phase 4 decision.

---

## Phase B sequencing — deliberate decision pending (legacy section)

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

---

## Phase 4 Path A Stage 2 — relocation decisions and Stage 2b brief (2026-05-31)

**Stage 1 landed** (commit `abb5568`).  The 10-declaration consumer chain
now takes `IsLagrangianVlasovSolution`; sorry 15 → 15 (pure signature
cascade as predicted).

**Stage 2 entry — architectural decision on items 5/6 close path
(settled by user, 2026-05-31)**:

**Relocate items 5/6 (and the dobrushin chain that depends on them) from
Basic.lean to CharFlow.lean.**  Not a toss-up — forced by the import
direction:

* Basic is the base; CharFlow imports Basic (line 33); Coupling imports
  Basic (line 29); nothing imports back into Basic.
* `convolveFunctionMeasure_lipschitz_in_x` lives in
  CharFlow.lean L75; items 5/6's substantive close requires it.
* The "duplicate ~30 lines in Basic" option is **forced** duplication
  (the only way to feed Basic something it can't import), not a
  convenience choice — and it puts a second copy of a delicate Lipschitz
  estimate next to the family where the q < 1 structural-debt bug lives.
  Two copies of the same bound is exactly the drift surface M-series
  discipline says to avoid.
* Precedent: `vlasovWellPosedness` already moved to CharFlow "so its
  proof can compose with the flow infrastructure."  Items 5, 6 are the
  identical case — flow-dependent proof content sitting in the statement
  layer.  Relocation fixes a layering miscategorization, not just dodges
  duplication.

**The dobrushin chain ripple (must budget)**:

Relocating items 5, 6 forces the consumer chain that depends on them to
follow, because Basic-resident declarations can't call CharFlow
declarations.  Chain to relocate:

* `w1ContOn_uscNarrow_via_pureFA` (Basic L1939, sorry'd) — Phase 3 item 5
* `wassersteinGronwallCoupling_derivBound_via_pureFA` (Basic L2098, sorry'd) — Phase 3 item 6
* `MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (Basic L1993, proved)
* `wassersteinGronwallCoupling_real_bound` (Basic L2141, proved)
* `wassersteinGronwallCoupling_ennreal_mul_comm` (Basic L2167, proved)
* `wassersteinGronwallCoupling_ofReal_le` (Basic L2178, proved)
* `MathlibTODO_wassersteinGronwallCoupling` (Basic L2221, proved)
* `dobrushin_C_choice` (Basic L2239, proved) — depends only on L, could stay in Basic, but cleaner to move with the chain for cohesion
* `convolveDiff_norm_le` (Basic L2249, proved) — wraps `MathlibTODO_convolveLipschitzEstimate`, could stay in Basic
* `wasserstein1_ofReal_exp_monotone` (Basic L2265, proved) — pure real-analysis, could stay in Basic
* `dobrushin_ennreal_bound` (Basic L2277, proved)
* `dobrushin_package_exists` (Basic L2303, proved)
* `dobrushin` (Basic L2334, proved) — **.tex thm:dobrushin marquee**

**Stays in Basic**:
* `DobrushinStabilityEstimate` (Basic L2366, def) — pure `Prop`-valued
  definition, no proof body, naturally lives near `meanFieldLimit`.
* `meanFieldLimit` (Basic L2392) — consumes `hDobrushin` as hypothesis,
  doesn't directly call `dobrushin`'s declaration in its body.

This is the §9 statement→pointer pattern already established for
`vlasovWellPosedness`: the proof content moves to CharFlow; the
external surface remains accessible (here via Basic's `meanFieldLimit`
which takes the Dobrushin estimate as a hypothesis, naturally allowing
either CharFlow's `dobrushin` or another producer to discharge it).

**Stage 2a scope** (this session): relocation only — items 5/6 still
sorry'd at their new CharFlow location.  Build verification.  Sorry
count 15 → 15.

**Stage 2b brief** (next session): substantive close of items 5/6 in
their new CharFlow location.  Steps:

1. Extract flow witnesses from `IsLagrangianVlasovSolution`'s second
   conjunct: `⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f⟩ := hf`.
2. Build Vlasov phase-space vector fields:
   `b_f t z := (z.2, -convolveFunctionMeasure gradW (spatialMarginal (f t)) z.1)`.
3. **Prove `max(1, L)`-Lipschitz of b_f ONCE** (the constant-adjacency
   exploit per user 2026-05-31): position part is 1-Lipschitz via
   `Prod.norm`; convolution part is L-Lipschitz via
   `convolveFunctionMeasure_lipschitz_in_x`; joint constant is `max(1, L)`.
4. Build Φ_f from charX_f, charV_f: `Φ_f t z := (charX_f t z, charV_f t z)`.
   HasDerivAt for Φ_f via `HasDerivAt.prodMk` of hflow_f's position +
   velocity HasDerivAt clauses.
5. Apply pure-FA `MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows`
   (for item 5) and `MathlibTODO_w1RightDerivBoundAlongLagrangianFlows`
   (for item 6).  Estimated ~150-250 lines.

**Key Stage 2b adjacency to exploit (per user 2026-05-31)**: the
`max(1, L)` flow-Lipschitz bound proved in step 3 is the **same constant
the contraction-debt fix needs** (true ratio
`L · (exp((max 1 L) · T) − 1) / (max 1 L) < 1`).  Stage 2b is the
natural place to prove that bound once and thread both:
* the Gronwall composition (items 5, 6 close), AND
* the corrected contraction constraint (where the previously-incorrect
  constraint was `L · (T + 1)² < 1` per the watch-list "additive offsets
  are structurally fatal" entry).

Rather than reopening the same estimate in a separate session, prove
once and use twice.  This collapses two pieces of structural work into
one Lipschitz-bound proof.

**Sorry trajectory under Stage 2b**: 15 → 13 (items 5, 6 close).

---

## Phase 4 Stage 3 — empirical-measure Newton-flow Lagrangian producer (flagged 2026-05-31)

**Backward-compat blind spot in Stage 1 cascade** (per user 2026-05-31):

Stage 1's "backward-compat trivial" framing was true for the marquee
Vlasov solution `f` — `vlasovWellPosedness` produces an
`IsLagrangianVlasovSolution` witness, so callers of upgraded `dobrushin`
or `meanFieldLimit` who use the marquee output Just Work.

**But**: `dobrushin` and `meanFieldLimit` were upgraded to require
`IsLagrangianVlasovSolution` on BOTH arguments.  The second argument in
the mean-field application is the empirical measure curve `μ^N`, NOT
the marquee solution `f`.  `vlasovWellPosedness` produces nothing for
`μ^N` — the Newton flow does.

**While `meanFieldLimit` keeps `hDobrushin` as a hypothesis**, this blind
spot doesn't bite immediately — the caller provides the Dobrushin
estimate directly and Stage 1's cascade doesn't require constructing
`IsLagrangianVlasovSolution` for `μ^N`.  But the moment we instantiate
the Dobrushin estimate for `(μ^N, f)` — i.e., write a proof that
`hDobrushin` holds by appeal to `dobrushin` — the empirical Newton-flow
producer comes due: we'd need to produce
`IsLagrangianVlasovSolution gradW (empiricalMeasureCurve N (X N) (V N))`.

**This is the one outstanding non-rename obligation** introduced by
Stage 1.  Worth a line in the Stage 2 / 3 / cleanup brief so it doesn't
vanish behind "backward-compat trivial."

**The Newton-flow Lagrangian producer (Stage 3 target)**: prove

```lean
theorem newtonSolutionIsLagrangian
    {d : ℕ} [NeZero d] (N : ℕ)
    (gradW : PhysSpace d → PhysSpace d)
    (X V : ℝ → Fin N → PhysSpace d)
    (hSol : IsNewtonSolution N gradW X V) :
    IsLagrangianVlasovSolution gradW (empiricalMeasureCurve N X V)
```

The Newton flow `((X t i, V t i))_{i ∈ Fin N}` itself is the
characteristic flow for the empirical measure; the construction is
direct.  Estimated ~80-150 lines (the IsLagrangianVlasovSolution
predicate's structure has 4 conjuncts, each provable by direct
manipulation of the Newton trajectories).

**Phase 4 endpoint under this Stage 3 work**: caller code can write

```lean
have hLag_N : IsLagrangianVlasovSolution gradW (empiricalMeasureCurve N (X N) (V N)) :=
  newtonSolutionIsLagrangian N gradW (X N) (V N) (hSol N)
have hLag_f : IsLagrangianVlasovSolution gradW f := (vlasovWellPosedness ... ).2.2.1
have hDob_N : DobrushinStabilityEstimate (empiricalMeasureCurve N (X N) (V N)) f C := by
  -- apply dobrushin (now Lagrangian-keyed) with both witnesses
  ...
exact meanFieldLimit ... hLag_f hDob_N ...
```

This is the complete Path A endpoint at the marquee-application level.

**Stage 3 work also retires Phase 3 items 1 and 3** (per the cleanup
doc's analysis) — those items defer to Phase 4 because they need the
Lagrangian-upgrade architectural commitment, which Stage 1 lands and
Stage 2/3 discharge.

---

## Phase 4 Stage 2a — section-tax operational note (2026-05-31)

**Anticipate, don't rediscover**: any future relocation of a declaration
out of Basic.lean pays the same "section-variable tax."  Basic.lean has
`variable {d : ℕ} [NeZero d]` at line 21; declarations inside that
section can omit the explicit binder.  When such a declaration relocates
to CharFlow (or any file without that section variable), the binder must
be added explicitly to the signature.

**Stage 2a empirical confirmation**: 3 declarations
(`dobrushin_ennreal_bound`, `dobrushin_package_exists`, `dobrushin`)
required explicit `{d : ℕ} [NeZero d]` insertions during the relocation.
The build failure at L9381 (`failed to synthesize instance of type
class NeZero d`) surfaced the tax — fixed in one extra round-trip per
declaration.

**Forward note for future relocation work**: at relocation planning time,
grep the proposed move-set for declarations that *omit* `{d : ℕ}` /
`[NeZero d]` binders; pre-flag the explicit additions needed.  Avoids
the build-fail-then-fix loop pattern.

This is operational discipline, not promotion-worthy (a single project
quirk).  Documented inline here so the next relocation arc has the
heads-up loaded.

---

## Phase 4 Path A Stage 2b part 3 — LocalSmallness soundness fix scope (diagnostic, 2026-05-31)

**Framing (verbatim, do not re-rank by sorry-count delta)**:

This corrects a false lemma currently in the tree: `LocalSmallness L T`
is defined at CharFlow L3840 as `(L:ℝ)·(T+1)² < 1`, which does not imply
the genuine contraction constraint.  This is a **soundness fix**.  It
does not move the sorry count.  It **blocks faithfulness of everything
above the local-existence step**.  Do not let any future ordering pass
re-rank it by sorry-count delta — it is invisible to that metric by
nature.

**Why this category needs naming**: every other Phase 4 item retires a
sorry that stands for a *true-but-unproven* lemma.  The `q < 1` gate at
`_picard_fixedPointFlow` (CharFlow L6503) stands for a *false* lemma
that currently typechecks.  Those are not the same priority class.
Trackers ordering by line-count or sorry-count delta will systematically
mis-rank this fix because it does not *move the sorry count at all* —
it corrects a constant in an already-"closed" surface.  Re-list it as
**soundness fix, sorry-count invariant, blocks faithfulness above
local existence** at every future ordering pass.

### The corrected constraint (target, pinned)

```
(L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) < 1
```

Inherited off `vlasovVectorField_lipschitzWith` (CharFlow L629) — the
joint phase-space Lipschitz constant of the Vlasov vector field is
`max(1, L)`, threaded through `Phi_supW1_contraction`'s Gronwall output.
Same constant as items 5/6's diff-bound (commit `33e8baa`, `e9d9aa4`)
— banked once, used three times: items 5, 6, and this soundness fix.

For the `0 < L < 1` W₁-regime the marquee theorem operates in,
`max 1 L = 1`, and the constraint simplifies to `L · (exp T - 1) < 1`.

### The fix mechanism (constraint lemma + citation sites, NOT inline re-derivation)

1. **Redefine `LocalSmallness L T`** (CharFlow L3840) to the corrected
   form above.  Single edit.
2. **Add one named consequence lemma** `q_lt_one_of_localSmallness`
   citing `vlasovVectorField_lipschitzWith` for the `max(1, L)` constant.
   Signature sketched below.
3. **Audit every site that currently unfolds `LocalSmallness` or
   internally derives the `q < 1` ratio** — replace each local
   derivation with a citation to the named consequence lemma.

**Critical discipline (the trap the user surfaced 2026-05-31)**: do not
re-derive the corrected ratio inline at any structural site.  The
original `q < 1` bug was not the wrong number; it was the local
derivation pattern at `_picard_fixedPointFlow` L6502-L6503 ("Sub-sub-
sorry: q < 1 from hTL").  Fixing the instance by recomputing the ratio
inline at that site rebuilds the exact mechanism that produces the next
bug.  Fix the mechanism, not just the number.  Three citation sites
(per user framing); reality is 6-8 (audited below).

### Cosmetic / structural triage table (this session's deliverable)

Each LocalSmallness consumer classified by whether the existing proof
survives the definition swap with a citation update only (cosmetic) or
needs its internal algebraic estimate reworked (structural).

| Site (line) | Owner | Class | Triage reason |
|---|---|---|---|
| L4187, L4222 | `exists_vlasov_perz_trajectory` | **structural** | Body computes `R := N(z) / (1 - L·(T+1)²)` (L4204-L4210); R selection depends on the `(T+1)²` shape.  Comment at L4212-L4221 explicitly documents the metric-dependent algebra.  Under the exp form, R needs to be reselected via the new contraction constant, and the algebraic R bound at L4225-L4239 reworked. |
| L4408, L4433 | `exists_vlasov_characteristicFlow_global_smallT` | cosmetic | Forwards `hTL` to `exists_vlasov_perz_trajectory` at L4433.  No internal unfold.  Survives intact once the per-z trajectory's signature stays `LocalSmallness L T`. |
| L5217, L5247 | `existsCharacteristicFlowMappingFor_picard_step` (approx; uses `ρ.extend`) | cosmetic | Forwards `hTL` to `exists_vlasov_characteristicFlow_global_smallT` at L5247.  No internal unfold. |
| L6358 + L6483-L6502 + L6575 | `vlasovWellPosedness_local_picard_fixedPointFlow` | **structural** | **The load-bearing site**.  L6502-L6503: `have hq_lt : q < 1 := by sorry` is the "q < 1 from hTL" sub-sub-sorry the user explicitly warned about.  q is defined at L6495 as `gronwallBound 0 (max 1 L) (L · 2M) T`.  The fix REPLACES this sorry by citing `q_lt_one_of_localSmallness`.  The comment at L6473-L6491 already states the genuine contraction ratio shape and proposes "add `hTL_contraction : L · (exp T - 1) < 1` as an additional hypothesis" — the fix supersedes by redefining `LocalSmallness` to exactly that shape.  Bonus: closes one sub-sub-sorry concretely (not in the 13-tracked sorry count, but in the body's open work). |
| L6689 (`_hTL`) | `vlasovWellPosedness_local_finalAssembly_moment` | cosmetic | Underscored hypothesis — taken structurally but unused in body. |
| L6815 (`_hTL`) | `vlasovWellPosedness_local_finalAssembly_isLagrangian` | cosmetic | Underscored hypothesis — taken structurally but unused in body. |
| L6986 + L7086/7112/7123 | `vlasovWellPosedness_local` | cosmetic | Passes `hTL` to sub-helpers (`_picard_fixedPointFlow`, `_finalAssembly_moment`, `_finalAssembly_isLagrangian`).  No internal algebraic dependency. |
| L7322 + L7371 | `vlasovWellPosedness_glue_step` | cosmetic | Forwards `hT_0_small` to `vlasovWellPosedness_local` at L7371.  No internal unfold. |
| L8275 + L8290-L8307 | `vlasovWellPosedness_forward` | **structural** | Body computes `T_0 := (1/√L - 1)/2` (L8293) derived from solving `L · (T_0 + 1)² = 1` with equality, then proves `hTL_T0 : (L : ℝ) * (T_0 + 1) ^ 2 < 1` (L8307-L8347 area) via the `(1 + √L)² / 4 < 1` algebra.  Under the exp form, the T_0 choice gets replaced wholesale: `T_0 := ln(1/L + 1) / 2`-style derivation (for `0 < L < 1` regime), and `hTL_T0` becomes an `Real.exp_lt`-based proof.  The rest of the `Nat.rec` iteration over T_0 stays intact. |

**Site count**: 9 site-clusters across 3 structural / 6 cosmetic.  Plus
4-6 docstring corrections (listed below).  Plus one consequence lemma
to add.  Total estimated scope: ~200-400 lines.  Single focused session,
or 2 sessions if structural sub-helpers' algebra proves more invasive.

### `q_lt_one_of_localSmallness` signature sketch (not Lean — notes)

```lean
/-- **W₁-regime contraction-ratio consequence of `LocalSmallness`**.

For `0 < L < 1` and `LocalSmallness L T`, the contraction ratio
arising from `Phi_supW1_contraction`'s Gronwall output — namely
`(L : ℝ) · (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ))`
— is strictly less than 1.  Equivalent to `L · (exp T - 1) < 1`
in the `L < 1` regime since `max 1 L = 1`.

**W₁-regime / `L < 1` specific by design** (per user 2026-05-31): this
lemma carries an explicit `hL_lt : (L : ℝ) < 1` binder.  The `L ≥ 1`
regime requires the truncated-distance Wasserstein W̄ refactor
(Dobrushin 1979, §5) — out of scope.  This lemma is intentionally NOT
generalized to accommodate both regimes; a generalized statement would
reintroduce shape-mismatch slack analogous to the bug being fixed, one
regime up.  Any future `L ≥ 1` proof attempting to cite this lemma gets
a type error on `hL_lt`, forcing it through the W̄ refactor route
rather than silently broadening the W₁-regime estimate.

**The `max(1, L)` constant** is inherited off
`vlasovVectorField_lipschitzWith` (CharFlow L629), the joint phase-space
Lipschitz constant of the Vlasov vector field.  Same constant items 5/6
cite; threaded once across three sites.

**Citation pattern (mechanism vs number)**: every site that previously
unfolded `LocalSmallness L T` to derive a contraction-related bound
internally cites this lemma instead.  No site re-derives the ratio
inline.  The `q < 1` bug was the local derivation pattern; the fix
replaces all such locals with a single named-lemma citation. -/
lemma q_lt_one_of_localSmallness
    (L : NNReal) (T : ℝ)
    (hL_pos : (0 : ℝ) < L)
    (hL_lt : (L : ℝ) < 1)        -- W₁-regime gate; fail loudly under L ≥ 1
    (hT_nn : 0 ≤ T)
    (hTL : LocalSmallness L T) :
    (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) < 1
```

**Note on alternate framings considered**:

* **Tautology framing**: with the redefined `LocalSmallness` matching
  the conclusion shape, the body is `exact hTL` (or `id`).  Acceptable;
  the value is the named entry-point, not the proof complexity.
* **`gronwallBound`-shape framing**: state the conclusion as
  `gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) T < D` for
  `D > 0`.  Closer to the consumer at L6495 but requires a
  `gronwallBound`-unfold step at each citation site.  Pick at execution
  time — the closed-form version (above) is the simpler entry-point.

The `(L : ℝ) * D` factor in q's actual definition at L6495 conflates
the contraction factor with the W₁-input bound D (the placeholder
`2·M`).  Per the comment at L6473-L6479, this is itself off-shape — q
should be the M-independent contraction ratio, not the ratio times D.
The execution-session fix should either: (a) redefine q at L6495 to be
the M-independent ratio, then cite `q_lt_one_of_localSmallness`
directly; or (b) keep q as-is and cite the lemma after a one-line
unfold.  Pick at execution.

### Docstring corrections (land in same commit as constraint change)

Per user instruction: docstring claims of the quadratic form *after*
the definition moves to exponential are themselves a faithfulness
smell.  Land docstring corrections together with the constraint change,
not as cleanup-after.

| Line | Site | Current claim → corrected claim |
|---|---|---|
| L3814-L3825 | `LocalSmallness` definition's section comment | "the smallness condition produced by the project's `W₁`-based contraction analysis" + "Currently defined as `(L : ℝ) * (T + 1) ^ 2 < 1`" → replace with corrected form description; note W̄ refactor remains a separate arc. |
| L4212-L4221 | Inside `exists_vlasov_perz_trajectory` (the structural site) | "TODO(W̄-refactor): LocalSmallness unfold site.  This body uses the algebraic form `(L : ℝ) * (T + 1) ^ 2 < 1` directly" → after the structural rework, replace with the exp-form unfold description. |
| L5722 | `_picard_fixedPointFlow`'s leading docstring (metric-dependence note) | "incompatible with the per-ball Picard-Lindelöf flow's quadratic-in-`T` smallness `LocalSmallness L T = L·(T+1)² < 1`" → "matches the now-corrected `LocalSmallness L T` exp form; original quadratic shape was the W₁-regime structural-debt finding (commit `580548e`), fixed in [Stage 2b part 3 commit]." |
| L6308 | `_picard_fixedPointFlow`'s 7-step plan docstring | "stronger than `hTL : L · (T+1)² < 1` alone for large `M_f₀`" → replace with the corrected constraint; verify whether the moment-bound `M`-dependent strengthening is still needed under the new definition (likely yes — the M-fixed-point is independent of the contraction constraint). |
| L6323 | `_picard_fixedPointFlow`'s metric-dependence note | "quadratic-shape smallness `LocalSmallness L T = L·(T+1)² < 1`" → corrected shape; remove the "is NOT implied" framing since the constraint is now the genuine one. |
| L7044 | Inside `vlasovWellPosedness_local`'s plan comment ("by linarith [hTL]") | The linarith hint references the polynomial shape; under exp form, switch to `Real.exp_lt_*` or `(by simpa using hTL)` depending on the structural site's actual proof. |

### Path C confirmation (deferred-audit is dead)

**Path C** (definition swap in one commit + audit-and-cite as a follow-up
diagnostic) does not work because the swap breaks every **structural**
site simultaneously.  The three structural sites
(`exists_vlasov_perz_trajectory`, `_picard_fixedPointFlow`,
`vlasovWellPosedness_forward`) embed the `(T+1)²` shape in their proof
bodies (R selection, T_0 derivation, q-definition framing), not just at
the predicate boundary.  After the swap, none of the three compiles
until its internal algebra is reworked.  There is no compiling
intermediate state.  Audit cannot be deferred behind a green build.

Next session executes the **full fix against this loaded inventory**:
definition swap + lemma + cosmetic citation updates (6 sites) +
structural rework (3 sites) + 6 docstring corrections + soundness-fix
framing in the commit body.  Single focused session, OR — if the
structural rework proves heavier than the audit projects — a further
split between (a) lemma + cosmetic in one commit and (b) structural in
follow-ups.  Decide at execution time.

### Watch-list update

The pre-promotion watch-list entry **"Additive offsets in smallness
constraints are structurally fatal"** (1 sighting, 2026-05-29) is at 2
sightings as of this triage.  The original sighting was the `(T+1)²`
additive offset in `LocalSmallness`; this session's triage is the
second sighting (same bug, scoped concretely).  Per the M-series
promotion criterion (2-3 sightings with structural certainty), advance
toward promotion: the principle is "additive offsets in smallness
constraints break the limit-shrinking property of the constraint."
Full promotion to M2 (or L11 if framed as a Lean-side gotcha) deferred
until a *different* manifestation surfaces — but the M-direction is
now near-locked.

### Stage 2b part 3 execution session — entry brief

When the execution session opens, the moves in order:

1. **Open with the triage table above** as P3 loaded context (cosmetic
   vs structural).  Decide single-session vs split.
2. **Apply the LocalSmallness redefinition** (CharFlow L3840) and the
   `q_lt_one_of_localSmallness` lemma (insertion site: near
   `LocalSmallness`'s definition for cohesion).
3. **Audit the 6 cosmetic sites** — `replace_all`-style updates,
   verify lint clean.
4. **Rework the 3 structural sites**:
   - `exists_vlasov_perz_trajectory`: replace R selection with
     exp-form-derived R; rework the algebraic bound at L4225-L4239.
   - `_picard_fixedPointFlow`: replace the `have hq_lt : q < 1 := by
     sorry` (L6503) with a citation to `q_lt_one_of_localSmallness`.
     Verify whether q's L6495 definition needs the M-independence
     correction noted above.
   - `vlasovWellPosedness_forward`: replace the `T_0 := (1/√L - 1)/2`
     derivation with `T_0 := ln(1/L + 1) / 2`-style (for `0 < L < 1`);
     replace `hTL_T0` proof with `Real.exp_lt_*` algebra.
5. **Apply the 6 docstring corrections** in the same commit.
6. **Commit body framing** (verbatim, per user 2026-05-31): "soundness
   fix, does not move the sorry count, corrects a constant in an
   already-'closed' proof, blocks faithfulness of everything above
   local existence."

**Sorry trajectory expectation**: 13 → 13 (declaration sorry count
invariant).  Sub-sub-sorry count: -1 (the `hq_lt` sub-sub-sorry at
L6503 retires concretely).  The fix is invisible to the declaration
metric, visible to the sub-sub-sorry metric AND the soundness audit.

### Out-of-scope confirmations

* **W̄ refactor** (truncated-distance Wasserstein, Dobrushin 1979 §5,
  retires the `L < 1` restriction): separate arc, post-cleanup, ~500-900
  lines per the existing `LocalSmallness` section comment estimate.
* **Sub-sub-sorries at L6508-L6511** (Picard sequence construction) and
  L6582+ (self-consistency): not in scope here; this fix is the `hq_lt`
  sub-sub-sorry only.
* **`L ≥ 1` regime**: `q_lt_one_of_localSmallness` deliberately fails
  loudly via `hL_lt : (L : ℝ) < 1` rather than silently broadening.
  This is by design (per M-series-anti-pattern reasoning); do not
  generalize the lemma.

### Three refinements to this diagnostic (user feedback, same day)

Three corrections to the framing above, captured here so next session
opens against the refined version, not the original.

**1. Promote the L6495 q-conflation finding to first-read gate**
(it was filed as "at-execution decision" / "bonus capture" — undersells
it).  The q-definition at L6495,
`q := gronwallBound 0 (max 1 L) (L · (2 · M)) T`, conflates the
contraction factor (M-independent) with the W₁-input bound D = 2M
(M-dependent).  Per the user's reading: *this conflation is plausibly
the actual root of the original bug*, not a parallel cleanup.
`(T+1)²` is a very natural thing to write if you've fused "how much
the map contracts" with "how big the input is" — the product of two
linear-ish growths reads as quadratic.

**Implication for next session's opening move**: read L6495 *first*,
*before* swapping `LocalSmallness`.  Decide whether the corrected
constraint can even be stated cleanly while q still fuses the two
quantities.  If it can't, de-conflating q is a **prerequisite** to
the fix, not a parallel cleanup — and that reorders the session
(q-redefinition lands before the predicate swap, not after).

This is the same mechanism warning the user gave for the predicate
layer, recurring one layer below: fixing the visible artifact
(`LocalSmallness` definition) without fixing the upstream conflation
(q-definition) rebuilds the cause that produces the next bug.

**2. Sorry-trajectory contingency: `hq_lt` retirement is a forecast,
not a sure thing**.  The "13 → 13 declarations, sub-sub-sorry −1"
projection above assumes all 3 structural reworks land — the new
constraint must be *provable* at each structural site under the
exp((max 1 L)·T) shape.  The triage predicts this but has not
verified it.

**Critical rule**: if a structural site resists the rework — meaning
the underlying estimate doesn't close under the new constraint shape
— the fix does NOT fall back to the `(T+1)²` form to keep the build
green.  That `(T+1)²` form is the false lemma being removed.  A
resisting structural site gets an honest sub-placeholder
(`MathlibTODO_*`-style declaration with the corrected statement,
sorry'd) or a focused next-stage decomposition.  Never the false
constraint.

This rule exists to prevent the failure mode where time pressure at
the structural rework step silently reverts to soundness-broken-but-
green.  Bar it explicitly in advance.

**3. Watch-list advance: near-locked, not promoted** ("Additive
offsets in smallness constraints are structurally fatal").  Two
*diagnostic* sightings without an executed fix is exactly the
over-extrapolation P5 guards against (P5 = verify the framework's own
pattern-extrapolations atom-by-atom before acting).

**Rule**: the structural reworks in next session's execution count
as the third, *confirming* sighting — but only if the additive-offset
reasoning actually predicts which structural sites close cleanly
under the exp form.  If the predictions hold, *then* the pattern has
earned M-series promotion.  If a structural site closes via reasoning
that doesn't match the additive-offset diagnosis, the pattern stays
on watch-list pending a different manifestation.

Status updated from "near-locked" to "near-locked, contingent on
post-execution confirmation" — same operational position, but the
P5-consistent framing makes it clear the diagnostic alone is not
sufficient evidence.

### Next session's opening sequence (updated)

Per the refinements above, the opening reads are reordered:

1. **L6495 q-definition** (P1 read, may gate the swap).  Determine
   whether q can express the corrected contraction ratio without
   first de-conflating with the W₁-input bound D.  If not, q-
   redefinition lands as a prerequisite commit before the predicate
   swap.
2. **L3840 LocalSmallness definition** + the triage table (P3 loaded
   context).
3. **The 3 structural sites**' current bodies (sketch the exp-shape
   reworks; identify any that might resist).
4. Then: swap + lemma + cosmetic + structural + docstrings, per the
   triage plan above — OR a 2-commit split if a structural site
   resists and needs a sub-placeholder, OR a 3-commit split if
   L6495 q-redefinition is required first.

Decide commit count at structural-rework time, not at session start.

---

## Stage 2b sequencing decision and process-audit signals (2026-05-31)

After the diagnostic addendums of commits `f38ba8b` and `16ea5ed`, two
candidates surfaced for the next execution session: the loaded
soundness fix (Stage 2b part 3 execution) or the separation lemma
(`wasserstein1_eq_zero_iff_measure_eq_of_prob`).  User direction
2026-05-31: soundness-first, locked, with reasoning that taught three
process-audit signals worth capturing in the notes (not just the
transcript) — particularly the third, which generalizes past this
project.

### The decision

**Stage 2b part 3 execution next session.**  Separation lemma
immediately after — but only after, not in place of.

### Observation 1 + boundary caveat — bound as a single rule

**Rule**: when sequencing among **ready** tasks, a decaying task goes
before a delay-invariant task.  Decay-asymmetry strictly dominates
compounding-asymmetry as a sequencing signal among the ready set.
Compounding-payoff arguments are arguments for "do this *soon*," not
"do this *first*" — they are not symmetric claims on the next-session
slot with decay-arguments.

**Boundary**: the rule applies *among ready tasks*.  A decaying task
that turns out blocked yields to a ready one — that's not a defection
from the rule, it's the rule's ready-condition.  L6495 is the specific
gate that determines which case we're in for the soundness fix.  If
L6495 reads as a de-conflation prerequisite that is not yet scoped
enough to execute, the soundness fix is genuinely blocked rather than
merely unappealing, and the separation lemma legitimately takes its
slot.  This is decision-after-the-read, not decision-from-appeal.

**What this rule does NOT say**: "always do the soundness fix first
no matter what."  Hardening it into an unconditional priority would
recreate the kind of overgeneralized constraint this whole arc has
been teaching distrust of.  The conditional structure is the rule;
the L6495 read is the discriminator.

### Observation 2 — appeal-asymmetry as risk gradient

**Pattern**: when two tasks compete for the same slot, the appeal
asymmetry between them is itself a risk-relevant signal.  A clean
banked-export task is appealing in a way an audit-and-rework grind is
not; that gradient is the slope along which "bank-first, soundness
next session" silently becomes "soundness the session after that."

**Operational rule**: when one option is appealing and the other isn't,
weight the unappealing option's case heavier by the magnitude of the
asymmetry, not lighter.  Appeal pulls scheduling in a direction; the
sequencing decision should counter-pull when the unappealing task is
the substantive one.

### Observation 3 — assertion-without-action as defer signal (NOT assertion-frequency)

**Tightened formulation** (per user 2026-05-31 — the bald version
overcorrects into a new failure mode): the defer-signal is *urgency
repeatedly asserted without being acted on*, not *repeated urgency*.
Some tasks genuinely *are* urgent and each session legitimately
surfaces a new reason to name it.  The discriminating question is not
"did the urgency claim get mentioned more than once," it's "did the
urgency claim *do any work* each time, or did I restate it while
acting on something else."

**Empirical sighting** (this arc): the soundness fix was named as
time-sensitive three times — at the framing turn (`f38ba8b`'s commit
body), at the contingency-rules turn (`16ea5ed`'s commit body), and
at the next-step suggestions turn.  Each individual urgency-naming was
correct.  The *pattern* across the three was assertion-without-action:
the three sessions advanced the *scoping* of the fix and not the
*fix itself*.  The false constraint survived three commits while
everything around it got more carefully scoped.  That's the
slow-motion ossification the user named, happening *to the fix itself*
— the process generated the diagnostic-and-refinement cycle as the
legitimating mechanism for not executing.

**Why the tightened formulation matters as a promotion candidate**:
the bald "repeated urgency = defer signal" reading would cause
second-guessing of genuinely-urgent tasks just because they were
named twice.  False positives that flag legitimate
urgency-naming-with-action would be the discipline framework's own
overcorrection.  The discriminator must be assertion-without-action,
not assertion-frequency.

**P5 connection (the meta-discipline check)**: at the second sighting
of this pattern, the discriminator that earns promotion is the same
discriminator that defines the pattern — was urgency named and
deferred, or named and addressed.  Don't let this one promote on the
strength of feeling insightful; it earns M-series / P-series only
when it correctly flags a *second* defer-without-action and not a
false positive on a task that was simply named twice.  This is P5
("verify the framework's own pattern-extrapolations") operating on
the candidate before it enters the framework — exactly the
self-referential guard the watch-list discipline requires.

**Watch-list entry**: "assertion-without-action as defer signal" — 1
sighting (this arc, 2026-05-31).  Promotion-candidate at 2-3
sightings *each verified against the assertion-without-action
discriminator*, not the assertion-frequency proxy.  Category to be
decided at promotion: probably P-series (process discipline) given
it's a self-audit signal about session-level execution patterns.

### The execution sequence (final form)

1. **Open Stage 2b part 3 execution on L6495**.  Read the q-definition
   gate.
2. **If L6495 admits the corrected constraint without de-conflation
   prerequisite**: proceed with swap + lemma + cosmetic citations +
   structural reworks + docstring corrections per the triage table
   above.  Single focused session, or 2-3 commit split per structural-
   rework difficulty.
3. **If L6495 reveals a de-conflation prerequisite that's scoped
   enough to execute this session**: q-redefinition lands first as a
   prerequisite commit, then the predicate swap follows.  Same session,
   reordered commit count.
4. **If L6495 reveals a de-conflation prerequisite that's NOT scoped
   enough to execute**: the soundness fix is genuinely blocked.  The
   separation lemma legitimately takes the slot; reassess and open
   the separation lemma instead.  This is the boundary condition of
   Observation 1's rule firing.

The L6495 read is the discriminator.  Either branch yields a
substantive, correctly-ordered session.  No appeal-driven defection
from the rule possible.

### Forward-look: separation lemma

Bankable whenever attempted.  No decay; no consumer dependency on the
soundness fix's intermediate state (item 3's close is gated downstream
of *both*, not between them).  After the soundness fix lands (this
session or next), the separation lemma is the natural next focused
unit — same pattern as `wasserstein1_le_of_lipschitz_map`'s banking
relative to item 6.

---

## Stage 2b part 3 — L6495 read result (2026-05-31): two-constraint discovery, Option A on M1-recursion, scope expansion

The L6495 read paid for itself twice over.  It confirmed Branch 3 at
the q-conflation layer *and* surfaced a second-order finding the
original framing didn't anticipate.  This is the gate doing its job:
**the bug is the fusion, one layer up from where we'd been looking**.

### Finding 1 (anticipated): q-conflation at L6495 is genuine

The current q at L6495 is
`gronwallBound 0 (max 1 L) (L · (2 · M)) T = 2M · q_true`, where
`q_true = (L / max(1,L)) · (exp((max 1 L)·T) - 1)` is the genuine
M-independent contraction ratio (Mathlib `gronwallBound` formula:
`δ · exp(K·x) + ε/K · (exp(K·x) - 1)`).

The downstream `h_contract : supW1On ≤ ENNReal.ofReal (q^k · D₀)` with
the wrong-q evaluates to `(2M·q_true)^k · 2M = (2M)^(k+1) · q_true^k`,
which does *not* contract for generic M > 1/2 even when q_true < 1.
The standard Phi_supW1_contraction output is `q_true · D` per step, so
`q_true^k · D₀` is the correct iterated bound.

**De-conflation fix is mechanically clear and in-session scope**:
redefine q at L6495 to `gronwallBound 0 (max 1 L) L T` (drop the 2M
from ε).  Then q = q_true, h_contract's form `q^k · D₀ = q_true^k · 2M`
is the standard contraction bound, and the hq_lt sorry at L6503
discharges as a one-line citation of the corrected LocalSmallness.

### Finding 2 (the deeper one): LocalSmallness is being asked to hold two independent constraints

The L6495 q-correction makes the contraction step work, but it does
*not* make `exists_vlasov_perz_trajectory`'s R-selection at L4204-L4210
work.  Those are different sub-proofs with different smallness
requirements:

1. **PL-buffer constraint** at `exists_vlasov_perz_trajectory`:
   `R · (1 - L·(T+1)²) ≥ N(z)` requires `L·(T+1)² < 1` for R > 0.  This
   is the per-ball Picard-Lindelöf flow's ball-geometry constraint,
   derived from the (T+1)-time buffer + L-Lipschitz fixed-point
   analysis.  *Not about contraction*.

2. **Contraction constraint** at `_picard_fixedPointFlow`:
   `q_true < 1` requires `L · (exp((max 1 L)·T) - 1)/(max 1 L) < 1`.
   This is the supW1On contraction-ratio constraint, from Gronwall on
   the W₁-based flow.

**These are independent in the `0 < L < 1` regime** (verified
numerically):
* L = 0.9, T = 0.4: quad fails (0.9·1.96 ≈ 1.76 > 1), exp holds
  (0.9·0.49 ≈ 0.44 < 1).  Quad stronger.
* L = 0.01, T = 5: quad holds (0.01·36 = 0.36 < 1), exp fails
  (0.01·147 ≈ 1.47 > 1).  Exp stronger.

Neither universally implies the other.  They come from two distinct
sub-arguments and constrain different mathematical structures.  The
single `LocalSmallness` predicate, in any single algebraic shape, can
only carry one of them.

**This is the genuine root** the L6495 gate revealed: the original
`(T+1)²` definition was the body's attempt to make one predicate
discharge two independent constraints.  The shape that *looked* like
it could cover both is the conflation generator.  The bug is the
fusion, not the shape.

### Option decision: A (two predicates) on the M1-recursion, not on architectural taste

The earlier framing offered Option A (two predicates) vs Option B
(conjunction) as "architectural honesty vs interface simplicity" —
which is the same symmetric-preference trap diagnosed two turns ago on
decay-vs-compounding.  That framing is wrong.  A and B are not two
flavors of the same thing.  They differ in *what they make impossible
to get wrong later*.

**B silently reconstructs the conflation generator**.  A conjunction
of two independent constraints under one name is precisely "one
predicate asked to hold the property of two sub-arguments" — the exact
thing being fixed.  B kills the false implication but leaves the
mechanism intact.  The next person to touch this sees one
`LocalSmallness`, projects the conjunct they need, and the independence
is re-buried inside an `∧`.  B is `(T+1)²`-fusion with the bug removed
but the *mechanism* preserved.

**M1 recursing one level**: the cascade taught "carry the natural
object, don't split-and-recombine" (one object → one predicate).  This
is the inverted case — there are genuinely *two* objects, and M1 cuts
the other way: don't fuse two natural objects into one name.  M1 is
not "fewer predicates"; it is "predicates that match the mathematical
structure."

A is M1; B is anti-M1.  **Option A on the M1-recursion reasoning**,
not on taste.

### The decision in concrete form

Two predicates, separately named:

```lean
def LocalSmallness_PL_buffer (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * (T + 1) ^ 2 < 1

def LocalSmallness_contraction (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) < 1
```

Consumers cite the constraint that matches their sub-argument.  The
existing `LocalSmallness` either becomes a synonym for the
PL-buffer-only form (matching what its current consumers actually use
algebraically) and the contraction sites take the new predicate, OR is
retired entirely with both new predicates replacing it.  Likely the
latter for clarity — `LocalSmallness` as a name no longer carries
meaning once the conflation it named is split.

**`T_0`-min consequence at `vlasovWellPosedness_forward`** (L8275):
T_0 must satisfy *both* `LocalSmallness_PL_buffer L T_0` and
`LocalSmallness_contraction L T_0`.  Concretely (for `0 < L < 1`
regime, `max(1, L) = 1`):
* PL-buffer: `T_0 < 1/√L - 1` (from `L · (T_0+1)² = 1` at equality).
* Contraction: `T_0 < ln(1/L + 1)` (from `L · (exp T_0 - 1) = 1` at
  equality).

A valid choice is `T_0 := min(1/√L - 1, ln(1/L + 1)) / 2` or similar
margin.  The min lands as an explicit `min` in the proof, which is
exactly the visible-distinct-thresholds property A is being chosen
for: if a future edit (W̄ refactor, or any reshape of one of the
constraints) changes one threshold, the type system points at the
consumers that depend on which.  B would re-bury this in a single
predicate's value.

### Scope expansion is real — and this is the legitimate-reorder case from Observation 1's caveat

The original Stage 2b part 3 budget was ~200-400 lines.  The actual
fix is now:

* q de-conflation at L6495 (single-line redefinition + hq_lt
  one-line citation).
* **Split LocalSmallness into two predicates** (new definitions +
  retire the old name).
* **Thread both predicates through the three top-level theorems**
  (`_local`, `_glue_step`, `_forward`) — every signature site that
  takes `hTL : LocalSmallness L T` becomes
  `(hTL_PL : LocalSmallness_PL_buffer L T) (hTL_con : LocalSmallness_contraction L T)`.
* **Fix the `T_0`-min choice** at `vlasovWellPosedness_forward` — the
  `T_0 := (1/√L - 1)/2` derivation becomes `T_0 := min(...) / 2`-style
  with both thresholds proved.
* The 3 structural reworks (R-selection, q-redefinition, T_0
  derivation).
* The 6 cosmetic citation updates (forwarders pick the right
  predicate).
* The 6 docstring corrections.

That's materially larger than the original budget.  **This is the
legitimate-reorder case from Observation 1's caveat** (`16ea5ed`,
"a decaying task that turns out blocked yields to a ready one").  It
isn't park-the-soundness-fix-because-unappealing; it's the gate read
revealing the fix is a multi-part architectural change that doesn't
fit one heroic session.

### Distinguishing this from defer-bias (per Observation 3, `ffe573d`)

The third observation's discriminator (assertion-without-action vs.
assertion-with-action) applies here as the test for whether this scope
update is honest or another defer-by-scoping.  The test:

**Am I scoping *instead of* touching the constraint, or scoping
*because I touched it and it revealed structure*?**

This session opened on the L6495 read — execution.  The read surfaced
a genuine architectural finding.  Scoping that finding before
proceeding is **action revealing structure**, not action substituted-
for-by-scoping.  The previous three diagnostic commits were
scoping-without-touching; this one is touching-and-discovering.
Different category.

**But the rule from Observation 3 still binds**: only ONE more scope
commit is legitimate here.  The next session must open on the actual
predicate split, not on a further read.  If the next session generates
yet another scope-update commit before any predicate edit lands, the
defer-bias is back regardless of how the prior scoping was justified.
That's the bar.

### Execution ordering (foundational layer first)

The fix is too large for one session; commit-level decomposition that
keeps the build green at each step:

**Commit 1 — foundational layer** (the predicate split + q de-conflation):
1. Redefine LocalSmallness → split into `LocalSmallness_PL_buffer`
   and `LocalSmallness_contraction`.  Both new predicates land in
   CharFlow (near the old L3840 site).
2. Update q at L6495 to the M-independent form.
3. Close hq_lt at L6503 by citing `LocalSmallness_contraction`.
4. Thread both predicates through the 3 top-level signatures
   (`_local`, `_glue_step`, `_forward`) and the 2 sub-helpers' `_hTL`
   underscored hypotheses (split into `_hTL_PL`, `_hTL_con`).
5. Update the cosmetic forwarders (5 sites) to forward both
   predicates.
6. Fix the `T_0`-min choice at `_forward`.

After Commit 1: build is green; PL-buffer sites take
`LocalSmallness_PL_buffer` (algebraically equivalent to the old
LocalSmallness — old proofs survive at those sites); contraction
sites take `LocalSmallness_contraction` (the new exp-form constraint);
the q-redefinition lands at L6495 and hq_lt closes by citation.

**Commit 2 — structural rework at `exists_vlasov_perz_trajectory`**:
The R-selection at L4204-L4210 already uses `(T+1)²` and continues to
satisfy the unchanged-algebraically PL-buffer constraint.  Likely
*minimal* rework if any — the predicate split preserves the algebraic
shape at the PL-site.  Verify and update citations.

**Commit 3 — docstring corrections + lint clear**:
The 6 docstring sites (L3814-L3825, L4212-L4221, L5722, L6308, L6323,
L7044) reframed to reflect the two-predicate structure.  Final pass.

**Sorry trajectory**: 13 → 13 declarations.  Sub-sub-sorry at L6503
(`hq_lt`) retires after Commit 1.  Sub-sub-sorry counts: -1 if
Commits 2-3 don't introduce any honest sub-placeholders; honestly
sub-placeholdered if a structural site genuinely resists (per the
no-fallback-to-quadratic bar — never the false constraint).

### Watch-list update — Observation 3 promotion guard

The "assertion-without-action as defer signal" watch-list entry (1
sighting, `ffe573d`) discriminator fires correctly in this case:
**this is action**, the scoping IS the structural finding the action
revealed.  The watch-list entry's discriminator works — it correctly
distinguishes legitimate-action-scoping from defer-bias-scoping.  But
no promotion yet; the entry doesn't earn promotion from a single
correct discrimination, only from a second confirming defer-without-
action sighting (per P5).  Status: discriminator functioning,
promotion still gated on a true second sighting.

### Next session opens on Commit 1 (actual predicate edit), per the one-more-scope-commit bar

This is the last scope commit for Stage 2b part 3.  Next session
opens on the foundational layer execution — predicate definitions,
q-redefinition, hq_lt citation, signature threading through the three
top-level theorems.  No further reads; no further scoping.  The
predicate split is the first edit.

---

## Forward-looking close discipline for the remaining internal queue (2026-05-31, post Stage 2b part 3)

Stage 2b part 3 is sealed (commits `2eed838`, `25c205b`, `d57c892`); the
next units in the close queue are the separation lemma (next session),
Stage 3 (Newton-flow Lagrangian producer), and item 3
(`dobrushin_uniqueness_On`).  Per user 2026-05-31, these closes proceed
under one new operational rule that makes them serve both the present
sorry count AND the W̄ horizon in one motion — forward-looking-and-closing
rather than one or the other.

### The rule

**Close the sorry now, but let `wasserstein1` touch the proof only
through its abstract properties — never through its concrete
`⨆`-definition.**

Four properties cover everything the project's W₁ proofs actually need:

* **Non-expansion under Lipschitz pushforward**:
  `wasserstein1_le_of_lipschitz_map` (Basic.lean, commit `bbd98f5`).
* **Triangle inequality**: standard W₁ triangle (cite project helper if
  needed; same shape under W̄).
* **Zero-iff-equal**: the separation lemma
  `wasserstein1_eq_zero_iff_measure_eq` to be banked next session.
* **Dual lower bound**: `W₁(μ, ν) ≥ ∫ f dμ - ∫ f dν` for 1-Lipschitz f
  (KR-dual lower direction, already implicit in project use).

A close that uses only these four is **W̄-survivor by construction**
because W̄ satisfies all four.  A close that unfolds `wasserstein1` to
its `⨆` is **W̄-reopened** — the unfold ties the proof to the concrete
dual representation; when W̄ arrives with a truncated-cost coupling
form, the proof has to be re-derived.

### Why this works without the typeclass

The full abstraction would be a `WassersteinLike` typeclass with these
properties as axioms, instances for both W₁ and W̄, and proofs
parameterized over the typeclass.  That is the eventual W̄-refactor
shape — but it's not required NOW.  Each proof that *behaves as if*
the typeclass existed (citing properties rather than unfolding) is
W̄-portable when the typeclass actually lands; the consumer interface
is already the interface.

This is the cheap version of the abstraction: discipline at proof
level now, harvest the typeclass mechanically later.

### The audible tell

**When a tactic wants to `simp [wasserstein1]`, `unfold wasserstein1`,
or reason about the `⨆`-form directly, that's the moment a close is
about to reopen under W̄.**  Discipline: reach for a property lemma
instead.

This costs friction on closes that would go faster by unfolding.  That
friction *is* the forward-looking work; the W̄ extension is cheap later
exactly in proportion to how consistently the friction is paid now.
Same trade as the Stage 2b part 3 predicate split — match the
structure to the math you're heading toward, not the math that's
locally fastest.

### Separation lemma — concrete statement shape (next session)

State `W₁(μ, ν) = 0 → μ = ν` (hypothesis-only contact with `wasserstein1`).
Body structure:

1. **Named sub-lemma** "equal integrals against a separating class → μ
   = ν" (pure separation-theory step, no W₁ in scope; routes via
   Mathlib's `ext_of_forall_integral_eq_of_IsFiniteMeasure`).
2. **W₁ feeds the class via dual lower bound**: `W₁(μ, ν) = 0` gives
   `∫ f dμ = ∫ f dν` for every 1-Lipschitz f (dual lower bound gives
   `∫ f dμ - ∫ f dν ≤ 0`; symmetry via `-f` 1-Lipschitz gives equality).
   This is the ONLY place W₁ enters the proof body.
3. **Apply the sub-lemma.**

When W̄ arrives, only step 2's W₁-specific feeder gets a W̄ variant
(`W̄(μ, ν) = 0` also gives equal integrals on 1-Lipschitz, because
truncated cost still controls bounded-Lipschitz test functions).  The
separation sub-lemma in step 1 is reused verbatim.

### P1 grep with forward-looking second question

**Original grep** (per the Stage 2b part 1 brief and prior sessions):
`ext_of_forall_integral_eq_of_IsFiniteMeasure` (Mathlib
`HasOuterApproxClosed.lean` L268) wants `f : Ω →ᵇ ℝ` (bounded
continuous).  That sets the approximation target: bounded continuous,
not Lipschitz directly.  Approximation step (~50 lines) lifts
1-Lipschitz equality of integrals to BC equality of integrals via
truncation-and-mollification on a Polish space with first-moment-bound.

**Added forward-looking question**: is the separating class (BC) one
that **W̄'s zero-condition also controls**?  Both W₁ and W̄ dominate
integration against bounded-Lipschitz functions (truncated cost still
controls 1-Lipschitz test functions with bounded-by-1 added on top),
and bounded-Lipschitz is dense in BC for Polish spaces — so W̄=0 also
gives equal BC integrals.  Survivor property confirmed.

If the proof's approximation step needs a property stronger than this
(unlikely but worth watching for), check W̄ satisfies it before
banking.

### Extends to Stage 3 + item 3

* **Stage 3 (Newton-flow Lagrangian producer)**: composes
  `IsLagrangianVlasovSolution` structure with Newton trajectories.  W₁
  doesn't appear in `IsLagrangianVlasovSolution`'s definition or in
  the Newton pushforward equation, so the rule mostly doesn't bite —
  but if any intermediate step routes through W₁, property-only is
  the rule.

* **Item 3 (`dobrushin_uniqueness_On` body)**: this DOES touch W₁
  heavily.  Composition:
  - Gronwall integration of `(W₁ (f t) (g t)).toReal` via item 6's
    right-deriv bound.
  - Initial value `W₁(f 0, g 0) = 0` from `f 0 = g 0` (via
    `wasserstein1_self` property).
  - Conclude `W₁(f t, g t) = 0` on `[0, T]`.
  - Apply separation lemma → `f t = g t`.

  Every step expressible property-only.  Item 3 is the largest test of
  the discipline — if it lands property-only, the rule is strongly
  validated as W̄-survivor for the project's full uniqueness chain.

### The honest cost flag

The rule costs vigilance per proof.  Every `simp` that wants to expand
`wasserstein1` is a decision point; the discipline is to inspect the
property family for a lemma covering the same step before letting the
unfold happen.

**Property-shortage = banking opportunity**: if a step genuinely needs
a property the family doesn't yet have, that's not a violation — it's
a finding.  Bank a new property lemma (named, stated abstractly) for
the step rather than leaving the unfold inline.  Same pattern as
`wasserstein1_le_of_lipschitz_map`'s banking against item 6's need
(commit `bbd98f5`), operating one level deeper: each W₁-shortage
becomes a banked-export opportunity that strengthens the property API
for both W₁ and future W̄.

### Watch-list candidate (1 sighting, pending discriminator-validated promotion)

This rule earns watch-list status at 1 sighting (the formulation in
this section, post-Stage-2b-part-3, 2026-05-31).  Discriminator at
subsequent close-sightings: does the proof body reference the property
API only (`wasserstein1_le_of_lipschitz_map`, the to-be-banked
separation lemma, etc.), or does it `simp [wasserstein1]` /
`unfold wasserstein1` / reason about the `⨆`-form directly?  Property-
only = W̄-survivor; unfold = W̄-reopened.

Promotion at 2-3 sightings WITH discriminator-validated separation of
survivor vs reopened closes during actual subsequent W̄-extension work
(or its absence — the discriminator works whether or not W̄ refactor
happens; survivor proofs are also more robust to other W₁ refactors).
Likely M-series at promotion (about mathematical structure: use the
structural properties, not the concrete representation), per the same
M1-recursion reasoning that landed the predicate split.

## Phase 4 Stage 2b part 5 Commit 2 — item 3 realign + close (2026-05-31)

**The W1ContOn `_On` check (the question the user posed before minting):**
is window-W1ContOn a *free restriction* of the proved universal
`MathlibTODO_wassersteinGronwallCoupling_W1ContOn` (→ proved corollary,
−1) or a *genuine new fact* (→ placeholder, 0)?  Atom-level read settled it
**against the prior**:

* The universal lemma already concludes `ContinuousOn (Icc 0 T)`, so there
  is no output-domain superset for `ContinuousOn.mono` to act on — the
  imagined "free restriction" mechanism doesn't apply.
* The gap is in the *hypotheses*.  The universal proof launders
  `IsVlasovSolution`'s **all-`t`** `HasDerivAt` through
  `W1ContOn_integralContAt` (Basic L2020) into *global* `Continuous`; the
  localized class (`WeakEvolutionEqOn`, CharFlow L534) carries `HasDerivAt`
  only on the **open** `Ioo 0 T`.  Endpoint continuity at `t ∈ {0,T}` is
  genuinely unsupplied → genuine new fact, net 0 on that fact.

**Soundness bug surfaced (the real finding).** Item 3 `dobrushin_uniqueness_On`
was stated over the *weak* `IsVlasovSolutionOn` class.  That class **cannot
soundly carry** the conclusion: the Gronwall step demands `ContinuousOn
(Icc 0 T)` (closed) of `t ↦ (W₁ (f t) (g t)).toReal`, but the weak PDE only
constrains the open `Ioo 0 T`, leaving the endpoint measures `f T`, `g T`
free (a weak solution may jump at `t = T`).  The "obvious" weak-class
placeholder would have been *banking a false statement*.  Fix: realign item 3
to `IsLagrangianVlasovSolutionOn` (the flow witness supplies the closed-window
pushforward `f t = (charX t)_# (f 0)` + boundary regularity, pinning the
endpoints).  This is exactly plan decision #5 (uniqueness over the Lagrangian
class), at **zero upstream cost** — the caller `vlasovWellPosedness_uniqueness`
already held the witness and was discarding it via `.1`.

**Granularity decided by soundness, not minimalism.** Considered peeling the
placeholder to the bare endpoint-continuity sub-fact, but the minimal
decomposition routes through item 5's USC, which *needs the flow witness item
3 lacks* — peeling would force a *stronger* hypothesis on the consumer.  The
weakest-sufficient *sound* statement is the whole closed-window continuity over
the Lagrangian-On class.  Not harmful fusion; the alternative is strictly worse.

**Deliverable.** Closed item 3 by composing:
`MathlibTODO_wassersteinGronwallCoupling_W1ContOn_On` (genuine boundary
placeholder, L8628) + `wassersteinGronwallCoupling_derivBound_via_pureFA_On`
(API-lock, L8657) + `wassersteinGronwallCoupling_gronwall_le` + `f 0 = g 0`
⇒ `W₁ = 0` + `wasserstein1_eq_zero_iff_measure_eq` (separation lemma).

**Cumulative-trajectory honesty (per watch-list).** Sorry count **14 → 15
(net +1)**: item 3 closed (−1), two `_On` things banked (+2).  Not net-0.
But item 3 is now a proved theorem; the genuine finding (boundary placeholder)
is isolated; only mechanical work is deferred.

**Named next-session mechanical task**:
`wassersteinGronwallCoupling_derivBound_via_pureFA_On` — a pure window-
restriction re-threading of item 6's ~220-line body (extract window flow
witness, keep the universal-in-`t` integrability/Lipschitz/diff-bound verbatim,
feed the already-window-shaped abstract placeholder
`MathlibTODO_w1RightDerivBoundAlongLagrangianFlowsOn`).  No new mathematics.

**Statement-correctness watch-list sighting (the inverse direction).** The
existing watch-list candidate is "statement too strong → weaken to match the
proof" (the `vlasovWellPosedness` forward-only refactor).  This is the
*inverse*: a statement *too weak to be sound* → strengthen the hypothesis
class.  Same statement-correctness axis (distinct from sorry-count metrics);
a second sighting of either direction advances the candidate.

## Phase 4 Stage 2b part 5 Commit 3 — derivBound_On closed via clamping (2026-05-31)

**Correction to Commit 2's "mechanical mirror, no new mathematics" claim.**
Atom-level reading of the helper signatures found a structural obstruction
(P2): `vlasovVectorField_lipschitzWith` (CharFlow L629) over-demands universal
`[∀ t, IsProbabilityMeasure (ρ t)]` + universal `h_int`, unsatisfiable by the
window class.  Resolved with the **local-clamping technique** (now promoted to
CLAUDE.md **L11**): clamp time into `[0, T]` via `clampT t := max 0 (min t T)`,
apply the universal helper to `spatialMarginal ∘ (f ∘ clampT)`, transfer the
Lipschitz bound to `f` on `[0, T]` via `clampT t = t` (`funext z; simp only
[vlasovVectorField, hmeas]`).  Everything else window-restricted cleanly.
Landed clean on the first build (commit `4eb294c`), sorry 15 → 14.  The
universal-`t` over-strength is recorded as an instance of the bidirectional
statement-correctness lesson (CLAUDE.md **M2**), not a new theme.

### ⚠ OWED — uniqueness is "structurally complete modulo two placeholders",
### but only *sound* once `W1ContOn_On` is discharged honestly.

The uniqueness chain (`vlasovWellPosedness_uniqueness` → `dobrushin_uniqueness_On`)
now bottoms out at two FA placeholders:
1. `MathlibTODO_w1RightDerivBoundAlongLagrangianFlowsOn` — abstract pure-FA
   right-deriv bound, shared with the universal item 6.  Genuine Mathlib-OT
   deferral.
2. `MathlibTODO_wassersteinGronwallCoupling_W1ContOn_On` — closed-window
   W₁-continuity over the Lagrangian-On class.  **NOT mechanical, and OWED.**

**Why W1ContOn_On is owed and load-bearing**: it is exactly the place where we
find out whether `IsLagrangianVlasovSolutionOn` *carries the endpoint
regularity* needed for closed-window (`Icc 0 T`) W₁-continuity, or whether the
predicate needs **enriching** (B2 boundary-regularity surgery) to expose the
`t ∈ {0, T}` continuity.  Until that's discharged, "uniqueness is closed" is a
claim resting on an unfilled placeholder whose *fillability* (and whose
predicate adequacy) is unverified.  The realign-to-Lagrangian-class fix
(`94d44a9`) made W1ContOn_On *sound to state*; it did not prove the endpoints
are actually available from the predicate.

**Sequencing rule (corrected framing, 2026-06-01 regroup)**: #13 goes first
**not** because it gates many consumers (consumer-count is the weak argument the
P7/P8 arc warned against) but because it is the **only board item whose honesty
is currently in question**.  The other 13 sorries are *known, soundly-stated
obligations* waiting to be filled; #13 is the one where "structurally complete
modulo placeholders" is **not yet sound**, because the predicate enrichment it
needs has not been shown to carry the boundary fact.  You do not build further
on a foundation whose soundness is owed.  That is a **soundness** rule, not a
dependency-count rule — restate it that way so the next ordering pass doesn't
re-derive it from consumer-count and get the right answer for the wrong reason.

### #13 fill-read result (2026-06-01) — conjunct shape DECIDED: `HasDerivWithinAt`

The gating sub-step: *what does `W1ContOn_On`'s fill consume at the endpoint?*
Read `MathlibTODO_w1UpperSemicontinuousAlongLagrangianFlows` (item 5, the USC
half, Basic L2185).  It consumes the flow as
`_hΦ_f : ∀ z t, HasDerivAt (fun s => Φ_f s z) (b_f t (Φ_f t z)) t` — the
**derivative** form, not mere continuity.  So the window USC analog the fill
routes through demands `HasDerivWithinAt ... (Icc 0 T)`.  Therefore:

* Conjunct shape = the **`HasDerivWithinAt` boundary bundle** (exactly Stage
  1.9's `exists_vlasov_characteristicFlow_global_smallT` output, CharFlow
  L4459–4463).  Matched, not over-strength (M2): the consumer genuinely
  demands the derivative form, and it is the form already proven upstream, so
  producers thread it at zero cost.
* `ContinuousOn`-only would be the **under-strength** failure mode (re-enrich
  mid-surgery when the window item 5 needs the derivative).

### #11 long-pole audit (2026-06-01) — the contraction is PROVED; #11 is bounded

Per the regroup's instruction to convert the long-pole unknown to a known:
cross-checked the Picard scaffolding against the sorry set.  **None of it is
sorry'd** — `Phi_step` (L5252), **`Phi_supW1_contraction` (L5779, the Stage-3
contraction crux)**, `picard_iterate_isCauchy_of_contraction` (L5957),
`picard_iterate_bundlesAs_VlasovMeasureCurve` (L6102),
`Phi_isProbabilityMeasure`/`Phi_hasMoment_le`/`Phi_asVlasovMeasureCurve`,
`VlasovMeasureCurve.extend*`, `constantCurve`, `supW1On` all have sorry-free
bodies.  So #11 `picard_fixedPointFlow` is **assembly of proved pieces**
(~150-220 lines: Picard sequence → apply contraction → bundle limit → extract
flow), **not** novel contraction proof.

**Endgame consequence**: the project has **no unbounded research-grade long
pole**.  All four project-internal items (#10 mechanical, #11 bounded assembly,
#12 glue assembly, #14 colimit assembly) are bounded; the substantive math
(contraction, pushforward W₁ bounds, flow growth) is already proved.  The
"close all internal sorries, leaving only FA placeholders" endpoint is
*bounded effort*, not a research effort.  Risk classes on the board: one
bounded-owed item (#13, soundness) and four bounded-assembly items; the nine FA
items are known/externalizable.  No item is unbounded-until-looked-at anymore.

### FA signature-purity audit (2026-06-01) — endpoint REDEFINED

Ran the purity audit on all nine FA placeholders (read signatures, not
docstrings).  "Reduce to MathlibTODO sorries" as previously phrased is **not
well-defined** — it treated ten placeholders as a uniform external pile.  They
are four distinct kinds:

* **Fully pure (liftable today, generic type)**: #1 `bcEqualFromLipschitzEqual`,
  #8 `lipschitzFlowTrajectoryLipBound`, #9 `lipschitzFlowAEMeasurable`.
* **Abbreviation-pure (trivially liftable)**: #5 `bcNarrowFromSmoothCompactNarrow`
  (only `PhaseSpace` abbrev).
* **W₁-dependent (liftable ONLY once Mathlib has a stable W₁)**: #2
  `cauchyW1_hasNarrowLimit`, #4 `w1LowerSemicontinuous…`, #6
  `w1UpperSemicontinuous…`, #7 `w1RightDerivBound…On` — all reference
  `wasserstein1` (the project's KR-dual W₁).  External-world dependency we
  don't control.
* **Genuinely internal, wearing the prefix**: **#3
  `convolveContinuousAtOfNarrowMoment`** — its conclusion is
  `ContinuousAt (fun t => convolveFunctionMeasure gradW (μ t) x)`, bound to the
  Vlasov-specific `convolveFunctionMeasure`.  This is **internal work
  mis-counted as external** — exactly the "internal sorry wearing
  MathlibTODO_" failure the purity question existed to catch.

**ACTION — #3 reclassified internal.**  It does not sit in the FA pile as-is.
Either restate it in kernel-convolution vocabulary (genuinely liftable) or
close it ourselves (standard, given the convolution kernel is Lipschitz).
**Internal-sorry count is therefore 5+1 = 6, not 5.**

**Endpoint redefinition (replaces "reduce to 10 MathlibTODO citations")**:
> Every *project-internal* sorry closed; remaining sorries partitioned into
> **{liftable-now, blocked-on-Mathlib-W₁, blocked-on-Mathlib-Prokhorov}**,
> with #3 restated-to-purity or closed-by-us.

**Bucket-2 = the two genuine hard-OT deliverables (the real handoff content)**:
the finished scaffold's two deepest holes are *exactly the two pieces of real
Wasserstein theory Mathlib lacks*:
* **#2** — W₁-completeness for Euclidean/Polish (Prokhorov + tightness +
  narrow→W₁ under moment control).  Prokhorov-for-Polish is not Mathlib-stable.
* **#7** — the W₁ right-derivative Gronwall *stability* estimate (the core
  Dobrushin inequality; the uniqueness side bottoms out here).

This is the cleanest possible outcome, not a defect: the project's genuine
contribution-to-Mathlib is *sharply localized to two named lemmas*; everything
else is ours-and-closed or standard-once-those-land.  The win condition for
**our** part of the work is **"everything internal closed, #2 and #7 cleanly
stated as the two hard external lemmas"** — and the audit showed 7 of 9 FA
items are Bucket-1, so we are closer to that than the raw count suggested.
The handoff plan should treat #2 and #7 as the deliverables to the
grad-student / AI-for-math effort, not as items in a uniform pile.

### #11 output-type seam read (2026-06-01) — SOUND (least-sound candidate verified)

Ran the seam read alone, on the *return type* of
`vlasovWellPosedness_local_picard_fixedPointFlow` (L6416-6453), per the rule
"check whether self-consistency is in the type or only the prose."

**Verdict: self-consistency is in the conclusion type.**  The `ρ` slot of the
`IsCharacteristicFlowOn` conjunct (L6419-6421) is
`fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)` —
the spatial marginal of the pushforward of `f₀` under *the same* `charX charV`
that are the flow.  Unfolds to `ρ_t = (charX t)_# (spatialMarginal f₀)`, and the
predicate forces `charV' = -(∇W ∗ ρ_t)(charX_t z)`: the force is generated by
the measure the flow produces.  Fixed-point condition, structural.  Hypotheses
(L6406-6415) carry **no** self-consistency assumption → genuine existence of a
self-consistent flow, non-circular, non-vacuous.

So `vlasovWellPosedness_local` + `_finalAssembly_isLagrangian` consume a
genuinely self-consistent flow.  **The project's deepest seam is sound; the
green build is not lying there.**  The recurring failure mode (q<1, weak-class,
discarded bundle) does NOT recur at this seam.

**Branch outcome** (per the pre-decided rule): #11 seam sound ⇒ soundness-cycle
check (d) is low-risk ⇒ **#13 surgery proceeds.**

**Bonus (de-risks #13)**: #11's return type already carries the
`HasDerivWithinAt ... (Icc 0 T)` boundary bundle (L6424-6430) + AEMeasurable
witness (L6445) + convolution continuity/integrability.  Since
`_finalAssembly_isLagrangian` consumes #11, the boundary bundle is in scope at
the one #13-surgery site previously flagged as least-certain to thread.  Source
confirmed present.

### #13 B2 enrichment surgery — LANDED, with a conjunct-shape flip (2026-06-01)

The pre-surgery Stage-C read (the last unverified bundle-source) **surprised**,
and flipped the conjunct shape — exactly the feasibility gap the read existed
to catch before the batch:

* Stage C (`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`, L3602-
  3613) carries boundary regularity as inputs `h_cont_Icc` (**`ContinuousOn
  (Icc 0 T)`**, directly) + `h_deriv_Ico` (`HasDerivWithinAt _ (Ici s) s` on
  `Ico`).  The `Ici s`/`Ico` derivative form does **not** convert to the two-
  sided `Icc`-form `HasDerivWithinAt` (#11's output form) I'd planned — the
  left half at interior points is missing.
* So `HasDerivWithinAt`-Icc would have broken Stage C mid-batch (need to enrich
  Stage C's input).  But `ContinuousOn (Icc 0 T)` is carried **verbatim**.

**Flip: conjunct = `ContinuousOn`, not `HasDerivWithinAt`.**  My earlier
"`HasDerivWithinAt` because item 5 takes `HasDerivAt`" reasoning mirrored item
5's *over-strong* hypotheses; the soundness `W1ContOn_On` actually needs is
closed-window W₁-continuity ⟸ closed-window narrow continuity ⟸ `ContinuousOn`
of the flow.  `ContinuousOn` is M2-weakest-sufficient *and* the form every
producer already supplies.  This **reverses** the earlier recorded decision
(which assumed `HasDerivWithinAt`); the read caught it before, not during.

**Surgery (atomic, landed green; declaration sorry count 14 → 14)**:
predicate `IsLagrangianVlasovSolutionOn` gained `∀ z, ContinuousOn (fun s =>
(charX s z, charV s z)) (Icc 0 T)`.  Producers threaded: `.toOn` (real, from
universal `HasDerivAt`→continuity), Stage C (real, `h_cont_Icc` verbatim),
per-`T_target` + `h_sol_m_on_n` (real, restrict via `.mono` from the boundary
bundle / `h_cont`); glue_step (#12) + universal-`f` assembly (#14) cont conjunct
**sorry'd** (those declarations were already sorry'd — bounded piecewise/colimit
continuity, no new declaration sorry).  Consumers: `derivBound_On` obtain + two
`h_sol_lag N` obtains gained trailing binders.

**Soundness discharged**: `W1ContOn_On`'s hypothesis now carries `ContinuousOn`
at the endpoints, so its closed-window W₁-continuity claim is **derivable** —
the owed-soundness item is closed.  `W1ContOn_On` remains a sorry'd FA
placeholder, but now a *soundly-stated* one (like the other FA items), no longer
"honesty in question."  Tactical notes for the file: `Continuous(On|WithinAt).prodMk`
(camelCase, not `.prod`); `HasDerivWithinAt.continuousWithinAt` is the bridge.

### Proved-modulo-sorry sweep (2026-06-01) — accounting the surgery's growth

The "14 → 14, all soundly stated" headline is true at the *declaration* level;
this sweep verifies it at the *obligation* level (the surgery grew #12/#14 by a
cont conjunct — declaration count flat, obligation grown).

**#12/#14 cont obligations are BOUNDED-INTERNAL, not hidden boundary lemmas.**
glue_step's signature already carries `h_prev_boundary` (L7418-7422 — f_prev's
flow as `HasDerivWithinAt _ (Icc 0 T)`), so f_prev's closed-window
`ContinuousOn` is derivable in-signature; g (= `local (f_prev T)`) carries its
own cont conjunct (enriched predicate); the **seam at s=T is pointwise-at-T
agreement by construction** (`charX_g(0, w) = w.1 = charX_prev T z`).  The
"more-than-pointwise" subtlety lives one level up at `t ↦ W₁` across the seam —
that is `W1ContOn_On`'s obligation, **not** #12's.  #12 grew by a bounded
piecewise-`ContinuousOn` glue; #14 by the same shape (colimit pieces agreeing
on overlaps via `h_agree`).  **No third hard-OT item; #2 + #7 remain the only
two.**

**General sweep CLEAN.**  Structural fact: a green build precludes the
"consumer destructures more than the type promises" pattern from hiding in
*proved* consumers (it would be a build error); it can only hide where a
*sorry'd* consumer sorry's over a missing witness.  The substantive sorry'd
bodies (#10/#11/#14) compose *proved* scaffolding (`picard_iterate_*`,
`exists_vlasov_characteristicFlow*`, `Phi_supW1_contraction`) or proved-modulo
declarations with green-honored types.  `_finalAssembly` (proved) absorbed the
surgery's cont via Stage C / #11's bundle, so #11's obligation did **not** grow
(its type already carried the `HasDerivWithinAt` bundle).  The only
obligation-growth on the board is the surgery's #12/#14 — fully accounted across
all six producers (4 absorbed with real proofs, 2 grew bounded).  No hidden
third instance.

**Tagging (hidden/visible × bounded/hard) of the 14**: all *visible* (green
build).  Bounded-internal: #10, #11, #12, #13, #14.  Bucket-1 FA (pure or
mod-W₁): #1, #4, #5, #6, #8, #9.  Internal-reclassified: #3.  **Hard-OT
(Mathlib-blocked): #2, #7 — and only these two.**

### #11 assembly read (2026-06-01) — bounded, 3 subtleties, 1 over-strength

Read #11's body before editing (the discipline that's caught every false/over-
strong statement this arc).  Steps 1-3, 5-7 + the conjunct-derivations
(`h_boundary`, `hM_ρ_bound`, `h_y_int_ρ`, `h_aemeas_out`) are **already proved**
(ride on `h_self_consist` + proved scaffolding).  Four sorries remain, in three
classes:

* **L6610 — Picard sequence + contraction (heart)**: build `x : ℕ →
  VlasovMeasureCurve d T M` by `Phi_step` + induction; per-step contraction
  `supW1On (x k) (x (k+1)) ≤ ofReal (q^k · D₀)` from `Phi_supW1_contraction`
  (which takes ~16 hyps — integrability/AEmeas/moment/two-flows — to supply for
  consecutive iterates).  `q < 1`, `picard_iterate_bundlesAs_VlasovMeasureCurve`
  (proved) consumes it (L6614 already wired).  Plumbing-heavy but bounded.
* **L6693 — self-consistency `Φ(ρ_lim) = ρ_lim`** (the subtle one): the Step-7
  flow (`exists_vlasov_..._global_smallT` against `ρ_lim.extend`) and Φ's
  internal flow are *separately constructed* against the same `ρ_lim` —
  identifying them is an **ODE-uniqueness** argument, not definitional.  This is
  the genuine mathematical content of the fixed point.
* **L6740 / L6757 — universal-`s` OVER-STRENGTH (B3)**: conclusion demands
  `∀ s, Continuous/Integrable (conv against spatialMarginal(pushforward s))` —
  universal `s` — but the construction controls only `[0,T]`; off-window
  `charX_s` is an uncharacterized total-function value (no finite-moment
  guarantee).  Traced up: **Stage C's hyps `hconv_cont`/`h_int` are `∀ s`**
  (L3620/L3630), forcing #11's conclusion universal.  The window weak-PDE
  (`Ioo 0 T`) almost certainly only needs window-`s` → these are likely
  over-strong, weakenable to `∀ s ∈ Icc 0 T`.  **P5 caveat**: do NOT assume —
  verify the weak-PDE cascade (`vlasovSolutionViaPushforward_isVlasovSolutionOn`
  and below) only consumes window-`s` before weakening.

**3-step assembly plan (focused next session — do NOT start at a session tail)**:

1. **Verify + weaken the universal-`s` over-strength** — *a soundness-sensitive
   cascade, not a cheap verification*.  Weakening Stage C's `∀ s`
   `hconv_cont`/`h_int` ripples to **every consumer of Stage C's universal form**,
   including the producers threaded in the #13 surgery.  **P5 gate**: the read
   *found* the over-strength; it did **not** prove the weakening is safe — those
   are different, and the gap is a P5 obligation.  Trace the weak-PDE cascade
   (`vlasovSolutionViaPushforward_isVlasovSolutionOn` and below) and confirm it
   consumes only window-`s` **before** weakening Stage C + #11 conclusion to
   `∀ s ∈ Icc 0 T`.  Only then do L6740/L6757 close from `h_self_consist` +
   `h_int_ρ_lim`.  This is the maneuver (weaken an over-strong statement) with
   the **highest hidden-soundness risk on the board** — run it with the P5 gate,
   never at a tail.

   **Fold item (d) — the soundness-cycle check — into THIS gate** (it becomes
   checkable here and is maximally relevant here, not as an orphaned later
   audit).  Stage C feeds the #13 producers; #13 feeds uniqueness; uniqueness
   feeds existence (#14); #14 consumes #11.  That is close to a *loop*, and
   weakening a conclusion (Stage C's) that sits upstream of a chain curving back
   toward #11 is exactly how a **circular soundness dependency** announces
   itself.  So the P5 gate's verification is **two questions, not one**:
   (i) does the weak-PDE cascade need only window-`s`?  and
   (ii) does any consumer of Stage C's universal form sit *downstream of #11*
   such that this weakening is circular?
   Prior (not proof): the #11-seam read showed self-consistency is
   *existential-from-non-self-consistent-data*, the structural fact that usually
   *prevents* such a cycle — but "usually prevents" is a prior, and step 1
   perturbs the exact edge, so verify rather than assume.  Same trace, one extra
   question; retires (d).
2. **L6610 Picard sequence**: assemble `x_n` + contraction (plumbing, bounded).
3. **L6693 self-consistency — THE ONE GENUINELY-NEW INTERNAL PROOF.**  Not
   "subtlety 3 alongside plumbing": it is the *only remaining internal step that
   is neither assembly nor statement-correction*.  Two separately-constructed
   flows against the same `ρ_lim` get identified, and that identification **is**
   an ODE-uniqueness theorem (Picard-Lindelöf uniqueness for the characteristic
   system).  **Step 3's opening move** (the #11 analogue of the separation-lemma
   grep): *is ODE uniqueness already banked in the scaffolding* — does some
   `exists_vlasov_characteristicFlow*` / PicardLindelof lemma give **uniqueness**,
   not just existence?  If existence-only, L6693 has a sub-target that is its own
   lemma, and step 3's size changes materially.  **Check banked-uniqueness before
   assuming self-consistency is "compose what's there."**

**Ordering rationale (lock this so the fresh session doesn't reorder under the
pull toward the substantive part)**: statement-correction (1) **before** body-
proof (2)/(3), per M2 — *fix the target, then aim*.  Proving the Picard assembly
against a universal-`s` conclusion you cannot deliver is wasted work you'd
unwind.  The natural temptation is "prove the heart first, fix the statement
after"; resist it — weaken to the correct, achievable `∀ s ∈ Icc 0 T` target
first, then steps 2/3 prove the right thing once.

### Complete map of remaining internal work (post-#11-read, 2026-06-01)

The internal pile is now fully characterized:
* **Bounded assembly**: #10 (mechanical), #12 (glue), #14 (colimit), #11 steps
  1-2 (Picard sequence + statement-correction).
* **One statement-correction cascade**: #11 step 1 (P5-gated, soundness-sensitive).
* **Exactly one genuinely-new internal proof**: #11 step 3 (ODE-uniqueness,
  pending the banked-uniqueness check).

Everything else is the FA partition (#1/#4/#5/#6/#8/#9 Bucket-1, #3 internal-
reclassify, #2/#7 the two hard-OT deliverables).  That is the whole distance to
the endpoint.

### #11 step 1 CLOSED via clamped flow — and the M-fixed-point decision (2026-06-01, commit `72af201`)

**Step 1 done, build green** (4 → 2 internal sorries in #11; L6740/L6757
closed, L6610 Picard + L6693 self-consistency remain).

**The route diverged from plan — a P5 finding.** The gate passed (the `_On`
cascade consumes `h_int`/`hconv_cont` only on `Icc 0 T`; no circular consumer).
But atom-level reading of the *weakening target* showed the planned "weaken
Stage C + #11 conclusion to `∀ s ∈ Icc 0 T`" is treacherous: every `_On`
cascade lemma has a **textually-identical global twin** that must stay
universal, and the body-threading sites (`h_int s x`) are non-unique across
twins — one mis-target silently breaks a proven global producer.  The plan's
premise (clean weakening) did not survive atom-level contact.

Took the **contained alternative**: #11 returns the *clamped* flow
`cX s := charX (clampToIcc T s)`.  Pushforward at any `s` = on-window
pushforward at `clampToIcc T s ∈ [0,T]`, so the universal conjuncts become
**genuinely true** (no weakening — conclusion stays universal), and window
conjuncts transfer via `clampToIcc`-congruence.  Zero cascade edits; the
soundness-cycle question (item d) is **moot** because nothing was weakened.

**M-fixed-point surfaced at step 2 (L6610).**  `Phi_step` outputs moment bound
`C_T·(M_f₀+1)`; `picard_iterate_bundlesAs` needs a *fixed-`M`* curve space; so
the iterate must satisfy `C_T(L,M,T)·(M_f₀+1) ≤ M`.  With `∇W` Lipschitz-not-
bounded (`AssW`, Basic L86), `C_T = A + B·M`, so this needs `B·(M_f₀+1) < 1`,
a **data-dependent** smallness #11's `M_f₀`-free hypotheses cannot supply for
large `M_f₀`.

**DECISION (user, faithfulness-first): option 2 — drop the constant-`M`
encoding, moment as a time-dependent envelope `M(t)` the dynamics propagate via
Gronwall.**  The *primary* rationale is **present-tense faithfulness in the W₁
regime**, not W̄-compatibility:

* The contraction ratio `q = gronwallBound 0 (max 1 L) (L·D) T` (L5838) is
  already **`M`-free** — the M-fixed-point is **not intrinsic to the math**, it
  is an artifact of the constant-`M` curve space (itself a consequence of the
  KR-dual W₁ needing finite first moments).
* So option 1 (add `B·(M_f₀+1)<1`) is an **overclaim-by-restriction**: it adds
  a smallness hypothesis **Dobrushin's theorem does not have and #11's own
  contraction does not need**, purely to service a self-imposed encoding
  artifact.  Same class as the weak-class-uniqueness and `q<1` findings — a
  wrong-*strength* statement caused by encoding, not by the math.  M2 too-strong
  direction: fix the *encoding*, not the statement.
* W̄-forward is the **second** reason only.  W̄ is the explicitly-deferred
  regime; justifying present scoped work by it would re-subordinate a present-
  faithfulness fix to an unscheduled future (the appeal-to-future-proofing the
  discipline has caught before).  Frame option 2 as **a W₁-regime faithfulness
  redesign that happens to be W̄-forward — NOT a W̄ task.**

**Next-session scoping (do NOT start at a tail; atomic-structural-cascade class,
same discipline as #13/#11).**  Open option 2 as its own focused session.
**Consumer-sweep FIRST**: enumerate every `VlasovMeasureCurve d T M` consumer
(`Phi_step`, `Phi_supW1_contraction`, `picard_iterate_bundlesAs`,
`constantCurve`, `.extend`/`.extend_*`, #11) before touching the field, then
decide the envelope's shape (drop `M` constant → `hasMoment t ≤ M(t)` with
`M : ℝ → ℝ` monotone, or a Gronwall-closed family).  Steps 2/3 (Picard sequence
+ self-consistency ODE-uniqueness) resume **after** the curve space is the
honest object.

### Option 2 progress: consumer sweep + escape VALIDATED in isolation (2026-06-01)

**Consumer sweep done.** The structure's only `M`-dependent field is
`hasMoment : ∀ t ∈ Icc 0 T, ∫‖y‖ ∂(ρ t) ≤ M` (L3931).  Every consumer is a
mechanical re-thread (`≤ M` → `≤ M t`) **except** `Phi_step`'s output growth
bound — the one place the envelope must be *proven preserved*.  Mechanical:
`supW1On_le_two_moment` (→ `sup_{[0,T]}M`), `extend_hasMoment` (→ `M (clamp t)`),
`constantCurve` (→ `M_f₀ ≤ M t`), `picard_iterate_bundlesAs` (`cauchyW1` is
applied **pointwise in t**, so just `M t`).

**Envelope shape (user-confirmed): general monotone `M : ℝ → ℝ`** (not a
hardcoded exponential), so `Phi_step` outputs its own envelope and `constantCurve`'s
constant `M_f₀` still fits.  Monotonicity is a property of the *specific* `m*`
(carried where used), NOT a structure field — keeps the structure clean.

**The escape is M_f₀-FREE** (key discovery): feeding the *time-local* moment
`m(t)` (not the sup `m(T)`) into the force, with `m` monotone, gives
`M_Φρ(t) ≤ A(t) + B(t)·m(t)` with `B(t)=(L/(1+L))(e^{(1+L)t}-1)` — `M_f₀`-free.
Canonical `m*(t)=A(t)/(1-B(T))` is Φ-invariant under `B(T)<1`, a constraint of
#11's existing **data-independent** shape (cf. `hTL_con`), NOT option 1's
`B·(M_f₀+1)<1`.  Fully faithful.

**VALIDATED (committed, additive, no structure change yet):**
* Piece A — `flow_distance_growth_bound_on_timedep` (commit `d8986f1`): the
  time-local per-`z` growth bound with monotone envelope forcing.
* Piece A.3 — `gronwall_envelope_exists` (commit `b758ba1`): the canonical
  envelope closes (monotone / dominates `M_f₀` / Φ-invariant) under `B(T)<1`.

**Remaining — the wide structural surgery (the "re-threading" unit):**
* **Piece A.2** (additive glue, ~30-40 lines): `phi_moment_envelope_le` —
  integrate Piece A over `f₀` via `integral_map` + `gronwallBound` affine-in-δ →
  `∫‖x‖ ∂(spatialMarginal (Measure.map (charX t) f₀)) ≤ gronwallBound M_f₀ (1+L)
  (g0 + L·m t) t`.  Completes the measure-level escape; can be standalone or
  folded into Piece C.
* **Piece B** (WIDE, atomic-structural-cascade): `VlasovMeasureCurve d T M` →
  `… (M : ℝ → ℝ)`, field `hasMoment : ∀ t ∈ Icc, ∫‖y‖ ≤ M t`; re-thread the 4
  mechanical consumers.  **Wrinkle to handle**: `supW1On_le_two_moment` needs a
  uniform `sup_{[0,T]} M` — for the monotone `m*` this is `m*(T)`, but the
  general structure needs either a `bddAbove`/continuity hook or to bound via
  `M T` under a monotonicity carry.  Check `supW1On_ne_top`'s actual consumers
  first (it may only need pointwise finiteness from `yIntegrable`).
* **Piece C** (`Phi_step` rewire): output into the envelope space, composing
  A.2 + A.3; the output curve's `hasMoment` uses the canonical `m*`.
* **Piece D** (#11): rewire the Picard sequence into `space(m*)`, replacing the
  constant-`M` obtain (L6500), closing the M-fixed-point; reconcile `B(T)<1`
  with #11's `hTL_con` (implied, or a hypothesis tweak — verify).

Order: A.2 (finish foundation) → B (wide) → C → D.  B is the risky wide one;
the validated foundation (A/A.2/A.3) means B/C/D are pure re-threading against a
proven escape.

### Option-2 progress + hTL_PL elimination decision (2026-06-01, commits d8986f1…8ae19f5, 462d79d)

**Done + committed**: Piece A (`d8986f1`), A.3 (`b758ba1`), A.2 (`5dfcb9a`),
B structure refactor `M : ℝ→ℝ` (`a198886`), C `Phi_step` per-`z` envelope-bound
exposure (`8ae19f5`).  The data-free escape is validated + the structure carries
the envelope; `Phi_step` now hands out Piece A's per-`z` bound (requires
`hM_mono`).

> **⚠️ CORRECTION (2026-06-01, NO-BALL-CHECK opening read — P5/M3 refutation
> of THIS plan's premise).**  The rebuild-first decision recorded below rests
> on a **FALSE premise**: `exists_vlasov_characteristicFlow` is **NOT sorry'd —
> it is fully proven.**  Atom-level evidence: no `sorry` token in its body
> (L1553–2290, grep + final-assembly read); its vendored
> `Vlasov.Mathlib.ODE.PicardLindelof` dependency is also `sorry`-free.  The
> "Currently sorry'd; closing it is the next follow-up session" at L1552 was a
> **stale docstring** — and this plan read that *interface* line as "the
> dominant fact" instead of reading the *construction* (the exact M3 corollary
> recorded this session: read the construction, not the interface).  The
> NO-BALL CHECK (Step 0) caught it because it forced the construction read.
> Docstring corrected in the same arc.
>
> **What `hTL_PL` actually is:** a *carried hypothesis*
> `LocalSmallness_PL_buffer L T := L·(T+1)² < 1` (CharFlow L4169), threaded from
> `exists_vlasov_perz_trajectory` (which discharges the per-ball flow's `hR` via
> `R := N(z)/(1-L(T+1)²)`) up to the marquee — already as a *named, droppable*
> hyp (`_hTL_PL` unused at `_finalAssembly_*`).  Real smallness (the `+1` forces
> `L < 1`, overclaim-by-restriction vs. Dobrushin), but **not a sorry.**
>
> **Consequence — the rebuild-first rationale below is VOID:** there is no
> sorry'd dependency under Piece D.  The existence chain is **proven through
> `Phi_step`**.  Open critical-path sorries (CharFlow): `picard_iterate_
> bundlesAs_VlasovMeasureCurve` (L6440, ×2), **#11 `vlasovWellPosedness_local_
> picard_fixedPointFlow`** (L6743, ×2 = Piece D), `vlasovWellPosedness_glue_
> step` (L7756, ×2), `vlasovWellPosedness_universal_existence` (L9490, ×2),
> plus 2 deferred `MathlibTODO_*`.
>
> **Revised path:** **Piece D closes NOW on the proven chain, carrying
> `hTL_PL`** (Option A).  `hTL_PL` elimination is a *separate, decoupled*
> faithfulness pass — a fixed-`δ` N-window *re-consumption* of the **proven**
> per-ball flow (NOT a rebuild; ~200–300 lines), deferrable because `hTL_PL` is
> already threaded for clean removal.  The "REBUILD SESSION — opening read" and
> "POST-REBUILD GATE" blocks below are **superseded** (the (c) sweep already
> ran here: per-ball flow + vendored PL both clean; the only thing the
> interface hid was a stale docstring, now fixed).
>
> ---
> _Historical record (premise now known false — retained for the P5 lesson):_

**Decided (user, after the hTL_PL trace + Step-0 gate): REBUILD the per-ball
flow FIRST, fresh session — NOT Piece D first.**  Rationale (the dominant fact):
`exists_vlasov_characteristicFlow` (L1552) is **sorry'd and mandatory** — the
marquee bottoms out through it regardless of `hTL_PL`/W̄.  The fixed-`δ` N-window
form is its *correct* discharge (PL-feasible on fixed `δ` → no `T`-smallness →
`hTL_PL` never generated; Piece-A-chainable; arbitrary-`L`-faithful).  Any other
closure re-incurs the single-ball geometry and thus `hTL_PL`.  So the N-window
rebuild is not "extra scope for faithfulness" — it is the *avoid-building-the-
per-ball-flow-twice* argument.  Closing D on the current sorry'd per-ball flow is
the declaration-vs-obligation illusion in the load-bearing spot (green build
lying about being finished where the per-ball sorry sits).

**Gate finding that killed Step 1's framed approach** (M3 gate corollary, first
use): "swap `perz_trajectory`'s R-selection to a Gronwall value" does NOT
eliminate `hTL_PL`.  The self-consistency is in the per-ball flow's `hR`
(`2a + … + M·(T+1)² ≤ R`, `M = ‖∇W 0‖ + L·(R+…)` so `M ∝ R` →
`R(1−L(T+1)²) ≥ N_z` for ANY finite `R`) — intrinsic to the single-ball-over-
`[0,T+1]` *geometry*, two levels below the clean interface.  Read the
construction, not the interface.

**REBUILD SESSION — opening read (do BEFORE the ~200-300 lines; ORDER matters).**
This is M3 applied to the *construction*, not the constraint: is the ball an
artifact to **replace** (now that Piece A is the dynamic object) or a node to
**refine**?  The banked plan silently assumed "refine into N windows" — that
assumption is exactly the kind the gate teaches to *check, not inherit*.

* **(0) NO-BALL CHECK — ask FIRST; it can shrink or eliminate the rebuild.**
  Does Piece A's *global* a-priori bound (`‖Z(t)‖ ≤ gronwallBound …`, already
  built) let me skip ball-localization entirely — invoke a global ODE existence
  on `[0,T+1]` (Mathlib's, or a direct Picard) with Piece A supplying the growth
  control the ball was manufacturing locally?  **If YES** → the rebuild is
  "balls → NO balls," smaller/cleaner than N-window, and the per-window
  re-anchoring + chaining management below is **moot** (no windows to manage).
  **If NO** — the ball plays a *compactness / fixed-point-domain* role Piece A
  can't replace, not just growth control → genuinely load-bearing; proceed to
  N-window **knowing** it (not assuming).  Either way you've run the M3 check on
  the construction: refining an artifact vs. replacing it.
* **(1)** [only if (0) = NO] per-window `hR` on a *fixed* small `δ` (e.g.
  `L·δ² < 1/4`) is genuinely satisfiable — no `T`-smallness.
* **(2)** [only if (0) = NO] chaining `⌈(T+1)/δ⌉` windows does NOT re-accumulate
  a smallness at the *chain* level — the envelope must **re-anchor per window**
  (each ball centered at the prior window's endpoint), else the window-count
  compounding is `hTL_PL` one level *above* per-window feasibility (same disease
  as inter-window `hTL_con` compounding).  The gate taught: constraint hides one
  level *below* expected (in `hR`); symmetric trap is one level *above* (chain
  count).  Find it in the opening read, not at line 250.

**Then**: rebuild closes the L1552 per-ball sorry + drops `hTL_PL` from every
threading site (`exists_vlasov_perz_trajectory` L4541, `global_smallT` L4765,
`Phi_step` L5576, #11 L6752, `vlasovWellPosedness_local` L7446;
`_finalAssembly_*` take it as unused `_hTL_PL` — clean drops).  Build green.
**Then Piece D** against the cleaned, *proven* chain (D never stands on a sorry):
`constantCurve` base (A.3 domination) → `Phi_step`→A.2→A.3 re-bundle into
`space(m*)` → `Phi_supW1_contraction`.  Remaining smallness = the genuine pair
`hTL_con` + `B(T)<1` (carry both; do NOT derive one from the other — independent
near-counterexample; W̄-consolidation target).  Weakest-sufficient: NO `hTL_env`.

**POST-REBUILD GATE — run the proved-modulo-sorry (c) sweep BEFORE declaring the
existence side finished.**  Clean-interface-over-a-load-bearing-sorry'd-node is
now a CONFIRMED recurring shape in this codebase — TWO instances (the per-ball
flow `exists_vlasov_characteristicFlow` L1552; the `_finalAssembly`/#11 seam),
both green-modulo-a-sorry in a load-bearing spot.  "The marquee bottoms out
cleanly" has been wrong twice in the *same* way; a third is cheaper to find by
sweep than by stumbling into it at line 250 of a later session.  The sweep's
job: which green declarations stand on a sorry'd or over-strong dependency the
interface hides.  Schedule it AFTER the rebuild, BEFORE the existence side is
called done — earned, not hypothetical hygiene.

### Piece D execution brief — close #11 on envelope space `m*` (2026-06-01, atom-level loaded context)

**Premise correction first:** the rebuild section above is SUPERSEDED — the
per-ball flow is proven (see the ⚠️ CORRECTION). Piece D closes **on the proven
chain**. Below is the complete atom-level map (all signatures read this session).

**Ready plumbing (all confirmed sorry-free this session):**
* **A.3 `gronwall_envelope_exists`** (CharFlow L579): under
  `hB : (L/(1+L))·(exp((1+L)·T)−1) < 1`, gives `m* : ℝ→ℝ` with
  `MonotoneOn m* (Icc 0 T)`, `∀t∈Icc, M_f₀ ≤ m* t`, and the **Φ-invariance**
  `∀t∈Icc, gronwallBound M_f₀ (1+L) (g0 + L·m* t) t ≤ m* t`.
* **A.2 `phi_moment_envelope_le`** (L678): from per-`z` growth `h_growth` →
  `∀t∈Icc, ∫‖x‖∂(map (charX t) f₀) ≤ gronwallBound (∫z‖z‖∂f₀) (1+L) (g0+L·m t) t`.
  (Initial moment is the **phase-space** `∫z‖z‖∂f₀`, not the spatial marginal.)
* **`Phi_step`** (L5577): input `ρ : VlasovMeasureCurve d T M`; output flow
  `(charX,charV)`, `C_T≥0`, the per-`z` growth conjunct `h_growth_timedep`
  (= A.2's `h_growth` input, with `m = M`, `g0 = ‖gradW 0‖`), and a bundled
  `σ : VlasovMeasureCurve d T (fun _ => C_T·(M_f₀+1))` with
  `σ.ρ t = map (charX t) f₀` on Icc. Needs `Mbar`, `hMbar : M t ≤ Mbar`,
  `hM_mono : MonotoneOn M (Icc)`, `hTL_PL`, `h_int_ext`.
* **`Phi_supW1_contraction`** (L6130, PROVEN): `(supW1On(Φρ,Φσ)).toReal ≤
  gronwallBound 0 (max 1 L) (L·D) T = q·D`, given `D` bounds `(W1(ρ,σ)).toReal`
  on Icc + full per-`z` flow regularity (init/cont/deriv/meas/int) for both.
* **`picard_iterate_bundlesAs_VlasovMeasureCurve`** (L6453, itself ×2 sorry —
  separate close): contracting sequence → limit `ρ_lim` + tendsto.

**KEYSTONE new infra — envelope re-bundling `Phi_step` → `space(m*)`** (helper
`Phi_step_envelope`, API-lock first): input `ρ : VlasovMeasureCurve d T m*`,
output flow + `σ' : VlasovMeasureCurve d T m*`.
  1. `Mbar := m* T`; `hMbar t ht := hm_mono ht ⟨…,le_refl⟩ ht.2 : m* t ≤ m* T`.
  2. `obtain ⟨charX,charV,C_T,_,hflow,h_growth_timedep,σ,hσ_eq⟩ :=
      Phi_step … m* (m* T) hMbar_nn hMbar hm_mono hTL_PL ρ h_int_ext`.
  3. New `hasMoment t ht`: `σ.ρ t = map (charX t) f₀` (hσ_eq) →
     `∫‖x‖∂(map charX t f₀) ≤ gronwallBound M_f₀ (1+L) (g0+L·m* t) t`
     (A.2, `m=m*`, `g0=‖gradW 0‖`, `h_growth=h_growth_timedep`, `h_meas` from
     Phi_step) → `≤ m* t` (A.3 Φ-invariance). `σ' := {σ with hasMoment := …}`
     (ρ/isProb/yIntegrable/hSupW1Cont carry unchanged).

**#11 restructure (the migration):**
  1. Signature: **ADD `hB : (L/(1+L))·(exp((1+L)·T)−1) < 1`.** Under Option A,
     #11 carries `hTL_PL` + `hTL_con` + `hB`.
  2. Replace trivial M-fixed-point (L6834) with
     `obtain ⟨m*, hm_mono, hm_ge, hm_inv⟩ := gronwall_envelope_exists
      M_f₀ ‖gradW 0‖ … L T hT.le hB` where **`M_f₀ := ∫z‖z‖∂f₀`** (phase-space,
     to match A.2 — see F1).
  3. Picard space `VlasovMeasureCurve d T (fun _ => M)` → `… d T m*` everywhere
     (the `obtain ⟨x,h_contract⟩` type, `picard_iterate_bundlesAs` call, ρ_lim).
  4. **Sorry 1** (Picard seq + contraction): `x : ℕ → VlasovMeasureCurve d T m*`
     by `Nat.rec`: base `x 0 := constantCurve μ₀` (moment OK:
     `∫‖x‖∂μ₀ ≤ ∫‖z‖∂f₀ = M_f₀ ≤ m* t` via `norm_fst_le` + hm_ge); step
     `x(k+1) := (Phi_step_envelope (x k)).σ'`. Contraction
     `supW1On(x k)(x(k+1)) ≤ q^k·D₀` by induction via `Phi_supW1_contraction`
     (D = q^{k−1}·D₀ from IH; flow regularity from the Phi_step_envelope calls).
  5. **Sorry 2** (self-consistency): `ρ_lim.extend t = spatialMarginal(pushforward
     charX charV f₀ t)` on Icc — space-agnostic, uses x/h_contract/ρ_lim/tendsto;
     Φ(ρ_lim)=ρ_lim by contraction+tendsto, triangle through `x n`.

**Consumer cascade (`hB` thread):** #11 → `vlasovWellPosedness_local` (~L7448) →
`vlasovWellPosedness_glue_step` (L7769) → `vlasovWellPosedness_universal_existence`
(L9503) → marquee. Each gains `hB`; the marquee **discharges** it by choosing
the local window `T₀` small (both `hTL_con` and `hB` → 0 as T → 0).

**FLAGS to resolve at execution:**
* **F1** A.2 initial moment is phase-space `∫z‖z‖∂f₀`; feed `gronwall_envelope_exists`
  the SAME `M_f₀`. Spatial `hasMoment` then follows (spatial moment ≤ phase-space).
* **F2** Is `hB` independent of `hTL_con` (= `q<1`, `gronwallBound 0 (max 1 L) L T<1`)?
  `K_env=1+L` vs `K_con=max 1 L`. Not obviously ordered — carry both unless a
  provable implication is found (then drop the weaker).
* **F3** `D₀` under envelope: currently `2*M`; recompute base `supW1On(x0)(x1)`
  bound with uniform `m* T` (likely `D₀ := 2·m*(T)` via `supW1On_le_two_moment`).
* **F4** `Phi_step_envelope` standalone (API-lock, cleaner) vs inline in #11. Prefer
  standalone.

**Order (P4 API-lock → leaves):** (1) `Phi_step_envelope` API-lock → green;
(2) #11 envelope restructure (+hB, two sorries restated) → green = API-lock commit;
(3) close `Phi_step_envelope` body (A.2+A.3); (4) close #11 sorry 1; (5) close #11
sorry 2; (6) thread `hB`, discharge at marquee small-T₀.

#### Piece D cascade map — refinements from execution (2026-06-01, post Phi_step_envelope API-lock)

**Landed:** `Phi_step_envelope` API-lock (CharFlow, right after `Phi_step` ~L5752):
signature locked + typechecks green; body `sorry` (+1, → CharFlow sorry inventory
11). Output = `_global_smallT` shape (flow + `IsCharacteristicFlowOn` + boundary
bundle) **+** `∃ σ : VlasovMeasureCurve d T m, σ.ρ t = map (charX t) f₀ on Icc`.
Body close = `Phi_step` internals + expose boundary + A.2/A.3 moment re-bundle.

**`hB` cascade — exact threading sites (mirror the `hTL_con` thread):**
* #11 `…_picard_fixedPointFlow` (L6807): add `hB`; sig currently `hTL_PL`(L6816)+
  `hTL_con`(L6817). Body: replace trivial M-fixed-point (L6885
  `⟨M_f₀, hM_f₀_nn, le_refl⟩`) with `gronwall_envelope_exists`; **redefine
  `M_f₀ := ∫z‖z‖∂f₀` (phase-space, F1)** — currently it is the *spatial* marginal
  moment (L6874). Picard space `(fun _ => M)` → `m`. Two sorries restated in
  `space(m)`. `q`/`hq_lt` UNCHANGED (M-independent, uses `hTL_con`).
* `vlasovWellPosedness_local` (`hTL_con` at L7511): add `hB`, pass to #11 (call L7611).
* `_finalAssembly_moment` / `_finalAssembly_isLagrangian` (`_hTL_con` at L7212/L7339):
  add `_hB` unused.
* `vlasovWellPosedness_glue_step` (`hT_0_small_con` at L7849): add `hB` for the window.
* `vlasovWellPosedness_universal_existence`: **the discharge site.** Currently
  `T_0 := min T_0_PL T_0_con / 2` and **already restricts to `L < 1`** (the
  `T_0_PL = (1/√L − 1)/2` selection at L8856 needs `√L < 1`; `hL_lt` used at L8894).
  To discharge `hB`: introduce `T_0_env` (threshold for `(L/(1+L))(e^{(1+L)T)−1)<1`),
  set `T_0 := min (min T_0_PL T_0_con) T_0_env / 2`, update the existing
  `min_le_left/right` steps in the `hTL_PL`(L8855) + `hTL_con`(L8892) discharges to
  the nested-min form, and add an `hB`-at-`T_0` discharge mirroring `hTL_T0_con`
  (L8892–8914): `T_0 < T_0_env`, `exp` monotone, `(L/(1+L))(e^{(1+L)T_0}−1) < 1`.

**Risk note:** the cascade is wide (6 theorems) + a real (small) analytic discharge.
Keep the tree green: legitimate to API-lock the `universal_existence` `hB`-discharge
as a 1-line `sorry` first (mirrors `hTL_T0_con` shape), then close. Don't half-land.

**Sorry accounting (cumulative-honesty):** project 14 → 15 at the `Phi_step_envelope`
API-lock (P4 expected temporary +1). Net trajectory once Piece D closes: the two
#11 sorries + the `Phi_step_envelope` body sorry retire (−3), modulo the
`picard_iterate_bundlesAs` ×2 (separate close) and the cascade adding no sorries.

#### Piece D — keystone CLOSED + mechanical #11 migration edit-list (2026-06-01)

**`Phi_step_envelope` body CLOSED first build try** (CharFlow ~L5752). Proven
infra; net-zero sorry (API-lock +1 retired). A.2 (`phi_moment_envelope_le`)
weakened `h_meas : ∀ t` → `∀ t ∈ Icc` (M2, no consumers) so the on-`Icc`-only
`charFlow_measurable_via_gronwall` measurability suffices. **Interface confirmed
at body level**: F1 anchor `∫z‖z‖∂f₀` (phase-space) matches A.2's `integral_map`
literal; `hm_inv` matches A.3's 3rd conjunct exactly ⇒ **cascade threads exactly
`hB`**, no side conditions, no form-mismatch.

**#11 `vlasovWellPosedness_local_picard_fixedPointFlow` migration — exact edits
(current line numbers):**
1. **Sig L6964**: add after `hTL_con` →
   `(hB : (L:ℝ)/(1+(L:ℝ))*(Real.exp((1+(L:ℝ))*T)-1) < 1)`.
2. **L7021 (F1)**: `let M_f₀ : ℝ := ∫ z, ‖z‖ ∂f₀` (drop `(spatialMarginal …)`).
   Fix `hM_f₀_spec` (L7023) — it is `∫spatial ≤ M_f₀`; either drop (check
   usage) or reprove `≤` via `norm_fst_le` (no longer `le_refl`).
3. **L7032-7033 (replace trivial M)**:
   `obtain ⟨m, hm_mono, hm_ge, hm_inv⟩ := gronwall_envelope_exists M_f₀ ‖gradW 0‖
     hM_f₀_nn (norm_nonneg _) L T hT.le hB`
   `have hm_nn : ∀ t ∈ Icc 0 T, 0 ≤ m t := fun t ht => le_trans hM_f₀_nn (hm_ge t ht)`
   `have hMbar_nn : 0 ≤ m T := hm_nn T ⟨hT.le, le_refl T⟩`
   `have hMbar_mono : ∀ t ∈ Icc 0 T, m t ≤ m T := fun t ht => hm_mono ht ⟨hT.le, le_refl T⟩ ht.2`
4. **L7136**: `let D₀ : ℝ := 2 * (m T)`; `hD₀_nn` via `by positivity`/`linarith [hMbar_nn]`.
5. **L7139 (sorry-1 type)**: `∃ x : ℕ → VlasovMeasureCurve d T m, ∀ k,
     supW1On (Icc 0 T) (x k).ρ (x (k+1)).ρ ≤ ENNReal.ofReal (q^k * D₀)`.
   (Body stays `sorry` — leaf. NOTE: the recursion closing this uses
   `Phi_step_envelope` per step; that helper is now proven.)
6. **L7147 (picard call)**: unchanged shape; `x : space m` flows through
   (`picard_iterate_bundlesAs` is generic in `M`), giving `ρ_lim : space m`.
7. **Step 7 `_global_smallT` (the `M hM_nn` + `extend_hasMoment` args)**: replace
   `M hM_nn (fun t => extend_hasMoment hT.le ρ_lim t)` with
   `(m T) hMbar_nn (fun t => le_trans (extend_hasMoment hT.le ρ_lim t)
      (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t)))`.
8. **Final witness L7257-7258**: `… , m T, hMbar_nn, ?_, …`.
9. **Conjunct (3) moment bound L7307-7310**: after the `rw`, goal is
   `∫‖y‖∂(ρ_lim.extend s) ≤ m T`; replace `exact extend_hasMoment …` with
   `exact le_trans (extend_hasMoment hT.le ρ_lim s)
     (hMbar_mono (clampToIcc T s) (clampToIcc_mem hT.le s))`.
   (`q`/`hq_lt` UNCHANGED — M-independent. Sorry-2 self-consistency UNCHANGED.)

**Consumer thread (add `hB`, mirror `hTL_con`):** `vlasovWellPosedness_local`
(sig L7658, pass to #11 call), `_finalAssembly_moment` (L7349) +
`_finalAssembly_isLagrangian` (L7476) as unused `_hB`, `glue_step` (L7967).
**Discharge** at `universal_existence` (L9701): add `T_0_env`, set
`T_0 := min (min T_0_PL T_0_con) T_0_env / 2`, fix the nested-`min` `min_le`
steps in the `hTL_PL`(L8855-area)+`hTL_con`(L8892-area) discharges, add
`hB`-at-`T_0` mirroring `hTL_T0_con`. **API-lock the hB-discharge as a 1-line
`sorry` first if the T_0-tightening is fiddly; keep green; close after.**

#### Piece D — envelope cascade LANDED GREEN (2026-06-02)

**Fired as pure mechanical signature-threading (discharge sorry'd upfront,
unconditionally). Built green on the first attempt; net +1 sorry (14→15), the
`hTL_T0_B` discharge — matching prediction.** The compiler verified threading
completeness (a missing `hB` arg = hard error, not silent pass).

Landed edits:
* **#11** migrated to envelope space `m` (F1 phase-space `M_f₀ = ∫z‖z‖∂f₀`;
  `gronwall_envelope_exists` → `m`; Picard space `space(m)`; `m T` uniform bound
  in Steps 6–9 + final witness; conjunct-(3) via `hMbar_mono`). Its **2 leaves
  preserved** (L7152 Picard-in-`space(m)`, L7236 self-consistency). `q`/`hq_lt`
  untouched (M-independent).
* **`hB` threaded**: `_local` (sig + #11 call), `glue_step` (sig + `_local`
  call), and **`vlasovWellPosedness_forward`** (the continuation tower — NOT
  `universal_existence`; my earlier edit-list mislabeled this) which *derives*
  `hTL_T0_B` internally (L9084, sorry'd) and threads to its `_local`/`glue_step`
  calls. `_finalAssembly_*` need no `hB` (downstream of #11's output, confirmed
  by green build). `universal_existence` calls `_forward` (signature unchanged) ⇒
  marquee unaffected.
* **A.2** (`phi_moment_envelope_le`) `h_meas` weakened `∀ t` → `∀ t ∈ Icc` (M2).

**Remaining Piece D leaves (close against the GREEN tree, isolated):**
1. **`hTL_T0_B` discharge** (`_forward` L9084): the analytic `T_0`-tightening —
   add `T_0_env` (exists since `B(0)=0`, `B` cont. strictly incr.), set
   `T_0 := min (min T_0_PL T_0_con) T_0_env / 2`, update the nested-`min`
   `min_le` steps in the PL(L~9015)+con(L~9053) discharges, prove
   `B(T_0) < 1`. Touches `_forward`'s `T_0` def only.
2. **#11 sorry-1** (L7152): Picard recursion in `space(m)` — base
   `constantCurve μ₀` (moment OK: `∫‖x‖∂μ₀ ≤ M_f₀ ≤ m t`), step via
   **`Phi_step_envelope`** (proven) + geometric contraction via
   `Phi_supW1_contraction` (proven), `D = q^{k-1}·D₀`.
3. **#11 sorry-2** (L7236): self-consistency `ρ_lim.extend t = spatialMarginal(
   pushforward charX f₀ t)` — space-agnostic, Φ(ρ_lim)=ρ_lim via contraction+
   tendsto, triangle through `x n`.
Plus `picard_iterate_bundlesAs` (×2, pre-existing) on the same path.

#### Piece D — hB discharge leaf CLOSED (2026-06-02)

**`hTL_T0_B` closed first build try; 15→14. The foundational risk did NOT
materialize** — the three thresholds intersect positively, envelope constraint
is compatible with the existing window selection (news obtained BEFORE building
the two #11 leaves on it, per the discharge-first ordering).

Edits (all in `vlasovWellPosedness_forward`):
* Added `T_0_env := Real.log (1 + (1+L)/L) / (1+L)`; `T_0 := min (min T_0_PL
  T_0_con) T_0_env / 2` (nested min-of-three).
* `hT_0_env_pos` via `div_pos (Real.log_pos _) h_1L_pos`; 3-way `lt_min`.
* 4 ripple sites: PL discharge `min_le` → `le_trans (min_le_left) (min_le_left)`;
  con discharge → `le_trans (min_le_left) (min_le_right)`; positivity `show`s.
* `hTL_T0_B`: `T_0 < T_0_env` → `(1+L)T_0 < log(1+(1+L)/L)` (`exp_lt_exp` +
  `exp_log`) → `exp((1+L)T_0)−1 < (1+L)/L` → `(L/(1+L))·(…) < (L/(1+L))·((1+L)/L)
  = 1` (`field_simp`).
* **L-range check (user-requested): PASS.** Proof uses only `hL_pos` (`L>0`), no
  stricter bound; `T_0_env > 0` for every `L>0` ⇒ `L<1` ceiling unchanged
  (it's a `T`-threshold, not an `L`-restriction). No faithfulness regression.

**Piece D status:** `Phi_step_envelope` proven · #11 envelope-migrated · hB
cascade threaded · hB discharge CLOSED. **Remaining: #11 sorry-1 (Picard
recursion in `space(m)`, L7152) + sorry-2 (self-consistency, L7236)** — both now
on a CONFIRMED-SOUND foundation. (Plus `picard_iterate_bundlesAs` ×2 on path.)
Project sorry count 14 (baseline), but Piece D ~75% landed.

#### Piece D — (i) enriched type LOCKED + (ii) scoped (2026-06-02)

**(i) DONE:** #11 sorry-1's existential enriched (architecture A) to expose, per
step `k`, the flow `(charXs k, charVs k)` against `(x k).extend` (= `Phi_step_
envelope`'s output shape verbatim) + pushforward identity `(x(k+1)).ρ t =
map (charXs k t) f₀`. **Elaborates green** (≠ validated — that's (ii)+(iii)).

**(ii) scoped — regularity layer found & RESOLVED.** Opening the `Nat.rec`:
`Phi_supW1_contraction` + `Phi_pointwise_contraction` declare the 6 flow-regularity
hyps (`h_meas`/`h_int_charX`/`h_yint_Phi` ρ,σ) as `∀ t`, but the exposed `charXs`
(IsCharFlowOn on `Ioo` + boundary on `Icc`) is controlled only on `Icc`.
**Resolution: M2-weaken both** `∀ t → ∀ t ∈ Icc` — confirmed both bodies use these
hyps only at `t ∈ Icc` (supW1On one's `intro t ht` block + its pass-through to the
pointwise lemma), and **both have zero functional consumers** (only the pointwise
lemma is called, inside the supW1On one), so weakening is FREE. **No clamp-bridge
needed** — the exposed unclamped `charXs` works directly. (Mirror of the A.2
weakening.)  [Line-drift note: `Phi_step_envelope`'s insertion shifted these ~200
lines; caught by re-grep — the "maps drift across edits" pattern.]

**sorry-1 plan (crystallized):**
1. M2-weaken `Phi_pointwise_contraction` + `Phi_supW1_contraction` (`∀t`→`∀t∈Icc`;
   `h_x t` → `h_x t ht`; free).
2. Recursion: `h_int_ext_gen : ∀ (ν : space m) t x, Integrable (gradW(x-·)) (ν.extend t)`
   (dominator, like `h_int_ρ_lim`); per-step `step ν := Phi_step_envelope … ν
   (h_int_ext_gen ν)` reshaped `∃ σ cX cV, (pushforward id) ∧ IsCharFlowOn ∧ bdry`;
   `x := Nat.rec (constantCurve μ₀-in-m) (fun _ ν => Classical.choose (step ν))`;
   `charXs k := <cX of step (x k)>`, etc. Flow-facts = `step`'s spec verbatim.
3. Contraction induction `supW1On(x k)(x(k+1)) ≤ ofReal(q^k D₀)`: base k=0 via
   `supW1On_le_two_moment_of_VlasovMeasureCurve (m T) hMbar (x0)(x1)` (= ofReal
   2(m T) = ofReal D₀); step via weakened `Phi_supW1_contraction` (exposed charXs
   + derived 6 facts) giving `.toReal ≤ q·D`, IH `D ≤ q^k D₀`, ENNReal↔toReal via
   `supW1On_ne_top_of_VlasovMeasureCurve`.

**sorry-2 plan** (after sorry-1): triangle `W1(ρ_lim t)(Φ(charX) t) ≤
W1(ρ_lim t)(x_n t)[→0, picard tendsto] + W1(x_n t)(Φ(charX) t)[=W1(Φ(charXs_{n-1}))
(Φ(charX)) ≤ q·D_{n-1}→0 via contraction w/ exposed flows]` → separation
(`wasserstein1_eq_zero_iff_measure_eq`, banked). **WATCH: the uniform-`D_{n-1}`
step** (`supW1On(x_{n-1})(ρ_lim)` from pointwise picard tendsto) — read the
`n→∞`-inside-sup for a hidden `sup_t lim_n ≤ lim_n sup_t` interchange; if it needs
LSC, check banked `#4 w1LowerSemicontinuous` before assuming free.

#### ⚠️ FRESH-SESSION OPENING for sorry-1 (read BEFORE executing — 2026-06-02)

The sorry-1 plan above is right, but its **opening move is NOT the `Nat.rec`** — it is
a **fresh re-verification of the M2-weakening's freeness**, for a specific reason:
the "both contractions use the 6 hyps only at `t ∈ Icc`" + "zero functional
consumers" reads were done LATE in a very long turn, in the SAME turn that the
line-drift misread bit (read `Phi_pointwise_contraction` as `Phi_supW1_contraction`
because `Phi_step_envelope`'s ~190 lines shifted everything). They are *probably*
right — but "probably right, verified late, on lemmas whose line numbers just
shifted" is exactly the state where executing-now converts a likely-clean signature
change into a possibly-wrong one threaded through a `Nat.rec` you'd then unwind.

**So sorry-1 opens with, in order:**
1. **Re-grep at CURRENT line numbers** (they will have drifted again if anything
   landed): locate `Phi_pointwise_contraction` + `Phi_supW1_contraction`; confirm
   (a) zero functional call sites of either (all hits comments except the pointwise
   call *inside* the supW1On one), and (b) both use `h_meas/h_int_charX/h_yint_Phi`
   ρ,σ only at `t ∈ Icc`. This is the discharge-first/body-first discipline applied
   to the weakening: re-confirm the thing that can quietly invalidate the assembly
   (a misread consumer of the weakened lemma) in FRESH conditions before the change.
2. THEN the free M2-weakening (`∀t`→`∀t∈Icc`; `h_x t`→`h_x t ht`).
3. THEN the `Nat.rec` recursion (step 2 of the banked plan).
4. THEN the contraction induction (step 3 of the banked plan).

**Carry-forward #2 (sorry-2, when reached):** the uniform-`D_{n-1}` step —
`supW1On(x_{n-1})(ρ_lim)` recovered from picard's POINTWISE tendsto — must be read
for a hidden `sup_t lim_n ≤ lim_n sup_t` interchange BEFORE assuming it is
LSC-free. The on-paper argument (geometric from conjunct (a) + triangle + pointwise
tendsto) says no LSC is needed; confirm that in the body. If it bites, the fallback
is the banked FA placeholder **#4 `w1LowerSemicontinuous…`** — check it exists/fits
before treating LSC as a new obligation.

Piece D standing: keystone proven · #11 migrated · cascade landed · discharge
closed · enriched type locked (elaborates; validated-pending) · regularity layer
resolved (free weakening, re-verify fresh per above). **Two leaves left:** sorry-1
(assembly, opens on re-grep-then-weaken) + sorry-2 (assembly + flagged interchange).

#### ⚠️ Sorry inventory — CORRECTED tiering (2026-06-02, post user purity-audit recall)

Prior inventory mislabeled two things (both caught by the user's checks):
* **`picard_iterate_bundlesAs_VlasovMeasureCurve` is PROVEN** (sorry-free, L6651–6844).
  It was wrongly listed "2 active sorries" — the awk mapped two *`private`* decls
  (which the `/^(theorem|lemma)/` pattern skipped) to it. So **sorry-2 consuming
  picard's output (ρ_lim + tendsto) does NOT stand on a sorry** — Check 2 clears.
* The two real warnings at L6845/L6870 are
  `MathlibTODO_lipschitzFlowAEMeasurable` (deferred pure-FA) and
  **`picardCharFlow_aemeasurable`** (INTERNAL Vlasov AEMeasurability) — the latter
  **consumed by #11's conclusion AEMeasurable conjunct (L7355)**, so it is a THIRD
  #11-dependency leaf beyond sorry-1/sorry-2 (closes that conjunct; itself bottoms
  in the deferred `MathlibTODO_lipschitzFlowAEMeasurable`, "mostly mechanical").

**The 14, correctly tiered:**
* **MathlibTODO_-prefixed (10):**
  - **7 ship-ready external**: `bcEqualFromLipschitzEqual_polish_firstMoment`,
    `w1LowerSemicontinuousAlongNarrowMomentCurves` (= the `#4` LSC fallback for
    sorry-2), `bcNarrowFromSmoothCompactNarrow`, `w1UpperSemicontinuousAlongLagrangianFlows`,
    `lipschitzFlowTrajectoryLipBound`, `lipschitzFlowAEMeasurable`, `W1ContOn_On`.
  - **2 hard-OT (multi-month; the real handoff deliverable)**:
    `cauchyW1_hasNarrowLimit` (Prokhorov+tightness), `w1RightDerivBoundAlongLagrangianFlowsOn`.
  - **1 MISLABELED-INTERNAL (owed, not a deferral)**: `convolveContinuousAtOfNarrowMoment`
    — its conclusion is `ContinuousAt (fun t => convolveFunctionMeasure gradW (μ t) x) t₀`,
    referencing the PROJECT def `convolveFunctionMeasure`; not liftable as a Mathlib
    citation as written. Either restate into pure kernel-convolution vocabulary
    (→ genuinely external) or close it internally. The `MathlibTODO_` prefix must
    not re-launder it into the trust bucket.
* **Internal / active (4):** `#11` (sorry-1 Picard recursion + sorry-2 self-consistency),
  **`picardCharFlow_aemeasurable`** (consumed by #11 conclusion), `glue_step`,
  `universal_existence`. **`picard_iterate_bundlesAs` PROVEN — not active.**

**Honest #11 closeout:** sorry-1 → sorry-2 (NOT on a picard sorry; clear) →
`picardCharFlow_aemeasurable` (co-requisite for #11's conclusion; internal-modulo
deferred FA) — THEN #11 fully closes. `glue_step`/`universal_existence` are the
genuinely-surrounding continuation work.

#### Piece D — sorry-1 prerequisites DONE (2026-06-02 cont.)

Two green, sorry-free pieces of sorry-1 landed (count steady 14):
1. **M2-weakening of both contraction lemmas** — re-verified FRESH at current line
   numbers first (zero functional consumers confirmed: `Phi_supW1_contraction`
   uncalled, `Phi_pointwise_contraction` called only inside it; both use the 6 hyps
   only at `t∈Icc`). Weakened `∀t`→`∀t∈Icc` (`Phi_pointwise_contraction` L6178,
   `Phi_supW1_contraction` L6328), usages `h_x t`→`h_x t ht`. Built green first try.
   The exposed unclamped `charXs` now feeds them directly (no clamp-bridge).
2. **`envelopeStep_contractionInputs` helper PROVEN** (inserted before #11's
   docstring, after `picardCharFlow_aemeasurable`). Takes a flow's exposed facts
   (`IsCharacteristicFlowOn` Ioo + boundary Icc + `h_int_ext`) against `ν : space m`
   and a uniform bound `Mbar`; outputs the 6 `Phi_supW1_contraction`-ready facts
   (`∀t∈Icc`: AEMeas, Integrable‖cX‖, Integrable‖·‖∘map; `∀z`: init, ContinuousOn,
   `vlasovVectorField (Ici s)` deriv). Body: `Stage_1_9_flow_boundary_regularity`
   (init/cont/deriv EXACT) + `charFlow_measurable_via_gronwall` (AEMeas) +
   `flow_distance_growth_bound_on` (growth → the 2 integrability facts via dominator
   + `integrable_map_measure`). **The seam-1 gap is now closed as proven infra.**

**Remaining sorry-1 (the Nat.rec + induction):** construct `x : ℕ → space m`,
`charXs/charVs` via `Phi_step_envelope` + `Classical.choose` (σ-first existential so
`x(k+1) = Classical.choose (step (x k))`); conjunct (b) flow-facts = `step`'s spec
verbatim; conjunct (a) contraction bound by induction — base `supW1On_le_two_moment`
(`= ofReal D₀`), step `Phi_supW1_contraction` fed by `envelopeStep_contractionInputs`
(both flows), `gronwallBound 0 K (L·D) T = q·D`, IH, ENNReal↔toReal via
`supW1On_ne_top`. (Placement gotcha learned: a helper between a docstring and its
theorem orphans the docstring — insert helpers BEFORE the consumer's docstring.)

#### ⚠️ FRESH-SESSION OPENING for the sorry-1 Nat.rec+induction (read BEFORE coding)

The seam-1 uncertainty is CLOSED (`envelopeStep_contractionInputs` proven, M2-weaken
done). What remains — dependent `Nat.rec` over `Classical.choose` + the contraction
induction with ENNReal↔toReal — is the most mechanically-fiddly construction left,
and a mechanical slip already happened this turn (helper placement orphaned #11's
docstring). So open the induction on TWO soundness checks BEFORE the `Nat.rec`,
because both are wrong-number traps invisible to a green build:

1. **Base-case `D₀`-IDENTITY (not just same-shape bound).** The induction proves
   `supW1On (x k) (x(k+1)) ≤ ENNReal.ofReal (q^k · D₀)`; at `k=0`,
   `supW1On (x 0) (x 1) ≤ ofReal D₀`. `D₀ := 2 * (m T)`. `supW1On_le_two_moment_of_
   VlasovMeasureCurve Mbar hMbar (x0) (x1)` outputs `≤ ofReal (2 * Mbar)` with
   `Mbar = m T` ⇒ `ofReal (2 * (m T)) = ofReal D₀`. **Verify this is a DEFINITIONAL
   match, not "a bound of the same shape you then massage to D₀."** This is the exact
   layer the project's first soundness bug lived (the `q := gronwallBound 0 (max 1 L)
   (L·2M) T` D₀/contraction-factor conflation, fixed `2eed838`). A `2·moment` vs `D₀`
   gap typechecks as `ℝ` and goes invisible. Pin `Mbar = m T` so `2*Mbar` IS `D₀`.

2. **ENNReal `ofReal`-NONNEGATIVITY carried explicitly.** The step needs
   `ofReal (q^k·D₀) * ofReal q = ofReal (q^(k+1)·D₀)` (or the additive/`toReal`
   analog). `ENNReal.ofReal` of a NEGATIVE collapses to `0` SILENTLY — so a bound can
   read `≤ 0` vacuously and look proved. Carry `0 ≤ q^k · D₀` (from `hq_nn` +
   `hD₀_nn`, both in scope) EXPLICITLY at each step so the `ofReal` multiplications
   compose. Finiteness side is `supW1On_ne_top_of_VlasovMeasureCurve` (banked); the
   nonnegativity side is the one to not assume. (M1 — sign errors hide at the
   structure-projection boundary; do the algebra in the natural home, project once.)

THEN the `Nat.rec`: `x := Nat.rec (constantCurve μ₀ ...) (fun _ ν => Classical.choose
(step ν))`; `step ν` = reshaped `Phi_step_envelope ... ν (h_int_ext_gen ν)` with σ
FIRST so `x(k+1) = Classical.choose (step (x k))`; `charXs/charVs` = the chosen
flow; conjunct (b) = `step` spec verbatim; conjunct (a) = the induction above, each
step calling the proven `envelopeStep_contractionInputs` (Mbar = m T) for both flows
to discharge `Phi_supW1_contraction`'s 6 hyps.

#### Piece D — sorry-1 CLOSED (2026-06-02 cont.) — #11 down to its last sorry

**The Picard recursion + contraction induction is fully proven (sorry-free).**
#11 now has ONLY sorry-2 (self-consistency, ~L7522). Declaration count holds at 14
(#11 still emits one warning for sorry-2); the token-level win is the whole ~250-line
sorry-1 body.

What landed:
* **Scaffold** (first pass, green first try): `h_int_ext_gen` (general conv-integrability),
  base-moment bound `hμ₀_le_m` (∫‖y‖∂μ₀ = ∫‖z.1‖∂f₀ ≤ M_f₀ ≤ m t), `step` (reshaped
  `Phi_step_envelope`, σ-first), the sequence `x/charXs/charVs` via `Nat.rec` +
  `Classical.choose`, `hx_succ` by `rfl`, `hspec` (triple-`choose_spec`), conjunct (b)
  `h_flow` from `hspec` verbatim.
* **Conjunct (a)** (contraction induction): base via `supW1On_le_two_moment` (the
  banked D₀-IDENTITY check passed — `Mbar = m T`, `2*Mbar` IS `D₀ = 2*(m T)`); step via
  the M2-weakened `Phi_supW1_contraction` fed by the proven `envelopeStep_contractionInputs`
  (both flows, 12 facts) + `hq_scale` (gronwallBound 0 K (L·D) T = D·q) + supW1On
  congruence-on-Icc (`iSup_congr` + the pushforward identity) + the banked NONNEGATIVITY
  check (`0 ≤ q^k·D₀` carried explicitly for the `ofReal`↔`toReal` lift via
  `ENNReal.toReal_mono`/`toReal_ofReal`).

**Mechanical gotcha (banked for next time):** the `[∀ t, IsProbabilityMeasure (ρ t)]`
instance arg to `Phi_supW1_contraction` would NOT synthesize for `ρ = (x k).extend`
(`x` is `let`-bound over `Classical.choose`, so `{M}`-inference is stuck "due to
metavariables") — local `haveI`s of the Pi type were not consulted either. Fix:
`@Phi_supW1_contraction d _ … (hPext (x k)) (hPext (x (k+1))) … f₀ _ …` — pass the two
`[∀ t, IsProb]` instances EXPLICITLY (via an abstractly-typed `hPext : ∀ ν t, IsProb
(ν.extend t)`, so applying to `x k` is substitution, not re-inference). The `@` bypasses
synthesis entirely; build green.

**Remaining on #11:** sorry-2 (self-consistency, the architecture-A triangle: open on
the uniform-`D` interchange read per the earlier banked flag) + the co-requisite
`picardCharFlow_aemeasurable` (internal-modulo-deferred-FA).

#### ⚠️ FRESH-SESSION OPENING for sorry-2 (run checks 1–2 BEFORE sorry-2 itself)

sorry-2 (self-consistency) is the one genuinely-new proof in the internal pile, and it
CONSUMES sorry-1's output (the exposed flows + the contraction bound). So before touching
it, run two cheap re-reads on the just-closed sorry-1 — green build proved the TYPES
elaborated, not that the semantics are right where it was non-mechanical:

1. **sorry-1 base-case hidden-dependency check** (the `D₀`-identity layer — where the
   project's first soundness bug lived). The base does
   `supW1On_le_two_moment_of_VlasovMeasureCurve (m T) hMbar_mono (x 0) (x 1)`. That lemma
   bounds `supW1On ρ σ ≤ ofReal(2·Mbar)` using BOTH `ρ.hasMoment` and `σ.hasMoment`
   (each `≤ m t ≤ m T`). `x 0 = constantCurve μ₀ ∈ space m` (A.3 domination, `m 0 ≥ M_f₀`).
   `x 1 = Classical.choose (step (x 0))` = `Phi_step_envelope`'s `σ`, which is in `space m`
   **via the A.2+A.3 envelope invariance** — so `x 1.hasMoment ≤ m t` is genuine, not
   vacuous. CONFIRM by reading that `x 1`'s `space m` membership routes to the
   `Phi_step_envelope` re-bundle, i.e. BOTH curves' moments genuinely `≤ m T`. (Green
   build already forces `x 1 : VlasovMeasureCurve d T m` at the lemma call — this is the
   semantic confirmation that the membership isn't leaning on an undischarged fact.)
2. **`@Phi_supW1_contraction` explicit-instance positional check.** The `@`-form passes
   `(hPext (x k)) (hPext (x (k+1)))` into the two `[∀ t, IsProb (·)]` slots (positions 8–9,
   right after `ρ = (x k).extend`, `σ = (x (k+1)).extend`). These two instances have
   DISTINCT types (`∀ t, IsProb ((x k).extend t)` vs `… (x (k+1)).extend …`), so a swap
   would NOT typecheck — green build ⇒ positionally correct. Quick-confirm they're not
   swapped (curve-specific types make this a 30-second read), closing the "green =
   elaborated, not correct" gap on the one non-synthesized part of the close.

3. **THEN sorry-2** (L~7522), opening on the **uniform-`D` interchange read**: the
   triangle's Term-2 needs `supW1On(x_{n-1})(ρ_lim)` (uniform) but picard exposes only
   POINTWISE `wasserstein1((x n).ρ t)(ρ_lim t) → 0`. Recover the uniform bound by geometric
   series (from `h_contract`) + triangle + pointwise tendsto — read whether the
   `n→∞`-inside-`sup_t` step smuggles a `sup_t lim_n ≤ lim_n sup_t` interchange. If it
   needs LSC, that is the banked PLACEHOLDER `#4 MathlibTODO_w1LowerSemicontinuous…` —
   meaning sorry-2 would STAND ON A SORRY (handle deliberately, don't let it pass as
   closed). The architecture-A bet is that the contraction bridges curve-distance to
   pushforward-distance WITHOUT ever taking a flow limit, so no LSC is needed — confirm
   that holds in the body. Final step: `wasserstein1 = 0 → μ = ν` is banked
   (`wasserstein1_eq_zero_iff_measure_eq`). Plus the co-requisite
   `picardCharFlow_aemeasurable` for #11's conclusion (internal-modulo-deferred-FA).

#### ✅ #11 sorry-2 CLOSED — #11 fully proven (2026-06-02) — sorry 14 → 13

`vlasovWellPosedness_local_picard_fixedPointFlow` is now **sorry-free**.  Build green
(`lake build Vlasov.OT.CharacteristicFlow`, EXIT 0).  The Picard fixed-point / self-
consistency equation — *the project's one genuinely-new piece of mathematics* — is
proven.

**Checks 1–2 (pre-write, both CLEAN):**
* (1) base-case hidden-dependency: `supW1On_le_two_moment_of_VlasovMeasureCurve` (L4248)
  genuinely consumes BOTH `ρ.hasMoment`/`σ.hasMoment` (each `≤ m t ≤ m T`); `x 1`'s
  `space m` membership is a structure field forced by the green build — `D₀ = 2·(m T)`
  matches `q^0·D₀`.  No undischarged fact.
* (2) `@`-instance positional: `Phi_supW1_contraction` takes `(ρ σ)` then
  `[∀t IsProb ρ][∀t IsProb σ]`; the call passes the two curves then the two `hPext`
  in matching order (distinct curve-specific types ⇒ green = not swapped).

**Interchange-read VERDICT — architecture-A bet HELD; sorry-2 does NOT stand on a sorry.**
NO LSC / NO `#4 MathlibTODO_w1LowerSemicontinuous…` dependency.  The mechanism (realised
in the body): the uniform bound `supW1On (x n) ρ_lim → 0` comes from sup-ing the *t-uniform*
helper `picard_iterate_limit_uniform_tendsto` over `s` — i.e. a **t-independent constant**
is passed through the *pointwise* limit, so no `sup_t lim_n ≤ lim_n sup_t` interchange ever
occurs.  Used `Dn n := (supW1On (Icc) (x n).ρ ρ_lim.ρ).toReal` as the explicit uniform `D`
feeding `Phi_pointwise_contraction` (Term 2).

**Proof shape (≈170 lines, CharFlow L7519+):** on `Icc`, `ρ_lim.extend t = ρ_lim.ρ t` and
`spatialMarginal(vlasovSolutionViaPushforward charX charV f₀ t) = map (charX t) f₀`
(`h_marg`, via `Measure.map_map measurable_fst` + `rfl`); `charX` is the flow built against
`ρ_lim.extend`, so RHS = `Φ(ρ_lim) t`.  Show `W₁(ρ_lim.ρ t, Φ(ρ_lim) t) = 0` by triangle
through `x(n+1) = Φ(x n)` (`h_flow n .2.2`): Term1 `= W₁(x(n+1) t, ρ_lim t) → 0` (pointwise
`h_tendsto` reindexed by `n+1`); Term2 `≤ ofReal(Dn n · q)` via `Phi_pointwise_contraction`
+ `gronwallBound_mono` + `hq_scale` (`gronwallBound 0 K (L·a) T = a·q`); both legs `→ 0`,
`ge_of_tendsto'` ⇒ `≤ 0`, then `wasserstein1_eq_zero_iff_measure_eq` (banked separation).

**Engineering notes for future scope:** `hCI` (per-step 6-fact `envelopeStep` bundle) and
`h_int_ext_gen` were LOCAL to the closed sorry-1 block — **rebuilt at main scope** from
`h_flow` + main-scope hyps (no touching the closed existential).  The ρ_lim flow's bundle
`hCI_lim` comes from `envelopeStep_contractionInputs` on `hflow_on_ρlim`/`h_boundary_ρlim`
(the `_global_smallT` boundary bundle matches `envelopeStep`'s `hbdry` exactly).  Un-discarded
`_h_tendsto → h_tendsto` at the picard-bundling `obtain` (L7442).

#### State-of-the-board after #11 close (13 declaration-level sorries, 2026-06-02)

**Deferred Mathlib-OT (9)** — `MathlibTODO_*`, separate-swing closures:
`bcEqualFromLipschitzEqual_polish_firstMoment` (Basic 1315), `cauchyW1_hasNarrowLimit`
(Basic 1428), `w1LowerSemicontinuousAlongNarrowMomentCurves` (Basic 1995 — the `#4` LSC,
NOT on #11's path), `bcNarrowFromSmoothCompactNarrow` (Basic 2074),
`w1UpperSemicontinuousAlongLagrangianFlows` (Basic 2185),
`w1RightDerivBoundAlongLagrangianFlowsOn` (Basic 2299),
`lipschitzFlowTrajectoryLipBound` (CharFlow 2994), `lipschitzFlowAEMeasurable`
(CharFlow 6853, private), `wassersteinGronwallCoupling_W1ContOn_On` (CharFlow 9765).

**Internal / active (4)** — the real remaining work:
* `MathlibTODO_convolveContinuousAtOfNarrowMoment` (Basic 1728) — internal-wearing-the-
  prefix (conclusion references project `convolveFunctionMeasure`); owed internal work.
* `picardCharFlow_aemeasurable` (CharFlow 6878, private) — #11's AEMeasurable-conjunct
  co-requisite (internal-modulo-deferred-FA).
* `vlasovWellPosedness_glue_step` (CharFlow 8450) — continuation glue.
* `vlasovWellPosedness_universal_existence` (CharFlow 10242) — universal-existence assembly.

The marquee `vlasovWellPosedness` is green (composes the above); per the watch-list
"clean-interface-over-a-load-bearing-sorry'd node", it is proved-modulo glue_step +
universal_existence (+ their deferred-FA leaves) — a `(c)` proved-modulo-sorry sweep is
the scheduled gate before declaring the existence side finished.

**Committed:** `5d725ed` (OT: close #11 self-consistency — the full Piece D arc).

#### (c) proved-modulo-sorry SWEEP — post-#11-close, CERTIFIED CLEAN (2026-06-02)

Ran the scheduled `(c)` sweep immediately after closing #11, focused on #11's
consumers — *because* closing the tree's biggest dependency (sorry'd → proven) is the
event most likely to have grown a hidden obligation (P10: green build certifies *types*
compose, not that consumers use the *realized* conclusion the way they used the *stub*).

**Call graph (live; the `.current` file is a stale backup, ignore):**
`picardCharFlow_aemeasurable` (sorry, L6878) → used in **#11 body** (L7806, produces #11
conjunct 7) → #11 (sorry-free body) → **sole consumer `vlasovWellPosedness_local`**
(destructures #11's 11-tuple at L8239) → `glue_step` (L8528) + continuation tower (L9641).
`glue_step`/`universal_existence` consume `vlasovWellPosedness_local`, **not #11 directly**.

**Finding 1 — NO grown obligation (the gate the user wanted before `glue_step`):**
#11's conclusion type was API-locked early (P4) and is byte-identical pre/post sorry-2 —
sorry-2 only filled the body.  `vlasovWellPosedness_local` was already written against the
**self-consistent-flow shape**: it consumes `_hflow_on` = #11 conjunct 2 =
`IsCharacteristicFlowOn gradW (fun t => spatialMarginal(vlasov…)) charX charV …` (the flow
against its OWN marginal), via `.1` (initial condition, L8254/8288/8319) and a wholesale
pass to the `_finalAssembly_*` helpers.  sorry-2 delivers the previously-*promised*
self-consistency as now-*realized*, with the same shape.  No consumer leaned on a stub
part the real proof realizes differently. **The descent foundation is sound.**

**Finding 2 — the one certified residual (the load-bearing node, pinned):**
#11 conjunct 7 (`_h_aemeas`, `∀ s, AEMeasurable (charX s,charV s) f₀`, consumed at L8309 +
passed to finalAssembly) routes through the still-sorry'd `picardCharFlow_aemeasurable`
(L6878, body = bare `sorry`).  Its documented closure = internal `HasDerivAt.prodMk` glue
**+** the deferred `MathlibTODO_lipschitzFlowAEMeasurable` (L6853).  So
`vlasovWellPosedness_local`, `glue_step`, `universal_existence`, and the marquee are all
**proved-modulo `picardCharFlow_aemeasurable`** via this one conjunct — i.e. internal-glue-
modulo-deferred-FA, NOT genuine open mathematics.  This is the watch-list's "clean-
interface-over-load-bearing-sorry'd-node" shape, now CERTIFIED (not predicted) and pinned
to a single node.  `_finalAssembly_moment`/`_finalAssembly_isLagrangian` pull no *other*
sorry (sorry-free, not in the list).

**Watch-list:** the sweep was run as a *scheduled gate* (its watch-list recommendation),
and the gate paid — it certified the seam rather than leaving "marquee bottoms out cleanly"
as an untested assertion.  This exercise argues for promoting the sweep-as-gate from
candidate to standing practice (the scheduling sharpening of P10).

#### `convolveContinuousAtOfNarrowMoment` accounting — DECISION: restate-to-purity

(Basic L1728.)  Its *conclusion* is about the project def `convolveFunctionMeasure`
(L1740), so it cannot be a clean upstream citation as-is (correctly NOT in the deferred
nine).  But its content is a **composition**: deferred-OT kernel (narrow + moment ⇒
`W₁(μ t, μ t₀) → 0`, Villani Ch. 6) **+** the already-PROVEN
`MathlibTODO_convolveLipschitzEstimate` (‖conv ρ x − conv σ x‖ ≤ L·W₁).  **Resolution
(M2 match-statement-to-math):** extract a pure narrow→W₁ placeholder
(`MathlibTODO_*` concluding e.g. `ContinuousAt (fun t => (wasserstein1 (μ t)(μ t₀)).toReal)
t₀` — pure measures/W₁, no `convolveFunctionMeasure`), then close
`convolveContinuousAtOfNarrowMoment` INTERNALLY by composing it with the proven Lipschitz
estimate (W₁→0 ⇒ ‖conv diff‖ → 0 ⇒ ContinuousAt).  Signature unchanged ⇒ consumer
`glue_step` case (a) `h_cont_g` undisturbed.  Net: sorry moves convolve → pure-OT leaf
(honest prefix); convolve becomes sorry-free-by-composition.  ~40-line body (ContinuousAt-
via-bound squeeze) — its own focused unit.

**Next-step menu (sweep gate now PASSED):**
1. `picardCharFlow_aemeasurable` (L6878) — highest leverage: its closure retires the single
   transitive sorry the whole existence side carries through #11 conjunct 7.  But hard part
   is deferred FA (`MathlibTODO_lipschitzFlowAEMeasurable`) → close-modulo-deferred-FA.
2. `convolveContinuousAtOfNarrowMoment` restate-to-purity (decided above) — additive,
   low-risk, sig-stable.
3. `glue_step` (L8450) / `universal_existence` (L10242) — continuation assembly, own
   sorries, now on a swept/sound foundation.

#### ✅ `picardCharFlow_aemeasurable` CLOSED GENUINELY (not modulo-FA) — sorry 13 → 11 (2026-06-02)

Opened the leaf on the **decomposition-verification read** (per discipline: verify the
documented decomposition *holds* before writing glue, because the campaign's signature
failure is plan-vs-realized divergence at the seam).  The read found the seam:

* The deferred FA leaf `MathlibTODO_lipschitzFlowAEMeasurable` demanded **global-in-`t`**
  HasDerivAt (`∀ z t : ℝ`) to prove a **global-in-`s`** conclusion.  The Vlasov flow has
  derivative control only on `Ioo 0 T` (off-window = uncontrolled `Classical.choose`), so
  the leaf's hypothesis was **unsuppliable** — the documented "compose with the FA leaf"
  plan does NOT hold.
* `picardCharFlow_aemeasurable`'s `∀ s` (global) conclusion was **over-strong**: its sole
  consumer (#11 conjunct 7, L7806) applies it only at `clampToIcc T s ∈ Icc 0 T`.  The
  global claim — the very thing that *looked* like it needed deferred FA — was an M3
  over-strength artifact.

**Resolution (genuine close, no deferred FA):** weaken the conclusion to `∀ s ∈ Icc 0 T`
(all the consumer uses), then close the body via the *already-proven*
`charFlow_measurable_via_gronwall` (genuine `Measurable` of the joint pair on `Icc`, from
the boundary bundle through `Stage_1_9_flow_boundary_regularity`).  Added `h_int` + `hbdry`
hyps (call site supplies `h_int_ρ_lim` + `h_boundary_ρlim`); consumer survives via
`clampToIcc_mem`.  **`MathlibTODO_lipschitzFlowAEMeasurable` had no other consumer →
removed as orphaned.**  Net: 13 → 11 (two sorries retired — one genuine close + one dead
deferred placeholder that was never a real obligation).

**Sweep-characterization revision (honest calibration):** the prior sweep report called
this node "internal-glue-modulo-deferred-FA" and the existence side's single transitive
sorry.  Verifying it (opening the leaf) showed that was *optimistic that deferred-FA was
needed* and *pessimistic about closeability* — it closes genuinely.  The existence side
now carries **no** transitive sorry through #11; it bottoms out only through `glue_step`
(L8426) + `universal_existence` (L10218).  This is the read-the-seam-before-the-glue
discipline producing a strictly better outcome than the plan promised — and the M3 pattern
(over-strong statement reaches for heavy machinery; right-sized statement closes with
proven tools) firing a *fourth* time.

**Clamp-totality precision (confirmed):** the windowing has no off-by-one.
`clampToIcc_mem {T} (hT : 0 ≤ T) (t : ℝ)` (L4358) requires only `0 ≤ T` and holds for
*every* real `t`, so the consumer's `intro s` (arbitrary real `s`) → windowed lemma at
`clampToIcc T s` with `clampToIcc_mem hT.le s` reconstructs #11's global `∀ s` conjunct-7
over the *clamped* flow.  Conjunct-7 IS the consumer's need (a conclusion conjunct, not a
hidden intermediate), so green on it certifies the reconstruction, not just that it
typechecks.

**State now: 11 sorries.** Internal/active: `glue_step`, `universal_existence`,
`convolveContinuousAtOfNarrowMoment` (restate-to-purity decided).  Deferred OT: the rest.

#### ⚠️ META-LESSON: the (c) sweep certifies STRUCTURE, not CONTENT (2026-06-02)

The picardCharFlow finding is bigger than M3.  The (c) sweep — which reads docstrings +
call-graph *shapes* — was **content-wrong about this node in BOTH directions at once**: it
asserted a dependency that didn't exist (the FA leaf was unsuppliable, never actually
invoked) AND missed that the node was genuinely closeable with proven tools.  Had the sweep
been trusted, "the existence side is proved-modulo one deferred-FA node" would have been
carried forward as a *true* statement — and it was false (the node was closeable; the
"deferred FA" pointed at a placeholder with zero real consumers).  It was caught only
because the docstring-derived certification was flagged "characterized-not-verified" and
the leaf was opened *before* building on it.

**Carried recalibration:** a (c) sweep certification is itself "characterized-not-verified"
wherever it rests on a node's *documented plan* (docstring / comment) rather than its
*realized proof*.  Structure-level green (types compose, call graph maps) does NOT certify
content-level claims like "closure plan: compose with deferred X".  So the remaining
internal nodes the sweep characterized as "continuation assembly, own sorries, sound base"
— `glue_step` (L8426), `universal_existence` (L10218) — are uncertified at the content
level.  **Each gets the same decomposition-verification read this node got** before the
descent trusts it: open the leaf, check whether its sorry is what the docstring says, and
expect (after this turn) at least one to surprise — either over-strong-and-cheaper (the
favorable M3 outcome here) or a documented-plan-with-a-seam.  Do NOT inherit "sound base"
on the sweep's word.

**Promotion candidate (P-series / discipline framework) — STATE THE BOUNDARY:** the
lesson is NOT "sweeps are worthless" (this sweep's *structural* map was right and load-
bearing — it correctly pinned picardCharFlow as THE node and that the rest bottom out only
through the two continuation nodes).  The precise boundary: **a (c) sweep's STRUCTURAL
claims (who consumes what, where sorries bottom out) are verified by the call-graph read
and are trustworthy; its CONTENT claims (what a node's closure requires) are only as good
as the docstring they're read from, hence characterized-not-verified.**  Call-graph-
certifies-structure vs leaf-read-certifies-content.  Conflating the two would make you
distrust the sound structural map.  This is the sweep-specific refinement of P10 (build-
permits-vs-audit-certifies); promote with the boundary, the way M3 was promoted with its
boundary (the boundary is the load-bearing half).  Sighting #1 = picardCharFlow.

**Committed:** `ab32da3` (picardCharFlow genuine close + orphan removal; 13→11).

#### Decomposition-verification read: `universal_existence` (outer node) — 2026-06-02

Read the OUTER continuation node first (it consumes `_forward` → `glue_step`; its spec is
what `glue_step` gets verified against, so reading the inner first risks the wasted-
verification trap).  Call graph: marquee (L10479) → `universal_existence` (L10218) →
`_forward` (L9411, `Nat.rec` tower) → `glue_step` (L8426).  Findings:

* **Seam #1 (t-domain / over-strength): ABSENT.** The marquee's conclusion (L10500–10515)
  is `universal_existence`'s conclusion *verbatim*, and the marquee's proof is `exact
  vlasovWellPosedness_universal_existence …` (L10528).  The forward-only
  `∀ T_target > 0 → IsLagrangianVlasovSolutionOn gradW f T_target` single-`f` shape was
  already M2-refactored (2026-05-30) to be minimal-for-marquee.  No over-strength layer;
  **`glue_step`'s spec is stable, won't shrink** (unlike the picardCharFlow case).  The
  docstring's step-4 "backward iteration (sorry)" is STALE (realized conclusion is
  forward-only).
* **Seam #2 (inter-window compounding): DISCHARGED, not hidden.** Compounding lives in
  `_forward`'s `Nat.rec` tower, which is **sorry-free in its own body** — the per-window-
  constant control is proven (via `L<1` + the `T_0` selection), not folded into
  "continuation assembly."  `universal_existence` itself only colimits (`sol n := Stage-5
  solution on [0,n+1]`) + agrees (via `vlasovWellPosedness_uniqueness`, which is PROVEN —
  not in the sorry list).
* **Actual content of `universal_existence`'s TWO own sorries — the recursive B2
  boundary-regularity-at-`t=0` pattern** (NOT what the docstring strategy emphasizes; this
  is the docstring-vs-realized seam):
  - L10359: `refine ⟨?_, sorry⟩` — the `IsLagrangianVlasovSolutionOn` **boundary
    `ContinuousOn`** conjunct (the AEMeasurable half `?_` IS proven via `h_aemeas_N`).
  - L10390: `rw [← h_eq]; sorry` — narrow **right-continuity at `t = 0`**; the inline
    comment (L10383–10389) says it needs "boundary ODE regularity at t = 0 beyond what
    `IsCharacteristicFlowOn` exposes."
  Both are the documented B2 sighting "Stage 6 narrow continuity at t=0" (commit `20500ee`
  lineage).  **Favorable angle:** #11's now-closed boundary bundle `h_boundary_ρlim`
  (HasDerivWithinAt on `Icc 0 T`, which INCLUDES `t=0`) already constructs the raw t=0
  regularity — it wasn't fully available before #11 closed.  Closing both is a recursive B2
  *enrichment* (additive, known pattern, NOT new math): thread the boundary bundle up
  through `_forward`/`glue_step`/the `IsLagrangianVlasovSolutionOn` predicate.
* **Orphan-check: none** (sorries are inline boundary gaps, not a call to a zero-consumer
  placeholder — no picardCharFlow-style double-retire bonus here).

**Sequencing consequence (re-validates "read outer first"):** the B2 enrichment is a
*cross-cutting* surgery DESIGNED from `universal_existence`'s t=0 need, threaded DOWN — it
will change what `glue_step` must expose (add a boundary conjunct).  So `glue_step`'s spec
is about to gain a boundary-at-endpoint requirement.  Reading `glue_step` in isolation
first would have verified it against the pre-enrichment spec.  **Next unit:** design the
recursive B2 boundary-bundle threading top-down (universal_existence need → predicate →
`_forward` → `glue_step`), per the B2 watch-list surgery shape (additive; retires multiple
boundary sub-sorries in one swing).  NOT new mathematics; NOT a deferred-OT leaf.

#### B2 boundary-thread MAP (verified end-to-end) — 2026-06-02

Mapped the full thread before any wide edit (the `#13`-shaped cross-cutting surgery
discipline).  **Self-correction worth recording (meta-lesson, 3rd sighting — on my OWN
map):** mid-read I claimed "glue_step has exactly one sorry (L8850), so its boundary
conjunct is already proven, so the close is localized to universal_existence."  That was a
STRUCTURAL claim from an incomplete grep (`^\s*sorry` misses inline `refine ⟨?_, sorry⟩`).
Reading to the leaf (L9092–9095) refuted it: glue_step's boundary `ContinuousOn` conjunct
IS sorry'd inline at **L9095**.  Exactly the call-graph-certifies-structure /
leaf-read-certifies-content boundary — and this time the wrong structural claim was *mine*,
caught by the leaf-read before it propagated into the surgery scope.  Complete sorry-token
inventory (inline+standalone) is mandatory before sizing a cross-cutting surgery.

**The predicate `IsLagrangianVlasovSolutionOn` (L866)** already carries (since the
2026-06-01 B2 enrichment) the conjunct `∀ z, ContinuousOn (fun s => (charX s z, charV s z))
(Icc 0 T)` — interval-wide, closed window.  B3 shape DECIDED = `ContinuousOn` (weakest-
sufficient; comment L877–884).  The cross-cutting groundwork (predicate has the conjunct;
producers structured to supply it) is done; the remaining work is discharging the sorry'd
instances.

**The thread (cross-cutting glue_step + universal_existence; preservation-across-seams
case — bounded):**
1. **glue_step L9095** (boundary `ContinuousOn` for glued flow on `Icc 0 (T+T_0)`):
   closes from glue_step's **PROVEN conjunct (vii)** (L9149 — the boundary `HasDerivWithinAt`
   bundle on `Icc 0 (T+T_0)`, including the across-seam `t=T` `HasDerivWithinAt.union`
   case).  `HasDerivWithinAt → ContinuousWithinAt → ContinuousOn` (prodMk).  ~15–25 lines,
   or fewer if (vii)'s construction is hoisted into a shared `have` consumed by both (vii)
   and L9095.  The hard across-seam continuity is ALREADY in (vii); L9095 is its weaker
   projection.
2. **universal_existence L10359** (boundary `ContinuousOn` on `Icc 0 T_target`): genuine
   once #1 lands.  STOP discarding `sol N`'s 7th component (the `_` at L10321 — bind it
   `h_boundary_N`), then `ContinuousOn.mono` from `Icc 0 (N+1)` to `Icc 0 T_target` (same
   flow `charX_N/charV_N`, subset interval).  ~5 lines.
3. **universal_existence L10390** (narrow right-continuity at `t=0`): DCT-at-0 from the
   now-genuine boundary `ContinuousOn` at 0 (it includes the endpoint), mirroring the
   interior `t₀>0` case (L10410+ pushforward `∫ g ∂f t = ∫ g(charX_N t z,…) ∂f₀` + DCT
   with `g` bounded by `C`), anchored at 0 via `ContinuousWithinAt` from `h_boundary_N`.
   ~30–50 lines.

**Producer-capacity (B3 weakest-producer check — all pass):** glue_step supplies via its
stronger proven (vii); `vlasovWellPosedness_local`/#11 supply `hg_boundary` (genuine
post-#11 close); `_forward` is sorry-free and propagates.  Weakest = glue_step L9095, which
can supply `ContinuousOn` from (vii).  No conjunct flip-down (unlike `#13`'s Stage-C
near-miss).

**Separate substantial sorry (NOT the B2 thread):** glue_step **L8850** — weak-PDE
derivative-continuity at the glue seam (`h_cont_g`; `ContinuousAt` of the derivative-
function at `T`), ~150–250 line DCT via `MathlibTODO_convolveLipschitzEstimate` (proven) +
narrow continuity of `spatialMarginal(f_next)` at `T`.  Independent; the genuinely hard
continuation obligation.

**Execution order (next unit):** #1 (glue_step L9095, unblocks the propagation) → #2
(univ_exist L10359, trivial once #1) → #3 (univ_exist L10390, DCT-at-0).  Build between.
Then glue_step L8850 as its own focused unit.  Sorry trajectory if the thread lands:
11 → 9 (glue_step boundary + the two univ_exist boundary/continuity; note glue_step keeps
its L8850 warning, so its declaration warning persists until L8850 also closes — declaration
count 11 → 10 when univ_exist's two close, glue_step stays warned for L8850).

#### ✅ B2 #1 DONE — glue_step boundary ContinuousOn closed via lemma extraction (2026-06-02)

Decision: named-lemma extraction (NOT inline duplication, NOT intra-proof hoist).  Executed
(delegated mechanical relocation, then independently verified to the leaf).  Three gates run
first: (0) sorry inventory reconciled; (1) **(vii) is metric-independent → extraction is
factoring/single-source, NOT W̄-insurance** — W̄ surface is the `wasserstein1`-carrying
estimates, not this flow-ODE bundle; (2) circularity clean (`h_prev_boundary` is
`HasDerivWithinAt`, `ContinuousOn` is a projection, never threaded).

* New `private lemma glue_step_boundary_bundle` (L8395, before glue_step): takes
  `charX_next/charV_next/f_next` abstract + defining-eq hyps (`hdef_X/V/f`) + `h_prev_boundary`
  + `hg_boundary` + `hg_init` + `hg_init_cond`; concludes (vii)'s `HasDerivWithinAt` bundle on
  `Icc 0 (T+T_0)` (incl. the across-seam `t=T` `.union`).  Fully proven, no sorry.
* Conjunct (vii) (L9421) rewired to one `exact glue_step_boundary_bundle … rfl rfl rfl …`.
* L9095 boundary sorry closed as the `.continuousWithinAt.prodMk` projection of the bundle.
* Verified faithful: lemma conclusion = (vii)'s exactly (not weakened); PDE leaf `h_cont_g`
  (now L9112, formerly L8850) + universal_existence sorries (L10404/L10435) untouched.
* Build green; **code tokens 13 → 12**; **declaration count steady at 11** (glue_step keeps
  its PDE-leaf warning).  Committed separable.

**Next:** #2 = univ_exist L10404 (un-discard `sol N`'s now-genuine boundary conjunct +
`ContinuousOn.mono`).  Read to the leaf before trusting the ~5-line estimate (standing
expectation: continuation layer carries more than its flat size); confirm `sol N` genuinely
supplies the boundary conjunct now that #1 made glue_step's real.  Build between #2 and #3.
