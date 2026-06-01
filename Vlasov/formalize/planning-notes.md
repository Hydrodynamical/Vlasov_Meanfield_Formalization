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
