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
