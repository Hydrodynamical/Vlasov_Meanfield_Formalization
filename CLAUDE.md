# Project memory — Vlasov formalization

Lessons that should persist across sessions. Brief, terse,
keyed to the failure mode they prevent.

## Series structure

Lessons are categorized into four series, each with a distinct
scope and a distinct trigger for "this rule applies":

* **L-series — Lean tool / agent-tool lessons**: idioms, elaborator
  quirks, parser quirks, sorry-prover spec engineering.  Apply at
  the Lean syntax/elaboration level or the agent-design level.
  When to consult: writing or debugging a Lean proof, or editing
  a sorry-prover / sorry-decomposer spec.
* **P-series — Process discipline**: when to ask, when to commit,
  when to delegate, when to pivot.  Apply at the per-turn-discipline
  level.  When to consult: at the start of a session and when a
  tactical plan starts surfacing repeated friction.
* **M-series — Mathematical structure**: principles about which
  mathematical structures to work in.  Apply at the proof-strategy
  level.  When to consult: when designing the shape of a proof
  before writing it.
* **B-series — Bridging architecture / structural-fix patterns**:
  when to introduce new infrastructure rather than patch existing
  seams.  Apply at the architecture-decision level.  When to
  consult: when frictions accumulate in succession across several
  attempted bridges.

The four series exist because the lessons genuinely operate at
different levels — they have different generalization paths,
different signals-to-act-on, and different audiences in the
agent's head when it applies them.  Empirically: post-Stage-4 the
project has lessons earned in all four categories, and grouping
them by series makes it easier to consult the right one at the
right moment.

## L-series — Lean tool / agent-tool lessons

### L1. Iteration-loop spec edits are easily ignored

**Failure mode**: adding a behavioural constraint as a sub-bullet
inside a workflow stage (e.g. `§4.1 step (a′)` in sorry-prover.md)
is unreliable. The model reads the spec, treats the constraint as
aspirational, and proceeds with its default instincts.

**Empirical confirmation**: the 2026-05-26 re-prove of
`wasserstein1_lt_top_of_finite_moment`. The §4.1 (a′)
"grep-validate before citing" step was in the spec; the prover
wrote `NNReal.eq_zero_or_pos` without grepping; build failed with
`Unknown constant`; safety net reverted the entire attempt.

**Fix**: constraints that should gate every edit (not just suggest
good behaviour) must live in the **Hard rules** block at the end
of the spec, alongside "never weaken the statement" and "never
finalise with a new sorry anywhere". The model treats Hard rules
as forcing because they're listed as constraints with explicit
violation consequences. Things tucked into workflow stages get
treated as polite suggestions, not gates.

**Generalisation**: when designing an agent spec, ask of each new
constraint — is this a STAGE in the workflow (do this here), or
a CONSTRAINT across all stages (don't ever do that)? The former
goes in the numbered sections; the latter goes in Hard rules.
Crossing the boundary breaks enforcement.

### L2. Spec edits need empirical validation

**Lesson**: don't assume "spec text == behaviour". After every
non-trivial spec edit on an agent, **observe a run** and look for
the behavior change you intended. The first cut of L1's fix
(in-loop step (a′)) read sensibly but didn't change behaviour;
the second cut (hoisted to Hard rules) changed behaviour
dramatically. Without the empirical run we would have shipped
the first cut and silently lost the enforcement.

**The cheap-and-fast observable**: look at the tool-call mix in
the agent log, NOT just whether the goal was achieved. Specifically:
- For the GREP BEFORE YOU CITE rule, the diagnostic is the
  **grep:edit ratio**. Before: ~3:1 (mostly post-error). After
  hoisting: ~15:1 (mostly pre-citation). The order of greps and
  edits in the log gives the same signal qualitatively.
- For other rules, find an analogous tool-call signature that
  betrays whether the rule fired.

**Workflow**: edit spec → revert the target sorry → run prover →
read the log's tool-call sequence → compare against expected
pattern → commit only if the pattern matches.

### L3. The Hard rules block is where forcing behaviour lives

**Empirical positioning evidence** (2026-05-26 two-run experiment):
- Run 1: rule placed in §4.1 sub-bullet — IGNORED.
- Run 2: same rule hoisted to Hard rules block — ENFORCED.

The placement is the discriminator, not the wording or the
emphasis ("mandatory" / "HARD RULE" labels). The Hard rules block
sits at the *end* of the spec, immediately before "End-of-run
report", and reads like the constitutional constraints of the
agent. Things listed there are treated as gates on every action;
things listed in workflow stages are treated as procedures for
that stage.

**Implication for spec maintenance**: when reviewing a spec for
clarity, look at the Hard rules block first — it tells you what
the agent will reliably do. The rest is procedural detail the
model may or may not internalise.

### L4. Enforcing pre-edit work makes wall-clock the new bottleneck

When the spec successfully enforces "grep before write", the
prover spends more wall-clock per edit. Run 2's prover used 4
edits + 6 builds + 60 greps in ~360s; it ran out of budget
before completing a long proof. Wall-clock is now the constraint,
not name-churn.

**Tuning options when this becomes the bottleneck**:
- Longer per-target timeout in `formalize.sh delegate()`
  (currently 900s for prover; default for `delegate` is 600s).
- Pre-supplied `proof_sketch` in the plan JSON — sketch fast
  path (§4.−1) skips much of the discovery work.
- Smaller helper lemmas via decomposer — each helper has its
  own shorter proof, finishes within budget.

The wall-clock bottleneck is a strictly better problem than the
name-churn-reverts-everything bottleneck — it represents the
prover making careful progress, just not finishing in time.

**But**: doubling the timeout (900s → 1800s) on `convolveLipschitz_inner_bound`
did NOT lead to closure (2026-05-26 third run). The prover hit
the §4 ITERATION cap (8 edits + 8 builds) before running out of
seconds. So the relevant bottleneck shifts as you tune: once
wall-clock is no longer the gate, the next ceiling is the
iteration cap. Pushing past it requires either (a) raising the
cap, (b) smaller helpers via decomposer, or (c) hand-proof.

### L6. Rate-limit exhaustion → silent CLI hang → empty logs

**Failure mode**: under five-hour rate limit exhaustion (or auth
issues), the `claude` CLI hangs silently producing 0 bytes of
stream-json output. The perl-alarm SIGALRM eventually fires
(good — agent is killed cleanly), but ~50 min of wall-clock is
wasted while we wait for the alarm.

**Empirical confirmation**: 2026-05-26 W1ContOn cycle 6. Three
consecutive agents (pre-verify + prover + post-verify) each
produced 0-byte logs and ran their full SIGALRM budgets
(600s + 1800s + 600s = 50 min total). All three silent. The
previous cycle's prover log had logged a `[rate-limit]` event
indicating the five-hour window was already pressured.

**Fix**: `formalize.sh delegate()` now spawns a silent-failure
watchdog that checks the `.jsonl` log size after 120s. If the log
is 0 bytes, the watchdog pkills the agent process. Bounds the
worst-case wall-clock cost of a silent failure at ~2 min per call
instead of the full SIGALRM budget.

**Generalisation**: SIGALRM is a *backstop* — it catches runaway
work eventually but doesn't distinguish "agent hung at startup"
from "agent making slow progress." Output-flow observation is
the better fast-signal: if a stream-json pipeline produces 0
bytes for N seconds, the agent is definitely not making
progress. Worth applying this watchdog pattern to any
long-running stream-buffering CLI.

### L5. The hard rule must specify the grep TARGET, not just the verb

**Failure mode**: even with "GREP BEFORE YOU CITE" hoisted to
Hard rules, the prover sometimes greps the LOCAL Lean file for a
name instead of the Mathlib install. The local grep finds the
prover's own bad references (it just wrote `apply wasserstein1_comm`
and now greps for `wasserstein1_comm` in the same file), returns
"yes I have it!", and the prover proceeds. Vacuous validation.

**Empirical confirmation**: the 2026-05-26 third run on
`convolveLipschitz_inner_bound`. The prover hallucinated
`wasserstein1_comm` (not in Mathlib; not in our project), wrote
`apply wasserstein1_comm`, then ran
`grep -rn 'wasserstein1_comm\b' /…/Basic.lean` and found its own
prior writes. The hard rule was satisfied syntactically (a grep
was done before the next edit), but the SEMANTICS — "confirm
the name exists in the upstream library" — was violated.

**Fix needed in the spec**: the hard rule's grep example must
include the explicit Mathlib install path
(`.lake/packages/mathlib/Mathlib/`) and reject local-only
greps. Suggested wording: "the grep MUST target a path
matching `.lake/packages/mathlib/Mathlib/…`; greppping the
project's own Lean file does not count."

**Generalisation**: precision in the example matters as much
as the prose. Models follow the example shape more than the
prose mandate. If the example shows
`grep -rn '…' .lake/packages/mathlib/…`, the model uses that
target. If the example is loose, the model uses whatever
target seems convenient — including the same file it's editing.

### L7. Inline `?_` placeholders inside chained Mathlib-API calls are fragile

**Failure mode**: when a proof writes `Foo.mono' ((bar_const x).add ?_)`,
Lean's elaborator is asked to synthesize the `?_`'s type by reasoning
*backward* through `Foo.mono'`'s expected first argument's shape, which
in turn depends on `bar_const x .add ?_`'s output type. With two or more
implicit arguments threading through nested API calls, the elaborator
gives up and reports "don't know how to synthesize implicit argument."

**Empirical confirmation**: 2026-05-29 Stage 2b W₁-bound-by-integral
proof attempt. The dominator construction inside `Integrable.mono'
((integrable_const |φ 0|).add ?_) hφ_meas_phys (Filter.Eventually.of_forall fun y => ?_)`
produced 5 errors of "don't know how to synthesize implicit argument
`g`" / "`p`", each at the inline `?_` site. The proof's algebra was
correct; the issue was purely elaboration. Reverted the ~85-line attempt.

**Fix**: build intermediate facts via named `have` statements *before*
passing to chained API calls. Replace
`Integrable.mono' ((bar_const x).add ?_)` with
`have h_dom : Integrable (fun y => |φ 0| + ‖y‖) ν := (integrable_const _).add h_norm_int` and
then `refine Integrable.mono' h_dom hφ_meas (...)`. Each `have` gives
Lean a fully-typed term to work with.

**Generalisation**: any construct asking Lean to synthesize more than
one implicit argument backward through nested API calls is a candidate
for explicit-intermediate refactoring. The rule of thumb: when a proof
has ≥2 threads of Bochner-integrability or AEStronglyMeasurable
synthesis, name them. Particularly for the
`Integrable.mono' / Integrable.add / integrable_const`-family inside
Bochner-integral proofs.

### L8. Iff-direction / equality-direction matters at API call sites (broadened framing)

**Failure mode**: Mathlib API often presents results as iff-statements
or as equalities with a "natural" direction.  When consuming the API,
the direction the caller needs may not match the direction the lemma
exposes.  Specific manifestations:

* `_map_measure` family (original L8): `integral_map`,
  `integrable_map_measure`, `lintegral_map` produce conclusions in
  the form `Integrable (g ∘ f) μ`, while project hypotheses are
  typically `Integrable (fun z => g (f z)) μ`.  Bridge via `.mp` /
  `.mpr` projections or `show ... from`, NOT `rw`.
* `ContinuousWithinAt.congr` (sighting at Phi_step): wants `g y = f y`
  for the NEW function `g` and the original `f`, not the natural-
  reading direction `f y = g y`.  Misreading the signature direction
  produces "type mismatch" at the .congr call.
* `lt_top_iff_ne_top` (sighting at Stage 4 Cauchy): a function expects
  `ε ≠ ⊤` directly; passing `lt_top_iff_ne_top.mpr hε_top` is one
  layer of wrapping off.

**Empirical confirmation** (three sightings across Stage 2b, Stage 4
Cauchy, Phi_step): the underlying issue is the same — the lemma's
exposed equality/iff is in one direction; the consumer assumes the
other.  Lean's elaborator rejects with "type mismatch" or "did not
find pattern" depending on whether the consumer used `rw` or `exact`.

**Fix**: at the call site, read the lemma's actual signature (don't
infer it from the name or the intuitive direction).  Then either:
1. Apply the iff-projection (`.mp` or `.mpr`) matching the direction
   the lemma actually exposes.
2. Use `show ... from ...` or `convert` to bridge the syntactic
   forms when the directions are inverted.
3. Match the lemma's argument order: e.g., `.congr h_eq` where
   `h_eq` is in the direction `lemma` consumes, not the direction
   the caller assumes.

**Generalisation**: when consuming Mathlib's API, the direction of
iff/equation matters as much as the predicate itself.  The pattern
recurs across `_map_measure` family, `.congr` family,
`lt_top_iff_ne_top` family, and likely many more.  Read the
signature; don't infer from the name.

### L9. Lean's elaborator treats syntactically-distinct-but-definitionally-equal forms as not-immediately-unifiable

**Failure mode**: forms that are *definitionally* equal (β-reducible,
unfoldable, or related by simple identities) are nonetheless treated
by Lean's elaborator as *not unifiable* at API call sites or in binder
positions.  The elaborator gives up without unfolding the definitions
to check equality.

**Empirical confirmation** (five sightings across Stages 1.8–4):

1. `simp only` non-β-reduction (Stage 1.8): `simp only [h]` doesn't
   automatically β-reduce after the rewrite; the result needs a
   subsequent `simp only []` or explicit unfolding to make further
   tactics work.
2. `|>.toReal` pipeline parsing (Stage 2b): `(wasserstein1 μ ν |>.toReal)`
   parses differently than `(wasserstein1 μ ν).toReal` in some
   tactic contexts; the pipeline form is treated as not-yet-applied.
3. `ℝ≥0∞` notation in binder lists (Stage 4 iterated triangle): using
   `ℝ≥0∞` in a `∀` binder works inline but fails when the binder is
   spread across multiple lines; the parser splits on the Unicode
   notation.
4. `∞` Unicode in binder pattern (Stage 4 bundling): `ρ_∞ : ...` as a
   binder fails the parser with "unexpected token `∞`; expected `,`
   or `binderPred`"; rename to ASCII (e.g., `ρ_lim`) to dodge.
5. `ContinuousWithinAt.congr` direction (Phi_step): the lemma's
   signature expects `g y = f y`, but the elaborator doesn't unfold
   the lambda to check directional equivalence; mismatch surfaces as
   "type mismatch."

**Fix**: prefer maximally-explicit forms over clever-but-tight ones.
Specifically:
1. Avoid `|>.field` in tactic contexts; use `(expr).field` or
   `have x := expr; x.field`.
2. For ENNReal-typed binders, use full `ℝ≥0∞` and keep on one line,
   or use the ASCII alternative `ENNReal`.
3. Avoid Unicode in binder names; ASCII names (e.g., `ρ_lim` over
   `ρ_∞`) sidestep parser quirks.
4. Read the lemma's exact signature (L8) and write the call site to
   match, rather than relying on the elaborator to unfold.

**Generalisation**: when a proof fails with "type mismatch" or
"unexpected token" at a position where the math is clearly right, the
first hypothesis to consider is "Lean's parser/elaborator sees a
distinction the math doesn't."  Look for: lambdas vs point-free,
ASCII vs Unicode, pipeline-applied vs directly-applied, iff-direction.

### L10. `ring` requires `CommRing`; additive-group goals are `abel` territory

**Failure mode**: writing `by ring` on a goal that's purely additive
(no multiplication of variables) — typically a difference simplification
like `-a - (-b) = b - a` or `(a + b) - (a + c) = b - c` — fails with
`ring made no progress` when the underlying type is an `AddCommGroup`
but not a `CommRing`.  The failure is opaque: the goal looks like
"obviously ring", but `ring` rejects because the type has no
multiplication structure.

**Empirical confirmation** (Phase 4 Stage 2b part 2, 2026-05-31, item 6
close): the difference of two Vlasov phase-space vector fields
`b_f t x - b_g t x = (0, -conv_f x.1 - (-conv_g x.1))` needs the
intermediate simplification
`-conv_f x.1 - (-conv_g x.1) = conv_g x.1 - conv_f x.1` on
`PhysSpace d = EuclideanSpace ℝ (Fin d)`.  `EuclideanSpace ℝ (Fin d)`
is `AddCommGroup` (under pointwise + and -) but **not** `CommRing`
(no pointwise multiplication is defined; the Euclidean structure is
inner-product not ring).  `by ring` fails; `by abel` closes.

**Fix**: when the goal is purely additive and the type is a vector
space / inner-product space / additive-group-not-ring, use `abel`
(or `abel_nf`).  Reserve `ring` for `CommRing` types (`ℝ`, `ℂ`, `ℝ≥0`,
`ENNReal`-where-defined, polynomial rings, etc.).

**Generalisation — this is structural, not a quirk**: phase-space
differences are *always* `AddCommGroup`-not-ring by construction.
Velocity-position vectors live in inner-product spaces or product
spaces of them; no multiplication is defined.  Every future
manipulation of `b_f - b_g`-style expressions, of flow-trajectory
differences, of joint-phase-space vector arithmetic, will hit this
same wall if started with `ring`.

**Operational rule**: at the moment you write `by ring` on a goal
involving phase-space / vector-space / inner-product-space elements,
spend the half-second to mentally type-check: "is this type a
`CommRing`?"  If not (and it usually isn't for vector-valued goals),
go directly to `abel`.  Avoids the build-fail-then-fix loop.

**Promoted at one sighting** (the standard threshold is 2-3) because
generality is *certain* not uncertain — the structural fact about the
domain (vector-valued differences are `AddCommGroup`-not-ring) holds
for every analogous future proof.  The watch-list exists for patterns
whose generality is unclear; this one's generality is locked in by
the math.

## P-series — Process discipline

### P1. Atom-level signature reading before drafting helper signatures

**Failure mode**: when planning a multi-step composition, the
natural approach is to draft helper signatures based on the
expected shape of the composition.  But the shape is wrong when
upstream API doesn't actually produce what the planning assumed.
The result: helper signatures drafted against an imagined API,
then 100-300 lines of code that doesn't compose against the
actual API.

**Empirical confirmation** (four sightings across Stages 1.7–4):

1. Stage 1.7 (`exists_vlasov_characteristicFlow_global_on_ball`):
   the original plan called for ~120 lines of cover-and-stitch
   construction.  Atom-level signature reading revealed that the
   per-ball flow is already parametric in both `(z₀, a)` — the
   "global-on-ball" lift is just a re-parameterisation, not honest
   stitching.  ~30 lines instead of ~120.
2. Stage 1.9 (`exists_vlasov_characteristicFlow_global_smallT`):
   the original plan called the per-ball flow "global-in-z" by
   misreading what it actually produces.  Atom-level reading at
   Stage 2's session opening caught the mismatch, surfaced the
   need for a true global-in-z theorem, and pivoted before
   writing Stage 2's body against the wrong assumption.
3. Stage 2c (`tendsto_integral_filter_of_dominated_convergence`):
   signature reading revealed the exact form of the DCT-with-
   filters that the W₁-continuity argument needed.  Avoided ~80
   lines of manual DCT reconstruction.
4. Stage 4 `picard_iterate_geometric_bound`
   (`geom_sum_Ico_le_of_lt_one`): after a 5-error revert from
   manual partial-sum reconstruction, 20 minutes of targeted
   signature reading at `Mathlib/Algebra/Order/Field/GeomSum.lean`
   found exactly the right lemma.  Collapsed the proof from a
   case-split-and-reconstruct attempt to a clean 4-step chain.

**Fix**: at the start of every session whose work composes ≥3
upstream lemmas, spend 15-30 minutes reading the actual signatures
of those lemmas (not just inferring from names or docstrings),
BEFORE drafting helper signatures.

**Generalisation**: the cheapest insurance against
"planned-against-imagined-API" repeats is to verify the API exists
in the assumed form before writing code against it.  This is the
discipline that makes the "structural-vs-tactical" question of P2
visible at session start rather than mid-implementation.

### P2. Structural-vs-tactical diagnosis when frictions cascade

**Failure mode**: when tactical signature-reading (P1) surfaces
multiple frictions in succession during a single arc, the natural
response is "patch each friction with a bridge."  But the bridges
themselves often hit further frictions, producing a cascade.  At
some point, the bridges-as-tactical-fix approach stops converging
and the right move is structural diagnosis: ask whether the
abstract specification and the constructive proof structure actually
align, and introduce new infrastructure rather than patching seams.

**Empirical confirmation** (two sightings):

1. Stage 2 → Stage 1.9 pivot: signature reading at Stage 2's
   session opening surfaced four frictions in succession (per-z
   global flow not produced by Stage 1.7 / Stage 1.8 measurability
   gap / `flow_distance_growth_bound` requires `IsCharacteristicFlow`
   / `Measure.map` requires AEMeasurable wrt source).  After the
   fourth, the response shifted from "land Bridge #4" to
   "structural diagnosis": the chain was not converging because
   Stage 1.7's output (ball-localized) was fundamentally not what
   Stage 2 needed (global-in-z).  Response: Stage 1.9 pivot, true
   global-in-z flow.
2. Path 3 pivot (Stage 4 Frictions 1–5): five frictions
   accumulated across two sessions (Stage 1.9 universal hypotheses
   vs VlasovMeasureCurve Icc / L<1 constraint / Ioo vs full-ℝ for
   growth bound / Ioo vs full-ℝ for Stage C / Stage 1.9 boundary
   regularity not exposed).  After the fifth, the response
   shifted from "land Bridge #5" to "structural diagnosis": the
   chain wasn't converging because the abstract predicates
   (`IsLagrangianVlasovSolution`) live at universal-in-`t`
   regularity but local existence operates on a finite window.
   Response: Path 3 `_On`-predicate family.

**Fix**: when ≥3 frictions surface in a single arc and each
friction's resolution surfaces another friction (the cascade
signature), pause and ask: "is the underlying problem
structural?"  If yes, the right move is new infrastructure (new
predicates, new abstractions) at the type level, not more
bridges.

**Generalisation**: P1 (signature reading) catches frictions at
the atom level; P2 catches the pattern that *multiple atom-level
frictions in close succession indicate a structural rather than
tactical problem*.  The combination of P1 + P2 makes structural
issues visible early — before 200+ lines of bridges have been
written and need to be reverted.

### P3. Diagnostic work in one session loads context for targeted execution in the next

**Failure mode**: when a session attempts substantive surgery at
the tail end of its budget without prior diagnostic work having
been committed in a previous session, the surgery typically
converts to documentation rather than landing — the session
spends its remaining budget discovering the closure path rather
than executing it.  Repeated across sessions, this produces a
slow-converging "documentation-then-revert" oscillation.  Inverse
failure mode: treating prior-session documentation commits as
"lost productivity" rather than "loaded context."

**Empirical confirmation** (three sightings):

1. Stage 1.7 reparameterization (commit `c00ba3b`): the per-ball
   flow lift came in at ~30 lines instead of the planned ~150
   because prior sessions' signature reading had identified the
   re-parameterization path.  Tail-end execution successful
   because the diagnostic work had been done.
2. Stage 2c DCT close: the
   `tendsto_integral_filter_of_dominated_convergence` invocation
   landed cleanly because preceding sketches identified the exact
   DCT-with-filters form.  Tail-end execution successful because
   the API selection had been pre-loaded.
3. Friction 5 close (commit `4b024ee`, this session): substantive
   surgery landed in tail-end budget because the prior session's
   documentation commit (`aec468b`) had precisely identified the
   surgery path (the per-ball flow's `h_d_within` internal
   construction at L1892-1907, L1916-1922 and the conversion idiom
   `nhdsWithin 0 (Icc 0 T) = nhdsWithin 0 (Ici 0)`), refined by
   this session's `+1` analysis adding strategic weight.

**Contrast — the failure mode**: two preceding sessions attempted
tail-end substantive closes on Friction 5 *without* the diagnostic
documentation in place; both converted to documentation rather
than landing.  Only the third attempt — with the documented
surgery path pre-loaded — succeeded.

**Fix**: when a substantive surgery cannot land in the current
session's remaining budget, commit the diagnostic conclusion as
focused documentation (the precise surgery path, the API atoms
involved, the elaboration idioms required) so the next session
can execute against the loaded context rather than re-discovering.
Conversely: at the start of a session intending substantive
surgery, look for and read prior documentation commits naming
the surgery path before drafting a fresh approach.

**Generalisation**: P1 is "atom-level signature reading within a
session before drafting helpers"; P3 is the cross-session
companion — diagnostic documentation accumulates as
session-spanning loaded context, with the empirical effect that
tail-end execution of documented surgery is achievable in
contrast to tail-end discovery-of-surgery being unreliable.  The
pattern makes the discipline framework's productivity compound
across sessions rather than reset each session.

### P4. API-lock-vs-substantive-proof: separate signature commitment from body discharge in dense composition arcs

**Failure mode**: when a theorem's body requires a substantive
multi-step composition that exceeds a single session's budget, the
natural attempt is to inline the full composition.  This produces
either (a) elaborator fragility (per L7) from threading 20+ hypotheses
in a single goal-state, (b) cascading sub-sorries that proliferate
within the inline body and prevent clean commit-checkpointing, or
(c) the previous-session failure mode where 200+ lines of inline
work get reverted because they fail to compile end-to-end.  Conversely,
deferring the entire theorem (signature included) blocks downstream
consumers from composing.

**Empirical confirmation** (three sightings):

1. Stage C `_On` packaging (commit `de1eb0f`): the localized
   `IsVlasovSolutionOn` predicate was committed with its signature
   locked and the substantive PDE-proof body sorry'd.  The signature
   commit let Stage 4's body draft composition while the PDE proof was
   handled in a separate focused session (`b77290c`).
2. Friction 5 helper (commit `fffde95`): the
   `Stage_1_9_flow_boundary_regularity` theorem was committed with
   signature locked and body sorry'd.  Two subsequent sessions
   attempted tail-end substantive close and converted to documentation;
   the third session (with the precise surgery path documented from
   the prior commits) closed the body substantively (`4b024ee`).
3. `vlasovWellPosedness_local` body (commits `94573e9`, `3623b5c`):
   the marquee local-existence theorem was first committed with
   its 7-step composition plan documented and body sorry'd, then
   structurally closed by decomposition into three named sub-helpers
   (`_picard_fixedPointFlow`, `_finalAssembly_moment`,
   `_finalAssembly_isLagrangian`) each with locked signature and
   sorry'd body.  The body's glue composition (~40 lines) is closed.

**Fix**: in dense composition arcs where a theorem's body requires
≥150 lines of substantive composition, separate the work into two
commits:

* **API-lock commit**: signature + documented proof strategy + sorry'd
  body.  Locks the interface so downstream consumers can compose
  against it.  Typical size: ≤50 lines including extensive docstring.
* **Substantive close commit(s)**: focused session(s) discharging the
  body.  Can be one session or multiple per the body's natural
  decomposition.

The trade-off: temporary sorry-count increase.  But the alternative
(inline-and-revert) costs more in wall-clock and produces nothing
durable.

**Generalisation**: P4 is the cross-session companion to L7+L8
elaboration discipline.  L7+L8 say "write small, explicit intermediate
steps within a proof body"; P4 says "at the theorem level, split
the API specification from the substantive body discharge."  Both
discipline the same underlying issue (elaborator fragility under
high-complexity composition) but at different scales.

**Composition with P3**: P3 says diagnostic work in one session loads
context for next-session execution.  P4 makes this discipline
operationally concrete: the diagnostic work IS the API-lock commit,
the targeted execution IS the substantive close commit.  Together
the two patterns produce the project's empirical productivity
compounding across sessions — P3 (the cognitive pattern) +
P4 (the commit-level pattern) = reliable session-bounded progress.

### P5. Discipline framework's own pattern-extrapolation needs atom-level verification

**Failure mode**: when the discipline framework's pattern-recognition
machinery (P-series, B-series, watch-list candidates) produces a
strategic recommendation that extrapolates from prior sightings to a
new situation, the recommendation is treated as a *conclusion* rather
than as a *hypothesis to verify*.  Pattern-extrapolation is a
reasonable starting hypothesis — established patterns predict likely
architectures — but the framework's own recommendations need the same
atom-level verification (P1) as any other claim.  Treating them as
exempt from verification produces over-scoped surgery plans, misdirected
architectural commitments, and the kind of cascade-discovery friction
that P2 then has to clean up mid-execution.

**Empirical confirmation** (two sightings):

1. **Stage 2 → Stage 1.9 pivot (commit `c00ba3b` arc, earlier session)**:
   the strategic recommendation "Stage C is the project blocker for
   `_glue_step` case (a)" was an extrapolation from the pattern "Stage C
   sorries are the hard substantive work in the project."  Atom-level
   reading discovered that the relevant Stage C `_on` producer
   (`vlasovSolutionViaPushforward_isVlasovSolutionOn` at L3337) is
   actually FULLY PROVED; the only sorry'd Stage C lemma is
   `vlasov_trajectory_lipschitz_bound` (universal, non-`_on`, at L2669)
   which is unrelated to `_glue_step` case (a).  The "Stage C is blocker"
   diagnostic was incorrect; the actual blocker was the B2 predicate-layer
   mismatch.

2. **B2 cascade extrapolation (commit `c25c8b0`, this session)**: the
   strategic recommendation "case (a) needs B2 surgery on
   `IsVlasovSolutionOn` (~400-600 lines, 4-layer cascade)" was an
   extrapolation from B2's three prior sightings.  Atom-level reading
   discovered Mathlib's `hasDerivAt_of_hasDerivAt_of_ne`
   (`Mathlib/Analysis/Calculus/FDeriv/Extend.lean` L177) and its one-sided
   variants `hasDerivWithinAt_{Iic,Ici}_of_tendsto_deriv` (L108, L142)
   provide a localized close path that sidesteps the B2 cascade entirely.
   Scope reduction: 30-50% (B2 surgery ~400-600 lines → localized inline
   DCT ~280-350 lines), plus avoidance of predicate-layer disruption.

**Fix**: when the discipline framework produces a strategic recommendation
(e.g., "this is a B2 cascade", "this is a Stage C blocker", "this is an
M-series statement-correction situation"), apply P1 (atom-level reading)
to verify the recommendation matches what the actual Mathlib + project
infrastructure supports.  The recommendation is the starting hypothesis;
the verification is the determinant.

**Generalisation**: P5 is the *self-referential* application of P1.  P1
says "verify the API exists in the assumed form before writing code
against it."  P5 says "the discipline framework's pattern-extrapolation
recommendations are claims, and like any claim they need verification
before acting on them."  The two patterns compose: P1 catches mismatches
at the implementation level; P5 catches mismatches at the *strategic*
level (which would otherwise produce over-scoped or misdirected
implementations downstream).

**Operational rule**: at the top of any session whose work composes
against a strategic recommendation from prior sessions, spend 15-30
minutes on atom-level reading to *verify* the recommendation's
premise.  The session's first commit can then be either (a) execution
against the verified premise or (b) a discovery commit refining the
recommendation per atom-level findings.  Pattern (b) is high-value —
it produces P3-style loaded context for the *next* session at the cost
of one session's execution work, but the loaded context typically
unblocks 2-3 future sessions of substantive work.

### P6. Brief-driven execution with pre-loaded diagnostics lands cleanly

**Positive pattern** (confirming-pattern companion to the warning
patterns P2 + P3 + P5).  When a session opens with a pre-loaded brief
from prior-session diagnostic work — atom-level identification of
Mathlib infrastructure, characterization of close path, line-count
estimates, identified lemma inventory — execution-mode work lands
cleanly without P2-style scope discoveries or P5-style strategic-
recommendation refinements mid-session.  Tactical deviations
(notation namespace fixes, term-level substitutions, minor
elaboration tweaks) remain expected and tractable; what's *absent*
is architectural surprise.

**Empirical confirmation** (two sightings):

1. **Sighting #1** (session of commits `56f8ddf` + `c25c8b0`,
   2026-05-30): cases (b)/(c) of `_glue_step` closed substantively
   in commit `56f8ddf` against the discovery diagnostic that
   `HasDerivWithinAt.union` was the close pattern (identified in
   prior session's `9be5c42`).  Then the same session pivoted to
   diagnostic mode for the case-(a) close path discovery (commit
   `c25c8b0`).  Execution against the pre-loaded discovery: clean,
   2 minor edits, no scope surprises.

2. **Sighting #2** (session of commits `bd11a2c` + `360813f`,
   2026-05-31): case (a) structural close + helper banking
   (commit `bd11a2c`) + h_cont_f LEFT side substantive DCT close
   (commit `360813f`).  Both executed against the pre-loaded brief
   from `c25c8b0` (close path: `hasDerivAt_of_hasDerivAt_of_ne` +
   one-sided variants + union).  Tactical deviations: `le_of_not_lt`
   → `not_lt.mp` rename, `Continuous.comp_aemeasurable` → explicit
   `hφ_cont.measurable.comp_aemeasurable`, `← h_prev_init` direction
   → `h_prev_init`, `f_prev 0` vs `f₀` bridges via `h_prev_init ▸`.
   No architectural surprises; estimated 280-350 line close
   delivered as 75-line helper + 50-line h_diff_ne + 70-line
   h_cont_f LEFT across the session (substantive estimate validated
   per-leaf, just split across multiple sessions).

**Composition with P5**: P5 says "verify the strategic recommendation
before acting on it."  P6 says "when the strategic recommendation
*has* been verified (in prior session) and the brief is concrete,
execution lands cleanly."  The two compose: P5 catches strategic
mismatches before they cascade into execution-mode P2 firings; P6
confirms that once P5 has been satisfied, execution works as
designed.  This is why the project's two-commit session structure
(discovery commit + execution commit, often paired) is the
empirically most productive cadence.

**Operational rule**: when planning a session, distinguish between
(a) sessions opening against a verified pre-loaded brief
(execution-mode, expect clean landing) and (b) sessions opening
without such a brief (diagnostic-mode, expect P5 verification work
and possibly a discovery-commit deliverable).  Type (a) sessions
can target substantive line-count delivery; type (b) sessions
target information-density delivery.  Mis-typing the session
(treating a type-b session as type-a) produces the P2 cascade
failure mode; correctly identifying the type matches expectations
to outcomes.

**Composition with the session-cadence watch-list**: P6 is the
*positive empirical pattern* of the session-cadence observation —
specifically, the success-mode of execution sessions when
diagnostic prep is loaded.  The watch-list entry remains as the
broader meta-observation about cadence as a concept; P6 is the
concrete pattern that makes one half of the cadence work
reliably.

### P7. Decay-asymmetry strictly dominates compounding-asymmetry as sequencing signal (among ready tasks)

**Failure mode**: when two tasks compete for a session slot and one
decays (gets harder per session of delay) while the other is
delay-invariant (same difficulty whenever attempted), the natural
framing is "ossification-cost vs. compounding-payoff," which presents
them as competing claims of similar weight.  That framing is wrong.
The decaying task and the delay-invariant task differ in *what changes
under delay*, not in *how appealing they are*; spending the
delay-invariant slot first leaves work-product on the table that could
have come for free later, while spending the decaying slot last loses
work-product that was reachable cheaply earlier.

**Empirical confirmation** (Stage 2b part 2 → part 3, 2026-05-31): two
candidates competed for the post-item-6 session slot — the soundness
fix (`LocalSmallness` retiring a false constraint) versus the
separation lemma (a bankable pure-FA export unblocking item 3).  The
initial framing as "ossification vs. compounding" presented them as
symmetric trade-offs.  The user-applied reframing as
"decay-vs-delay-invariant" identified the asymmetry: the separation
lemma keeps; the soundness fix degrades each session that proof
structure ossifies around the false constraint.  Decision: soundness
first.  Empirically validated when the L6495 read surfaced a second-
order finding that would have invalidated a separation lemma built
atop the about-to-change constraint.

**Boundary condition (part of the rule)**: the rule applies *among
ready tasks*.  A decaying task that turns out blocked yields to a
ready one — that's not a defection from the rule, it's the rule's
ready-condition.  At Stage 2b part 3 execution, the L6495 read was the
specific gate determining which case the soundness fix was in (turned
out to be Branch 3: scoped enough, ready).  Without the gate-read,
"always do the decaying task first" would harden into an unconditional
constraint — exactly the overgeneralization the discipline framework
distrusts.

**Operational rule**: when sequencing among ready tasks, weight by
decay-asymmetry, not by appeal-symmetry-of-competing-arguments.
Compounding-payoff is an argument for "do this soon," not "do this
first."  If both tasks are ready, the decaying one goes first; the
delay-invariant one yields, since it'll be exactly as bankable later.
If the decaying task turns out blocked, the rule's ready-condition
fires and the delay-invariant task legitimately takes the slot.

### P8. Appeal-asymmetry between competing tasks is itself a risk gradient

**Failure mode**: when two tasks compete for a slot and one is
appealing (clean banked-export, satisfying signature work,
metric-visible payoff) while the other isn't (audit-and-rework grind,
no sorry-count movement, corrects an existing artifact), the natural
weighting assigns each task its mathematical merits and lets the
choice emerge.  But the appeal-gap is itself a signal — it's the
slope along which "do the appealing one first, the grindy one next
session" silently becomes "the grindy one the session after that,"
because each session that passes leaves the appealing task as
satisfying as ever and the grindy task as unappealing as ever.  The
appeal gap is decision-stable across sessions; it doesn't get
resolved by deferral, only re-encountered.

**Empirical confirmation** (Stage 2b part 2 → part 3, 2026-05-31):
the separation lemma vs. soundness fix choice (see P7) ALSO had a
strong appeal asymmetry — separation lemma was the clean banked-
export move; soundness fix was an audit-and-rework grind that didn't
move the sorry count.  The same appeal asymmetry made the
"compounding payoff" framing more attractive than the decay framing,
which is exactly the slope that would have re-encountered the choice
session-after-session.

**Operational rule**: when choosing between two tasks where one is
appealing and the other isn't, **weight the unappealing task's case
heavier by the magnitude of the appeal asymmetry**.  Appeal pulls
scheduling in a direction; the sequencing decision should counter-
pull when the unappealing task is the substantive one.  This is the
inverse of how appeal-weighting feels natural; the rule deliberately
fights the natural gradient.

**Composition with P7**: P7 says "decay dominates among ready tasks."
P8 says "appeal-asymmetry is a defer signal pointing at the
unappealing task as the substantive one."  Together: when a decaying
task is also unappealing and a delay-invariant task is also
appealing, BOTH rules point the same direction (unappealing-decaying
first).  When they point opposite directions, the decay rule
dominates per P7's structure.

### P9. Assertion-without-action as defer-tell (NOT assertion-frequency)

**Failure mode**: across multiple sessions, the same task can be
named as time-sensitive or urgent multiple times without being acted
on substantively — each session that mentions urgency might also
produce a diagnostic, a scope refinement, a "next session executes"
brief, etc.  Each individual urgency-naming is correct; the *pattern*
across them is that scoping advances while the urgent thing itself
sits untouched.  This is slow-motion ossification happening to the
urgent task; the diagnostic-and-refinement cycle becomes the
legitimating mechanism for not executing.

**Empirical confirmation** (Stage 2b part 3 diagnostic arc,
2026-05-31): the soundness fix (`LocalSmallness` correcting a false
predicate) was named as time-sensitive in three commits — the
initial scope-commit (`f38ba8b`), the contingency-refinements commit
(`16ea5ed`), and the sequencing-decision commit (`ffe573d`).  Each
individual naming was correct (the false constraint genuinely was
ossifying).  But across the three, the pattern was urgency asserted
while scoping advanced and the actual constraint stayed untouched.
The fourth commit (`b7d4d05`, L6495 read result) was the first
commit that *acted* — it executed L6495 reading rather than
re-scoping.  The first three were "urgency asserted, scoping
advanced"; the fourth was "scoping discovered structure during
action."

**Discriminator (the tight formulation, NOT the bald one)**: the
defer-signal is *urgency repeatedly asserted without being acted on*,
not *repeated urgency*.  Some tasks genuinely *are* urgent and each
session legitimately surfaces a new reason to name them.  The
discriminator is **did the urgency claim do any work each time, or
was it restated while acting on something else?**  The bald version
("repeated urgency = defer signal") would cause second-guessing of
genuinely-urgent tasks named-with-action; the discriminator
distinguishes the failure mode (assertion-without-action) from the
healthy mode (assertion-with-action).

**Distinguishing the failure mode in real time**: scoping-because-
touching-revealed-structure ≠ scoping-instead-of-touching.  The
L6495 read at Stage 2b part 3 execution (commit `b7d4d05`) is an
instance of scoping-because-touching: the session opened on
execution, the read surfaced structure, the scoping commit captured
the finding.  That's not defer-bias; that's the gate-read doing its
job.  Defer-bias is when the session opens on scoping *instead of*
opening on execution.

**P5 connection (the meta-discipline guard)**: at the second sighting
of this pattern in the future, the discriminator that earns promotion
is the same discriminator that defines the pattern — was urgency
named-and-deferred, or named-and-addressed.  This pattern earns
promotion when it correctly flags a *second* defer-without-action,
not a false positive on a task that was simply mentioned twice with
action.  P5 ("verify the framework's own pattern-extrapolations
atom-by-atom") operates on this pattern's own promotion candidacy.

**Generalisation**: this is the most cross-project of the three new
P-series entries.  P7 and P8 are about sequencing under bias; P9 is
the meta-rule about distinguishing legitimate-urgency-naming from
urgency-as-deferral-cover.  Useful wherever a process generates
diagnostic-and-refinement cycles around urgent work.

### P10. Build-permits vs. audit-certifies — green build is consistent with multiple stories

**Failure mode**: after a non-trivial refactor (predicate split,
hypothesis rename, signature cascade), `lake build` clean is
necessary but not sufficient for "the refactor preserved meaning."
The build certifies typechecking against the new types; it does not
certify that consumers are using the new types *for the same
mathematical purpose* as the old.  A predicate that was doing
double-duty inside a body — discharging two conceptually distinct
sub-arguments off one hypothesis — would split cleanly at the
signature layer (each consumer takes whichever new predicate matches
its signature site) but the body might silently drop the second use,
because the contraction obligation (e.g.) might be discharged
elsewhere or be vacuous.  The build doesn't catch that; only a body-
level audit does.

**Empirical confirmation** (Stage 2b part 3 Commit 2,
`exists_vlasov_perz_trajectory` audit, 2026-05-31): the triage
predicted this site was "structural-but-survivable" — meaning the
PL-buffer-only constraint should suffice for the body that previously
took the conflated `LocalSmallness`.  The build at Commit 1 was clean,
which is *consistent with* single-purpose use but does not *prove*
it.  The actual audit traced every consumption of `hTL_PL` (single
unfold at L4249 → R-existence chain at L4250-L4310; `hbound_local`
at L4316-L4373 leans on R and Lipschitz growth, not the predicate;
flow call at L4377-L4396 passes R, not the predicate).  The trace
confirmed single-purpose; the build merely permitted single-purpose
to be a story consistent with typechecking.

**Operational rule**: after a refactor that changes hypothesis
semantics (predicate splits, signature reshapes, predicate renames
that fuse-or-defuse meaning), don't certify the refactor "complete"
on the strength of a green build alone.  Body-level audit at each
consumer is the certification step.  This applies even — especially
— when the triage predicted the consumer survives.  "Survivable" is
the prediction; the read is the confirmation.  Predictions that
turn out wrong AFTER a green build are exactly the failure mode
this rule prevents.

**Composition with P1**: P1 says "atom-level signature reading at
the API layer before drafting helper signatures."  P10 is the same
discipline at the body layer after refactoring: atom-level consumer
reading after green build to confirm single-purpose use of refactored
hypotheses.  P1 is pre-execution; P10 is post-execution.  Both are
applications of "the answer that *typechecks* is not necessarily the
answer that *means what you think it means*."

**Generalisation**: the "build-permits vs. audit-certifies" pattern
applies past Lean — to any compiled or statically-typed system where
type-correctness is consistent with multiple semantic interpretations.
After a refactor whose correctness depends on consumer-level
semantics (not just consumer-level types), the audit is the
certification step.  Green build is a precondition, not a proof.

## M-series — Mathematical structure

### M1. Minimize structure-projection boundaries

**Failure mode**: when a proof crosses between two mathematical
structures (e.g., `ℝ` and `ℝ≥0∞`, `ℝ` and `NNReal`, ENNReal and
its `.toReal` projection), the natural approach is to project to
the "more familiar" structure (usually ℝ) early and stay there.
But each projection boundary requires finiteness/non-negativity
side conditions, which fail or clutter the proof when the
underlying argument doesn't naturally produce them.

**Empirical confirmation** (three sightings across Stage 4):

1. `supW1On_iterated_triangle` (Stage 4): proved entirely in
   ENNReal, never projecting to ℝ.  ENNReal addition is
   well-defined with `⊤` as absorbing element, so no finiteness
   side conditions arise.  Clean inductive proof.
2. `MathlibTODO_cauchyW1_hasNarrowLimit` placeholder
   strengthening: reformulating the Cauchy hypothesis from
   `.toReal < ε` to ENNReal-form `wasserstein1 ν_m ν_n < ε`
   removed the finiteness side conditions that would otherwise
   clutter every call site.
3. `picard_iterate_geometric_bound` (Stage 4): the proof stays in
   ENNReal except for one cleanly-localized
   `ENNReal.ofReal`-boundary at the bridge between the structural
   argument (`supW1On` in ENNReal) and the closed-form algebra
   (real geometric series).  ONE boundary, not several.

**Fix**: when a proof's natural structure is ENNReal (or NNReal,
or any "augmented" structure with absorbing elements), prefer to
stay in that structure.  Project to ℝ only at the boundary where
a real-valued closed form is genuinely needed (e.g., to invoke a
real-analysis lemma).  Minimize the number of such boundary
crossings — ideally to one.

**Generalisation**: the principle isn't "stay in ENNReal
absolutely."  It's "minimize structure-projection boundaries,
because each boundary adds side conditions and elaboration cost."
The principle applies whenever the natural mathematical structure
isn't ℝ — at the boundary between any two related structures,
prefer to do the algebra in whichever one is the natural home of
the argument.

## B-series — Bridging architecture / structural-fix patterns

### B1. Predicate enrichment over per-site bridging

**Failure mode**: when an abstract predicate is insufficient for
the constructive proof structure (the proof produces structural
witnesses the predicate doesn't carry, or operates on a finite
window where the predicate quantifies universally), the natural
response is to add per-site bridge lemmas that close the gap at
each consumer.  But each bridge has its own friction; the chain
proliferates; the project accumulates lemma-level technical debt.

**Empirical confirmation** (two sightings):

1. `IsLagrangianVlasovSolution` introduction (early in the arc):
   the abstract `IsVlasovSolution` predicate says "weak PDE
   holds" but doesn't carry a characteristic flow.  Per-site
   bridges to produce or consume the flow (uscNarrow_lag /
   derivBound_lag / H1_lag / SC.8_lag) would have required ~4
   parallel bridge families.  Instead, *enrich the predicate*:
   `IsLagrangianVlasovSolution := IsVlasovSolution ∧ ∃ flow,
   ...`.  The flow witness becomes part of the predicate's
   structure, available at every consumer without per-site
   bridging.
2. `_On` predicate family (Stage 4 Path 3 pivot): the abstract
   `IsLagrangianVlasovSolution` quantifies universally in `t`;
   local existence operates on `[0, T]`.  Per-site bridges
   between Stage 1.9's Ioo-flavored flow and the universal Stage
   C predicate would have required 2-3 bridge families with
   accumulating sorries.  Instead, *enrich the predicate family*:
   add `IsVlasovSolutionOn`, `IsLagrangianVlasovSolutionOn` as
   `_On`-localized mirrors.  The localized form is natural for
   local existence; the global form is recoverable via gluing.

**Fix**: when the abstract type-level statement and the
constructive proof structure disagree, the resolution is usually
a new predicate (or predicate variant), not a workaround at every
consumer site.  Specifically: when ≥3 consumers would need
parallel bridges to compose against a structurally-misaligned
predicate, introduce a new predicate that aligns with the
constructive proof structure.

**Generalisation**: predicate enrichment is the type-level
counterpart to function-level abstraction.  Where a function with
many similar callers benefits from a more general signature, a
predicate with many similar consumer-bridges benefits from a more
specific (or differently-structured) statement.  The signal is
"≥3 bridges with the same shape" or "cascade signal from P2";
the response is to lift the bridging to the type level.

### B2. Boundary regularity at predicate-layer boundaries — recursive Friction-5 surgery

**Failure mode**: predicates that work on open or half-open
intervals (`Ioo 0 T`, `Ico 0 T`) don't cover the boundary point
`t = T` (or `t = 0`), but downstream consumers (gluing,
continuation, conjunct wire-up, narrow continuity) need data at
the boundary.  Without exposure of the boundary regularity, the
consumers can't compose.

**Empirical confirmation** (three sightings):

1. **Friction 5** (commit `4b024ee`, 2026-05-29): the per-ball
   characteristic flow's `IsCharacteristicFlowOn (Ioo 0 T)` form
   excludes `t = T`.  `Phi_step`'s gluing argument requires
   `HasDerivAt` at `t = T` from both sides.  Fix: enriched the
   chain per-ball-flow → per-z → Stage 1.9 to expose
   `HasDerivWithinAt` on the closed `Icc 0 T` form.
2. **`_glue_step` boundary at `t = T`** (commit `eb3c260`,
   2026-05-30): the gluing-step at `t = T` between `f_prev` and
   `g` requires `HasDerivAt` from both sides.  Same enrichment
   pattern needed (one architectural layer up: enrich
   `vlasovWellPosedness_local`'s output).
3. **Stage 6 narrow continuity at `t = 0`** (commit `20500ee`,
   2026-05-30): `ContinuousOn (Ici 0)` of the integral against the
   glued `f` requires `ContinuousWithinAt _ (Ici 0) 0`.  The
   per-window flow's `IsLagrangianVlasovSolutionOn` provides
   regularity on `Ioo 0 T` only.  Boundary at `t = 0` requires the
   same kind of enrichment.

**Common surgery shape**:

1. Identify a downstream consumer needing boundary data.
2. Identify the upstream producer chain whose internal proofs
   already construct the boundary regularity but discard it.
3. Enrich the producer chain's conclusion to expose the boundary
   bundle as an additional conjunct.
4. Downstream consumer destructures the bundle and closes the
   boundary cases.

All three surgeries are **additive** (no closed proof bodies
modified) and retire multiple sub-sub-sorries in one swing.

**Fix**: when a downstream consumer's sub-sub-sorries are
characterized as "at the boundary point `t = T`" (or `t = 0`),
identify the upstream chain that internally constructs the
boundary regularity, then add the boundary bundle as an
additional output conjunct.  Don't try to derive boundary
regularity from open-interval data — it's not derivable; the
upstream chain has it but discards it.

**Generalisation**: B2 is the specific shape of B1 for the
`Ioo`-vs-`Icc` boundary case in localized predicate families.  B1
says "enrich predicates over per-site bridging"; B2 says "the
specific predicate enrichment that retires the boundary mismatch
is to expose the upstream-already-constructed boundary regularity
as an additional conjunct."

The pattern is **recursive** across architectural layers: Friction 5
was at the per-ball-flow layer; `_glue_step` boundary was at the
`vlasovWellPosedness_local` layer; Stage 6 narrow continuity is at
the `_universal_existence` layer.  Each layer's surgery is the same
shape but at a higher level of composition.  This is a **fractal
property of the architecture**: the same kind of mismatch exists at
multiple scales, requiring the same kind of work at each scale.

**B2-prophylaxis (forward-looking corollary)**: when defining new
localized predicates that quantify over open or half-open intervals
(`∀ t ∈ Ioo 0 T, ...`, `∀ s ∈ Ico 0 T, ...`), expose boundary data
in the initial definition rather than reactively at consumer time.
This is the inverse of B2 operating preemptively — enrich at
predicate-definition time so that downstream consumers don't trigger
B2 surgery cascades.

The cost is a single extra conjunct at definition time; the benefit
is avoiding the recursive enrichment work that B2's empirical history
shows is required whenever any downstream consumer crosses a boundary.

Pragmatically: when introducing a new `IsXxxOn` predicate family in
the project (or in cleanup-phase work), the predicate's definition
should include:
1. The universal-on-`Ioo` ODE/PDE claim (matching the open-interval
   regularity the construction produces).
2. **The boundary-data claim** at endpoints (HasDerivWithinAt on
   `Icc 0 T` at t = 0 and t = T, or equivalent boundary regularity
   for the predicate's content).

The cleanup document should reference this prophylactic rule for any
post-cleanup architectural work to avoid relitigating the B2 surgery
at new layers.

**B2-anti-prophylaxis (counter-refinement, 2026-05-30, commit `c25c8b0`)**:
B2 surgery isn't always the right shape — sometimes Mathlib infrastructure
provides a *localized* alternative that sidesteps the B2 cascade entirely.
Discovered empirically when scoping `_glue_step` case (a)'s close: the
originally-planned B2 cascade on `IsVlasovSolutionOn` (~400-600 lines,
4-layer cascade + new HasDerivWithinAt-DUI helper) was sidestepped by
Mathlib's `hasDerivAt_of_hasDerivAt_of_ne` (`Mathlib/Analysis/Calculus/
FDeriv/Extend.lean` L177) + one-sided variants
`hasDerivWithinAt_{Iic,Ici}_of_tendsto_deriv` (L108, L142).  Localized
inline close: ~280-350 lines, no predicate-layer disruption, no new
Mathlib placeholders.

**Operational rule (B2-anti-prophylaxis)**: when a B2 pattern is
*hypothesized* for a new boundary mismatch, before committing to the
B2 surgery, **check Mathlib for localized derivative-extension lemmas**
(`FDeriv/Extend.lean` is the canonical home).  Specifically:
1. Does the consumer need HasDerivAt at a boundary point that's interior
   to a larger open set (where HasDerivAt holds at every nearby
   non-boundary point)?  → Try `hasDerivAt_of_hasDerivAt_of_ne` or its
   neighborhood-localized variant.
2. Does the consumer need HasDerivWithinAt on `Iic T` or `Ici a` at a
   boundary point that already has HasDerivAt on the open interior +
   continuous extension of the derivative?  → Try
   `hasDerivWithinAt_{Iic,Ici}_of_tendsto_deriv`.
3. Only if Mathlib provides no localized alternative, commit to the
   B2 cascade.

**Generalisation**: B2-prophylaxis says "enrich predicates at definition
time to avoid reactive surgery."  B2-anti-prophylaxis says "before
committing to B2 surgery reactively, check whether Mathlib provides a
*localized* alternative that closes the consumer without touching the
predicate."  The two are not in tension — prophylaxis applies at
predicate-definition time (proactive); anti-prophylaxis applies at
consumer-close time (reactive).  The forward-looking lesson for future
kinetic-theory formalization: when localized predicates produce boundary
mismatches, search `FDeriv/Extend.lean` (and analogues) *before*
committing to predicate enrichment.

This is also P5 (discipline framework's pattern-extrapolation needs
atom-level verification) operating concretely: B2's three prior sightings
predicted "case (a) needs B2 cascade"; P1 atom-level reading of Mathlib's
extension lemmas refuted the prediction.

## Watch-list

Candidates accumulating sightings, not yet promotion-ready under
the three-sighting threshold (with the discipline pairing of
"promote within ~5 sessions of reaching threshold" to prevent
indefinite watch-listing):

* **Statement-level mismatches between claimed and proved — the
  inverse-of-API-lock pattern**: 1 sighting (forward-only refactor
  in commit `de135c7`, 2026-05-30).  Diagnostic: when proving a
  theorem requires significant case structure for edge cases that
  aren't part of the mathematical content (here, the `t < 0`
  backward-time case for a forward Cauchy problem), the statement
  is probably too strong, and tightening the *external* statement
  is the right fix rather than building proof machinery for the
  unnecessary cases.  This is the inverse of the API-lock pattern
  (P4): API-lock loosens *internal* interfaces to allow incremental
  closure; statement-correction tightens the *external* interface
  to match what the proof actually produces.

  **Empirical evidence**: the marquee theorem `vlasovWellPosedness`
  was originally stated as `∃! f : ℝ → Measure (PhaseSpace d), ...`
  with universal-in-`t` conjuncts.  The proof's content (forward
  Picard iteration from `t = 0`) only establishes forward-time
  existence.  The mismatch required ~30 lines of sub-sub-sorried
  case-split machinery in the marquee body to "handle" `t < 0` —
  machinery that wasn't actually proving anything.  The refactor
  restated the marquee to forward-only existence (`∃ f, f 0 = f₀
  ∧ ∀ t ∈ Ici 0, ... ∧ ∀ T > 0, IsLagrangianVlasovSolutionOn ...`),
  matching Dobrushin 1979's actual claim, and the case-split
  machinery disappeared along with the corresponding sub-sub-sorry.

  **Adds a new metric axis** (per the 2026-05-30 strategic message):
  "statement correctness" — distinct from declaration count and
  sub-sub-sorry count.  A statement-correctness improvement doesn't
  move sorry-count metrics but is genuine research-artifact value,
  worth foregrounding in the cleanup document as evidence that the
  formalization surfaced and corrected a statement-mathematical-
  content mismatch.

  **General principle**: when an `∃!` (or universal-in-`t`)
  conclusion forces case structure for cases not in the
  mathematical content, replace `∃!` with `∃` and restrict the
  quantification to the domain the proof actually covers.  The
  inverse of "enrich the predicate" (B1) — here we *restrict*
  the predicate.

  Probably M-series rather than P or B — about the mathematics of
  correctly stating theorems, not about process discipline or
  architectural patterns.  Trigger: 2 more sightings.
  (B2 promoted to B-series proper at commit reflecting this session,
  with 3rd sighting: Stage 6 narrow continuity boundary at t = 0.)
* **Session-type cadence — diagnostic vs execution as distinct operating
  modes**: 1 sighting (this session, 2026-05-30, commits `56f8ddf` +
  `c25c8b0`).  Diagnostic: sessions that prioritize atom-level reading
  (P1) and diagnostic-loading (P3) produce *more* strategic value per
  session than sessions that prioritize execution against pre-loaded
  diagnostics.  Diagnostic sessions are higher-information-density
  (each commit unblocks multiple future sessions); execution sessions
  are higher-line-count-density (each commit closes substantive work).
  Both are valuable; the project's pace would probably improve from
  *deliberately interleaving* them rather than treating diagnostic work
  as "preparation" for execution work.

  **Empirical example (this session)**: option 3 substantive close
  (commit `56f8ddf`, +112 lines, -2 sub-sub-sorries — execution-mode)
  paired with discovery commit (`c25c8b0`, +42 lines doc, 30-50% scope
  reduction on next session's planned work — diagnostic-mode).  The
  discovery commit's value (P3 loaded context that retired the B2
  cascade framing and rerouted to a localized Mathlib path) is arguably
  larger than the execution commit's, despite zero direct sorry
  closure.  Three P1 atom-level wins in this single session
  (option-3 close path discovery, Stage C verdict refinement, case-(a)
  close path discovery) correlate with the session's deliberate
  diagnostic orientation.

  **Operational hypothesis**: the project's session-cadence should
  alternate roughly 1:1 between diagnostic-oriented and execution-
  oriented sessions, rather than running pure-execution sessions until
  diagnostic gaps surface mid-execution (which produces P2-style
  cascade-friction).  Empirical confirmation: the user's strategic
  framing of this session as "B2 surgery focused execution" with
  authorization for diagnostic pivoting produced the highest-value
  discovery commit of the recent arc despite being scoped as execution.

  **Sighting #2 (2026-05-31)**: session of commits `bd11a2c` +
  `360813f` executed h_cont_f LEFT close + helper banking against
  the brief loaded by `c25c8b0`'s discovery commit.  Pure execution
  mode, no diagnostic pivoting, ~145 lines substantive across two
  commits.  Tactical deviations only (notation namespace, term-level
  substitutions); no architectural surprises.  This validates the
  cadence hypothesis: the diagnostic→execution alternation produces
  reliable execution sessions when the prior diagnostic was concrete.

  Status: **partially promoted as P6** (positive empirical pattern of
  brief-driven execution).  Watch-list entry remains for the broader
  meta-observation about cadence as a concept (P6 captures only the
  positive-execution half).  Further sightings of the *deliberate
  interleaving* principle (and especially of mis-typed sessions producing
  P2 firings as the cost of skipping diagnostic prep) would promote
  the broader meta-discipline.

  Trigger for full meta-promotion: 2 more sightings of the cadence
  pattern (interleaving working as concept, not just brief-driven
  execution working as concept).

* **Cascade-as-signal**: 1 sighting (Stage 4 Bridge #1 →
  Friction 5 discovery).  Diagnostic: "resolving friction N
  requires infrastructure that's currently blocked by friction
  N+1."  Trigger: 2 more sightings.  Promotion candidate as a
  B-series companion to B1 (B2?) or as a P-series companion
  to P2 (P3?); decide at promotion based on whether the
  pattern is observed structurally or process-discipline-wise.
* **Local-clamping technique**: 1-2 sightings (Phi_step's
  clamped-flow technique; possibly `VlasovMeasureCurve.extend`
  if counted as the same pattern at the measure-curve level).
  Diagnostic: "downstream consumer demands universal-in-t
  hypotheses, upstream provides on-Icc behavior; define a
  clamped version internally and discharge equality via
  clamp-identity-on-Icc."  Trigger: 1-2 more sightings.
  Promotion candidate as L-series (tactical Lean pattern) or
  M-series (mathematical structure of clamping); decide at
  promotion.
* **Strategic-conversation diagnosis → focused-session execution
  (meta-level P3)**: 1 sighting (Stage 6 + architectural priming
  session, 2026-05-30).  Diagnostic: when the strategic conversation
  between sessions produces a detailed brief (as opposed to the
  diagnostic work happening within a session), the resulting focused
  session executes against pre-loaded context without surfacing
  P2-style mid-session scope discoveries.  Empirical evidence: the
  Stage 6 + architectural priming session executed two commits
  exactly as scoped (additive priming + substantive close), no
  cascade surprises, no scope explosions, sorry trajectory matched
  prediction (10 → 10).  P3 (within-session diagnostic) and P4 (API-
  lock pattern at commit level) both operated at the proof-discipline
  layer; this is the same compounding effect operating at the
  *meta*-level: the diagnostic work happens in strategic
  conversation between sessions, the execution happens in focused
  sessions with detailed instructions.  Trigger: 2 more sightings.
  Promotion candidate as a P3 addendum ("cross-session context-loading
  also works at the strategic-conversation layer") or as its own
  P-series entry.  Either way, register it as a healthy operational
  cadence that the project should preserve.
* **Cumulative-trajectory honesty in API-lock commit framing**:
  2 sightings (Stage 5 commit-framing critique 2026-05-29 +
  substantive-close-phase declaration-vs-sub-sub-sorry distinction
  2026-05-30).  Diagnostic: per-turn commit messages using
  "structural content improved without net sorry growth" framing are
  honest about the *immediate* turn but obscure the *cumulative*
  trajectory when API-lock-pattern (P4) accumulates over many
  sessions.  Empirical arc: project went from 7 sorries (post-
  Friction-5) to 11 sorries (post-Stage-5) via four discipline-
  correct API-lock commits; each individual framing was honest at
  the per-turn level, but the multi-session cumulative effect of
  +4 sorries was not explicitly named.

  **Refinement from 2026-05-30 substantive-close phase**: the
  pattern recurses — substantive body closes that don't reduce
  declaration count.  The original API-lock pattern was "commit a
  sorry'd signature, discharge the body later."  The recursive
  pattern is "discharge a body, surfacing sub-sub-sorries that
  replace the parent sorry."  Each iteration improves structural
  content (the body's mathematical content is now visible and
  composable) without reducing the warning count.  This is genuine
  progress as long as each iteration's sub-sub-sorries are strictly
  more tractable than the parent sorry — empirically validated by
  the Friction 5, sub-helper enrichment, `_finalAssembly_*`
  consolidation, and Stage 6 `h_agree` retirements.

  Fix (two-part):
  1. In commit messages for API-lock work, include an explicit
     cumulative-trajectory line ("project sorry count: X → Y across
     the post-Z arc; pending substantive closes: N") in addition to
     the per-turn delta.
  2. **Track two metrics**, not one:
     - *Declaration count*: count of sorry-using declarations
       (externally visible in the file's warning output).
     - *Sub-sub-sorry count*: total sorries including those inside
       laid-out bodies (honest measure of remaining work).

     The two diverge during the substantive-close phase: declaration
     count holds flat while sub-sub-sorry count fluctuates as bodies
     decompose and individual sub-claims retire.  The full picture
     requires both.

  Trigger: 1 more sighting.  Promotion candidate as a P-series
  addendum to P4 (communication-discipline companion to the
  commit-pattern discipline P4 names) or as its own P-series entry
  (calibration-honesty discipline) — decide at promotion.
* **Additive offsets in smallness constraints are structurally
  fatal**: 1 sighting (Stage 1.9's `L · (T+1)² < 1` constraint,
  diagnosed 2026-05-29 via comparison with Dobrushin 1979).
  Diagnostic: smallness constraints with shape `L · (T + c)^α < 1`
  for *additive* `c > 0` are unable to be satisfied for any
  `L ≥ c^{-α}` regardless of `T`, since `(T + c)^α ≥ c^α`.
  Constraints with shape `L · T^α < 1` (no additive offset) are
  satisfiable for any `L > 0` by taking `T < L^{-1/α}`.  In the
  Vlasov well-posedness arc, the `(T+1)²` offset traces to two
  sources in the per-ball flow construction: (a) the working
  interval `[0, T+1]` used to dodge the HasDerivWithinAt boundary
  issue (≡ Friction 5's surgery target), and (b) per-window
  position-drift bookkeeping that collapses linear and quadratic
  terms.  Sources (a) and (b) are independent; fixing (a) alone
  via Friction 5 surgery moves the constraint from `L·(T+1)² < 1`
  to `L · T² < 1`, which still satisfies the Dobrushin-style
  "small enough T wins" property for any `L > 0`.  Net scope
  consequence: leaving the `+1` in place silently restricts
  well-posedness to `L < 1`; removing it (Friction 5 surgery) is
  the load-bearing precondition for the Stage 5 continuation
  tower to work for arbitrary Lipschitz constants.
  Trigger: 2 more sightings.  Promotion candidate as B-series
  (architectural — "remove additive offsets rather than absorb")
  or M-series (mathematical — "the +1 destroys the limit-shrinking
  property of the constraint"); decide at promotion based on
  whether subsequent sightings are architectural or proof-shape.

## Vlasov-specific design choices

(See `formalize/DESIGN.md` for the full version. Highlights:)

- **`wasserstein1` is defined via the KR dual sup-formula.** This
  trade-off makes static Lipschitz tests easy (the easy direction
  of KR is the definition) and makes dynamic regularity hard
  (sup of a continuous family is only LSC). The two
  `MathlibTODO_wassersteinGronwallCoupling_*` placeholders
  (`W1ContOn`, `derivBound`) are the consequence.
- **`MathlibTODO_*` are sorry'd theorems, not axioms.** The 2026-05
  refactor unified trust under one bucket (`sorry`); the
  `MathlibTODO_` prefix marks "should eventually be filled by a
  Mathlib citation". Sorry-prover skips them via §0 skip rule.
- **`HasFiniteFirstMoment μ` = `IsProbabilityMeasure μ ∧ Integrable (·.norm) μ`.**
  Used as the hypothesis at dobrushin-level call sites; the
  `wasserstein1_lt_top_of_finite_moment` lemma extracts
  `wasserstein1 ≠ ⊤` from this.

## Patterns catalogue cross-reference

The Lean-proof patterns catalogue lives in
`.claude/agents/sorry-decomposer.md` §3.1.6 (5 patterns as of
2026-05-26: HasDerivAt.fun_sum vs .sum; real_inner_smul_left vs
inner_smul_left; etc.). It's specifically about Lean idiom
choices, not agent design. Keep agent-design lessons here,
Lean-idiom lessons there.
