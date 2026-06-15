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

### L11. Local-clamping to satisfy universal-`t` hypotheses from window data

**Failure mode**: a downstream proof has data only on a window `[0, T]`
(window probability, window integrability, window moments), but a helper
lemma it must call demands *universal*-in-`t` hypotheses — typically a
`[∀ t, IsProbabilityMeasure (ρ t)]` instance or a
`(h_int : ∀ t x, …)` argument.  The window class cannot synthesise the
universal instance (off-window the measures are unconstrained), so the
helper cannot be applied directly.  Restating the helper to take pointwise
hypotheses is the "clean" fix but is invasive when the helper has many
consumers.

**Empirical confirmation** (3 sightings: `Phi_step`'s clamped flow,
`VlasovMeasureCurve.extend`, and `wassersteinGronwallCoupling_derivBound_via_pureFA_On`
— the last on 2026-05-31, landed clean on the first build):
`vlasovVectorField_lipschitzWith` (CharFlow L629) demands universal
`[∀ t, IsProbabilityMeasure (ρ t)]` + universal `h_int`, but a window
Lagrangian solution supplies probability only on `[0, T]`.

**Fix**: extend the window object to a universally-valid one by *clamping
the parameter into the window*, apply the universal helper to the clamped
object, then transfer the conclusion back on the window where clamp = id:

1. `set clampT : ℝ → ℝ := fun t => max 0 (min t T)` — lands in `[0, T]`
   for every `t`, and `clampT t = t` on `[0, T]`
   (`min_eq_left ht.2`, `max_eq_right ht.1`).
2. Build the universal instance / hypothesis for the clamped curve
   `fun t => ρ (clampT t)` from the window data at `clampT t ∈ [0, T]`.
3. Apply the universal helper to the clamped curve.
4. Transfer on `[0, T]`: since the consumed object depends on the curve
   only through its value at `t` (e.g. `vlasovVectorField gradW ρ t`
   reads only `ρ t`), `clampT t = t` gives a *value* equality; discharge
   the function equality with `funext z; simp only [theDef, hmeas]`
   (where `hmeas : ρ (clampT t) = ρ t` by `rw [hclampT_id t ht]`), then
   `rw [← h_eq]; exact (clamped result)`.

**Generalisation**: prefer clamping over a pointwise restatement of the
helper when the helper has ≥3 consumers (additive, non-invasive — B-series
preference).  The technique works whenever the consumed quantity depends on
the universally-quantified parameter only locally (so a value-equality on
the window suffices to transfer the conclusion).  This is the L-series
(tactical) companion to the B1 "enrich vs. bridge" decision: clamping is a
*local* bridge that avoids touching shared infrastructure.

### L12. Develop fiddly proofs in a scratch file that IMPORTS the slow target, not in the target itself

**Failure mode**: closing a large, mechanical proof (e.g. a 150-line
measure-theory bridge with many fiddly lemma-name / `simp`-set / `rw`-direction
errors) directly inside a big file means every build iteration recompiles that
whole file.  When the file is large (`Coupling.lean` ≈ **374 s** per `lake
build`), and the proof needs 6–8 iterations, that is 30–50 min of pure build
wall-clock — the iteration loop, not the math, becomes the bottleneck.

**Empirical confirmation** (Foundation B / H2 bridge close, 2026-06-07): the
matrix→measure bridge + measurable lift had ~13 lemma-name/`simp`/`rw` errors
across the atom-decomposition, weight-sums, measurability, integral identities,
and the optimal-coupling marginals/cost.  Iterating in `Coupling.lean` would
have been ~8 × 374 s.

**Fix — the trick**: develop the proof in a throwaway scratch file that
`import`s the target module:

1. Revert the target declaration to a single `sorry` so the slow file compiles
   **once** (374 s) and its `.olean` is cached.
2. Create `Vlasov/Scratch.lean` with `import Vlasov.OT.Coupling`, `open …`,
   `namespace …`, and an `example` whose statement is **verbatim** the target's
   (signature copied, `theorem foo` → `example`).  Paste the proof body.
3. Iterate with `lake env lean Vlasov/Scratch.lean` — this compiles **only the
   scratch** (the imported module is cached), so each cycle is ~15–60 s, a
   **5–25× speed-up**.
4. When the scratch is green (0 errors, 0 sorries), port the body verbatim back
   into the target, `rm` the scratch, and do **one** final full build + the
   `#print axioms` cert.

**Why it works**: `lake env lean <file>` (or `lake build` of a leaf module)
recompiles only that file against cached `.olean`s.  The expensive dependency is
paid once; all iteration happens against the fast leaf.  The scratch sees every
project def the target sees (it imports the same module + opens the same
namespace), so the proof that closes in the scratch closes verbatim in the
target.

**Generalisation**: whenever the edit-build-fix loop on a declaration is
dominated by *recompiling its host file* rather than by the proof difficulty,
move the development to an importing scratch leaf.  Applies to any large Lean
file; the bigger the host and the more iterations expected, the larger the win.
Pairs with P4 (API-lock): revert to `sorry` to keep the host compiling while the
scratch carries the in-flight work.

### L13. `ContDiff ℝ ⊤` means real-analytic (`ω`), NOT C^∞ — and vacuates compact-support test classes

**Failure mode**: in current Mathlib, `ContDiff`'s smoothness order has type
`WithTop ℕ∞`, whose top `⊤` is `ω` = **real-analytic**, not C^∞.  C^∞ is the
*lower* element `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`.  So `ContDiff ℝ ⊤ φ` silently
means *analytic*.  Because real-analytic `+` `HasCompactSupport` ⟹ `φ = 0`
(identity theorem), any predicate of the shape
`∀ φ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → …` has test class `{0}` and is
**vacuously true** — the classic "the weak-solution test class is secretly
empty" trap.

**Why it hides**: it is almost always a *silent semantic regression from a
Mathlib bump* — code written when the order was `ℕ∞` (`⊤ = ∞ = C^∞`) keeps
building after the `WithTop ℕ∞` refactor redefined `⊤` to analytic, because
consumers only use `.differentiable` / `.continuous_fderiv` (which analytic
also supplies) and a vacuous `∀`-hypothesis discharges trivially.  The build
stays green; the vacuity surfaces only when something *constructs* a test
function (mollifier/bump), which can never be analytic+compact.

**Empirical confirmation** (2026-06-13, Vlasov project @ mathlib v4.29.1): the
entire weak-solution side (`IsVlasovSolution`, `IsVlasovSolutionOn`,
`WeakEvolutionEq(On)`, the SC helpers, the new `IsLinearVlasovSolutionOn`) used
`ContDiff ℝ ⊤` at 12 sites — all vacuous.  Surfaced when the weak⟹Lagrangian
bridge's measure-extensionality lemma (the first declaration that must *produce*
test functions) proved unclosable.  The marquee `vlasovWellPosedness`/`dobrushin`
were NOT vacuously true (their flow/pushforward content via
`IsLagrangianVlasovSolution`'s `∃ flow` conjunct is real), but their embedded
weak-PDE conjunct was contentless.

**Diagnosis** (decisive, ~30s via a `lake env lean` scratch):
`#check fun (φ : ℝ → ℝ) => (ContDiff ℝ ⊤ φ : Prop)` prints `ContDiff ℝ ω φ`;
and `example (φ : ℝ → ℝ) (h : ContDiff ℝ (∞ : WithTop ℕ∞) φ) : ContDiff ℝ ⊤ φ := h`
FAILS (`type mismatch ∞ vs ω`) — C^∞ does not imply `⊤`.

**Fix**: replace `ContDiff ℝ ⊤` → `ContDiff ℝ (⊤ : ℕ∞)` (the inner-`ℕ∞` top,
auto-coerced to the C^∞ element).  This form is **clash-free** (needs no
`open scoped ContDiff`, so it dodges the ENNReal `∞`/`⊤` notation collision);
`decide` proves `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ (⊤ : WithTop ℕ∞)`.  The fix is
typically **proof-safe** (consumers use only finite-order facts) but it
*de-vacuates* the predicate, so producers must then genuinely prove the claim
for all C^∞ test functions — confirm with a full rebuild + `#print axioms`
re-cert.

**Generalisation**: whenever a Mathlib upgrade touches a notation whose meaning
is order/lattice-dependent (`⊤`, `∞`, `⊥`), re-confirm what the symbol *means*
in the new version before trusting green builds — a green build is consistent
with a silently-vacuous statement (P10/P11).  Especially suspect any
`∀ φ, [smoothness] φ → HasCompactSupport φ → …` weak-formulation test class.

### L14. `choose` over `∀z ∃N` destroys parameter-regularity of the witness

**Failure mode**: `choose f … using (h : ∀ z, ∃ N, P z N)` (i.e. AoC /
`Classical.choice`) returns a section `f : Z → _` carrying ONLY the *fiberwise*
facts `∀ z, P z (f z)`.  Those constrain `f z` separately per `z` and say nothing
joint in `z`, so **any regularity of `z ↦ f z` — continuity, measurability,
smoothness — is NOT entailed** and is generally unprovable from the `choose`
output.  AoC gives a function, never a *nice* one.  This bites **even when the
witness is unique** per `z` (so the bundle `{(z,N) : P z N}` is genuinely the
graph of a regular function): `choose` discards canonicity — it returns *a*
section of a graph, with no proof its value is *the* unique solution, and
regularity is a property of the canonical map the `∃`-interface cannot expose.

**Empirical confirmation** (C3 / V2, 2026-06-15): `#3`'s 2nd conjunct needs
`Continuous (z ↦ M z t)` for the variational fundamental matrix `Ṁ=A(s,z)·M`,
`M 0=I`.  The body did `choose M … using (λ z, exists_fundamentalMatrix (A(·,z)))`;
the `choose`'d `M` carries only per-`z` `(M0/cont-in-s/ODE)`, so continuity in
`z` is **not derivable** — V2 is unprovable as scaffolded, despite the solution
being unique (linear ODE, continuous coefficients).

**Fix — four routes to preserve continuity/measurability** (decision rule):
* **A — explicit canonical construction** (preferred when a formula exists):
  don't `choose`; define `f z := Φ z` regular-in-`z` by formula, prove `P z (Φ z)`
  separately.  Continuity = uniform/loc-uniform limit with a **`z`-independent**
  majorant (M-test) or finite composition; measurability = closure under
  `tsum`/`∫`/`iSup`/limits.  *(V2: `M z = picardSum`; mirror the already-proven
  `picardSum_continuousOn` M-test in the parameter `z` instead of time.)*
* **B — uniqueness bridge** (witness opaque but unique): keep `choose`'s `f z`,
  build explicit regular `g z` (Route A), prove `f z = g z` ∀z via uniqueness
  (`ODE_solution_unique`), transport regularity.  Use when consumers already
  depend on `f`.
* **C — measurable selection** (no formula, no uniqueness): continuity may fail,
  but measurability via Kuratowski–Ryll-Nardzewski / von Neumann selection
  (thin Mathlib support — fallback).
* **D — bake regularity into the `∃`** (you own the lemma): restate
  `∀ z, ∃ N, P z N` → `∃ F, Regular F ∧ ∀ z, P z (F z)`; destructure once, no
  `choose`-over-`z`.  *(`exists_fundamentalMatrix` → `…_family`.)*

**Generalisation**: `∀z ∃N, P` and `∃F ∀z, P z (F z) ∧ Regular F` are **not
interchangeable for regularity** — **the quantifier order is where
parameter-regularity lives**.  `∀∃` discards it; `∃∀`-with-a-regularity-conjunct
keeps it.  Same family as L13/P10/P11: a typechecking interface (here, a bare
`∃`) can be silently too weak for the property a consumer needs — check what the
*construction* exposes, not just what typechecks.  Full routing in the memory
note `choose-destroys-parameter-regularity`.

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

### P11. A verification that ran against a FAILED build is STALE — not certification

**Failure mode**: a move/edit is followed by `build + secondary-check` (e.g.
`lake build && #print axioms`).  The build FAILS, but the secondary check still
prints a passing result — because it ran against the *previous* build's cached
artifacts (`.olean`s), which reflect the last GOOD state, not the current broken
one.  Reading the passing secondary check as success is a false certification:
the thing it certified (the marquee's axiom footprint) is the OLD footprint, and
the current edit hasn't actually compiled.  The trap is subtle precisely because
the secondary check looks green — the eye goes to it and skips the build status
above it.

**Empirical confirmation** (Phase D move 2, 2026-06-07): the OT-core extraction's
first cut grabbed a dangling docstring (boundary off by 25 lines).
`lake build` failed (`unexpected token 'end'`), but the chained
`#print axioms` footprint check still printed both marquee theorems as
`[propext, Classical.choice, Quot.sound]` — STALE, against the move-1 `.olean`s.
Reading that as "footprint held" would have been a false pass on a move that
did not compile.  Caught by reading the build status first; reverted →
re-diagnosed the true boundary → redid.

**Fix / operational rule**: the secondary certification check (`#print axioms`,
a probe, a coverage report) is meaningful ONLY when the build it ran against
SUCCEEDED.  Read the build status FIRST; a green secondary check against a failed
build is stale and proves nothing.  When chaining `build && check` in one command,
gate on the build's exit/status before trusting the check — or run the check as a
separate step only after confirming the build is green.  This is the temporal
companion to P10 (build-permits-vs-audit-certifies): P10 says a green build is
consistent with multiple stories; P11 says a green *check* is consistent with the
build never having succeeded.  Both: the instrument means nothing until you
confirm what it actually ran against.

**Generalisation**: applies to any edit→build→verify loop with cached build
artifacts (Lean `.olean`, compiled objects, test binaries).  After a failed
build, every downstream check is reporting the last good build.  Move-and-verify
requires verifying the *current* move compiled before reading any verification of
it.

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

### M2. Match the statement to the mathematics — bidirectional

**Principle**: a declaration's statement (both its conclusion *and* its
hypotheses) should match exactly what the mathematics supports — no more,
no less.  Mismatches go in two directions, and the fix direction is the
opposite of the mismatch:

* **Too strong → weaken.**  When proving a declaration forces case
  structure or machinery for content that isn't in the mathematics, the
  statement claims more than the proof produces; tighten the *external*
  statement rather than build proof machinery for the phantom cases.
  This is the inverse of the P4 API-lock pattern (API-lock *loosens
  internal* interfaces for incremental closure; statement-correction
  *tightens the external* interface to match what's proved).
* **Too weak → strengthen.**  When a statement's hypotheses are too weak
  to make the conclusion *sound* (the conclusion can fail under the stated
  hypotheses), strengthen the hypothesis class.  A green build does not
  protect you here (the body may be sorry'd, or the unsoundness only bites
  a consumer); soundness is a property of the *statement*, checked by
  asking "can I build a model of the hypotheses where the conclusion
  fails?"

**Empirical confirmation** (3 sightings):

1. **Conclusion too strong → weaken** (`vlasovWellPosedness`, commit
   `de135c7`): the `∃!` over all `t : ℝ` forced ~30 lines of `t < 0`
   case-split machinery for a *forward* Cauchy problem.  Restated to
   forward-only `∃` on `Ici 0` (matching Dobrushin 1979); the phantom
   machinery vanished.
2. **Hypotheses too weak → strengthen** (`dobrushin_uniqueness_On`, commit
   `94d44a9`, 2026-05-31): stated over the weak `IsVlasovSolutionOn` class,
   whose open-interval weak PDE leaves the endpoint measures `f T`, `g T`
   free — so the closed-window W₁-continuity the Gronwall step needs is
   *not a consequence* (a weak solution may jump at `T`).  The obvious
   placeholder would have banked a false statement.  Strengthened to
   `IsLagrangianVlasovSolutionOn` (flow witness pins the endpoints via the
   closed-window pushforward); plan-consistent, zero upstream cost.
3. **Hypotheses too strong → weaken — *the universal-`t` over-strength
   instance*** (placeholder instances + `vlasovVectorField_lipschitzWith`,
   commit `21dbaf7`, 2026-05-31): helper lemmas whose bodies use data only
   at a single `t` nonetheless quantified `[∀ t, IsProbabilityMeasure (ρ t)]`
   universally.  This is *not a new theme* — it is the too-strong direction
   of M2 applied to *hypothesis signatures* (as sighting 1 applies it to
   the *conclusion*).  The abstract placeholder's universal instances were
   weakened to window-explicit `∀ t ∈ Icc 0 T, …` (weakest-sufficient);
   `vlasovVectorField_lipschitzWith` itself was left universal (≥3 consumers
   → clamp instead, per L11, rather than restate).  The general tell:
   a hypothesis quantified more broadly than the body consumes is
   over-strong, and the right fix is to weaken the *quantifier* to what's
   actually used.
4. **Hypotheses too strong → weaken — *the encoding-artifact / overclaim-by-
   restriction instance*** (#11 M-fixed-point, decision 2026-06-01, commit
   `72af201` arc): the constant-`M` `VlasovMeasureCurve` curve space forces a
   fixed-point equation in `M` (need `M` bounding a flow whose growth depends on
   `M`), which can only be closed by adding a data-dependent smallness hypothesis
   `B·(M_f₀+1)<1` to the marquee.  That hypothesis is **not in Dobrushin's
   theorem and not needed by the project's own contraction** (the contraction
   ratio `q` is already `M`-free — verified).  So the over-strength is an
   **artifact of an encoding choice** (constant-`M` field, itself downstream of
   the KR-dual W₁ needing finite moments), not of the math.  Fix: **fix the
   encoding** (moment as a time-dependent envelope `M(t)`), not the statement.
   The tell distinct from sightings 1–3: the over-strength does not show up as
   "proof needs phantom machinery" or "quantifier broader than the body" — it
   shows up as *"the only way to close the proof is to add a hypothesis the
   reference theorem lacks."*  When closing a proof seems to *require* narrowing
   the theorem below the known result, suspect the encoding, not the math.
   **Forward-compat with a deferred regime (here W̄) is a secondary bonus, never
   the primary reason** to pick the encoding fix — see the watch-list entry on
   future-proofing-as-secondary.

**Operational rule**: when a statement and its proof disagree, ask which
direction the disagreement runs.  Phantom proof-machinery for absent
content ⇒ the conclusion (or a hypothesis quantifier) is too strong, weaken
it.  A conclusion that can fail under the stated hypotheses ⇒ the
hypotheses are too weak, strengthen them.  Both are *statement-correctness*
fixes — a metric axis distinct from sorry-count, and genuine
research-artifact value (the formalisation surfaced and corrected a
statement↔content mismatch).

### M3. Static-self-consistency artifacts dissolve under the moving boundary; genuine analytic constraints do not

**Principle**: a smallness constraint that arises from a *static* construction
forcing some construction parameter to bound its own dynamically-generated
growth — a self-consistency / fixed-point in the parameter — is an **artifact**.
It dissolves when the construction is rebuilt on the sharp *time-local* (Gronwall)
a-priori bound: feed the dynamic expansion, not the worst-case static estimate,
and the fixed-point evaporates.  A smallness constraint that arises from a
*genuine analytic mechanism* — a contraction ratio `< 1`, an envelope-closure
inequality — is **real**: it does NOT dissolve and must be carried (it is the
deferred W̄-consolidation target, not removable in W₁).  **[2026-06-07: the
parenthetical "not removable in W₁ / W̄ target" is CORRECTED — see the refinement
block at the end of M3.  Contraction/envelope ARE removable in plain W₁ by the same
small-`δ`-per-window boundary; the real W₁-vs-W̄ split is moment-tracking-vs-moment-
free.]**

**The boundary is the load-bearing half** (without it the lesson over-applies):
one must NOT try to dissolve genuine contraction/envelope constraints (`hTL_con`,
`B(T)<1`) the same way — they are not self-consistency artifacts; the moving
boundary leaves them exactly where they are.

**Empirical sightings — the artifacts** (one pathology, two guises):
* **Moment fixed-point** (option 2): a *constant* `M` must bound a flow whose
  moment growth depends on `M` — statistical self-consistency.  Dissolved by the
  time-dependent envelope `m(t)` (Pieces A/A.2/A.3).
* **PL-buffer `hTL_PL` = `L·(T+1)²<1`**: a *fixed radius* `R` must bound a flow
  whose force-expansion depends on `R` (the single-ball Picard-Lindelöf `hR`:
  `… + M·(T+1)² ≤ R` with `M = ‖∇W 0‖ + L·(R + …)`, so `M ∝ R`, giving
  `R(1−L(T+1)²) ≥ N_z` for *any* finite `R`) — spatial self-consistency, the
  *identical* trap in a different costume.  Dissolved by a fixed-`δ` N-window
  reconstruction on the Gronwall a-priori bound (each short window PL-feasible
  with no `T`-smallness; Piece A chains them globally).
* (Earlier static-over-strength siblings: `q<1`-because-fused, universal-`s`,
  `HasDerivWithinAt`-over-strong — all static-construction artifacts removed by
  the right dynamic/localized form.)

**The genuine constraints — NOT artifacts, carried**: `hTL_con` (measure-space
contraction ratio `<1`) and `B(T)<1` (envelope closure, A.3).  First-order
identical (`≈ L·T`) but independent (numerical near-counterexample); the W̄
refactor's target, not dissolvable in W₁.

**Diagnostic — artifact vs. genuine**: trace the constraint's unfold site.  If it
makes a *construction parameter* (radius, constant moment bound) positive /
large-enough to contain its own growth → **artifact** (dissolve via the moving
boundary).  If it makes a *contraction ratio* `<1` or an *envelope inequality*
close → **genuine** (carry; W̄ target).

**Gate corollary (the cost of the cure)**: the moving-boundary dissolution of a
construction-parameter artifact is a *reconstruction of the construction node*
(here: rebuild the per-ball flow as a fixed-`δ` N-window), not a localized
parameter-swap — because the self-consistency is intrinsic to the static node's
shape (the single-ball `hR`), not to the *choice* of the parameter.  Read the
unfold site's host before sizing: a parameter-swap that leaves the static node
intact re-generates the same constraint.

**Read-the-construction-not-the-interface (the gate corollary proving itself,
2026-06-01, first use)**: the read that checks *where a constraint lives* must
read the **construction**, not the **interface**.  `exists_vlasov_perz_trajectory`'s
*interface* (its conclusion: `γ` + ODE + boundary) was clean — no `R`, no
`(T+1)²` — which is exactly what made "swap the R-selection" sound right.  The
constraint lived **two levels down**, in the per-ball flow's `hR` geometry, and
was re-generated for *any* finite `R`.  A clean interface says nothing about
where a static self-consistency hides; only reading the construction body does.
**The level is not fixed**: a constraint can hide one level *below* where you
expect (here: in `hR`, not the R-selection), and — symmetrically, the trap to
watch when *rebuilding* — one level *above* (in the window-**count** compounding
across an N-window chain, not the per-window feasibility).  Before sizing a
reconstruction, read for both: per-window `hR` on a fixed `δ` must be satisfiable
*and* chaining `⌈(T+1)/δ⌉` windows must not re-accumulate a smallness (the moment
envelope must re-anchor per window).  Found in the opening read, this is cheap;
found at line 250 of the rebuild, it is the mid-construction refutation the gate
exists to prevent.

**Refinement + Phase-C way-forward (2026-06-07, from the Dobrushin §5–6 reference read
[`Dobrushin79.pdf`] + four Phase-C scoping agents over `CharacteristicFlow.lean`).**

*The correction.*  M3's "genuine contraction/envelope constraints are not removable in
W₁ / are the W̄ target" claim (above, and in the **Diagnostic** and **genuine
constraints** paragraphs) is **over-pessimistic**.  Dobrushin 1979 §5–6 imposes **no
smallness on `L` at all**: the per-window contraction `γ(|Δ|)<1` (eq. 5.16) is forced by
**shrinking the window `|Δ|`**, not by `L`-smallness, and `γ(δ)→0` as `δ→0` for *any*
fixed Lipschitz constants.  So `hTL_con` (`L·(exp T−1)<1`) and the envelope `B(T)<1` are
**offset-free** (`B(0)=0`, continuous increasing) and **dissolve in plain W₁ by the same
moving boundary — small `δ`-per-window — that the PL-buffer needs.**  They are *not* a
W̄-only target.  (The "first-order identical but independent" point about con vs. env
stands; only the "not removable in W₁" classification is wrong.)

*The real distinction.*  W₁-vs-W̄ is **moment-tracking-vs-moment-free, not
removable-vs-not.**  Dobrushin uses the *bounded* ground metric `ρ=min(dist,1)` (eq. 5.1)
solely so that `ρ̄≤1` makes the force-Lipschitz estimate (5.6) hold from `‖∇W‖_{C¹}`
alone with **zero moment bookkeeping** — that is the *only* thing boundedness buys.
Plain W₁ (the project's unbounded `wasserstein1`) instead must **carry a first-moment
envelope `M(t)` across windows** (the existing `HasFiniteFirstMoment` / flat-`max`
machinery).  `M(t)` grows like `exp(C·L·t)` but stays *finite on every finite interval*,
which is all W₁-finiteness of the force estimate requires — and forces **no** `L`-
smallness.  So W̄ is *convenient* (gives Dobrushin's moment-free Banach-per-window proof
verbatim) but **NOT essential** for arbitrary-`L` global well-posedness.

*What survives unchanged (the artifact + gate corollary were confirmed).*  The PL-buffer
`L·(T+1)²<1` is a genuine static-construction artifact with the additive `+1`: it traces
to `exists_vlasov_extend_one_window`'s **fixed `[t_start, t_start+1]` bound interval**
(`CharacteristicFlow.lean:1616`), propagating into `V_max` and the R-selection
`N_z/(1−L·(T+1)²)`.  The **gate corollary** holds — dissolving it is a *reconstruction of
the per-window node* (adaptive `[t_start, t_start+δ]` → R-selection `N_z/(1−L·δ²)`,
threshold `T_0_PL : 1/√L−1 ⇒ 1/√L`, positive for **all** `L`), not a cheap surgery.  The
window-**count** compounding the gate warns about does NOT bite here: moment accumulation
is already **flat-`max`** (no compounding) and the window length `T_0(L)` is
**moment-independent**, so `⌈T_target/T_0⌉` stays finite for any `L` and there is no
per-window moment-blowup to re-anchor.

*Net Phase-C plan (potential way forward — plain-W₁, no W̄):*
1. **Reconstruct the per-window flow node** (`exists_vlasov_extend_one_window` →
   adaptive-`δ` bound interval; propagate through `exists_vlasov_characteristicFlow` +
   the R-selection) to dissolve `(T+1)²` → `δ²`.  ← the single load-bearing piece.
2. `LocalSmallness_PL_buffer` → `L·T²<1`; recompute `T_0_PL` dropping the `−1`.
3. Strip `hL_lt : L<1` from `vlasovWellPosedness_forward` (`:11247`), `_uniqueness`
   (`:12633`), `_universal_existence` (`:12701`), `vlasovWellPosedness` (`:13014`).
4. The contraction/envelope (small `δ`) and the flat-`max` moment envelope carry
   arbitrary `L` as-is.
5. Re-cert `#print axioms` (expect `[propext, Classical.choice, Quot.sound]` to hold) +
   an `example` instantiating the marquee at some `L ≥ 1`.
W̄ remains a legitimate *alternative* (moment-free, Dobrushin-verbatim) but is now known
to be optional, not required.

*Process note for whoever opens Phase C:* the window-machinery agent reported "3 boundary
sub-sorries in `_glue_step`" — those are **historical docstring prose**, not live sorries
(the project is certified 0-sorry; `dobrushin` is axiom-clean and depends on the full
gluing chain).  Trust `#print axioms`, not in-file "sorry'd" comments (cf. the stale
"MathlibTODO_ are sorry'd" note that `#print axioms` also disproved).

**Phase-C surgery brief (atom-level verified, 2026-06-07).**  Diagnostic-mode read of the
actual construction (P1/P6) confirming the plain-W₁ plan above and *correcting* an
over-optimistic in-file note.  The `L<1` restriction has **exactly one** structural origin —
the `(T+1)²` in the PL-buffer — and the reconstruction site is the M3-predicted node, not the
lighter consumer-swap the in-file note claimed.

* **The propagation chain (root→marquee), with line numbers in `CharacteristicFlow.lean`:**
  1. `exists_vlasov_extend_one_window` (L1604) — **the root**: `hbound` over the fixed
     `[t_start, t_start+1]` (L1616); `δ = min 1 ((a/2)/((V_max+a+M)+1))` (L1620).
  2. `exists_vlasov_characteristicFlow` (L2004): `hR : … + M·(T+1)² ≤ R` (L2031), `hbound`
     over `[0, T+1]` (L2032), `V_max = ‖z₀.2‖+a/2+M·(T+1)` (L2057).  Inductive-body `(T+1)`
     sites at L2138, L2231–2274, L2587–2607.
  3. `exists_vlasov_perz_trajectory` (L4624): consumes `hTL_PL`; `R := N_z/(1−L·(T+1)²)` (L4696).
  4. `LocalSmallness_PL_buffer L T := L·(T+1)² < 1` (def L4267).
  5. `vlasovWellPosedness_forward` (L11240): `T_0_PL = 1/√L − 1` (L11261); the discharge algebra
     `L·(T_0+1)² = (1+√L)²/4 < 1 ⟺ √L < 1 ⟺ L < 1` (L11329–11338).

* **P5 correction — the in-file note at `exists_vlasov_characteristicFlow` L1994–2003 was WRONG**
  (now corrected in-place).  It claimed a "localized consumer swap, not a rebuild": re-consume
  `exists_vlasov_characteristicFlow` with a short `T := δ` to discharge `hR` at `L·δ² < 1`.  But
  the `+1` is **hardcoded in this theorem's own `hR`/`hbound`** (inherited from the root's unit
  force-window), so `T := δ` gives `hR : … + M·(δ+1)² ≤ R`, i.e. `L·(δ+1)² < 1`, which **still
  forces `L < 1`** (since `(δ+1)² > 1`).  Verified by tracing the `hR` *shape*, not the interface
  — exactly the M3 gate-corollary "read the construction, not the interface."  Dropping the offset
  to `L·δ²` genuinely requires reconstructing the root node.

* **Two confirmations that make the rest cheap:**
  1. The `min 1` in `δ` (L1620) is **redundant**: denominator `(V_max+a+M)+1 ≥ a+1`, so
     `δ ≤ (a/2)/(a+1) < 1/2 < 1` always.  The reconstruction is therefore "state the force-window
     as `[t_start, t_start + (a/2)/((V_max+a+M)+1)]`" (the un-`min`'d δ — all signature inputs, so
     expressible in the hypothesis) instead of the loose unit window.  Trajectories / Picard /
     gluing are untouched; it tightens a *stated* window from the loose unit bound to the actual
     step δ.
  2. Contraction (`T_0_con`, L11262) and envelope (`T_0_env`, L11268) thresholds are positive for
     **all** `L > 0` (L11287–11295); they use `hL_lt` only *cosmetically* — the `max(1,L)=1`
     simplification at L11344.  For `L ≥ 1` recompute with the `max(1,L)=L` branch (contraction
     becomes `exp(L·T_0)−1 < 1`, threshold `log 2 / L`, positive for all `L`).  M3's "contraction /
     envelope carry arbitrary L" is verified — only the PL-buffer needed surgery.

* **Net edit list (load-bearing piece first):**
  (1) restate `exists_vlasov_extend_one_window`'s force-window to adaptive δ + drop `min 1`;
  (2) propagate `(T+1) → T` (and `V_max`, the `Icc 0 (T+1)` force-window) through
  `exists_vlasov_characteristicFlow`'s inductive body — the bulk of the work;
  (3) `LocalSmallness_PL_buffer → L·T² < 1`; `perz_trajectory` `N_z`/R-selection `(T+1)² → T²`;
  (4) `T_0_PL → 1/√L`; the `(1+√L)²/4` discharge algebra → `1/4 < 1` (all `L`); replace the
  `max(1,L)=1` simplifications (forward + `_uniqueness` + `_universal_existence`) with the
  general `max(1,L)=L` branch;
  (5) strip `hL_lt : (L:ℝ) < 1` from the four marquee theorems (L11247, L12633, L12701, L13014);
  (6) re-cert `#print axioms` + an `example` at some `L ≥ 1`.
  Develop step (2) against an importing scratch leaf (L12) — `CharacteristicFlow.lean` is a slow
  host and the body restate will take many iterations.

### M4. Removing a chained/tiled smallness restriction: EXACT tiling, not naive offset-drop — and certify by instantiating the forbidden value

**Principle**: when a smallness restriction (`parameter < threshold`) is imposed
by a construction that CHAINS or TILES short pieces to cover a target interval,
and you remove the restriction by shrinking the pieces, the naive move — "drop
the additive offset in the constraint" — can produce a threshold that is
*general-looking but secretly data-dependent*, because the chain OVERSHOOTS the
target by a reach-slack the interface does not expose.  The correct fix is EXACT
tiling: pick the piece width so the chain lands EXACTLY on the target
(`δ' = T/N`, `N·δ' = T`), killing the slack.  The restriction is then genuinely
removed — and you certify that by instantiating the construction at a parameter
value the old restriction FORBADE.

**The trap, concretely** (Phase C, the `(T+1)² → T²` removal, 2026-06-07): the
per-window flow chained `N = ⌈T/δ⌉` *fixed-width* windows, OVERSHOOTING `T` to
`N·δ ∈ [T, T+δ)`.  Smallness `L·(T+1)²<1` (the `+1` an artifact of a fixed unit
force-window).  Naive fix: "drop the +1 → `L·T²<1`, threshold `T<1/√L`, positive
for all L — done."  **WRONG**: re-deriving on the overshoot gives `L·(T+δ)²<1`,
threshold `T < 1/√L − δ_max` where `δ_max` depends on the problem data
(`a, M, V_max`) — positive for small `L`, but NEGATIVE for large `L` (when
`δ_max > 1/√L`).  The naive fix MOVES the wall (data-dependent), it does not
remove it; it compiles, strips the binders, passes a naive build, and *still*
secretly requires small `L`.  EXACT tiling `δ' = T/N` (so `N·δ' = T`, no
overshoot) lands the clean `L·T²<1`, threshold `T<1/√L`, positive for ALL `L`.

**How you CATCH it** (M3 gate corollary, applied to the threshold): read the
construction's ACTUAL reach (the overshoot to `N·δ`), not the interface's stated
bound ("covers `[0,T]`").  The interface says "covers `[0,T]`"; the construction
reveals it builds on `[0, N·δ]` and restricts — the slack lives in that gap.
Reading only the interface ("just drop the +1") misses it; reading the
construction surfaces it *before any code*.

**How you CERTIFY removal** (the acceptance test): a green build with the
restriction-binder stripped is NOT sufficient — a path could still secretly need
the restriction (a threshold silently data-dependent), surfacing only at a large
parameter value.  The certification is an `example` instantiating the
construction at a value the OLD restriction FORBADE (here `L = 2 ≥ 1`); it
typechecks iff the restriction is genuinely gone.  Binder-strip *permits* the
forbidden value; the `example` *certifies* it — the same permit-vs-certify split
as P10 (build-permits vs audit-certifies) and B's `#print axioms`.

**Empirical confirmation** (3 sightings — promoted from the watch-list at the
third): (1) Stage 1.9 `L·(T+1)²<1` diagnosis — additive offset structurally fatal
(`(T+c)^α ≥ c^α` forbids `L ≥ c^{−α}` regardless of `T`); (2) Stage 2b part 3
predicate-split confirmation (the discriminator fired: the offset-fatal
prediction matched the breakage shape); (3) Phase C `(T+1)²→T²` removal via exact
tiling, certified by the `L=2` example (`9d47480`).  The first two established
"additive offsets are fatal"; the third added the RESOLUTION (exact tiling, NOT
the predicted W̄ refactor), the general-looking-but-data-dependent trap
(`L·(T+δ)²`), and the forbidden-value acceptance test.

**Operational rule**: when removing a chained/tiled smallness restriction —
(a) read the construction's actual reach (overshoot?), not the interface's stated
bound; (b) use exact tiling (`δ'=target/N`) to kill the slack, not a naive
offset-drop; (c) certify with an `example` at a previously-forbidden parameter
value, not just a green build with the binder stripped.

**Generalisation**: M4 is M3 (artifact dissolves under the moving boundary; read
the construction not the interface) specialised to the THRESHOLD of a chained
construction, fused with B's certify-don't-assert (the forbidden-value
instantiation is the threshold's `#print axioms`).  Applies to any "remove a
smallness/largeness restriction by chaining short pieces": the overshoot-slack
trap and the exact-tiling fix recur.

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

### B3. Conjunct shape: lower bound = consumer-need, upper bound = producer-capacity

**Principle**: when enriching a predicate with a new conjunct (B1/B2), the
conjunct's *strength* is bounded **below** by what the consumer needs and
**above** by what *every* producer can supply.  Weakest-sufficient (M2) lives
in that intersection.  Reading only the consumer fixes the lower bound and can
leave you at an over-strong shape that some producer cannot supply — which
breaks the producer mid-surgery.  Reading only the producers risks
under-strength.  **Read both before fixing the conjunct.**

**Empirical confirmation — first clean sighting** (the #13 B2 enrichment,
2026-06-01, commit `f113581`): the conjunct shape was first set to
`HasDerivWithinAt` by reading the *consumer* (item 5's USC takes `HasDerivAt`,
so the window analog "needs the derivative").  That reasoning was
correct-for-the-right-reason about the consumer and **still wrong**, because it
never checked the *producers*.  The pre-surgery Stage-C read supplied the
missing half: Stage C carries boundary regularity as `ContinuousOn (Icc 0 T)`
(directly) + `HasDerivWithinAt _ (Ici s) s` (on `Ico`) — and the `Ici`/`Ico`
form does **not** convert to the two-sided `Icc` `HasDerivWithinAt`.  So no
producer could supply the over-strong shape; the upper bound was `ContinuousOn`.
The intersection (and the M2-weakest-sufficient point) was `ContinuousOn`, which
also turned out sound for the consumer (USC of W₁ comes from flow continuity,
not its derivative — item 5's `HasDerivAt` was itself over-strong).  Flipping
to `ContinuousOn` *simplified* the surgery rather than enlarging it.

**Operational rule**: before committing a predicate-enrichment conjunct, read
(a) the consumer's genuine need (lower bound, often weaker than the existing
consumer's *stated* hypotheses, which may be over-strong) **and** (b) every
producer's available data (upper bound).  The conjunct goes at the
weakest-sufficient point in `[lower, upper]`.  This is the producer-side
complement to the consumer-need rule; the cost is one extra read (the
producer-capacity read), and it is the read that catches "over-strong-but-
unsupplyable" *before* the atomic batch rather than mid-break.

## Watch-list

Candidates accumulating sightings, not yet promotion-ready under
the three-sighting threshold (with the discipline pairing of
"promote within ~5 sessions of reaching threshold" to prevent
indefinite watch-listing):

* **Clean-interface-over-a-load-bearing-sorry'd/over-strong node → the
  proved-modulo-sorry sweep is a SCHEDULED gate, not optional hygiene** (process
  discipline, 2 sightings, 2026-06-01).  **Pattern**: a declaration whose
  *interface* (signature/conclusion) is clean and green nonetheless stands on a
  dependency that is sorry'd or over-strong *in a load-bearing spot* — the
  interface hides the obligation, so "this side bottoms out cleanly" reads true
  while the real work sits one or two levels down.  **Sightings**: (1) the
  `_finalAssembly`/#11 seam (green-modulo a sorry in the load-bearing spot); (2)
  the per-ball flow `exists_vlasov_characteristicFlow` (L1552) — sorry'd,
  mandatory, the marquee's existence side bottoms out through it, surfaced only
  by reading the *construction* not the interface (M3 gate corollary).  **Why it
  promotes the sweep**: "the marquee bottoms out cleanly" has now been wrong
  *twice in the same way*; a third instance is cheaper to find by a deliberate
  `(c)` proved-modulo-sorry sweep (which green declarations rest on a sorry'd /
  over-strong dependency the interface hides) than by stumbling into it at
  line 250 of some later session.  **Operational rule (forming)**: schedule the
  sweep as a *gate before declaring a side (existence / uniqueness) finished*,
  not as discretionary cleanup — the recurring shape has earned it.  This is the
  scheduling sharpening of P10 (build-permits-vs-audit-certifies): P10 says
  green ≠ certified; this says *when* the recurring shape makes the audit
  mandatory.  Trigger: 1 more sighting → promote (likely as a P10 addendum or a
  standalone P-series "audit-as-scheduled-gate").

* **Future-proofing-as-secondary — present-faithfulness is the primary axis for
  scoped work** (process discipline, flagged 2026-06-01, user-corrected).
  **Failure mode**: when a present scoping decision has a clean forward-
  compatibility story with a *deferred* regime, the forward-compat becomes the
  *primary* stated reason for the choice — turning a scoped decision into a
  referendum on the unscheduled future.  This is appeal-to-future-proofing; it
  re-subordinates a present fix to a regime you have deliberately deferred, and
  it picks the *wrong primary axis* (the decision then gets re-made by "is it
  X-forward" instead of "is it right now").  **Empirical sighting (1)**: #11
  M-fixed-point — I framed option 1 vs option 2 as a "referendum on W̄"
  (the deferred truncated-metric regime), when the load-bearing reason for
  option 2 is **present-tense faithfulness in the W₁ regime being formalized**
  (option 1 adds a hypothesis Dobrushin's theorem lacks — see M2 sighting 4);
  W̄-compat is a *genuine bonus* but the *second* reason.  User flagged this as
  a recurring pattern ("caught you before") — same family as the M2/weakest-
  sufficient overbuild guard.  **Fix**: when a scoped choice has both a present-
  correctness reason and a forward-compat reason, **lead with the present one**;
  state forward-compat as the secondary bonus, never the justification.  If the
  *only* reason for the work is forward-compat with a deferred regime, the work
  itself is probably out of scope.  **Promotion**: P-series candidate (decision-
  framing discipline); needs 2 more cataloged sightings with commits (the
  user's asserted priors are not yet catalogued — P5: verify before promoting).

* **Framework ossification — lessons must CHANGE AN ACTION, not just be
  cited** (meta-discipline, flagged 2026-06-01).  The framework grew a lot
  this arc (B3, M2, L11, the P7-P10 sequencing cluster) and it paid — every
  lesson fired changed a concrete move: B3 flipped a conjunct, M2 realigned a
  hypothesis class, P5 held an edit at a tail, L11 chose clamping over a
  pointwise restatement.  As the count climbs, the risk shifts from *missing a
  lesson* to *the framework being consulted as ritual rather than as
  load-bearing*.  **The tell it is still load-bearing**: each time a lesson is
  cited in a writeup, it should have *altered* something done — a tactic, an
  ordering, a hold, a statement.  **The tell it has started ossifying**: a
  session where lessons get name-dropped in the report but did not change any
  action taken.  When that appears, apply M1/weakest-sufficient *to the
  framework itself* — keep what is load-bearing, prune what has become
  decorative commentary.  Not a problem now (every lesson this arc changed a
  move); the thing to watch as the lesson count grows.  Trigger: first session
  where a cited lesson demonstrably changed nothing → prune pass.

* **Statement-level mismatches between claimed and proved → PROMOTED
  to M2** (2026-05-31).  Reached 3 sightings across both directions:
  conclusion-too-strong (`vlasovWellPosedness` forward-only refactor,
  `de135c7`); hypotheses-too-weak-for-soundness (`dobrushin_uniqueness_On`
  → Lagrangian class, `94d44a9`); hypotheses-too-strong (universal-`t`
  over-strength on pointwise-true helpers, `21dbaf7`).  See M-series M2
  ("Match the statement to the mathematics — bidirectional"); the
  universal-`t` over-strength is recorded there as an *instance* of the
  too-strong direction, not a separate theme.  The "statement correctness"
  metric axis (distinct from declaration / sub-sub-sorry counts) is part
  of M2.
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
* **Local-clamping technique → PROMOTED to L11** (2026-05-31).
  Reached 3 sightings (Phi_step's clamped flow; `VlasovMeasureCurve.extend`;
  `wassersteinGronwallCoupling_derivBound_via_pureFA_On`, `4eb294c`).
  Landed as L-series (tactical Lean pattern), the local-bridge companion
  to B1's enrich-vs-bridge decision; see L11.
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
  fatal → PROMOTED to M4** (2026-06-07): reached the third sighting at
  Phase C (the `(T+1)²→T²` removal via exact tiling, certified by the
  `L=2` example, commit `9d47480`).  The third sighting was NOT the
  predicted W̄ refactor — it was the *resolution* of the very offset
  the entry diagnosed, which is why it promoted with the exact-tiling
  fix + the general-looking-but-data-dependent trap (`L·(T+δ)²`) + the
  forbidden-value acceptance test folded in.  See M-series M4.  Original
  watch-list text retained below for the sighting history.

  **Additive offsets in smallness constraints are structurally
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

  **Update (Stage 2b part 3, 2026-05-31)**: now at 2 sightings —
  the original Stage 1.9 sighting (`+1` additive offset diagnosis)
  plus the Stage 2b part 3 confirmation by actual constraint
  correction (predicate split into PL-buffer with `(T+1)²` and
  contraction with `exp((max 1 L)·T)`, retiring the false single
  predicate).  Discriminator at the second sighting fired correctly:
  the additive-offset-is-structurally-fatal prediction matched the
  actual breakage shape.  **Near-locked for M-series promotion** at
  a third structural sighting of the pattern in a different
  manifestation (probably the W̄ refactor when it lands — different
  smallness constraint family, same additive-offset-vs-multiplicative-
  shape distinction).

* **Property-based proof discipline for forward-looking closes —
  `wasserstein1` touches proofs only through its abstract
  properties, never through its `⨆`-definition**: 1 sighting
  (formulation post-Stage-2b-part-3, 2026-05-31).  Diagnostic: when
  closing a sorry whose proof would naturally `simp [wasserstein1]`
  or `unfold wasserstein1` to reason about the dual sup directly,
  the resulting close is W̄-reopened (when the eventual truncated-
  metric W̄ refactor replaces `wasserstein1`'s concrete form, the
  unfold-based proofs must be re-derived).  A close that uses only
  the four named property lemmas — non-expansion under Lipschitz
  pushforward (`wasserstein1_le_of_lipschitz_map`), triangle, zero-
  iff-equal (the separation lemma to be banked), KR-dual lower
  bound — is W̄-survivor by construction, because W̄ satisfies all
  four.

  **Empirical pattern (the one to test at subsequent sightings)**:
  property-only closes are durable across refactors of the
  underlying metric, but cost vigilance per proof (every `simp` that
  wants to expand `wasserstein1` is a discipline checkpoint).  The
  cost-benefit: friction now ↔ free extension later, proportional
  to how consistently the discipline is paid.

  **Discriminator at subsequent close-sightings**: does the proof
  body reference the property API only, or does it `simp
  [wasserstein1]` / `unfold wasserstein1` / reason about the `⨆`-form
  directly?  Property-only = W̄-survivor; unfold = W̄-reopened.
  Promotion at 2-3 sightings WITH discriminator-validated separation
  of survivor-vs-reopened on actual subsequent closes.

  **Why not promote now**: the rule is stated cleanly but hasn't been
  TESTED.  P5 (verify framework's pattern-extrapolations atom-by-atom)
  says wait for empirical confirmation: the next session's separation
  lemma is the first test, item 3's Dobrushin uniqueness body is the
  largest test.  If both close property-only, the rule is empirically
  earned at 2-3 sightings.  Promote to M-series likely
  ("predicates/proofs match the mathematical structure, not the
  concrete representation" — same M1-recursion reasoning that landed
  the LocalSmallness predicate split).  See planning-notes commit
  TBD for the full operational rule + separation-lemma application.

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
