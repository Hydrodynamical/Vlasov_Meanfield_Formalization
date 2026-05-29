# Project memory — Vlasov formalization

Lessons that should persist across sessions. Brief, terse,
keyed to the failure mode they prevent.

## Agent-design lessons

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

### L8. Mathlib's `_map_measure` family has `g ∘ f` ↔ `fun z => g (f z)` syntactic mismatch

**Failure mode**: `integral_map`, `integrable_map_measure`, and
`lintegral_map` produce conclusions in the form `Integrable (g ∘ f) μ`
or `∫ x, g x ∂(μ.map f) = ∫ x, (g ∘ f) x ∂μ`, while our hypotheses are
typically written as `Integrable (fun z => g (f z)) μ` or
`fun z => g (f z)`. Definitionally these are equal, but Lean's `rw`
doesn't match `(fun z => g (f z))` against the pattern `(g ∘ f)` (or
vice versa) — leaving the rewrite step stuck with "Did not find an
occurrence of the pattern."

**Empirical confirmation**: 2026-05-29 Stage 2b W₁-bound proof's two
`rw [← integrable_map_measure ...]` calls failed for this reason. Also
surfaced earlier in Stage C's chain-rule work (where `(diff ∘ flow)` vs
`fun z => diff (flow z)` was the same mismatch).

**Fix**: use `show ... from ...` to bridge the syntactic form, or use
`convert` instead of `rw` when consuming `_map_measure` family lemmas.
Example: instead of
`rw [← integrable_map_measure hφ_meas (h_meas s)]; exact h_phi_int_s`,
write
`have : Integrable (fun z => φ (charX s z)) f₀ :=
   (integrable_map_measure hφ_meas (h_meas s)).mp h_phi_int_s; exact this`
(which uses the iff-version's `.mp` projection directly).

**Generalisation**: when consuming Mathlib's `_map_measure` family,
expect the source-vs-target syntactic forms to need an explicit bridge.
The general pattern: `_map_measure` lemmas in Mathlib are written in
"point-free" `(g ∘ f)` form, project code usually writes "point-full"
`fun z => g (f z)` form, and the bridge is `show` / `convert` / `.mp` /
`.mpr` rather than `rw`.

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
