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
  (currently 600s default).
- Pre-supplied `proof_sketch` in the plan JSON — sketch fast
  path (§4.−1) skips much of the discovery work.
- Smaller helper lemmas via decomposer — each helper has its
  own shorter proof, finishes within budget.

The wall-clock bottleneck is a strictly better problem than the
name-churn-reverts-everything bottleneck — it represents the
prover making careful progress, just not finishing in time.

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
