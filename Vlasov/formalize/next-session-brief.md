# Next-session brief (as of 2026-06-05, HEAD = `d46feb3`)

Durable hand-off. Build green; **2 sorries** (Basic 1, Coupling 1, CharFlow 0).

## Where this lands — the surface is `{#2, B}`, and it maps onto the two goals

The deferred surface went 13 → 8 → 6 → 4 → 3 → **2**. The two remaining
sorries are not a to-do list; they are the two *user goals*, and those two
goals collapse to **one program** (see next section):

* **#2** (`MathlibTODO_cauchyW1_hasNarrowLimit`, Basic 1625) — Picard /
  Prokhorov narrow limit. In-project *under W̄*; needs Foundation A under
  plain W₁ (see below).
* **Foundation B** (`foundationB_optimal_coupling_exists`, Coupling 276) —
  the one OT attainment theorem Mathlib lacks; sole sorry-dependency of the
  mean-field marquee `dobrushin`. A genuine external, not an attack target.

The marquee — existence **and** uniqueness **and** mean-field — runs on the
single `dobrushin_integrated_flow_bound_On` core (force-estimate-free).

## The strategic finding (this session): the two goals are ONE program (W̄)

User goals, stated this session: (1) make everything hinge only on external
Foundation B, everything else sorry-free; (2) after that, remove the `L < 1`
restriction. **These are not sequential — they are the same W̄ move.**

* **#2's conclusion-shape read is DONE (verified, not labelled).** #2
  *concludes W₁-convergence*, not just narrow-limit existence: Basic 1588,
  `Tendsto (fun n => wasserstein1 (ν n) μ) atTop (𝓝 0)`. Its sole consumer
  `picard_iterate_bundlesAs_VlasovMeasureCurve` (CharFlow 6969) **re-exports
  that exact W₁-tendsto** as its own conclusion (CharFlow 6948/7003) and uses
  it to pin the Picard fixed point — **not weakenable** (the curve space and
  the contraction live in W₁). So under plain W₁, closing #2 sorry-free
  *requires the narrow ⟹ W₁ upgrade = Foundation A*, a **second** external.
  That contradicts goal (1). ⟹ **There is no "only B under plain W₁"
  milestone worth chasing.**
* **W̄ dissolves exactly that dependency.** Under the cutoff cost
  `c = min(dist,1)` the dual test class is *bounded* 1-Lipschitz, so W̄
  metrizes narrow convergence directly (Mathlib Lévy–Prokhorov / Portmanteau).
  A becomes Mathlib-or-near-Mathlib; #2 reduces to Prokhorov tightness
  (in-project) + moment-LSC. **A dissolves; #2 goes in-project.** (goal 1)
* **"Remove L<1" forces W̄ regardless.** The `L<1` restriction is the
  construction artifact — the `(T+1)²` *additive* smallness offset (M3
  artifact-vs-genuine; "additive offsets are structurally fatal" watch-list).
  Only the cutoff cost / moving-boundary program removes it. (goal 2)

So **doing goal 2 (W̄) delivers goal 1** — W̄ is the mechanism that makes
"only B" true *and* lifts `L<1`. The plan is already on disk:
`~/.claude/plans/clear-picture-now-the-starry-sparrow.md`.

## Next move — the W̄ program, Phase 1 = O2 cost-parameterization

Per the plan, the load-bearing prerequisite is the **O2 cost-parameterization**
(everything after rides on it landing green with zero consumer churn):

* Replace the concrete `wasserstein1` def with a cost-parameterized core
  `wassersteinCost (c)` over the oscillation test predicate; `wasserstein1 :=
  wassersteinCost dist`. Add the bridge `|f x − f y| ≤ dist x y ↔
  LipschitzWith 1 f`.
* Re-prove the 6 cost-generic property lemmas over `wassersteinCost c`. The
  bulk is **`wassersteinCost_le_of_lipschitz_map` (~50–80 lines)** — a genuine
  re-proof (rewrites Lipschitz-composition as cost-composition), NOT a
  one-liner. O2 total ~100–150 lines.
* Consumer churn near-zero **by property-only discipline** (the new def is only
  *propositionally* equal to the old; the only structural-touch sites are the
  6 API lemmas + 2 cost-coupled bridges).

Then: add `foundationA_*` (cost-generic) → A dissolves under W̄ → close #2
in-project. Add the W̄ def → moment lemmas unconditional → `L<1` lifts. Foundation
B stays the sole genuine external.

**Caveats to verify at W̄-time (do not pre-assume — plan flags both):**
1. The cutoff must reach B's *hard core* (optimal-coupling **attainment** under
   `min(dist,1)`: bounded-and-LSC ✓ + tightness ✓), not merely B's
   integrability side-conditions.
2. The `L<1` lift is the *artifact* `(T+1)²` offset, **not** the *genuine*
   contraction `B(T)<1` (M3 — the latter is carried; "all L" means
   local-in-time per L à la Dobrushin, not unconditional global).

## DONE log

* **6 → 4** (`a83fc35`): deleted orphaned #3/#4 + 5 dead helpers.
* **4 → 3** (`ca12381`): orphaned + deleted #7 via the marquee L=0
  producer-switch (`M_ρ` discharged by the affine `(1+T)·M_{f₀}` bound).
* **3 → 2** (`d46feb3`, this session): closed **#1**
  `bcEqualFromLipschitzEqual` by reducing to `μ = ν` —
  `thickenedIndicator δ F` is bounded **Lipschitz** (Mathlib
  `lipschitzWith_thickenedIndicator`), so the 1-Lipschitz hypothesis applies
  after scaling by `(K+1)⁻¹`; its integral → `μ F` as `δ→0`; limit-uniqueness
  + `ext_of_generate_finite` over the closed-set π-system gives measure
  equality. **Metric-agnostic (no `wasserstein1`) ⟹ W̄-survivor.** First-moment
  hypotheses turned out vestigial for this route (signature unchanged ⟹
  consumers untouched). Built clean first try (P1/P6 — atom-level reading
  loaded the whole route before drafting).
  Side effect: **`wasserstein1_eq_zero_iff_measure_eq` now fully sorry-free**
  (its only sorry'd dependency was #1) — the uniqueness path's separation step
  no longer routes through a placeholder.

## Marquee axiom footprints

* `vlasovWellPosedness` (existence) → sorryAx now traces to **{#2} only**.
  Monotone removal of #1 from the prior `{#1, #2}` certification (at
  `ca12381`); closing a fully-proved lemma can only *remove* a footprint
  entry. Re-run `#print axioms` for a fresh certification if precision needed.
* `dobrushin` (mean-field stability) → sorryAx = **Foundation B only** (unchanged;
  never depended on #1).
* `meanFieldLimit` → axiom-clean `[propext, Classical.choice, Quot.sound]` — but
  a **naming artifact** (see Standing items), not a B-free deliverable.

## Standing items (off the critical path — do not let evaporate)

* **`meanFieldLimit` — RESOLVED: naming-artifact, *with its consequence*.** A
  prior read (2026-06-05) concluded it is **CONDITIONAL**: it takes the
  Dobrushin stability estimate as a *hypothesis* (`hDobrushin`) and never
  discharges it (a one-line Grönwall composition), so its axiom-cleanness is a
  **naming artifact, NOT a B-free deliverable**.
  **Consequence (the load-bearing part):** the project does **NOT** currently
  have an unconditional, axiom-clean mean-field-limit theorem. The genuine
  mean-field deliverable is **`dobrushin` (proven modulo Foundation B)** plus the
  N→∞ convergence; `meanFieldLimit`'s cleanness is packaging. Do **not** let
  "`meanFieldLimit` is axiom-clean (resolved)" read as "the mean-field limit is
  axiom-clean." **No re-read needed** unless upgrading `meanFieldLimit` to the
  unconditional statement — which routes through B (wiring: discharging
  `hDobrushin` for the atomic empirical curve `μ^N` is not a direct `dobrushin`
  application — `μ^N`'s flow is Newton dynamics — so the integrated core is the
  route, but the wiring is a genuine gap).
