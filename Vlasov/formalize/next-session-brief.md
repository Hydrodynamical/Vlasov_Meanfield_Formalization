# Next-session brief (as of 2026-06-05) — Option 3 LANDED; B pinned to one labeled bridge

Build green (8251 jobs); **1 sorry** (`Coupling.lean:276`/body L291 =
Foundation B). Only `CharacteristicFlow.lean` changed this arc.

---

## THE LANDING (terminal milestone, certified `ab33346`)

Option 3 is done and probe-verified. **Everything mathematical in the project
now stands B-free; Foundation B is pinned to exactly one labeled conversion.**

* **`vlasovWellPosedness` (existence + uniqueness)** → `[propext,
  Classical.choice, Quot.sound]` — axiom-clean.
* **`dobrushin_meanfield_On`, `dobrushin_package_exists` (mean-field stability
  core, primal coupling metric)** → `[propext, Classical.choice, Quot.sound]`
  — **B-free**. Proved via Dobrushin's own method (1979 eq 6.8): the coupling-
  generic `dobrushin_integrated_flow_bound_On` run for *every* coupling π, then
  `le_iInf` (constant pulled through with `ENNReal.div_le_iff_le_mul`). No
  optimal coupling, no attainment.
* **`dobrushin` (all-dual W₁ headline, statement unchanged)** → `[propext,
  sorryAx, Classical.choice, Quot.sound]`. The `sorryAx` traces **only** to the
  single `wasserstein1_eq_coupling` (Foundation B) bridge — provably, because
  `dobrushin_package_exists` (the thing it `obtain`s from) is itself clean and
  the *only* other lemma `dobrushin` invokes is that bridge.

### The precise B framing (state it exactly; do not let it blur)

* **B is one labeled CONSUMER line**: `dobrushin`'s single
  `rw [wasserstein1_eq_coupling (f 0) (g 0) 0 hfm0 hgm0]`.
* **The sorry did NOT move**: it still lives in the bridge's dependency
  `foundationB_optimal_coupling_exists` (`Coupling.lean:276`, body `sorry` at
  L291), reached via `wasserstein1_eq_coupling → foundationB_coupling_le_dual →
  foundationB_optimal_coupling_exists`. "B isolated to one line" means one
  *consumer*-line in the dependency graph, with the sorry in the bridge's body.
* **B's role is exactly the dual↔coupling metric identification** (Kantorovich–
  Rubinstein hard direction / optimal-coupling attainment), and it is
  **dynamically inert**: needed only to state the headline in the literature-
  standard dual-W₁ form rather than Dobrushin's native coupling form. The
  footprint *proves* the dynamics, existence, uniqueness, and the mean-field
  *stability core* do not touch it.

This is the campaign's terminal form: Vlasov well-posedness (existence +
uniqueness) and the mean-field stability core are unconditional modulo Lean's
standard axioms; the single irreducible OT input is pinned to one dynamically-
inert metric-conversion bridge.

---

## Follow-ups (honestly gated — do NOT bank the optimistic version unread)

### (1) `meanFieldLimit` coupling variant — the interesting one (GATED on an hInit read)

`meanFieldLimit` (Basic:2599) is currently all-dual on BOTH the estimate
(`DobrushinStabilityEstimate`, Basic:2573) and `hInit`
(`wasserstein1 (μ^N_0) f₀ → 0`), so it routes through the all-dual `dobrushin`
(B-dependent corollary). A coupling variant would route through the **B-free
coupling core** — making the mean-field *limit itself* B-free.

**The gate (read this before banking "the mean-field limit is B-free"):** does
the B-free `meanFieldLimit` keep the *standard* initial-convergence hypothesis,
or a *strengthened* one?
* Coupling-convergence of initial data (`wasserstein1_coupling (μ^N_0) f₀ → 0`)
  is **stronger** than dual-W₁/narrow initial convergence (since `W₁_dual ≤
  W₁_coupling`). It is "natural for empirical measures" (they couple to the
  limit naturally) but is genuinely a stronger hypothesis than the literature's
  narrow/W₁ initial convergence.
* **The read**: does the easy direction (`wasserstein1 ≤ wasserstein1_coupling`,
  B-free) squeeze the *initial* convergence too — i.e. can narrow/W₁-`hInit`
  give `wasserstein1_coupling (μ^N_0) f₀ → 0` B-free? If YES → the mean-field
  limit is B-free with **standard hypotheses** (strong result). If NO → the
  B-free limit carries a **stronger coupling-`hInit`**, and the *standard*-
  hypothesis limit still routes through the all-dual `dobrushin` (B). That is
  the **same Option-1 trade (zero-axiom via hypothesis-strengthening) surfacing
  at the limit level** — the LHS-vs-hypothesis subtlety that has governed every
  metric-switch this campaign.
* Note the asymmetry that makes the squeeze plausibly-one-directional: the easy
  direction squeezes a *conclusion* LHS down (W₁_dual ≤ W₁_coupling) for free,
  but a *hypothesis* needs the convergence to hold in the stronger (coupling)
  metric — the wrong direction for the easy squeeze. So expect the read to land
  on "stronger coupling-`hInit` needed" unless the empirical-measure structure
  provides coupling-convergence directly. Read it; don't assume.

### (2) GC `wasserstein1_optimal_coupling_exists` — confirmed safe (grep-verified this session)

* **Callerless**: zero invocations project-wide post-refactor (its only caller
  was the old `dobrushin_meanfield_On`). ✓
* **Bridge-independent**: `wasserstein1_eq_coupling`'s proof uses
  `foundationB_coupling_le_dual` (a sibling consumer of
  `foundationB_optimal_coupling_exists`), **not** the attainment lemma — so
  deleting it does NOT break the bridge or relocate B. ✓
* Therefore safe to delete (trivial cleanup; touches `Coupling.lean`, needs its
  own build + commit). It is NOT "where B lives" — `foundationB_optimal_
  coupling_exists` (the sorry) is.

---

## The Dobrushin-paper perspective (durable context, 2026-06-05)

R. L. Dobrushin, "Vlasov equations," *Funct. Anal. Appl.* **13**:2 (1979),
pp. 115–123 (`Dobrushin79.pdf`, repo root). His metric ρ̄ (eq 5.3) is the
**primal coupling-inf** of the **bounded** cost `min(dist,1)` (eq 5.1) — the
coupling core now matches his primal form. His stability (Prop 4, eq 6.8) uses
ε-optimal / inf couplings, never attainment — which is why the B-free core is
faithful, not a compromise. No L<1: his smallness is on the time-interval
length, removed by chaining (§6). The bounded cost metrizes weak convergence
(p. 121) — relevant to the mean-field *limit* (Thm III).

## The horizon (separate arcs — NOT the current follow-ups)

1. **L<1 → global (Theorem I).** Window-chaining (§6); metric-independent
   (the `(T+1)²` offset lives in the ODE ball-geometry, per M3). Per-window
   moment re-anchoring is the hard part.
2. **Mean-field limit (Theorem III), unconditional.** Beyond follow-up (1)'s
   hInit question: "empirical measures μ^N of the N-particle Newton ODE are
   weak Vlasov solutions" (Dobrushin's elementary calc, currently a gap; μ^N's
   flow is Newton dynamics, so not a direct `dobrushin` application). Cleanest
   in W̄ (bounded cost metrizes weak convergence).
3. The eventual main theorem bundles **I (global) + Prop 4 (stability) + III
   (mean-field)**; part II (C¹ density regularity) is out of scope.

## DONE log

* **6 → 1** (`a83fc35`/`ca12381`/`d46feb3`/`4b96eb6`/`0af6c4d`): orphan/dead-
  helper deletes; #1 (`bcEqualFromLipschitzEqual`); banked
  `wasserstein1_le_liminf_of_narrow` (proved A is a phantom); #2
  (`cauchyW1_hasNarrowLimit`). Marquee certified axiom-clean.
* **Perspective + Option-3 goal** (`eb70fac`/`f63b6b7`): Dobrushin-paper read;
  soundness leaf-read corrected "free swap" → Option 3 (B-free coupling core +
  labeled all-dual corollary).
* **Option 3 LANDED** (`ab33346`): B-free coupling core
  (`dobrushin_meanfield_On`, `dobrushin_package_exists`); `dobrushin`
  all-dual via the one `wasserstein1_eq_coupling` bridge. Probe-verified (P10).
* **O2 cost-parameterization** (`61a3745`/`09fbeca`/`83dabff`): DONE.

## Standing note — `meanFieldLimit` vs `dobrushin`

`meanFieldLimit` is axiom-clean **but conditional** (takes the estimate as a
hypothesis). Making the mean-field *limit* unconditional-and-B-free is exactly
follow-up (1), gated on the `hInit` read. Do not state "the mean-field limit is
B-free" as settled until that read lands.
