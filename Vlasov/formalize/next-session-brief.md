# Next-session brief (as of 2026-06-06) — Phase A done (B shrunk + sized); Phase B = build KR duality

Build green; **1 sorry** = `foundationB_coupling_le_dual` (`Coupling.lean:288`),
now in its weakest irreducible form — the hard-direction KR duality inequality
`wassersteinCost_coupling c μ ν ≤ wassersteinCost c μ ν`.

**ACTIVE: Phase B — build KR duality (the shrunk B).**  Route + verified Mathlib
inventory + helper skeleton are in **`formalize/kr-duality-plan.md`** (Route 1:
discrete approximation + limit; the implementation session opens against that
doc).  Phase A.0 (`656e9b9`) shrank B from attainment + strong duality + equality
to this inequality alone (consumer `dobrushin` needs only `coupling ≤ dual`;
attainment dropped, two dead lemmas deleted).  A.1 sized the residual: a genuine
~250–500-line from-scratch OT build, NO Mathlib scaffolding (no Kantorovich /
Wasserstein / Fenchel–Rockafellar).  Approved order (plan
`clear-picture-now-the-starry-sparrow.md`): B → zero external axioms at L<1, then
Phase C (remove L<1 via window-chaining).

The sections below are the durable terminal-state record (everything else B-free)
from before the Phase A shrink; still accurate.

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

### (1) `meanFieldLimit` coupling variant — RESOLVED (`55c6296`)

The read landed exactly as the asymmetry predicted. Added
`DobrushinStabilityEstimateCoupling` + `meanFieldLimit_coupling` (in CharFlow,
where both Basic's mean-field machinery and `wasserstein1_coupling` are visible —
**Basic does not import Coupling**, so the variant cannot live in Basic).
Probe-verified **B-free**: `[propext, Classical.choice, Quot.sound]`.

**Answer — the initial-convergence type a B-free mean-field limit requires:**
**coupling-metric initial convergence** `wasserstein1_coupling (μ^N_0) f₀ → 0`.
* The easy direction `wasserstein1 ≤ wasserstein1_coupling` does NOT supply it
  from dual-W₁ `hInit`: dual-small does not bound the coupling (wrong direction
  for a *hypothesis*); dual→coupling is the hard direction = Foundation B.
* Coupling-`hInit` is **mathematically equal** to dual-W₁ convergence (KR
  duality) and is the **natural form for empirical measures** (exhibit couplings
  to bound the cost from above — easier than controlling the dual sup). So it is
  a **nominal, not real, strengthening** — the Option-1 hypothesis-vs-axiom trade
  surfacing at the limit level, at nominal cost.
* The conclusion stays **dual-W₁** convergence (the genuine metric). The all-dual
  `meanFieldLimit` (Basic) remains the standard-`hInit` form, routing through the
  all-dual `dobrushin` (the single B bridge).

**Net:** the mean-field *limit* is B-free with coupling-`hInit`. What remains for
an *unconditional* mean-field limit is NOT a metric question — it is discharging
the stability estimate for empirical μ^N ("μ^N is a weak Vlasov solution"; μ^N's
flow is Newton dynamics, not a direct `dobrushin` application). See horizon item 2.

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
* **Mean-field limit B-free (coupling form)** (`55c6296`): added
  `DobrushinStabilityEstimateCoupling` + `meanFieldLimit_coupling`; probe-verified
  `[propext, Classical.choice, Quot.sound]`. Settled follow-up (1): the B-free
  limit requires coupling-metric `hInit` (nominal strengthening; KR-equal to
  dual-W₁, natural for empirical measures). Conclusion stays dual-W₁.
* **O2 cost-parameterization** (`61a3745`/`09fbeca`/`83dabff`): DONE.

## Standing note — `meanFieldLimit` vs `dobrushin`

Two forms now coexist: the all-dual `meanFieldLimit` (Basic, conditional,
standard dual-W₁ `hInit`, routes through the all-dual `dobrushin` = the single B
bridge) and the B-free `meanFieldLimit_coupling` (CharFlow, conditional,
coupling-`hInit`). Both are conditional on the Dobrushin estimate. The genuine
open work for an **unconditional** mean-field limit is discharging that estimate
for empirical μ^N (horizon item 2: "μ^N is a weak Vlasov solution"; μ^N's flow is
Newton dynamics) — a metric-independent gap, not a Foundation-B question.
