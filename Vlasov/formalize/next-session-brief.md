# Next-session brief (as of 2026-06-05, HEAD = `0af6c4d`)

Durable hand-off. Build green; **1 sorry** (Coupling 1; Basic 0, CharFlow 0).

## Terminal map — existence + uniqueness are axiom-clean; one genuine external (B)

The deferred surface went 13 → … → 3 → 2 → **1**, and the **1** is qualitatively
the end of the "characterize the deferred surface" program. Certified by the
axiom checker (probes inserted, full build, footprint read firsthand, probes
removed — the P10 discipline at its strongest):

* **`vlasovWellPosedness` (existence + uniqueness)** → `[propext,
  Classical.choice, Quot.sound]` — **axiom-clean, no `sorryAx`.** The
  existence/uniqueness theorem is **unconditional modulo Lean's standard
  axioms.** No sorry, no `native_decide`, no custom axiom anywhere in its
  dependency tree.
* **`dobrushin` (mean-field stability)** → `[propext, sorryAx,
  Classical.choice, Quot.sound]` — the lone `sorryAx` traces to **Foundation B
  only**.
* **Sole sorry in the project**: `foundationB_optimal_coupling_exists`
  (`Coupling.lean:276`).

## What this *is* — A was a phantom, certified

The campaign spent many sessions believing the deferred surface was **two**
foundations, A (narrow↔W₁ metrization) and B (coupling attainment). The marquee
being axiom-clean **without A** is the proof that **A was never load-bearing** —
not "we found a clever way around A" but "the argument that supposedly required
it stands without it, and the checker confirms A's absence." The conflation
(one-directional W₁-LSC mistaken for the full narrow⟺W₁ metrization) is refuted
by the axiom checker itself.

**The A-vs-B asymmetry is the accurate picture** (do not blur "one external"
into "one Mathlib gap from done"):
* **A factored** into the *easy* LSC direction (`wasserstein1_le_liminf_of_narrow`,
  proved in-project) — it dissolves.
* **B does not factor.** Optimal-coupling attainment is a real
  compactness-on-the-coupling-space *existence* fact; it is irreducible in a way
  A was not. B is the one *genuine* external.

**The conceptual result, now mechanical**: W₁'s metric role (topologizing
measures — Cauchy/limit/continuity) and dynamical role (the force-estimate
contraction) **decouple**. Existence completeness = narrow-compactness
(Prokhorov, from moments) + W₁-LSC bridge, with the **contraction left in W₁**
(unbounded-Lipschitz ∇W intact, no bounded-∇W). The topology/dynamics
decoupling is not a heuristic — it is certified by the footprint. Consequently
**W̄ is unnecessary for "only B"** (confirmed, not conjectured).

## Foundation B — the lone external, characterized (not opaque)

B is now the entire remaining surface; the campaign has banked findings about its
*shape*, which the next session should use rather than treat B as a black box:

* **Possibly shrinkable to ε-optimal.** Dobrushin's *faithful* argument (his 6.8)
  uses **ε-optimal couplings**, not full attainment. So B *might* shrink below
  `foundationB_optimal_coupling_exists` if the mean-field route is re-examined to
  need only the easy KR direction + an ε-witness. **This ε-shrink read is the
  CHEAP first move on B** — it might dissolve B to something already provable,
  the same "the external is smaller than it looks" pattern that just erased A.
  Scout it *before* committing to a full attainment proof.
* **Backed by existing OT infrastructure.** Prokhorov + portmanteau + the banked
  cost-generic `wassersteinCost` layer. The one unverified spot is whether those
  compose to attainment on the **product / coupling space** (the product-LSC
  question) — that is B's crux and its handoff-spec.
* **Does not harden under W̄, stated cost-generically** (gate-2 read). W̄ buys B
  nothing here.

## Three genuinely-different next directions (distinct kinds of work)

1. **Foundation B — ε-optimal-shrink scout (CHEAP, recommended first).**
   Re-examine whether `dobrushin` consumes full attainment or only the easy KR
   direction + an ε-optimal witness. Might dissolve B. This is the A-shaped move:
   read before building. *Closes the mean-field marquee if it lands.*
2. **Foundation B — full attainment proof.** The Prokhorov + portmanteau +
   LSC-on-coupling-space assembly; product-space attainment composition is the
   crux. The honest OT existence theorem if the ε-shrink doesn't dissolve it.
3. **L<1 removal — the *separate* arc.** Window-chaining (Dobrushin §6),
   **metric-independent** (the `(T+1)²` offset lives in the ODE ball-geometry,
   not any Wasserstein step — W̄-independent too). Mathematically settled,
   Lean-hard; the moment-bootstrap re-anchoring per window is the core
   difficulty. A distinct future project, orthogonal to B.

And the honest fourth option: **stop the formalization-down arc here.**
Existence + uniqueness axiom-clean + mean-field modulo one characterized
external is a genuine, publishable-shaped result. "Drive B to zero" vs "write up
the L<1 extension" vs "this is the natural resting point" is a **project
decision (Joe's, about what the artifact is for)**, not a next-Lean-task default.

## DONE log (this arc)

* **6 → 4** (`a83fc35`): deleted orphaned #3/#4 + 5 dead helpers.
* **4 → 3** (`ca12381`): orphaned + deleted #7 via the marquee L=0 producer-switch.
* **3 → 2** (`d46feb3`): closed **#1** `bcEqualFromLipschitzEqual` (thickened-
  indicator determining class; metric-agnostic ⟹ W̄-survivor).
* **Banked** (`4b96eb6`): `wasserstein1_le_liminf_of_narrow` — static narrow-LSC
  of W₁ (Villani 6.9, KR-dual + truncation). The scout that proved A is a phantom.
* **2 → 1** (`0af6c4d`): closed **#2** `cauchyW1_hasNarrowLimit` (narrow-
  compactness + W₁-LSC + Cauchy). Marquee certified axiom-clean.
* **O2 cost-parameterization** (`61a3745`/`09fbeca`/`83dabff`, earlier): DONE —
  `wassersteinCost` core + cost-generic property layer + `wassersteinBar` +
  instantiations, all sorry-free. (Recorded here because a prior brief
  mislabelled it "to build"; it is banked. W̄ is now known unnecessary for
  only-B regardless.)

## Standing note — `meanFieldLimit` vs `dobrushin`

`meanFieldLimit` is axiom-clean **but conditional** (takes the Dobrushin estimate
as a hypothesis, one-line Grönwall; cleanness is a naming artifact). The genuine
mean-field deliverable is **`dobrushin`** (modulo Foundation B) + N→∞ convergence.
Do **not** let "the surface is {B}" read as "the mean-field limit is one gap from
done" without noting B is the *attainment* theorem and `dobrushin` genuinely
consumes it (irreducible, unlike A). Upgrading `meanFieldLimit` to unconditional
routes through B (wiring `hDobrushin` for the atomic empirical `μ^N` is not a
direct `dobrushin` application — `μ^N`'s flow is Newton dynamics — so the
integrated core is the route; a genuine gap).
