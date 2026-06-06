# Next-session brief (as of 2026-06-05) — GOAL: dissolve Foundation B in the coupling metric

Build green; **1 sorry** (`Coupling.lean:276` = Foundation B). Marquee
`vlasovWellPosedness` (existence + uniqueness) is axiom-clean
`[propext, Classical.choice, Quot.sound]`; `dobrushin` (mean-field stability)
adds `sorryAx`, tracing to **Foundation B only**.

---

## The Dobrushin-paper perspective (2026-06-05)

Grounded in the source paper — R. L. Dobrushin, "Vlasov equations," *Funct.
Anal. Appl.* **13**:2 (1979), pp. 115–123 (`Dobrushin79.pdf` in the repo root).
Reading it against the code establishes that **Foundation B is not needed by
Dobrushin's actual method** — it is an artifact of the project stating its
results in the KR-**dual** `wasserstein1` rather than the **primal**
coupling-inf Dobrushin works in.

Three structural facts from the paper:

1. **His metric is the primal coupling-inf of the *bounded* cost.** Eq (5.1):
   `ρ(x,x') = min(|x−x'|, 1)`; eq (5.3): `ρ̄(μ,ν) = inf_{couplings m} ∫ ρ dm`.
   That is the project's banked **W̄**, defined the *primal* way. Two
   load-bearing choices: the bounded cost makes ρ̄ **metrize weak convergence**
   (stated explicitly p. 121) — exactly the topology the mean-field limit
   (Thm III) lives in; the primal/inf form makes **ε-optimal couplings free**.
   The project's dual-sup *unbounded* `wasserstein1` is the deviation that
   created both "Foundation B" and the moment-finiteness machinery.
2. **No L<1.** His smallness is `C₂|Δ| < 1` and `γ(|Δ|) < 1` — on the **length
   of the time interval**, removed by decomposing Δ into short sub-intervals
   (§6). Theorem I is **global** for any Lipschitz force. Our `L<1` is purely
   an artifact of contracting over the whole interval at once.
3. **Stability (Prop 4, eq 6.8) uses an ε-optimal coupling** —
   `∫ ρ m⁰ ≤ ρ̄(μ⁰, μ̄⁰) + ε` — which exists for free from the infimum, no
   attainment; then ε→0. The project's right-derivative (`#6`) route is what
   forced the two-sided **equality** pinch → attainment → B.

### Atom-level B-trace (verified)

Foundation B enters the **entire** dependency tree at exactly ONE place:
* `dobrushin_meanfield_On` (`CharacteristicFlow.lean:12485`) obtains the
  optimal coupling π₀ at **L12506** (`wasserstein1_optimal_coupling_exists`,
  Foundation B) carrying the **equality** `∫⁻ edist dπ₀ = wasserstein1 (f 0)(g 0)`,
  used once at `hbase_eq` (**L12541**) to place the dual `wasserstein1 (f 0)(g 0)`
  on the RHS.
* `dobrushin` (**L13443**) concludes
  `wasserstein1 (f t)(g t) ≤ ofReal(exp(C t)) · wasserstein1 (f 0)(g 0)`
  (**L13459–60**) — the dual on the RHS is the *only* reason the equality
  (= B) is needed.

This is the same "the external is smaller than it looks" pattern that already
dissolved Foundation A (the narrow↔W₁ phantom): the campaign's two foundations
were both consequences of definitional choices, not of the mathematics.

---

## GOAL (locked, 2026-06-05): B-dissolution in the coupling metric

**Decision (Joe's):** dissolve B by restating the mean-field stability with the
**primal coupling metric `wasserstein1_coupling` on the RHS** (= Dobrushin's
actual metric ρ̄), proved by his ε-optimal / iInf argument. **Leave the marquee
`vlasovWellPosedness` in the dual W₁** — no project-wide metric migration. This
is the *localized* dissolution: fastest path to **zero external OT axioms**,
marquee untouched.

Not a weakening: under KR duality the two metrics agree; we simply stop
*assuming* duality (B) in order to prove the estimate. The coupling-RHS form is
*more* faithful to Dobrushin, who works entirely in the primal metric.

### Surgery (concrete plan)

Targets, in order: `dobrushin_meanfield_On` (CharFlow:12485) →
`dobrushin_package_exists` → `dobrushin` (13443). Change each conclusion's RHS
from `wasserstein1 (f 0)(g 0)` to `wasserstein1_coupling (f 0)(g 0)`
(`wasserstein1_coupling = wassersteinCost_coupling dist`, Coupling.lean:235/243).
LHS stays dual `wasserstein1 (f t)(g t)` (the easy direction
`W₁_dual ≤ coupling-cost` already supplies it).

**Primary route — direct iInf (cleanest, no ε):**
* The shared core `dobrushin_integrated_flow_bound_On` (consumed at L12519)
  applies to **any** coupling π of `(f 0, g 0)` — it uses only the marginal
  hypotheses `hmarg_f / hmarg_g`. So for *every* coupling π:
  `W₁(f t,g t) ≤ ofReal(∫‖Φf−Φg‖dπ) ≤ ofReal((∫‖ω.1−ω.2‖dπ)·exp)
   = (∫⁻ edist dπ) · ofReal(exp)`.
* LHS is independent of π ⟹ `le_iInf` over the coupling binder:
  `W₁(f t,g t) ≤ ofReal(exp) · ⨅_{π : IsCoupling} ∫⁻ edist dπ
   = ofReal(exp) · wasserstein1_coupling (f 0)(g 0)`.
  (Distribute the constant `ofReal(exp) ≠ ⊤` across the nested
  `(π)(_:IsCoupling π (f 0)(g 0))` iInf — `ENNReal.mul_iInf` family.)
* No attainment, no ε, no B. This is the faithful primal Prop 4.

**Fallback — Dobrushin eq 6.8 (ε-optimal):** if distributing the constant over
the nested-iInf binder is fiddly, pull an ε-optimal coupling π₀^ε from the iInf
(`wasserstein1_coupling (f 0)(g 0) < ⊤` from finite first moments ⟹ a
near-minimizer exists), run the *existing* chain unchanged, and close with
`ENNReal.le_of_forall_pos_le_add` (ε→0).

### Garbage-collect after dissolution
B's only necessary consumer is L12506. Once it is rerouted, **verify no other
consumers** then delete: `foundationB_optimal_coupling_exists` (Coupling:276),
`foundationB_coupling_le_dual` (296), `wasserstein1_eq_coupling` (318),
`wasserstein1_optimal_coupling_exists` (335). Result: **0 sorries**;
`#print axioms dobrushin` → `[propext, Classical.choice, Quot.sound]` (no
`sorryAx`). Re-certify with the probe-insert → full-build → read → probe-remove
discipline (P10) — do not trust a "green build" claim alone.

### Verify
`cd …/Vlasov/Vlasov && lake build Vlasov.OT.Coupling Vlasov.OT.CharacteristicFlow`
green; full-project `grep` for `sorry` empty; `#print axioms vlasovWellPosedness`
and `#print axioms dobrushin` both `[propext, Classical.choice, Quot.sound]`.

---

## The horizon (separate arcs — NOT this goal)

1. **L<1 → global (Theorem I).** Window-chaining per §6; **metric-independent**
   (the `(T+1)²` additive offset lives in the ODE ball-geometry, per M3, not in
   any Wasserstein step). Per-window moment re-anchoring is the hard part.
   Several sessions; orthogonal to the metric.
2. **Mean-field limit (Theorem III), rigorous.** stability (now B-free) +
   "empirical measures μ^N of the N-particle Newton ODE are weak Vlasov
   solutions" (Dobrushin's elementary calculation, currently a gap — note
   μ^N's flow is Newton dynamics, so it is *not* a direct `dobrushin`
   application; the integrated core is the route) + the weak-convergence
   framing, which is **clean in W̄** because the bounded cost metrizes weak
   convergence (p. 121). This is where the banked `wassersteinBar` finally
   earns its keep — for III specifically, not for existence.
3. The eventual "main theorem" that emulates Dobrushin bundles **I (global) +
   Prop 4 (stability) + III (mean-field)** — parts I / Prop 4 / III of his
   Theorem; part II (weak⇒strong / C¹ density regularity) is deliberately out
   of scope.

---

## Certified state (unchanged, durable)

* **`vlasovWellPosedness` (existence + uniqueness)** → `[propext,
  Classical.choice, Quot.sound]`. Unconditional modulo Lean's standard axioms;
  no `sorryAx`, no `native_decide`, no custom axiom in its dependency tree.
* **Foundation A was a phantom**, certified: the marquee is axiom-clean
  *without* A. A factored into the easy LSC direction
  (`wasserstein1_le_liminf_of_narrow`, proved in-project); B is the one genuine
  external — and (this brief) is itself dissolvable by the primal restatement.
* **Topology/dynamics decoupling** certified: W₁'s metric role
  (Cauchy/limit/continuity) and dynamical role (force-estimate contraction)
  decouple; existence completeness = narrow-compactness (Prokhorov) + W₁-LSC,
  contraction left in W₁ (unbounded-Lipschitz ∇W intact).

## DONE log (this arc)

* **6 → 4** (`a83fc35`): deleted orphaned #3/#4 + 5 dead helpers.
* **4 → 3** (`ca12381`): orphaned + deleted #7 via the marquee L=0 producer-switch.
* **3 → 2** (`d46feb3`): closed **#1** `bcEqualFromLipschitzEqual` (thickened-
  indicator determining class; metric-agnostic ⟹ W̄-survivor).
* **Banked** (`4b96eb6`): `wasserstein1_le_liminf_of_narrow` — static narrow-LSC
  of W₁ (Villani 6.9, KR-dual + truncation). The scout that proved A is a phantom.
* **2 → 1** (`0af6c4d`): closed **#2** `cauchyW1_hasNarrowLimit` (narrow-
  compactness + W₁-LSC + Cauchy). Marquee certified axiom-clean.
* **O2 cost-parameterization** (`61a3745`/`09fbeca`/`83dabff`): DONE —
  `wassersteinCost` core + cost-generic property layer + `wassersteinBar` +
  instantiations, all sorry-free. (W̄ is now known unnecessary for existence;
  it is the natural vehicle for the mean-field limit, Thm III.)

## Standing note — `meanFieldLimit` vs `dobrushin`

`meanFieldLimit` is axiom-clean **but conditional** (takes the Dobrushin
estimate as a hypothesis; cleanness is a naming artifact). The genuine
mean-field deliverable is **`dobrushin`** (after this goal: B-free) plus the
N→∞ convergence (horizon item 2). Upgrading `meanFieldLimit` to unconditional
routes through the empirical-measures-are-solutions step, not a direct
`dobrushin` application (μ^N's flow is Newton dynamics).
