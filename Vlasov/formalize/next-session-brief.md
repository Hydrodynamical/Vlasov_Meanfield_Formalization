# Next-session brief (as of 2026-06-05) — GOAL: B-free coupling core + labeled all-dual corollary (Option 3)

Build green; **1 sorry** (`Coupling.lean:276` = Foundation B). Marquee
`vlasovWellPosedness` (existence + uniqueness) is axiom-clean
`[propext, Classical.choice, Quot.sound]`; `dobrushin` (mean-field stability)
adds `sorryAx`, tracing to **Foundation B only**.

---

## The Dobrushin-paper perspective (2026-06-05)

Grounded in the source paper — R. L. Dobrushin, "Vlasov equations," *Funct.
Anal. Appl.* **13**:2 (1979), pp. 115–123 (`Dobrushin79.pdf` in the repo root).
Reading it against the code establishes that **Foundation B is needed only for
one thing** — identifying the project's KR-**dual** `wasserstein1` with the
**primal** coupling-inf Dobrushin works in. Everything else (existence,
uniqueness, the mean-field limit, the Dobrushin-metric stability) is B-free.

Three structural facts from the paper:

1. **His metric is the primal coupling-inf of the *bounded* cost.** Eq (5.1):
   `ρ(x,x') = min(|x−x'|, 1)`; eq (5.3): `ρ̄(μ,ν) = inf_{couplings m} ∫ ρ dm`.
   That is the project's banked **W̄**, defined the *primal* way. The bounded
   cost makes ρ̄ **metrize weak convergence** (p. 121) — the topology the
   mean-field limit (Thm III) lives in; the primal/inf form makes **ε-optimal
   couplings free**. The project's dual-sup *unbounded* `wasserstein1` is the
   deviation that created "Foundation B".
2. **No L<1.** Smallness is `C₂|Δ| < 1` / `γ(|Δ|) < 1` — on the **time-interval
   length**, removed by decomposing Δ into short sub-intervals (§6). Theorem I
   is **global** for any Lipschitz force.
3. **Stability (Prop 4, eq 6.8) uses an ε-optimal coupling** — exists free from
   the infimum, no attainment; then ε→0. **And Dobrushin's own stability is
   stated in his primal metric ρ̄ — there is no "dual W₁" in the paper.** So the
   coupling-metric stability is the *faithful* one; the project's all-dual form
   is its own representational choice (and the one that costs B).

### Atom-level B-trace (verified, current state)

Foundation B enters the dependency tree at exactly ONE place:
`dobrushin_meanfield_On` (`CharacteristicFlow.lean:12485`) obtains the optimal
coupling π₀ at **L12506** (`wasserstein1_optimal_coupling_exists`, B) carrying
the **equality** `∫⁻ edist dπ₀ = wasserstein1 (f 0)(g 0)`, used once at
`hbase_eq` (**L12541**) to put the dual `wasserstein1 (f 0)(g 0)` on the RHS.
`dobrushin` (**L13443**) concludes
`wasserstein1 (f t)(g t) ≤ ofReal(exp(C t)) · wasserstein1 (f 0)(g 0)`
(**L13459–60**). The dual on the RHS is the *only* reason the equality (= B) is
needed.

---

## GOAL (locked + soundness-corrected 2026-06-05): Option 3

### Soundness resolution (P5 leaf-read on the locked goal — verified against the code)

The original "dissolve B by switching the RHS to `wasserstein1_coupling`, prove
via `le_iInf`, delete the B section" framing was *partly illusory*. The leaf-read
corrects it:

* **The duality bridge `wasserstein1_eq_coupling` (`wasserstein1_coupling =
  wasserstein1`) IS a corollary of Foundation B** (Coupling:318), and is
  currently **used nowhere** outside `Coupling.lean` — the dynamics never
  convert coupling↔dual.
* **The easy direction `wasserstein1 ≤ wasserstein1_coupling` is B-free**
  (`wasserstein1_le_wasserstein1_coupling`, Coupling:111) — so the squeeze
  `0 ≤ wasserstein1 ≤ wasserstein1_coupling` is free.
* **What the B-free route actually yields is the *mixed* form**, not all-dual:
  `wasserstein1 (f t)(g t) ≤ exp · wasserstein1_coupling (f 0)(g 0)` — LHS the
  genuine dual W₁ metric (free), RHS the primal coupling cost. **Both** the
  `le_iInf` and the ε-optimal (eq 6.8) routes land here; **ε-optimal does NOT
  rescue the all-dual RHS** (an ε-optimal coupling approaches the *coupling* inf
  `≥` dual W₁; equating to dual W₁ is the hard direction = B). The mixed form is
  *strictly weaker* than the current all-dual statement (RHS bigger).
* **`meanFieldLimit` (Basic:2599) is wired all-dual** on both ends: consumes
  `DobrushinStabilityEstimate` as `wasserstein1 (μ^N_t)(f t) ≤ exp ·
  wasserstein1 (μ^N_0)(f 0)` and `hInit` as `wasserstein1 (μ^N_0) f₀ → 0`.

**Verdict:** B *dissolves* for the mean-field **limit** and the **Dobrushin-metric
(coupling) stability**; B *stays* for the **all-dual-W₁ quantitative stability
estimate** (it needs the duality bridge). Neither a free swap nor an illusion —
a clean factoring of exactly where B is and isn't needed. (M2: the all-dual and
coupling forms are *different statements*; the B-free one is the coupling/mixed
form.)

### Decision (Joe's, 2026-06-05): Option 3 — provide BOTH

1. **B-free coupling core** — dynamics + mean-field limit in the coupling metric;
   zero external axioms there.
2. **All-dual corollary** via the single, explicitly-labeled
   `wasserstein1_eq_coupling` (B) bridge — so the literature-standard
   `W₁(f_t,g_t) ≤ exp·W₁(f_0,g_0)` headline remains available, with Foundation B
   isolated to **one labeled conversion**.

Net: existence + uniqueness + **mean-field limit** + Dobrushin-metric stability all
become axiom-clean `[propext, Classical.choice, Quot.sound]`; the **all-dual W₁
stability estimate is the lone B-corollary** (`sorryAx`, isolated to the bridge).
The mean-field limit "in W₁" (dual-metric convergence on the LHS) is delivered
B-free via the easy-direction squeeze.

### Surgery (fresh session — open with the two confirming reads, then execute)

**Opening reads (P5 gate — confirm BEFORE editing):**
- Confirm `dobrushin_integrated_flow_bound_On` (consumed at CharFlow:12519) is
  genuinely **coupling-generic**: takes an *arbitrary* π with the marginal hyps
  `hmarg_f / hmarg_g`, not the optimal one. (Call site strongly suggests yes.)
- Read `DobrushinStabilityEstimate`'s definition (the predicate `meanFieldLimit`
  consumes) so the coupling-form `dobrushin` discharges its coupling variant.

**Core (B-free):**
1. `dobrushin_meanfield_On` (CharFlow:12485): keep the existing chain — its LHS is
   *already* dual `wasserstein1 (f t)(g t)`, derived B-free (easy direction,
   L12570). Replace the optimal coupling π₀ (L12506, B) + `hbase_eq` (L12541, the
   equality) with: run the integrated bound for **every** coupling π of
   `(f 0, g 0)`, then `le_iInf` ⟹ RHS `= wasserstein1_coupling (f 0)(g 0)`.
   Conclusion RHS dual→coupling. (Distribute `ofReal(exp) ≠ ⊤` over the nested
   coupling iInf — `ENNReal.mul_iInf` family. **Fallback:** ε-optimal coupling +
   `ENNReal.le_of_forall_pos_le_add`.)
2. Thread the coupling-RHS through `dobrushin_package_exists` (CharFlow:13394).
3. Coupling-form mean-field limit: a coupling variant of
   `DobrushinStabilityEstimate` + a coupling-`hInit` variant of `meanFieldLimit`;
   the **conclusion stays dual W₁** via the squeeze (`0 ≤ wasserstein1 ≤
   wasserstein1_coupling`). The coupling `hInit` (`wasserstein1_coupling (μ^N_0)
   f₀ → 0`) is the *natural* hypothesis for empirical measures — established by
   *exhibiting* couplings, never attainment.

**All-dual corollary (the one labeled B use):**
4. Keep the all-dual `dobrushin` (CharFlow:13443, current statement) as a one-line
   corollary of the coupling core + `wasserstein1_eq_coupling` (B). Label it
   clearly as the **sole** Foundation-B consumer.

**Do NOT delete the Foundation-B section** (contrast the original goal's
garbage-collect step): under Option 3, B remains as the labeled
`wasserstein1_eq_coupling` bridge feeding the all-dual corollary.
`wasserstein1_optimal_coupling_exists` (Coupling:335) *can* be deleted (its only
consumer, L12506, is gone); `foundationB_optimal_coupling_exists` (276),
`foundationB_coupling_le_dual` (296), `wasserstein1_eq_coupling` (318) **stay** —
now the labeled B surface.

**Verify (P10 — probe-insert → full-build → read → probe-remove; do not trust a
"green build" claim alone):** `#print axioms` should show the coupling core + the
unconditional coupling-form mean-field limit as `[propext, Classical.choice,
Quot.sound]`; the all-dual `dobrushin` corollary as `[propext, sorryAx,
Classical.choice, Quot.sound]`, the `sorryAx` tracing *only* to the single
`wasserstein1_eq_coupling` bridge. `vlasovWellPosedness` unchanged (clean).
`cd …/Vlasov/Vlasov && lake build Vlasov.OT.Coupling Vlasov.OT.CharacteristicFlow Vlasov.Basic`
green.

---

## The horizon (separate arcs — NOT this goal)

1. **L<1 → global (Theorem I).** Window-chaining per §6; **metric-independent**
   (the `(T+1)²` additive offset lives in the ODE ball-geometry, per M3, not in
   any Wasserstein step). Per-window moment re-anchoring is the hard part.
2. **Mean-field limit (Theorem III), unconditional.** The coupling-core makes the
   *conditional* `meanFieldLimit` dischargeable B-free; the remaining gap to an
   *unconditional* statement is "empirical measures μ^N of the N-particle Newton
   ODE are weak Vlasov solutions" + establishing `wasserstein1_coupling (μ^N_0)
   f₀ → 0` (exhibit couplings, B-free). μ^N's flow is Newton dynamics, so it is
   *not* a direct `dobrushin` application — the integrated core is the route.
   Cleanest in W̄ (bounded cost metrizes weak convergence).
3. The eventual "main theorem" emulating Dobrushin bundles **I (global) + Prop 4
   (stability) + III (mean-field)** — his parts I / Prop 4 / III; part II
   (weak⇒strong / C¹ density regularity) is deliberately out of scope.

---

## Certified state (unchanged, durable)

* **`vlasovWellPosedness` (existence + uniqueness)** → `[propext,
  Classical.choice, Quot.sound]`. Unconditional modulo Lean's standard axioms;
  no `sorryAx`, no `native_decide`, no custom axiom in its dependency tree.
* **Foundation A was a phantom**, certified: the marquee is axiom-clean *without*
  A. A factored into the easy LSC direction (`wasserstein1_le_liminf_of_narrow`,
  proved in-project). B is the lone genuine external — and (this brief) is now
  isolated to a single labeled duality bridge.
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
* **Perspective + goal locked** (`eb70fac`): Dobrushin-paper read; B traced to one
  line; goal set (this brief refines it to Option 3 after the soundness check).
* **O2 cost-parameterization** (`61a3745`/`09fbeca`/`83dabff`): DONE —
  `wassersteinCost` core + cost-generic property layer + `wassersteinBar` +
  instantiations, all sorry-free.

## Standing note — `meanFieldLimit` vs `dobrushin`

`meanFieldLimit` is axiom-clean **but conditional** (takes the Dobrushin estimate
as a hypothesis; cleanness is a naming artifact). Under Option 3 the *coupling
variant* of `meanFieldLimit` becomes dischargeable by the **B-free** coupling-form
`dobrushin`, giving an unconditional, B-free mean-field limit (modulo horizon
item 2: empirical-measures-are-solutions + coupling-`hInit`). The all-dual
`meanFieldLimit` would route through the labeled B bridge.
