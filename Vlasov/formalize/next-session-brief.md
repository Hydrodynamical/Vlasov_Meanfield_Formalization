# Next-session brief (as of 2026-06-05, HEAD = `ca12381`)

Durable hand-off. Build green; **3 sorries** (Basic 2, Coupling 1, CharFlow 0).

## Where this lands — the milestone-of-milestones

The deferred surface went 13 → 8 → 6 → 4 → 3 across these sessions, and the **3**
is qualitatively different from the 13: it is not "13 gaps shrunk to 3 gaps," it
is the surface **resolved into one genuine external + two in-project closes**:

* **Foundation B** (`foundationB_optimal_coupling_exists`, Coupling 291) — the one
  OT attainment theorem Mathlib lacks; sole sorry-dependency of the mean-field
  marquee `dobrushin`. A genuine external, not an attack target.
* **#1** (`MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment`, Basic 1465) —
  existence-side separation. In-project.
* **#2** (`MathlibTODO_cauchyW1_hasNarrowLimit`, Basic 1590) — Picard existence /
  Prokhorov narrow limit. In-project.

The marquee — existence **and** uniqueness **and** mean-field — runs on the single
`dobrushin_integrated_flow_bound_On` core (force-estimate-free). Every W₁-specific
external (#3/#4/#5/#6/#7/#8) either dissolved under the integrated-core migration
(orphaned) or retired by construction. The deferred surface is now **minimal and
correctly typed**.

## Marquee axiom footprints (certified `#print axioms`, 2026-06-05)

* `vlasovWellPosedness` (existence) → `[propext, sorryAx, Classical.choice,
  Quot.sound]`; the `sorryAx` traces to **{#1, #2} only** — not #7 (orphaned and
  deleted), not B. Certified: the L=0 Lagrangian path now runs through the
  sorry-free producer `…isLagrangianVlasovSolutionOn` (4366), itself
  `[propext, Classical.choice, Quot.sound]` (no sorryAx ⟹ Foundation-B-free), so
  the producer-switch **replaced** the #7 path rather than supplementing it.
* `dobrushin` (mean-field stability) → sorryAx = **Foundation B only**.
* `meanFieldLimit` → axiom-clean `[propext, Classical.choice, Quot.sound]`. See
  Standing items — conditional / naming-artifact per a prior read; keep visible.

## DONE log

* **6 → 4** (commit `a83fc35`): deleted orphaned #3/#4 + the 5 dead helpers
  (`w1ContOn_lscNarrow_via_pureFA`, `W1ContOn_integralContAt`, `W1ContOn_lt_top`,
  `W1ContOn_toRealContOn`, `dobrushin_C_choice`). The integrated core dissolved the
  A-side W₁-continuity surface; #3/#4 were its orphaned narrow-machinery.
  **The dead-helper cleanup is COMPLETE — not a pending task** (verified by grep,
  all five gone).
* **4 → 3** (commit `ca12381`): orphaned + deleted #7 via the marquee L=0
  producer-switch. Re-pointed the `∀T …On` conjunct through the sorry-free
  `…isLagrangianVlasovSolutionOn` (4366); the `M_ρ` hypothesis discharged by the
  affine `(1+|s|)‖z‖` bound → `(1+T)·M_{f₀}` (machine-verified by the green build,
  not just predicted). Cascade-deleted the 364-line orphaned chain (#7,
  `vlasovTrajectoryLipschitzBound`, `…isVlasovSolution`, `…isLagrangianVlasovSolution`).
  Ordering held: leaf-check `M_ρ` → rewire (green) → certify axioms-clean →
  delete last (replace→verify→delete, the #5/#6/#8 shape).

## Next move — #2, then #1 (both in-project, W̄-independent)

* **#2** `cauchyW1_hasNarrowLimit` (Basic 1590) — **NEXT. GATED on the
  conclusion-shape read** (same shape as the #7 RECLASSIFIED gate just navigated;
  P5 — the "Prokhorov, in-project, easy" label is a prior characterization the
  leaf-read verifies, not a formality). The read:
  - What does `cauchyW1_hasNarrowLimit` actually *conclude* — narrow-limit
    existence, or W₁-convergence-to-the-limit?
  - What does its caller (the Picard existence path) actually *need* from it?
  - If narrow-limit-existence suffices for the caller → tightness (Markov) →
    Prokhorov narrow limit (Mathlib has Prokhorov), in-project, **clean close**.
  - If the caller needs W₁-convergence → it **drags the hard narrow ⟹ W₁
    bridge**. NB this is *existence-side*, a **different consumer** than the
    marquee stability path — re-confirm the hard direction isn't needed *here*.
  The gate decides clean-Prokhorov vs bridge **before** committing to a path.
* **#1** `bcEqualFromLipschitzEqual…` (Basic 1465) — existence-side separation via
  `wasserstein1_eq_zero_iff_measure_eq`. Subalgebra-separation / BC-density close;
  A-side-flavored but LIVE and in-project.
* **Foundation B** (Coupling 291) — the sole genuine external; not an attack
  target (optionally shrinkable to ε-optimal, Dobrushin 6.8).

Sequence: ~~6→4~~ **DONE** (`a83fc35`) → ~~#7 orphan (4→3)~~ **DONE** (`ca12381`)
→ #2 (gated on conclusion-shape read) → #1. Foundation B stays the external.

## Standing items (off the #2/#1 critical path — do not let evaporate)

* **`meanFieldLimit` — RESOLVED: naming-artifact, *with its consequence*.** A prior
  read (2026-06-05) concluded it is **CONDITIONAL**: it takes the Dobrushin
  stability estimate as a *hypothesis* (`hDobrushin : ∀ N,
  DobrushinStabilityEstimate (μ^N) f C`) and never discharges it (a one-line
  Grönwall composition), so its axiom-cleanness `[propext, Classical.choice,
  Quot.sound]` is a **naming artifact, NOT a B-free deliverable**.
  **Consequence (bank this — it is the load-bearing part):** the project does
  **NOT** currently have an unconditional, axiom-clean mean-field-limit theorem as
  a deliverable. The genuine mean-field deliverable is **`dobrushin` (proven modulo
  Foundation B)** plus the N→∞ convergence; `meanFieldLimit`'s cleanness is
  packaging. Do **not** let "`meanFieldLimit` is axiom-clean (resolved)" read as
  "the mean-field limit is axiom-clean" — the resolution was precisely that the
  clean `meanFieldLimit` *isn't* the full limit. **No re-read needed** unless
  someone wants to upgrade `meanFieldLimit` to the unconditional statement — which
  routes through B. (Wiring detail if upgraded: discharging `hDobrushin` for the
  *atomic* empirical curve `μ^N` is not a direct `dobrushin` application —
  `dobrushin` wants both args `IsLagrangianVlasovSolution`, `μ^N`'s flow is Newton
  dynamics — so the integrated core, which applies to any coupling-of-measures, is
  the route, but the wiring is a genuine gap.)

## The W̄ forward program (separate future project)

The W̄ (truncated-metric) migration as a *forward* program — restate the stability
estimate over `c = min(dist, 1)`, extend the marquee to `L ≥ 1` — is NOT on the
current critical path. The A-side W̄ *harvest* evaporated (the integrated core
orphaned #3/#4 rather than needing dissolution). W̄ remains a clean future pivot,
additive at the def layer (`wassersteinBar := wassersteinCost (fun x y => min (dist x y) 1)`).
