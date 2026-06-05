# Next-session brief (as of 2026-06-05, HEAD = `5b6ff4a`)

Durable hand-off. Build green; 6 sorries (Basic 4, Coupling 1, CharFlow 1).

## Current state — marquee on the integrated coupling core

Both halves of the marquee route through the single
`dobrushin_integrated_flow_bound_On` core (base-generic, axiom-clean):

* **uniqueness** — `dobrushin_uniqueness_On` at `proj = id`, `π₀ = f 0`
  (commit `118729d`); axiom-clean.
* **mean-field** — `dobrushin_meanfield_On` at `proj = fst/snd`, `π₀` = optimal
  coupling (Foundation B); `dobrushin_package_exists` re-pointed through it
  (commit `72999aa`). Retired #5/#6 (8 → 6), deleted the ~15-decl dead chain.

## REACHABILITY RE-TYPING (named-axiom trace, verified 2026-06-05)

Traced #1/#2/#3/#4/#7 as distinct axioms against the marquee theorems
(`#print axioms`). **Proven** live/orphaned split:

| sorry | name | reached by | verdict |
|---|---|---|---|
| #1 | `MathlibTODO_bcEqualFromLipschitzEqual_polish_firstMoment` | `vlasovWellPosedness` | **LIVE** (existence-side separation, CharFlow 8284) |
| #2 | `MathlibTODO_cauchyW1_hasNarrowLimit` | `vlasovWellPosedness` | **LIVE** (Picard existence) |
| #7 | `MathlibTODO_lipschitzFlowTrajectoryLipBound` | `vlasovWellPosedness` | **LIVE** (existence L=0) |
| #3 | `MathlibTODO_w1LowerSemicontinuousAlongNarrowMomentCurves` | *no marquee* | **ORPHANED** |
| #4 | `MathlibTODO_bcNarrowFromSmoothCompactNarrow` | *no marquee* | **ORPHANED** |
| B | `foundationB_optimal_coupling_exists` | `dobrushin` (sole dep) | **LIVE** (genuine external) |

* `vlasovWellPosedness` reaches `{#1, #2, #7}` — **not** #3/#4, **not** B.
* `dobrushin` reaches `sorryAx` = **Foundation B only** (proven earlier too).
* `meanFieldLimit` is **axiom-clean** `[propext, Classical.choice, Quot.sound]`
  — depends on NO sorry. **RESOLVED (statement read, 2026-06-05):** it is
  **CONDITIONAL — case (a)**. It takes the Dobrushin stability estimate as a
  *hypothesis* `hDobrushin : ∀ N, DobrushinStabilityEstimate (μ^N) f C` and never
  discharges it; its proof is the one-line Grönwall composition
  `sup_{[0,T]} W₁(μ^N_t, f_t) ≤ e^{CT}·W₁(μ^N_0, f_0) → 0`. That is *why* it is
  axiom-clean while `dobrushin` is not — it assumes the estimate `dobrushin`
  works to *prove*, so it never touches the optimal coupling. **The
  axiom-cleanness is a naming artifact, NOT a B-free deliverable.** The
  *unconditional* mean-field limit is `meanFieldLimit ∘ dobrushin`, which routes
  through Foundation B. So the mean-field external is still B.
  **Secondary gap (real remaining content):** discharging `hDobrushin` is not a
  direct application of `dobrushin` — `dobrushin` requires *both* arguments to be
  `IsLagrangianVlasovSolution`, but the empirical curve `μ^N` is atomic (its flow
  is the Newton dynamics, not the Lagrangian-witness shape). The integrated core
  applies to any coupling-of-measures so it is dischargeable in principle, but
  the wiring `dobrushin`-as-stated → empirical curve is a genuine gap, not a
  one-liner. Do NOT re-open `meanFieldLimit` as a "B-free win" — it's a
  conditional composition theorem (the standard propagation-of-chaos shape).

**The integrated core dissolved the A-side W₁-continuity surface too.** #3/#4
(LSC-of-the-dual-sup, BC-density-for-narrow-continuity) were the narrow-machinery
the core obviated — it works on `∫‖Φ_f − Φ_g‖dπ` and never forms
`t ↦ W₁(f t, g t).toReal`. They are now **vestigial/orphaned**, like #5/#6.
The planned A-side W̄ *harvest* is largely **moot** — deletion is cheaper than
dissolution.

## Next move — deletion pass (6 → 4), the cheap collapse

The orphaned cluster (all mutually dead, nothing live reaches them):

* #3, #4 (orphaned sorries)
* the dead helpers: `w1ContOn_lscNarrow_via_pureFA` (calls #3/#4 + the others),
  `W1ContOn_integralContAt`, `W1ContOn_lt_top`, `W1ContOn_toRealContOn`,
  `dobrushin_C_choice`

Delete together in one revertable commit → **6 → 4**. The cluster sits roughly
Basic.lean L1455 (#1, **LIVE — keep**) far above, and L2102–2374 (the #3/#4 +
helpers block). **Delete carefully**: verify nothing LIVE is interspersed in
2102–2374 (read decl boundaries; #1 at 1455 and #2 at 1568 are far above and
LIVE — do not touch). Build-verify (compiler catches a mis-cut).

## Remaining genuinely-live surface (after the deletion pass → 4)

* **#7** `lipschitzFlowTrajectoryLipBound` (CharFlow) — L=0 reroute to the
  sorry-free `_isLagrangianVlasovSolutionOn` producer, then delete #7 + callerless
  wrappers. **Most characterized; reroute-and-delete, not a hard proof. Cleanest.**
* **#2** `cauchyW1_hasNarrowLimit` (Basic) — tightness (Markov) → Prokhorov narrow
  limit (Mathlib has Prokhorov). Caveat: its exact conclusion (narrow-limit vs
  W₁-convergence) decides clean-close vs drags-a-bridge — read it first.
* **#1** `bcEqualFromLipschitzEqual…` (Basic) — existence-side separation
  (`wasserstein1_eq_zero_iff_measure_eq` → CharFlow 8284). A-side-flavored but
  LIVE; subalgebra-separation / BC-density close.
* **Foundation B** (Coupling) — the **one genuine OT external**; sole dep of the
  mean-field marquee. Not an attack target; optionally shrinkable to ε-optimal
  (Dobrushin 6.8).

**Next constructive arc is the existence-side closes (#7, #2, #1)** — all
in-project, W̄-independent — NOT the A-side W̄ dissolution (evaporated for #3/#4).
The W̄ migration as a *forward* program (restate stability, extend to L ≥ 1)
remains a separate future project.

Sequence: deletion pass (6→4) → #7 (reroute) → #2 (after conclusion-shape read)
→ #1. Foundation B stays the external. (`meanFieldLimit` flag RESOLVED above —
conditional, not a B-free win; do not re-open. The real remaining mean-field
content is wiring `hDobrushin`'s discharge for the empirical curve, which the
current `dobrushin` signature doesn't directly cover.)
