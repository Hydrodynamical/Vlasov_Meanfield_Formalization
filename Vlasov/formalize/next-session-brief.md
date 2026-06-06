# Next-session brief (as of 2026-06-05, HEAD = `a83fc35`)

Durable hand-off. Build green; 4 sorries (Basic 2, Coupling 1, CharFlow 1).

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

## DONE — deletion pass (6 → 4), commit `a83fc35`

Deleted the orphaned cluster (#3, #4 + dead helpers `w1ContOn_lscNarrow_via_pureFA`,
`W1ContOn_integralContAt`, `W1ContOn_lt_top`, `W1ContOn_toRealContOn`,
`dobrushin_C_choice`) — 280-line cut, Basic.lean only, build green, deletion-
completeness doubly certified (named-axiom trace + green build). Inventory now
**4**: Basic #1 (1465), #2 (1590); CharFlow #7 (3461); Coupling B (291).

## Remaining genuinely-live surface (after the deletion pass → 4)

* **#7** `lipschitzFlowTrajectoryLipBound` (CharFlow 3446) — **NEXT TARGET.
  CORRECTED CHARACTERIZATION (read-3 fork verdict, 2026-06-05, P5 catch):** the
  prior "cleanest reroute-and-delete, zero proof" label was over-optimistic. #7's
  own docstring (RECLASSIFIED 2026-06-03) carries the real gate — the reroute
  threads a uniform first-moment bound `M_ρ`, "close NOT BUILT." Read 3 settled the
  fork **FAVORABLE / small-thread orphan** (certified):
  - Chain to #7 is single-caller-linear, no shared-consumer trap: marquee L=0
    (13476) → global Lagrangian `…isLagrangianVlasovSolution` (4109, only caller
    13476) →[4132]→ global plain `…isVlasovSolution` (3931, only caller 4132) →
    `vlasovTrajectoryLipschitzBound` (3484, only caller 4001) → #7. All 4 orphanable.
  - Marquee needs only per-T `IsLagrangianVlasovSolutionOn` (discharged 13600–13602
    via `hf_lag.toOn`), which the **certified sorry-free** producer
    `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn` (4366) concludes
    directly — `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no
    sorryAx (its weak-PDE dep 4197 uses sorry-free `vlasov_trajectory_lipschitz_bound_on`
    3736, never 3931/#7).
  - The `M_ρ` gate **relocates** to the marquee L=0 site as 4366's `M_ρ`
    hypothesis — but at L=0 the flow is affine and the `(1+|t|)‖z‖` bound is ALREADY
    present at 13444–13461, so `M_ρ := (1+T)·M_{f₀}` is a small thread. The
    general-L "could be large" fear is sidestepped (only ever instantiated at L=0).
  **Execution**: re-point the marquee `∀T …On` conjunct (13600–13602) to a per-T
  `…isLagrangianVlasovSolutionOn` (4366) call (build the On-form flow hyps by
  adapting the existing global discharges at 13477–13513; supply `M_ρ`); then
  cascade-delete 4109 → 3931 → `vlasovTrajectoryLipschitzBound` → #7 (~600 lines).
  Twin `vlasov_trajectory_lipschitz_bound_lag` (3532) is already callerless — leave
  (proved alt, W̄-useful) or delete. Net **4 → 3**. Small-thread orphan, NOT
  zero-proof — but decisively cheaper than close-via-twin (general-L) or #2.
  **Execution ordering — the `M_ρ` discharge is THIS surgery's soundness crux, and
  4366's certification does NOT cover it.** `#print axioms (4366) = [propext,
  Classical.choice, Quot.sound]` certifies 4366's body *given* its `M_ρ` hypothesis;
  it does NOT certify the rewire's *discharge* of that hypothesis. 4366 takes `M_ρ`
  as a hypothesis (`∀ s ∈ Icc 0 T, ∫‖y‖ ∂spatialMarginal(f s) ≤ M_ρ`), so the
  rewire must discharge it with an actual bound. So the FRESH SESSION'S FIRST
  leaf-check (before the rewire, well before the cascade delete): does the affine
  bound at 13444–13461 actually give `∫‖y‖ ∂spatialMarginal(vlasovSolutionViaPushforward
  charX charV f₀ s) ≤ (1+T)·M_{f₀}` for all `s ∈ Icc 0 T`, in the quantifier/form
  4366's `hM_ρ` wants? "Small thread" is the *prediction*; this leaf-check is the
  *confirmation*. Then: rewire second; **cascade-delete LAST**, gated on the rewired
  marquee being `#print axioms`-clean (no new sorryAx, no Foundation-B leakage from
  the new path) — replace→verify→delete, the same shape as #5/#6/#8; never delete
  the ~600-line old path before the new one is axioms-clean (else a subtly-wrong
  `M_ρ` discharge leaves the marquee's L=0 existence resting on it AND the revert is
  the whole surgery). Also confirm the affine `M_ρ` bound is L=0-specific and matches
  the rewired path's scope — the cascade is single-caller-linear (global producer
  3931's only caller is 4132), so nothing needs the global producer at general L,
  but the affine bound only covers L=0; confirm that alignment at execution.
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

Sequence: ~~deletion pass (6→4)~~ **DONE** (`a83fc35`) → #7 (certified small-thread
orphan, see above) → #2 (after conclusion-shape read)
→ #1. Foundation B stays the external. (`meanFieldLimit` flag RESOLVED above —
conditional, not a B-free win; do not re-open. The real remaining mean-field
content is wiring `hDobrushin`'s discharge for the empirical curve, which the
current `dobrushin` signature doesn't directly cover.)
