# Next-session brief (as of 2026-06-05, HEAD = `72999aa`)

Durable hand-off so the next session opens warm. Build green; 6 sorries.

## Current state — marquee on the integrated coupling core

Both halves of the marquee now route through the single
`dobrushin_integrated_flow_bound_On` core (base-generic, axiom-clean):

* **uniqueness** — `dobrushin_uniqueness_On` at `proj = id`, `π₀ = f 0`
  (commit `118729d`); axiom-clean (no `sorryAx`).
* **mean-field** — `dobrushin_meanfield_On` at `proj = fst/snd`, `π₀` = optimal
  coupling (Foundation B); `dobrushin_package_exists` re-pointed through it with
  `C = 2·(max 1 L)`, windowing each `t ≥ 0` at `T = t+1` via `.toOn`
  (commit `72999aa`). Retired #5/#6 (8 → 6) and deleted the ~15-declaration
  dead chain (`MathlibTODO_wassersteinGronwallCoupling` and below).

**Axiom decomposition (verified to the leaf, axiom-naming technique):**
`dobrushin` depends on `[propext, Classical.choice, Quot.sound,
foundationB_optimal_coupling_exists]` with **no `sorryAx`** — its sole
sorry-dependency is Foundation B, zero A-side / existence leakage.
`vlasovWellPosedness` carries `sorryAx` (existence side) but **not** Foundation B.

## Remaining surface (6 sorries), cleanly typed

| sorry | file | type |
|---|---|---|
| Foundation B (`foundationB_optimal_coupling_exists`) | OT/Coupling.lean | the **one genuine OT external** — sole mean-field dependency; maybe shrinkable to ε-optimal (Dobrushin 6.8) |
| #1 `bcEqualFromLipschitzEqual_polish_firstMoment` | Basic.lean | A-side (W̄ dissolution: subalgebra separation) |
| #2 `cauchyW1_hasNarrowLimit` | Basic.lean | existence-side (Prokhorov) |
| #3 `w1LowerSemicontinuous…` | Basic.lean | A-side (W̄: native-bounded-sup-LSC) |
| #4 `bcNarrowFromSmoothCompactNarrow` | Basic.lean | A-side (W̄: Portmanteau citation) |
| #7 `lipschitzFlowTrajectoryLipBound` | OT/CharacteristicFlow.lean | isolated in-project close (L=0 reroute), W̄-independent |

## Standing small task — confirmed-dead helper cleanup (DEFERRED)

After the mean-field re-point, these five Basic.lean helpers are
**confirmed callerless** (verified 2026-06-05: only comment/docstring
references; `W1ContOn_integralContAt` is called solely by the also-dead
`w1ContOn_lscNarrow_via_pureFA`):

* `W1ContOn_lt_top`
* `W1ContOn_toRealContOn`
* `W1ContOn_integralContAt`
* `w1ContOn_lscNarrow_via_pureFA`  *(this one references #3/#4)*
* `dobrushin_C_choice`

**Disposition: confirmed-dead, delete in a focused revertable commit.** They sit
**adjacent to the retained #3/#4 placeholders** in Basic.lean — delete carefully
(verify docstring-start/end boundaries; do NOT touch #3 ≈ L2104 / #4 ≈ L2183).
Not mystery dead code — intentionally retained to keep the 8→6 milestone commit
off the delicate #3/#4 region.

## Next constructive arc (when opening fresh)

**A-side W̄ dissolution** — now *reachable* because the consumers route through
the integrated core. #3/#4 take the bounded-cost dissolution (native-bounded-
sup-LSC / Portmanteau), then #1 via subalgebra, then #2/#7 existence-side.
W̄-durable; the consumer-need reads are done (all dissolve via cheap directions,
no hard metrization bridge).

**First-read discipline (do before building):** re-confirm each A-side
placeholder's W̄ dissolution actually *reaches* its consumer now that the
consumers migrated to the integrated core — the reachability changed, so the
dissolution mechanism's reach must be re-verified, not assumed.

`#7` is takeable anytime as a self-contained shorter task.
