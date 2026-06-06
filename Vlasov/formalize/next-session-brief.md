# Next-session brief (as of 2026-06-05, HEAD = `d46feb3`)

Durable hand-off. Build green; **2 sorries** (Basic 1, Coupling 1, CharFlow 0).

## Where this lands — the surface is `{#2, B}`

The deferred surface went 13 → … → 3 → **2**. The two remaining sorries:

* **#2** (`MathlibTODO_cauchyW1_hasNarrowLimit`, Basic 1625 / sorry 1647) —
  Picard / Prokhorov narrow limit. In-project *under W̄*; needs Foundation A
  under plain W₁ (see strategic finding).
* **Foundation B** (`foundationB_optimal_coupling_exists`, Coupling 276) — the one
  OT attainment theorem Mathlib lacks; sole sorry-dependency of `dobrushin`.
  A genuine external, not an attack target.

The marquee — existence **and** uniqueness **and** mean-field — runs on the single
`dobrushin_integrated_flow_bound_On` core (force-estimate-free *on the uniqueness/
mean-field side*; the existence/Picard side is still W₁ + force-estimate, see below).

## Strategic finding (this session): two goals, two COUPLED arcs (not one cost-swap)

User goals: (1) everything hinges only on external Foundation B; (2) remove `L<1`.
The earlier draft of this brief fused these into "one W̄ move." **That was wrong —
corrected here.** They are two coupled arcs:

* **#2's conclusion-shape read is DONE (verified).** #2 *concludes W₁-convergence*
  (`Tendsto (fun n => wasserstein1 (ν n) μ) atTop (𝓝 0)`, Basic 1588). Its sole
  consumer `picard_iterate_bundlesAs_VlasovMeasureCurve` (CharFlow 6969) re-exports
  that exact W₁-tendsto (CharFlow 6948/7003) to pin the Picard fixed point — **not
  weakenable**. So under plain W₁, closing #2 sorry-free needs the narrow ⟹ W₁
  upgrade (= Foundation A, a *second* external). **No "only B under plain W₁".**

* **Goal 1 (only-B) = the W̄ program.** Under `c = min(dist,1)` the dual test class
  is *bounded* 1-Lipschitz, so W̄ metrizes narrow directly (Mathlib Lévy–Prokhorov /
  Portmanteau). A becomes Mathlib-or-near; #2 reduces to Prokhorov tightness +
  moment-LSC, in-project. **A dissolves; #2 in-project.** This is what W̄ delivers.

* **Goal 2 (remove `L<1`) is a DISTINCT arc — W̄ does NOT accomplish it.** The
  `L<1` restriction is the `(T+1)²` *additive* offset, and (per M3 + the
  additive-offset watch-list) that offset lives in the **ODE ball-geometry** (the
  per-ball Picard–Lindelöf `hR`), **not in any Wasserstein step**. Removing it is
  the **window-chaining arc** (Dobrushin §6: fixed-δ N-window reconstruction on the
  Gronwall a-priori bound) — **metric-independent**. W̄ *enables/simplifies* the
  moment-control inside that chaining (bounded cost), but the offset-removal is the
  separate windowing work. **Do not scope "all-L falls out of W̄"** — the offset
  would still be sitting in the trajectory geometry.

Net: W̄ ⟹ only-B. Window-chaining ⟹ all-L. W̄ *enables* the chaining but isn't it.

## DONE log

* **6 → 4** (`a83fc35`): deleted orphaned #3/#4 + 5 dead helpers.
* **4 → 3** (`ca12381`): orphaned + deleted #7 via the marquee L=0 producer-switch.
* **3 → 2** (`d46feb3`, this session): closed **#1** `bcEqualFromLipschitzEqual` by
  reducing to `μ = ν` — `thickenedIndicator δ F` is bounded **Lipschitz**, so the
  1-Lipschitz hypothesis applies (scaled by `(K+1)⁻¹`); its integral → `μ F` as
  `δ→0`; `ext_of_generate_finite` over the closed-set π-system. **Metric-agnostic ⟹
  W̄-survivor.** First-moment hypotheses vestigial; signature unchanged. Built clean
  first try. Side effect: **`wasserstein1_eq_zero_iff_measure_eq` now fully
  sorry-free** (its only sorry'd dependency was #1).
* **O2 cost-parameterization — DONE, several sessions ago** (verified by grep this
  session; do NOT rebuild): `wassersteinCost c` core (Basic 900); cost-generic
  property layer `_self/_comm/_triangle/_le_of_lipschitz_map/_dual_lower_bound`
  (Basic 1042/1056/1084/1201/1327), all sorry-free; `wassersteinBar := wassersteinCost
  (min dist 1)` (Basic 1372) + all five `wassersteinBar_*` instantiations
  (Basic 1376–1397); the `min(dist,1)` additivity sanity-check validated at the time.
  Commits: **`61a3745`** (`_le_of_lipschitz_map` cost-generic, the ~70-line hard
  piece), **`09fbeca`** (remaining four property lemmas; `_triangle` needs no
  `c`-triangle hyp), **`83dabff`** (wassersteinBar def + instantiations). The earlier
  brief mislabelled this as "Phase 1 to build (~100–150 lines)" — that was a stale
  pre-O2 framing; it is banked.

## Next phase of the W̄ program — the EXISTENCE/PICARD consumer migration

O2 (the cost layer) is done; the remaining W̄ work is **migrating #2's consumer
chain off W₁ onto `wassersteinBar`**, so #2's conclusion becomes W̄-convergence (→
Prokhorov-tightness + moment close, no Foundation A). This is the existence-side
analog of the uniqueness/mean-field migration already done onto the integrated core,
and it is **substantial**, because the Picard tower is W₁-stated:

* `supW1On` (CharFlow 4144) + `supW1On_comm/self/triangle/iterated_triangle`
  (4148–4197) + `supW1On_le_two_moment…`/`…_ne_top…` (4333/4353).
* `Phi_supW1_contraction` (CharFlow 6612), the geometric/Cauchy contraction, and the
  bundler `picard_iterate_bundlesAs_VlasovMeasureCurve` (6939) + `VlasovMeasureCurve`'s
  `hW1Cont` field — all in W₁.

**The crux is the force-estimate fork (re-surfaced — NOT a mechanical swap).**
`Phi_supW1_contraction`'s Gronwall bounds its cross-field term through the
*measure-metric* force estimate `MathlibTODO_convolveLipschitzEstimate`
(`‖∇W∗ρ − ∇W∗σ‖ ≤ L·W₁`, consumed at CharFlow 4404 and 6329). One-substituting
`W₁ → W̄` makes that **false for unbounded ∇W** (the δ₀/δ_R wall; Dobrushin's
bounded-`B` requirement). So migrating the Picard contraction onto W̄ is **not** a
cost-generic instantiation — it needs either:
  (a) **bounded ∇W** (Dobrushin's `C_b¹` — the honest hypothesis), or
  (b) **re-architecting the existence contraction onto the coupling/integrated
      route** (the way uniqueness/mean-field already went).
This is the existence-side version of the force-estimate decision already made for
the marquee. **It is the substantive content of the W̄ existence migration**, and
the thing to scope first — before touching `supW1On`'s cost layer (which, being
property-only over the now-banked `wassersteinBar`, is the mechanical part).

## Marquee axiom footprints

* `vlasovWellPosedness` (existence) → sorryAx now **{#2} only** (monotone removal of
  #1 from the prior `{#1,#2}` certified at `ca12381`). Re-run `#print axioms` for a
  fresh certification if needed.
* `dobrushin` (mean-field) → sorryAx = **Foundation B only** (never depended on #1).
* `meanFieldLimit` → axiom-clean, but a **naming artifact** (see Standing items).

## Standing items (off the critical path — do not let evaporate)

* **`meanFieldLimit` — RESOLVED: naming-artifact, *with its consequence*.** It is
  **CONDITIONAL** (takes the Dobrushin estimate as a *hypothesis* `hDobrushin`,
  discharges it via one-line Grönwall), so its axiom-cleanness is **packaging, NOT a
  B-free deliverable**. The genuine mean-field deliverable is **`dobrushin` (modulo
  Foundation B)** + N→∞ convergence. Do **not** let "`meanFieldLimit` is axiom-clean"
  read as "the mean-field limit is axiom-clean." No re-read needed unless upgrading to
  the unconditional statement (routes through B; wiring `hDobrushin` for the atomic
  empirical `μ^N` is not a direct `dobrushin` application — `μ^N`'s flow is Newton
  dynamics — so the integrated core is the route, a genuine gap).

## Process note (P5 — completed-mis-remembered-as-pending, ×3 this session)

This brief shipped, twice in two turns, a *completed* item framed as pending: the
dead-helper cleanup (already done in `a83fc35`) and now the O2 cost-parameterization
(done in `61a3745`/`09fbeca`/`83dabff`). Plus `meanFieldLimit` (resolved, framed as
re-bankable). The brief-carrying mechanism drifts toward stale "to-build" framings
inherited from before the work landed. **Cheap guard before opening any "Phase N":
grep the committed record for the artifacts that phase would build; if they exist
sorry-free, the phase is DONE — re-point, don't rebuild.**
