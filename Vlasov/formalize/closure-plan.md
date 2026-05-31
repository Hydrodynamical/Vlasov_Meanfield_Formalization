# Closure plan — project-internal sorry → MathlibTODO-only state

**Session**: 2026-05-31, post-`bc7987e`. Single deliverable: this plan.
No Lean changes.

**Inventory state at session open**:
- 11 declarations using sorry (Basic.lean: 5 = 4 MathlibTODO + 1
  project-internal; CharFlow.lean: 6 declarations with sorries inside,
  spanning 11 sorries total — 1 MathlibTODO + 10 project-internal sub-
  sub-sorries across 5 declarations + 1 standalone).
- **Project-internal sorries**: 11 (across 6 declarations).
- **MathlibTODO sorries**: 5 (4 in Basic + 1 in CharFlow:
  `MathlibTODO_dobrushin_uniqueness_On`).

**Endpoint**: every sorry is a `MathlibTODO_*` declaration. The 11
project-internal sorries close via the categorization below.

---

## Sorry 1: `Basic.lean` L1490 — `w1_lscNarrow_integralContOn_lip`

**Goal (atom-level)**:
```
ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T)
```
Hypotheses: `IsVlasovSolution gradW f`, `∀ t, HasFiniteFirstMoment (f t)`,
`T : ℝ`, `0 ≤ T`, `φ : PhaseSpace d → ℝ`, `LipschitzWith 1 φ`.

**Category**: 3 (statement-level refactor).

**Closure path**: the project already has `w1_lscNarrow_integralContOn_lip_lag`
(Basic.lean L1508+) substantively proved using `IsLagrangianVlasovSolution`
+ pushforward equation. The non-`_lag` version remains sorry'd because
mollification approach (the docstring's strategy) fails for non-uniform-
in-t first moments — closing it requires DiPerna-Lions superposition
principle (out of scope per `vlasovWellPosedness`'s scope statement).

Concrete restate: change hypothesis from `IsVlasovSolution` to
`IsLagrangianVlasovSolution`, making this lemma a thin wrapper around
`_lag`. **OR** remove the lemma entirely if no consumer depends on it
(check: `grep w1_lscNarrow_integralContOn_lip` outside its definition;
likely a dead lemma since `_lag` is the working version).

**New placeholder**: none.

**Estimated scope**: ~20 lines in 1 session (restate or remove).

**Dependencies**: none.

---

## Sorry 2: `CharacteristicFlow.lean` L2688 — `vlasov_trajectory_lipschitz_bound` (SC.8 abstract)

**Goal (atom-level)**:
```
∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
  nhd ∈ nhds t ∧
  (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
    (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
  Integrable bound f₀
```
Hypotheses: gradW, ρ, charX, charV, f₀ as probability, φ smooth + compact
support, `IsCharacteristicFlow` (universal), gradW continuous, convolution
continuous, t : ℝ.

**Category**: 3 (statement-level refactor).

**Closure path**: the project has `vlasov_trajectory_lipschitz_bound_lag`
(L2899+) and `vlasov_trajectory_lipschitz_bound_on` (L2962+) substantively
proved. The non-`_lag`/`_on` universal version remains sorry'd because
the existential `bound` needs an integrability hypothesis (M_ρ-like)
which the universal signature lacks.

Concrete restate: add `M_ρ` + first-moment hypotheses matching the `_on`
variant's signature. **OR** remove the lemma entirely (the project uses
`_lag` / `_on` exclusively; `vlasov_trajectory_lipschitz_bound` may be
dead).

**New placeholder**: none.

**Estimated scope**: ~20 lines in 1 session (restate or remove).

**Dependencies**: none.

---

## Sorry 3: `CharacteristicFlow.lean` L6351 — `_picard_fixedPointFlow.hq_lt`

**Goal (atom-level)**:
```
q < 1
```
where `q := gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * (2 * M)) T`.

Hypotheses in scope: `LocalSmallness L T` (i.e., `L * (T+1)² < 1`),
`hT : 0 < T`, `M_nn : 0 ≤ M`.

**Category**: 3 (statement-level refactor — add hypothesis).

**Closure path**: the existing comment at L6336-6342 documents the
issue: `LocalSmallness L T` doesn't directly give `gronwallBound (...) T < 1`.
The cleanest fix per the comment is to add a new hypothesis
`hTL_contraction : L · (exp T - 1) < 1` (the Gronwall version of the
smallness constraint) and propagate through `vlasovWellPosedness_local`,
`_glue_step`, `_forward`.

This is a structural restate: the hypothesis change ripples through
three callers (each needs to thread the new hypothesis OR prove it
from a stronger smallness constraint).

**New placeholder**: none.

**Estimated scope**: ~30-50 lines in 1 session (hypothesis addition +
propagation through `_local`, `_glue_step`, `_forward`).

**Dependencies**: none (this is a pure structural change; doesn't
depend on other sorries).

---

## Sorry 4: `CharacteristicFlow.lean` L6359 — `_picard_fixedPointFlow` Picard sequence + contraction

**Goal (atom-level)**:
```
∃ x : ℕ → VlasovMeasureCurve d T M,
    ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
         ENNReal.ofReal (q ^ k * D₀)
```
Hypotheses: f₀, charX/charV setup, μ₀, M, q (Picard contraction factor),
D₀ (initial bound), hq_nn, hq_lt (sorry 3 above).

**Category**: 1 (closeable against existing infrastructure).

**Closure path**: compose `Phi_step` (CharFlow L4xxx) for the iteration
step + `Phi_supW1_contraction` (CharFlow L5xxx) for the contraction bound
+ induction on n. The body is the "load-bearing Picard math" per the
docstring; estimated 150-220 lines.

**New placeholder**: none.

**Estimated scope**: ~150-220 lines in 1-2 sessions (the largest single
substantive close in the Category 1 group).

**Dependencies**: requires sorry 3 (`hq_lt`) to be closed first, since
the result-bound uses `q` and the contraction needs `q < 1` to apply.

---

## Sorry 5: `CharacteristicFlow.lean` L6442 — `_picard_fixedPointFlow` self-consistency

**Goal (atom-level)**:
```
∀ t ∈ Set.Icc (0 : ℝ) T,
  ρ_lim.extend t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)
```
Hypotheses: ρ_lim from `picard_iterate_bundlesAs_VlasovMeasureCurve`,
charX/charV from Stage 1.9 flow against ρ_lim.extend, contraction bound
from sorry 4.

**Category**: 1 (closeable against existing infrastructure).

**Closure path**: triangle through `x n` using contraction + tendsto.
Specifically: `supW1On (Φ ρ_lim) ρ_lim ≤ supW1On (Φ ρ_lim) (Φ ρ_n) +
supW1On (Φ ρ_n) ρ_n + supW1On ρ_n ρ_lim`; first → 0 via Φ continuity,
middle = supW1On (x_{n+1}) (x_n) ≤ q^n · D₀ → 0, third → 0 by tendsto.
Yields Φ(ρ_lim) = ρ_lim; then `Φ ρ_lim = spatialMarginal ∘
vlasovSolutionViaPushforward charX charV f₀` by definition of Φ.

**New placeholder**: none.

**Estimated scope**: ~80 lines in 1 session.

**Dependencies**: requires sorry 4 (Picard sequence + contraction) since
the triangle argument uses x_n's contraction.

---

## Sorry 6: `CharacteristicFlow.lean` L6489 — `_picard_fixedPointFlow` universal-in-s convolution continuity

**Goal (atom-level)**:
```
∀ s, Continuous (fun x_pt =>
  convolveFunctionMeasure gradW
    (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x_pt)
```
Hypotheses: per L6486 comment, "needs extend_convCont applied via
h_self_consist."

**Category**: 1 (closeable against existing infrastructure).

**Closure path**: for `s ∈ Icc 0 T`, use `VlasovMeasureCurve.extend_convCont`
(already used at L6402-6412 for `ρ_lim.extend`) + sorry 5 (self-consistency)
to bridge. For `s ∉ Icc 0 T`, the spatial marginal is the clamped value;
use the clamp identity past T.

**New placeholder**: none.

**Estimated scope**: ~30 lines in 1 session.

**Dependencies**: requires sorry 5 (self-consistency) to bridge
ρ_lim.extend ↔ spatialMarginal.

---

## Sorry 7: `CharacteristicFlow.lean` L6494 — `_picard_fixedPointFlow` AEMeasurable witness

**Goal (atom-level)**:
```
∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀
```
Hypotheses: charX/charV from Stage 1.9 flow construction; the comment
at L6490-6491 notes "Stage 1.8 territory — requires continuity-in-z of
the Picard fixed-point construction."

**Category**: 2 (closeable by introducing a new `MathlibTODO_*` placeholder).

**Closure path**: the continuity-in-z (and thus measurability) of the
Picard fixed-point construction is a non-trivial property — Stage 1.9's
output `exists_vlasov_characteristicFlow_global_smallT` does not expose
it directly. The comment explicitly defers to "Stage 1.8 territory."

The right closure adds a new placeholder for the AEMeasurable property
of the per-z trajectory in the Picard fixed-point construction:

**New placeholder**:
```lean
/-- Mathlib-TODO: AEMeasurable-in-initial-condition of the characteristic flow
constructed via Stage 1.9's `exists_vlasov_characteristicFlow_global_smallT`.

The Picard fixed-point construction is continuous in the initial condition
on the bounded ball (via the contraction); measurability over the full
phase space follows from per-ball construction + Carathéodory measurable
selection. -/
theorem MathlibTODO_picardFlowAEMeasurable
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) ...
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (μ : Measure (PhaseSpace d)) :
    ∀ s, AEMeasurable (fun z => (charX s z, charV s z)) μ
```

**Bucket-1 PR scope**: focused single-theorem PR; the continuity-in-z
property of Picard fixed-points is standard ODE theory (Hartman, Coddington-
Levinson) but the AEMeasurable wrapper isn't currently in Mathlib.

**Estimated scope**: ~30-50 lines (placeholder + 5-10 line use at L6494)
in 1 session.

**Dependencies**: none (this is independent of other Picard sub-sorries).

---

## Sorry 8: `CharacteristicFlow.lean` L6501 — `_picard_fixedPointFlow` universal-in-s convolution integrability

**Goal (atom-level)**:
```
∀ s (x : PhysSpace d),
  Integrable (fun y => gradW (x - y))
    (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
```
Hypotheses: same as sorry 6 (charX/charV + h_self_consist).

**Category**: 1 (closeable against existing infrastructure).

**Closure path**: same shape as sorry 6 — for `s ∈ Icc 0 T`, use the
dominator pattern at L6378-6398 (Lipschitz gradW + first moment) +
sorry 5 (self-consistency) bridge. For `s ∉ Icc 0 T`, the clamped value's
integrability follows from clamp identity past T.

**New placeholder**: none.

**Estimated scope**: ~30 lines in 1 session.

**Dependencies**: requires sorry 5 (self-consistency).

---

## Sorry 9: `CharacteristicFlow.lean` L7559 — `_glue_step` case (a) `h_cont_g`

**Goal (atom-level)**:
```
ContinuousAt (fun t' =>
  (∫ z, (inner z.2 (gradXφ z) -
          inner (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                (gradVφ z)) ∂(f_next t')) + 0) T
```
Hypotheses: φ smooth + compact support, gradXφ/gradVφ gradients,
f_next defined piecewise from f_prev + g, T+T_0 > 0.

**Category**: 1 (closeable against existing infrastructure — including the
newly-landed `MathlibTODO_convolveContinuousAtOfNarrowMoment`).

**Closure path**: per planning-notes.md decomposition, ~330-540 lines
across 4-5 commits:
- Sub-helper A: narrow continuity of `t ↦ spatialMarginal(f_next t)` at T
  for general bounded continuous test functions (~80 lines).
- Sub-helper B: moment continuity of `t ↦ ∫ ‖y‖ ∂(spatialMarginal(f_next t))`
  at T (~80 lines).
- Sub-helper C: convolution integrability uniformity (~30-50 lines).
- h_cont_g LEFT close composing A + B + C + `MathlibTODO_convolveContinuousAtOfNarrowMoment`
  + outer DCT (~150 lines).
- h_cont_g RIGHT close mirroring LEFT (~150 lines).
- Union for h_cont_g → `_glue_step` cluster retirement (~20 lines).

**New placeholder**: already landed (`MathlibTODO_convolveContinuousAtOfNarrowMoment`,
commit `a123d63`).

**Estimated scope**: ~330-540 lines in 2-3 sessions.

**Dependencies**: depends on the landed placeholder. No project-internal
sorry dependencies.

---

## Sorry 10: `CharacteristicFlow.lean` L8572 — Stage 6 t=0 boundary

**Goal (atom-level)**:
```
ContinuousWithinAt (fun t => ∫ z, g z ∂(f t)) (Set.Ici 0) 0
```
(after `rw [← h_eq]` which substitutes `0 = t₀`).

Hypotheses: g continuous + bounded range, sol N agreement, h_sol_lag N's
flow witnesses, narrowness of f t at t > 0 (proved in surrounding code).

**Category**: 1 (closeable against existing infrastructure).

**Closure path**: per planning-notes.md (Stage 6 t=0 P5 finding banked
in `ebbcdeb`): same DCT pattern as h_cont_f LEFT/RIGHT but applied at
the t=0 endpoint.
- Enrich `_universal_existence`'s destructure of `h_sol_lag N` to extract
  boundary regularity from `vlasovWellPosedness_local`'s output bundle
  (~30-50 lines threading).
- Apply `continuousWithinAt_of_dominated` with constant bound + pointwise
  continuity from boundary regularity (~30-50 lines).

**New placeholder**: none.

**Estimated scope**: ~80-100 lines in 1 session.

**Dependencies**: none (boundary regularity already in
`vlasovWellPosedness_local`'s output bundle; just needs threading).

---

## Sorry 11: `CharacteristicFlow.lean` L8720 — Marquee `L ≥ 1` regime

**Goal (atom-level)**: the marquee theorem's conclusion (existence of
forward-only Vlasov solution) for the case `L ≥ 1`.

Hypotheses: `hL_pos : 0 < L`, `hL_lt : ¬(L < 1)` (i.e., `L ≥ 1`).

**Category**: 3 (statement-level refactor).

**Closure path**: per the comment at L8718-8720 ("out of scope pending
M-series +1 removal"), the L≥1 regime requires the W̄ refactor (removing
the additive `+1` offset in the smallness constraint, allowing arbitrary
Lipschitz constants).

Concrete restate options:
- (a) Add `hL_lt : (L : ℝ) < 1` as a hypothesis to `vlasovWellPosedness`,
  removing the case split entirely. The marquee's scope becomes "0 ≤ L < 1
  regime." Out-of-scope items become external (project doesn't claim them).
- (b) Keep current case structure with the L≥1 case routing through a new
  `MathlibTODO_vlasovWellPosednessLargeL` placeholder. Adds a placeholder
  but keeps the marquee's universal-L claim.

Option (a) is cleaner per the M-series statement-correctness pattern
(commit `de135c7`'s forward-only refactor precedent). The marquee
documents its scope honestly.

**New placeholder**: optional (option (b) only).

**Estimated scope**: ~20 lines in 1 session (restate marquee
hypothesis + simplify case split).

**Dependencies**: none.

---

## Aggregate

**Category 1 sorries** (closeable against existing Mathlib + project
infrastructure): **6** (sorries 4, 5, 6, 8, 9, 10). Total estimated
**~470-650 lines** across **~4-6 sessions**.

**Category 2 sorries** (require new MathlibTODO placeholder): **1**
(sorry 7). Adds **1** new MathlibTODO placeholder
(`MathlibTODO_picardFlowAEMeasurable`). Total estimated **~30-50 lines**
across **1 session**.

**Category 3 sorries** (closeable by restating surrounding declaration):
**4** (sorries 1, 2, 3, 11). Total estimated **~90 lines** across
**~2-3 sessions** (sorries 1, 2 may be combined into one cleanup session;
sorry 3 propagation is its own session; sorry 11 is its own).

**Total work to MathlibTODO-only state**: **~590-790 lines** across
**~7-10 focused sessions**.

**Final MathlibTODO inventory**:
- Currently: 5 (4 in Basic.lean + 1 in CharFlow.lean: `MathlibTODO_dobrushin_uniqueness_On`).
- Wait — recount: 5 in Basic (1170, 1461, 1768, 1892, plus
  the newly landed 1461 `MathlibTODO_convolveContinuousAtOfNarrowMoment`)
  + 1 in CharFlow (`MathlibTODO_dobrushin_uniqueness_On` at L8322) = **6**.
- After closure plan (Category 2 adds 1): **7** placeholders.
- Plus Stage 6 may surface another placeholder if Stage 6 t=0 requires
  threading enrichment that's actually a sub-placeholder; estimated
  no additional placeholder per the P5 finding.

**Endpoint placeholder count: 7.**

---

## Closure ordering recommendation

Per the brief's criteria: (a) cluster retirements where possible;
(b) Category 1 before Category 2; (c) foundational before dependent;
(d) avoid tail-end >150-line attempts.

**Phase 1 — Category 3 quick wins** (1-2 sessions):
1. **Session 1**: sorries 1 + 2 cleanup. Both are restate-or-remove
   restatements of legacy lemmas. Likely ~40 line combined session
   (`w1_lscNarrow_integralContOn_lip` + `vlasov_trajectory_lipschitz_bound`).
   Retires 2 declarations directly (10 → 8 sorry'd declarations).
2. **Session 2**: sorry 11 — marquee L≥1 restate. Restate marquee
   hypothesis to `L < 1`, simplify case split. ~20 lines. Removes the
   L≥1 sub-sorry; marquee's "L < 1" case becomes the only substantive
   case.  Sub-sub-sorries: -1.

**Phase 2 — Foundational Category 3** (1 session):
3. **Session 3**: sorry 3 — `hq_lt` hypothesis addition + propagation
   through `_local`, `_glue_step`, `_forward`. ~30-50 lines. Unblocks
   Phase 3-4 by giving the q < 1 contraction parameter.

**Phase 3 — Cheap Category 1 + Category 2** (1-2 sessions):
4. **Session 4**: sorries 6 + 8 — universal-in-s conv continuity +
   integrability for `_picard_fixedPointFlow`. ~60 lines combined.
   (Depends on sorry 5 which is Phase 4; if Phase 3 happens first, these
   are partial — but the universal-in-s `t ∈ Icc 0 T` case can close,
   leaving only the `t ∉ Icc 0 T` clamp-identity part.)
5. **Session 5**: sorry 7 — AEMeasurable placeholder + use. ~30-50 lines.
   Adds 1 new MathlibTODO placeholder. Sorry trajectory: +1 placeholder,
   -1 sub-sub-sorry (sorry 7 retires inside `_picard_fixedPointFlow`).

**Phase 4 — Substantive Category 1** (3-4 sessions):
6. **Session 6**: sorry 4 — Picard sequence + contraction. ~150-220 lines.
   Heart of the Picard fixed-point construction. Foundational for sorry 5.
7. **Session 7**: sorry 5 — self-consistency. ~80 lines. Composes sorry 4's
   contraction with tendsto. After this, sorries 6/8 can fully close
   (clamp-past-T part).
8. **Session 8**: sorry 10 — Stage 6 t=0 boundary. ~80-100 lines. Stage 6
   declaration retires (cluster).
9. **Sessions 9-11**: sorry 9 — `_glue_step` h_cont_g. ~330-540 lines
   across 2-3 sub-sessions per the planning-notes decomposition:
   - Sub-session A: sub-helpers (narrow continuity + moment continuity +
     integrability uniformity) for spatialMarginal(f_next). ~190 lines.
   - Sub-session B: h_cont_g LEFT substantive. ~150 lines.
   - Sub-session C: h_cont_g RIGHT + union → `_glue_step` cluster retires.
     ~170 lines.

**After all sessions complete**:
- Project-internal sorries: 0.
- MathlibTODO declarations: 7.
- Build clean.

**Cluster retirements achieved**:
- Session 1: `w1_lscNarrow_integralContOn_lip` + `vlasov_trajectory_lipschitz_bound`
  (if removed) OR restated.
- Session 2: marquee declaration becomes sorry-free if L≥1 was its last
  sub-sub-sorry. (Currently marquee has only the L≥1 sub-sub-sorry per
  the inventory — yes, marquee cluster-retires in Session 2.)
- Session 5: AEMeasurable retired from `_picard_fixedPointFlow` body.
- Sessions 6+7+4+5+6+8: progressively retires `_picard_fixedPointFlow`'s
  remaining sorries (4, 5, 6, 8 close after sorry 5 lands at Session 7).
  `_picard_fixedPointFlow` declaration retires after Session 7 (or Session
  4 if Session 4 fully closes 6+8 modulo Session 5's residual; cluster
  retirement requires all 6 sub-sub-sorries closed).
- Session 11: `_glue_step` declaration retires (cluster).
- Session 8: `_universal_existence` declaration retires (cluster, since
  Stage 6 t=0 is its only sub-sub-sorry).

Final declaration retirement count: 5 project-internal declarations
retire (w1_lscNarrow, vlasov_trajectory_lipschitz_bound, marquee,
_picard_fixedPointFlow, _glue_step, _universal_existence — adjusted to
4 if marquee restate doesn't fully retire but moves to a placeholder).

---

## Uncharacterized items

None. All 11 project-internal sorries cleanly categorize into 1/2/3.
No P2 firings during inventory.

---

## Trajectory implication

Phase A endpoint (substantive completion in `0 < L < 1, t ≥ 0` regime):
**after Session 11** at the recommended ordering. That's **~11 focused
sessions** to MathlibTODO-only state — substantially larger than the
prior "3-4 focused sessions" framing, which had been based on closure
estimates that hadn't accounted for the full project-internal sorry
inventory.

The original "Phase A endpoint at 3-4 sessions" assumed `_picard_fixedPointFlow`'s
6 sub-sub-sorries collapsed under their own closure dynamics; the
inventory pass reveals each is a focused leaf requiring its own session
(or pair of sessions). The substantive scope is real.

**Honest framing**: ~7-11 focused sessions to MathlibTODO-only state.
Of those:
- ~5 sessions are cheap (Phase 1-3): 2 in Phase 1 + 1 in Phase 2 +
  2 in Phase 3. These retire many declarations quickly.
- ~6 sessions are substantive (Phase 4): sorries 4, 5, 9 (3 sub-sessions),
  10. These are the load-bearing closes.

W̄ refactor remains separate post-MathlibTODO-only work, adding another
2-4 sessions for that arc.

**Total trajectory**: ~11 sessions to MathlibTODO-only state +
~2-4 sessions for W̄ refactor (if pursued) = ~13-15 focused sessions
to absolute Phase A+B completion.

The cleanup document phase can run in parallel with W̄ refactor or
sequentially per the Phase B sequencing decision (still pending).
