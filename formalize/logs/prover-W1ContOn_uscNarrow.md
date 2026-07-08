# Agent run: sorry-prover on `MathlibTODO_W1ContOn_uscNarrow`

**Date**: 2026-05-28
**Outcome**: structural-failure (0 iterations, sorry left in place)
**Agent ID**: aebd7f004d54fadb7

## Target

`MathlibTODO_W1ContOn_uscNarrow` in `Vlasov/Basic.lean`.
Signature was widened in commit `5372fac` with characteristic-flow
hypotheses (the Eulerian → Lagrangian gap), expecting the widening
plus the OT infrastructure to yield a ~5-line composition proof.

## Why the proof fails (agent's diagnosis)

The project's `wasserstein1` is defined via the **KR dual** formula
`⨆ h 1-Lipschitz, ENNReal.ofReal (∫ h dμ − ∫ h dν)`. This is a
pointwise supremum of continuous-in-t functionals (under
`IsVlasovSolution`'s `WeakEvolutionEq`-derived continuity), and:

- **Sup of continuous → LowerSemicontinuous, NOT UpperSemicontinuous.**

The USC proof via the *primal* (coupling) formula
`⨅ π coupling, ∫⁻ edist ∂π` would compose:

  USC of integrand-in-t (from `HasDerivAt.continuousAt` on flow)
  → USC of ∫ integrand (continuous integral lemma)
  → USC of ⨅ over couplings (`upperSemicontinuousOn_biInf`).

But the project only has the **easy** direction
`wasserstein1 ≤ ⨅ coupling, ∫⁻ edist ∂π`
(`wasserstein1_pushforward_le_iInf`, Coupling.lean L270). The
**EQUALITY** (the hard direction of Kantorovich-Rubinstein, requiring
Hahn-Banach + Prokhorov) is marked `← TODO` in
`Vlasov/OT/Coupling.lean` line 12.

USC of the *upper bound* does not imply USC of the *bounded function*.

## Mathlib state

- Mathlib has **no** `Wasserstein` files at all (confirmed via `find`).
- All three missing pieces — KR hard direction, optimal coupling
  existence, pushforward equality — are absent.
- Mathlib *has* `upperSemicontinuousOn_biInf`, `upperSemicontinuousOn_iInf`,
  and friends — these are downstream lemmas that would apply *if* the
  equality were available.

## Wished-for API to unblock this target

A theorem of the shape

```lean
theorem wasserstein1_eq_iInf_coupling
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_fm : Integrable (fun x => dist x base) μ) -- or analogous
    (hν_fm : Integrable (fun x => dist x base) ν) :
    wasserstein1 μ ν = ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
      ∫⁻ z, edist z.1 z.2 ∂π
```

(or just the `≥` direction, since `≤` is already proved).

With this in hand, `uscNarrow` becomes a real ~5-line composition.

## CLAUDE.md confirmation

The project's persistent memory has this exact trade-off documented
under "Vlasov-specific design choices" — `wasserstein1`'s dual-formula
definition makes dynamic regularity (USC, derivBound) "hard". The
**planning loop missed this signal**. A planner-side L-lesson: before
launching an agent on a `MathlibTODO_*` target, re-read CLAUDE.md's
trade-off section.

## Agent workflow observations (sorry-prover side)

1. **§0 skip rule worked correctly**: the agent recognized this as
   structurally blocked and exited at iteration 0 rather than wasting
   iterations on doomed tactics.
2. **Diagnosis accuracy**: the agent's structural analysis (sup of
   continuous → LSC, equality needed for USC) was precise and matched
   the project's own design memo.
3. **Logging gap**: the agent's report claimed it had written to this
   log path, but the file did not exist on disk. The §6 logging step
   appears to be at risk of being silently skipped under the §0 fast-
   exit path. Possible spec edit: require the log file to be created
   even on structural-failure exits.

## Recommended unblocking move (not pursued in this session)

Either (a) prove the hard direction of KR in the project as a new
top-level theorem `wasserstein1_eq_iInf_coupling`, or (b) introduce it
as `MathlibTODO_wasserstein1_eq_iInf_coupling` placeholder and close
usc/derivBound conditionally on it.

Both targets (`uscNarrow` and `derivBound`) share this blocker.

---

## 2026-05-28 · Second attempt · `MathlibTODO_W1ContOn_uscNarrow`

**Result:** skipped (structurally blocked — see analysis below)
**Iterations:** 0/8
**Sorry count:** 4 → 4 (no change)
**Pre-flight (§3.5):** validated `wasserstein1_eq_wasserstein1_coupling`, `upperSemicontinuousOn_iInf`, `ContinuousOn.upperSemicontinuousOn`; 0 dropped hints; 0 in-loop rejections.

### Context

The prior attempt correctly diagnosed the fundamental blocker. This
second attempt was triggered with the newly-available lemma
`wasserstein1_eq_wasserstein1_coupling` in `Vlasov/OT/Coupling.lean:272`.
The question: does this new equality plus the iInf-based USC machinery
yield a closed proof?

### Why the answer is still No

**Blocker 1 — KR equality itself uses a sorry (transitive).**
`wasserstein1_eq_wasserstein1_coupling` is proved by `le_antisymm`
using:
  - `wasserstein1_le_wasserstein1_coupling` (fully proved), AND
  - `MathlibTODO_wasserstein1_coupling_le_wasserstein1` (sorry'd,
    Coupling.lean:253 — the hard direction of KR).

Lean's sorry-propagation rule: any theorem proved using a sorry'd
theorem is itself flagged as "declaration uses sorry". So replacing
the target sorry with a proof that calls `wasserstein1_eq_wasserstein1_coupling`
would eliminate the warning on line 1248 of Basic.lean, but the
warning would reappear — we'd still have 4 sorry warnings total
(the KR hard direction + the three others). The goal is 4 → 3.

**Blocker 2 — Coupling index set varies with t.**
After rewriting `wasserstein1 (f t) (g t)` to
`wasserstein1_coupling (f t) (g t) = ⨅ π (_ : IsCoupling π (f t) (g t)), ∫⁻ edist ∂π`,
the infimum is over couplings of `(f t, g t)`. This index set varies
with `t`. Mathlib's `upperSemicontinuousOn_iInf` requires a FIXED
index type `ι : Type*` — i.e., `⨅ (i : ι), f_i t`. There is no
`upperSemicontinuousOn_iInf_varying_domain` lemma.

To reduce to the fixed-index case, one would push forward a fixed
coupling `π₀` of `(f 0, g 0)` via flow maps `(Φ_t, Ψ_t)` satisfying
`f t = (Φ_t)_# (f 0)`, `g t = (Ψ_t)_# (g 0)`. Then
`wasserstein1_coupling (f t) (g t) ≤ ∫⁻ edist(Φ_t(z.1), Ψ_t(z.2)) dπ₀`
for every `π₀`, and the infimum over the fixed set of initial couplings
is USC via `upperSemicontinuousOn_iInf` provided continuity of
`t ↦ ∫⁻ edist(Φ_t(z.1), Ψ_t(z.2)) dπ₀` (which follows from
continuity of the flow).

**Blocker 3 — Flow data absent from signature.**
The current signature has `hf : IsVlasovSolution gradW f`, which
provides `WeakEvolutionEq` (weak PDE data for smooth compactly-
supported test functions φ). It does NOT provide characteristic flow
maps `Φ_t : PhaseSpace d → PhaseSpace d` satisfying
`Measure.map Φ_t (f 0) = f t`. Adding flow data would require
widening the signature — which the user explicitly reverted from a
prior attempt.

**Why `WeakEvolutionEq` cannot substitute for flow data.**
`WeakEvolutionEq` gives `HasDerivAt (fun s => ∫ φ d(f s)) _ t` only
for φ ∈ C_c^∞. The 1-Lipschitz test functions in the `wasserstein1`
KR dual are NOT in C_c^∞ (they may have support ℝ^d). So the
`WeakEvolutionEq` continuity (`W1ContOn_integralContAt`, Basic.lean:1283)
does not apply to the test functions appearing in the `wasserstein1`
definition. There is no direct route from `IsVlasovSolution` to
USC of `t ↦ wasserstein1 (f t) (g t)`.

### Structural diagnosis

The theorem `MathlibTODO_W1ContOn_uscNarrow` requires all three of:
1. The hard direction of KR (`MathlibTODO_wasserstein1_coupling_le_wasserstein1`).
2. Characteristic flow maps `Φ_t`, `Ψ_t` (or equivalent Lagrangian data).
3. Continuity of the flow in `t` (for the dominated-convergence argument
   on `t ↦ ∫⁻ edist(Φ_t z.1, Ψ_t z.2) dπ₀`).

None of these is currently available in the project without additional
either Mathlib API or new hypotheses. The theorem is correctly named
with the `MathlibTODO_` prefix — it represents a genuine API gap.

### Lookup trail
- `wasserstein1_eq_wasserstein1_coupling` — `Vlasov/OT/Coupling.lean:272`
  (confirmed: transitively sorry'd via line 253)
- `upperSemicontinuousOn_iInf` — `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1197`
  (requires fixed index type; does not apply to varying-domain infs)
- `upperSemicontinuousOn_biInf` — `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1201`
  (same constraint; `p : ι → Prop` is a fixed predicate on a fixed `ι`)
- `ContinuousOn.upperSemicontinuousOn` — `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:799`
  (would work IF we had ContinuousOn, which requires flow data)
