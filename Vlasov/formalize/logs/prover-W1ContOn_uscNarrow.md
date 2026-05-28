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
