# Design notes — Vlasov formalization

## What the project formalizes

A Lean 4 / Mathlib formalization of the N-particle Vlasov mean-field
derivation (the "Dobrushin route"). The headline results are:

- **`weakEvolutionEmpiricalMeasure`** (prop:weak): the empirical
  measure of N Newton particles solves a weak Vlasov equation up to
  an explicit O(1/N) diagonal-correction residual.
- **`empiricalMeasureSolvesVlasov`** (cor:empirical-vlasov): the
  residual vanishes for trajectories avoiding the diagonal.
- **`dobrushin`** (thm:dobrushin): Wasserstein-1 stability of Vlasov
  solutions: ∃ C > 0, ∀ t ≥ 0, W₁(f_t, g_t) ≤ exp(C·t)·W₁(f_0, g_0).
- **`meanFieldLimit`**: combines `prop:weak` + `thm:dobrushin` to
  conclude convergence of empirical to Vlasov.

`weakEvolutionEmpiricalMeasure` and `empiricalMeasureSolvesVlasov` are
**fully proved** (no sorry).  `dobrushin` and `meanFieldLimit` are
proved *modulo* a small set of placeholder declarations representing
genuine gaps in Mathlib's measure-theory / OT infrastructure.

## The placeholder set

Three `theorem MathlibTODO_… := by sorry` placeholders, each labelled
honestly:

### 1. `MathlibTODO_convolveLipschitzEstimate`

> ‖(∇W ∗ ρ)(x) − (∇W ∗ σ)(x)‖ ≤ L · W₁(ρ, σ)

Decomposed into four constructive helpers via the dual-formula
(Kantorovich–Rubinstein "easy direction") proof.  The four helpers
ARE provable using existing Mathlib API — see the textbook 5-step
proof recorded in the docstrings + plan JSON.  Currently all four
remain sorries due to a structural issue with the statement (see
"Statement issue" below).

### 2. `MathlibTODO_wassersteinGronwallCoupling_W1ContOn`

> t ↦ (W₁(f_t, g_t)).toReal is continuous on [0, T].

Genuine PDE / measure-valued-ODE gap.  Needs either:
- narrow continuity of Vlasov solutions (a result *about Vlasov*, not
  about W₁) + the triangle inequality for W₁; or
- the equivalence with the coupling definition + tightness arguments.

Not provable from the dual formula alone; the sup of a continuous
family of functions is generally only lower semicontinuous, not
continuous.

### 3. `MathlibTODO_wassersteinGronwallCoupling_derivBound`

> liminf of difference quotient of t ↦ (W₁(f_t, g_t)).toReal
> is bounded by C·(W₁(f_t, g_t)).toReal.

Genuine PDE / coupling-theory gap.  This is literally Dobrushin's
1979 characteristic-flow coupling argument: pick the joint
distribution π_t := (Φ^f_t × Φ^g_t)_# π_0 for the characteristic
flows and an initial optimal coupling π_0, then bound how the cost
grows.

Not provable from the dual formula.  Requires (i) building the
characteristic flow for measure-valued ODEs, (ii) the equivalence
of dual and coupling definitions of W₁ (= full KR duality).

### 4. `vlasovWellPosedness` (carries a raw `sorry`)

Existence and uniqueness for the Vlasov equation. Not yet decomposed.
A deep PDE result that needs measure-valued Picard-Lindelöf +
narrow-continuity propagation. Out of scope for the current phase.

## Design choice: dual-formula `wasserstein1`

In `Basic.lean` we define

```lean
noncomputable def wasserstein1 (μ ν : Measure α) : ENNReal :=
  ⨆ (f : α → ℝ) (_ : LipschitzWith 1 f),
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
```

This is the **Kantorovich–Rubinstein dual formula** taken as the
*definition*. Trade-offs:

| Aspect | Dual definition (chosen) | Coupling definition |
|---|---|---|
| KR "hard direction" | Free (it's the definition) | Needs proof = full KR theorem |
| Static Lipschitz tests (convolveLipschitz) | Trivial — `le_iSup₂` against the definition | Needs KR "easy direction" |
| Dynamic regularity (W1ContOn, derivBound) | Hard — sup of continuous family is only LSC | Trivial — via flow pushforward |
| Mathlib infrastructure | Inner products + Bochner integrals ✓ | Couplings / joint measures ✗ |

The choice is appropriate for **static** mean-field statics
(convolveLipschitzEstimate) but is the wrong primitive for
**dynamic** stability arguments (W1ContOn, derivBound). The two
remaining sub-placeholders honestly capture this trade-off.

A future Mathlib contribution that fills the OT chapter (couplings,
optimal-coupling existence, KR equivalence theorem,
characteristic-flow theory for measure-valued ODEs) would retire
the dynamic placeholders. Estimated cost: ~1500–4000 lines across
many files, person-months of work. This is the "Shortcut A+B" path:
Lagrangian Vlasov solutions + coupling W₁, with KR equivalence as a
bridge lemma.

## Statement issue: `(wasserstein1 ρ σ).toReal`

The decomposer-generated convolveLipschitz helpers and the
wassersteinGronwallCoupling cascade conclude in `.toReal`-form
inequalities like

> ‖(∇W ∗ ρ)(x) − (∇W ∗ σ)(x)‖ ≤ L · (wasserstein1 ρ σ).toReal

`ENNReal.toReal` maps `⊤ ↦ 0`, so the inequality is **false** when
`wasserstein1 ρ σ = ⊤` (which can happen for measures lacking finite
first moments).

For our Vlasov setting all measures have finite first moments by
`HasFiniteFirstMoment`, so `wasserstein1` is in fact always finite
at the call sites — but the helper-level statements don't expose this.

To close the cascade we'd add a side hypothesis
`(hW : wasserstein1 ρ σ ≠ ⊤)` to each helper, propagate it through
the call sites, and prove `wasserstein1_lt_top_of_finite_moment`
(provable in ~30–50 lines via the bound
`sup_φ |∫φd(μ - ν)| ≤ ∫‖y‖d(μ + ν)`).  This is structural work
beyond the current cleanup pass.

## Sorry inventory (post-cleanup)

8 sorries total, all categorised:

| # | Location | Category |
|---|---|---|
| 1 | `vlasovWellPosedness` body | Deep PDE — no plan yet |
| 2-5 | `convolveLipschitz_*` helpers + parent body | Statement-blocked (`.toReal` finiteness) |
| 6 | `MathlibTODO_W1ContOn` | Genuine PDE placeholder |
| 7 | `MathlibTODO_derivBound` | Genuine PDE placeholder |
| 8 | `wassersteinGronwallCoupling_ofReal_le` + parent | Statement-blocked downstream |

The cleanup pass closed **10 of the original 18** sorries —
specifically every sorry that didn't require either (a) the
finiteness lemma, (b) measure-valued ODE theory, or (c) a deep PDE
existence theorem.
