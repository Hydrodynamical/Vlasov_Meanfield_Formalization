## 2026-05-28T12:00:00Z · w1_lscNarrow_integralContOn_lip

**Result:** failure — structural blocker
**Iterations:** 0/8 (no edit attempted; blocker identified at analysis phase)
**Sorry count:** 4 → 4 (no change)
**Pre-flight (§3.5):** validated 3 hints; dropped 0; rejected 0 in-loop citations

### What didn't work

**Structural analysis: why the proof is blocked**

The target is `ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T)` for 1-Lipschitz φ,
given `IsVlasovSolution gradW f` and `HasFiniteFirstMoment (f t)` for all t.

**Available hypotheses and what they give:**
- `IsVlasovSolution gradW f` unfolds to: for every smooth compactly-supported φ_k, 
  `HasDerivAt (t ↦ ∫ φ_k d(f t)) _ t` at every t (via `WeakEvolutionEq`). This implies 
  `Continuous (t ↦ ∫ φ_k d(f t))` for each smooth c.s. φ_k (used by `W1ContOn_integralContAt`).
- `HasFiniteFirstMoment (f t)` = `IsProbabilityMeasure (f t) ∧ Integrable (‖·‖) (f t)` 
  for each FIXED t. In particular, `∫ ‖z‖ d(f t) < ∞` for each fixed t.

**The mollification approach:**

Let φ_n be smooth c.s. approximations to φ. For each n:
- `t ↦ ∫ φ_n d(f t)` is continuous (by `W1ContOn_integralContAt`).
- `∫ φ_n d(f t) → ∫ φ d(f t)` for each fixed t (by DCT at the measure f t, using
  `|φ_n - φ| ≤ C(1 + ‖z‖)` ∈ L^1(f t)).

To conclude `ContinuousOn (t ↦ ∫ φ d(f t))` from the pointwise limit of continuous functions,
we need UNIFORM CONVERGENCE of `∫ φ_n d(f t)` in t over [0,T].

**The blocking gap:**

`|∫ (φ_n - φ) d(f t)| ≤ ∫_{‖z‖≤n} 1/n d(f t) + ∫_{‖z‖>n} 2(|φ(0)| + ‖z‖) d(f t)`
`≤ 1/n + 2|φ(0)| * f_t{‖z‖ > n} + 2 * ∫_{‖z‖>n} ‖z‖ d(f t)`.

For UNIFORM convergence in t over [0,T], we need:
`sup_{t ∈ [0,T]} ∫_{‖z‖>n} ‖z‖ d(f t) → 0 as n → ∞`.

This is UNIFORM INTEGRABILITY (or uniform tightness of first moments) of the family 
`{f t | t ∈ [0,T]}`. This does NOT follow from the pointwise hypothesis 
`∀ t, Integrable (‖·‖) (f t)`.

**The 3-epsilon argument also stalls:**

For a fixed t₀, the natural 3-epsilon argument is:
```
|∫ φ d(f t) - ∫ φ d(f t₀)|
  ≤ |∫(φ - φ_n) d(f t)| + |∫ φ_n d(f t) - ∫ φ_n d(f t₀)| + |∫(φ_n - φ) d(f t₀)|
```
- Term 2 → 0 as t → t₀ (continuous for fixed n).
- Term 3 → 0 as n → ∞ (DCT at t₀).
- Term 1 = `|∫(φ - φ_n) d(f t)|` for t near t₀: requires controlling 
  `∫_{‖z‖>n} ‖z‖ d(f t)` for t near t₀, which is a continuity statement for the 
  function `t ↦ ∫_{‖z‖>n} ‖z‖ d(f t)`. But `z ↦ ‖z‖ * 1_{‖z‖>n}` is NOT smooth c.s.,
  so the same argument applies recursively. The induction does not terminate.

**For BOUNDED functions (uniform approximation works):**

For `ψ = φ * χ_R` (smooth truncation of φ bounded on B(0,R)), the approximation by
smooth c.s. functions converges UNIFORMLY (not just pointwise), so `t ↦ ∫ ψ d(f t)` 
IS continuous. The remaining tail `∫_{‖z‖>R} |φ| d(f t)` requires first-moment control.

**What's missing:**

The proof requires one of:
1. `∃ C, ∀ t ∈ [0,T], ∫ ‖z‖ d(f t) ≤ C` (uniform moment bound, not in hypotheses), OR
2. Narrow continuity of `t ↦ f t` (i.e., `∫ g d(f t) → ∫ g d(f t₀)` for ALL bounded 
   continuous g, which is stronger than just smooth c.s. g), OR
3. A Gronwall-type first-moment propagation result (requires LipschitzWith on gradW, 
   not assumed in this lemma's signature).

The `vlasovWellPosedness` theorem (also sorry'd, line 800) would provide narrow 
continuity as part of its conclusion. If that theorem were proved, it would close this gap.

### Wished-for Mathlib API / missing hypothesis

- Either add `hf_unif : ∃ C, ∀ t ∈ Set.Icc 0 T, ∫ z, ‖z‖ ∂(f t) ≤ C` as a hypothesis,
- Or make `IsVlasovSolution` imply narrow continuity (which it does in the PDE literature 
  but requires more setup in Lean formalization).

### Lookup trail

- `W1ContOn_integralContAt` — `Vlasov/Basic.lean:1364`
  Gives `Continuous (t ↦ ∫ φ d(f t))` for smooth c.s. φ.
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — 
  `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:58`
  Dominated convergence for FIXED measure; doesn't handle varying measures.
- `MeasureTheory.continuousOn_of_dominated` —
  `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:453`
  ContinuousOn for FIXED measure; not applicable with varying measures.
- `TendstoUniformlyOn.continuousOn` —
  `.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformApproximation.lean:115`
  Limit of uniform convergent sequence of continuous functions is continuous.
  Would work IF we had uniform convergence in t, which requires uniform moment bounds.
- `UniformContinuous.exists_contDiff_dist_le` —
  `.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean:48`
  Gives smooth approximations of uniformly continuous functions. Used in mollification.
- `LipschitzWith.uniformContinuous` —
  `.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:188`
  1-Lipschitz φ is uniformly continuous. Used to get smooth approximations.

