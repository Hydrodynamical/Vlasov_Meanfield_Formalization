## 2026-05-26T00:00:00Z · (no tex label) · W1ContOn_lt_top

**Result:** success
**Iterations:** 1/8
**Sorry count:** 8 → 7
**Pre-flight (§3.5):** dropped 0 hint(s); validated 1 sketch lemma (`wasserstein1_lt_top_of_finite_moment`, confirmed in Basic.lean:889); rejected 0 in-loop citation(s)

### Candidate table (Mode B: most-tractable)

| Sorry (decl name) | Plan | Difficulty | Score | Source | Sketch? |
|---|---|---|---|---|---|
| W1ContOn_lt_top | MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json | 2 | 4 | plan-aware | N |
| W1ContOn_toRealContOn | MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json | 2 | 4 | plan-aware | N |
| MathlibTODO_wassersteinGronwallCoupling_W1ContOn (residual) | MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json | — | 4 | plan-aware-residual | Y |
| W1ContOn_integralContAt | MathlibTODO_wassersteinGronwallCoupling_W1ContOn.json | 3 | 3 | plan-aware | N |
| MathlibTODO_W1ContOn_lscNarrow | — | — | skip | MathlibTODO | N |
| MathlibTODO_W1ContOn_uscNarrow | — | — | skip | MathlibTODO | N |
| vlasovWellPosedness | (none) | — | 1 | rubric | N |

Selected: `W1ContOn_lt_top` (score 4, no deps, leaf node).
The residual glue (score 4, sketch Y) ranks equally but depends on `W1ContOn_toRealContOn`
being proved first; `W1ContOn_lt_top` is a prerequisite so it's the right starting point.

### Final proof

```lean
intro t
obtain ⟨hf_prob_t, hf_int_t⟩ := hf_prob t
obtain ⟨hg_prob_t, hg_int_t⟩ := hg_prob t
haveI : IsProbabilityMeasure (f t) := hf_prob_t
haveI : IsProbabilityMeasure (g t) := hg_prob_t
exact wasserstein1_lt_top_of_finite_moment (f t) (g t) hf_int_t hg_int_t
```

### Lookup trail
- `wasserstein1_lt_top_of_finite_moment` — `Vlasov/Vlasov/Basic.lean:889` (project file, already proved)
- `HasFiniteFirstMoment` — `Vlasov/Vlasov/Basic.lean:773` (project file, definition)

### Reasoning
`HasFiniteFirstMoment μ = IsProbabilityMeasure μ ∧ Integrable (fun z => ‖z‖) μ`.
The target `W1ContOn_lt_top` needed to introduce `t`, destructure both `hf_prob t` and `hg_prob t`
into their components, bring the `IsProbabilityMeasure` instances into scope via `haveI`,
then apply the already-proved `wasserstein1_lt_top_of_finite_moment` with the integrability
witnesses. The proof closed in one iteration.
