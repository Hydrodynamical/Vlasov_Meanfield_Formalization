## 2026-05-28T00:00:00Z · w1_lscNarrow_summand_lscOn

**Result:** success
**Iterations:** 1/8
**Sorry count:** before (line 1288 had sorry) → after (sorry removed)
**Pre-flight (§3.5):** dropped 0 hint(s); validated 2 Mathlib lemmas (`ENNReal.continuous_ofReal`, `ContinuousOn.lowerSemicontinuousOn`); rejected 0 in-loop citation(s). Also validated `Continuous.comp_continuousOn'` pre-edit.

### Final proof

```lean
  (ENNReal.continuous_ofReal.comp_continuousOn'
    (w1_lscNarrow_diff_contOn gradW f g hf hg hf_prob hg_prob T hT φ hφ_lip)).lowerSemicontinuousOn
```

### Lookup trail
- `ENNReal.continuous_ofReal` — `.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:70`
- `Continuous.comp_continuousOn'` — `.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:519`
- `ContinuousOn.lowerSemicontinuousOn` — `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:219`

### What worked
Composition direction: `Continuous.comp_continuousOn'` takes `(hg : Continuous g) (hf : ContinuousOn f s)` and produces `ContinuousOn (fun x => g (f x)) s`. So `ENNReal.continuous_ofReal.comp_continuousOn' h_diff` gives `ContinuousOn (fun t => ENNReal.ofReal (∫ φ d(f t) - ∫ φ d(g t))) (Icc 0 T)`. Then `.lowerSemicontinuousOn` is the trivial promotion. One edit, one build.
