## 2026-05-28T00:00:00Z · w1_lscNarrow_of_summands

**Result:** success
**Iterations:** 1/8
**Sorry count:** 7 → 6
**Pre-flight (§3.5):** dropped 0 hint(s); validated 2 Mathlib lemma names (`lowerSemicontinuousOn_iSup`, `lowerSemicontinuousOn_biSup`); rejected 0 in-loop citations.

### Final proof

```lean
unfold wasserstein1
exact lowerSemicontinuousOn_biSup (fun φ hφ => h_summands φ hφ)
```

### Lookup trail
- `lowerSemicontinuousOn_iSup` — `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:646`
- `lowerSemicontinuousOn_biSup` — `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:650`

### Proof structure

`wasserstein1 (f t) (g t)` unfolds to `⨆ (φ : PhaseSpace d → ℝ) (_ : LipschitzWith 1 φ), ENNReal.ofReal (∫ z, φ z ∂(f t) - ∫ z, φ z ∂(g t))`.

`lowerSemicontinuousOn_biSup` handles exactly the `⨆ i (hi : p i), F i hi x` pattern (double supremum where the inner index is a subtype proof), reducing the goal to showing LSC of each leaf `t ↦ ENNReal.ofReal(∫φ d(f t) − ∫φ d(g t))`, which is exactly `h_summands φ hφ`.

The strategy of applying `lowerSemicontinuousOn_iSup` twice also works (and is how `biSup` is implemented internally), but `biSup` collapses both steps to one.
