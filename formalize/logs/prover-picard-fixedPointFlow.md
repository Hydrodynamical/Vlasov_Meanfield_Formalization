## 2026-05-29 · picard_fixedPointFlow · vlasovWellPosedness_local_picard_fixedPointFlow

**Result:** structural close (user-specified done criterion met; Lean sorry-count per-declaration unchanged at 4)
**Iterations:** 4 edit+build cycles
**Sorry count:** 4 → 4 declarations (per Lean warning count); body changed from single top-level sorry (L6137) to structured body with 4 sub-sub-sorries
**Lines added:** ~226 (L6137 → body of ~226 lines)
**Pre-flight (§3.5):** No plan file for this target. All Mathlib names validated inline during iteration.

### What was done

The single `sorry` body of `vlasovWellPosedness_local_picard_fixedPointFlow` (L6137) was replaced with a ~226-line structural proof laying out the 8-step Picard fixed-point composition. Two sub-sub-sorries were substantively closed; 4 remain as acknowledged mathematical deferrals.

### Sub-sub-sorries identified (4 remaining)

1. **`hq_lt : q < 1` (L6223)** — Contraction factor q = gronwallBound 0 (max 1 L) (L*(2M)) T < 1. Requires showing the Gronwall bound is small given L*(T+1)² < 1 and M's relationship to the constraint. Mathematical content: the contraction rate of the spatial-marginal Picard map is < 1 on the small-T interval.

2. **Picard sequence + contraction (L6231)** — `∃ x : ℕ → VlasovMeasureCurve d T M, ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k+1)).ρ ≤ ENNReal.ofReal (q^k * D₀)`. Requires: (a) inductive construction of the sequence using `Phi_step` applied to each iterate, (b) showing M is stable across iterations (the M-fixed-point problem), (c) applying `Phi_supW1_contraction` to each consecutive pair with ~24-hypothesis threading. This is the load-bearing Picard analysis.

3. **`h_self_consist` (L6314)** — `∀ t ∈ Icc 0 T, ρ_lim.extend t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)`. This is the Picard fixed-point equation: the limit ρ_lim equals the spatial marginal of the pushforward of f₀ under the flow built against ρ_lim. Proved via triangle through x_n using contraction + limit tendsto.

4. **`hconv_cont` (L6361)** — `∀ s, Continuous (fun x_pt => convolveFunctionMeasure gradW (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x_pt)`. Requires universal-in-s integrability of gradW against the spatial marginal of the pushforward; for s ∈ Icc 0 T follows from h_self_consist + h_int_ρ_lim + convolveFunctionMeasure_lipschitz_in_x; for general s requires additional extension argument.

### Closed substantively

- **`h_int_gradW_μ₀`**: Integrable (fun y => gradW (x - y)) (spatialMarginal f₀). Proved via: AEStronglyMeasurable from hL.continuous; dominator ‖gradW 0‖ + L*‖x‖ + L*‖y‖ integrable by hμ₀_int; Integrable.mono'.

- **`h_int_ρ_lim`**: Integrable (fun y => gradW (x - y)) (ρ_lim.extend t). Identical proof structure using VlasovMeasureCurve.extend_yIntegrable for the dominator.

### Structural composition laid out

The body now executes 8 steps:
1. Spatial marginal setup (μ₀, hμ₀_int, M_f₀) — closed
2. M-fixed-point (M := M_f₀, minimal; real fixed-point requires analysis) — partially closed
3. Integrability h_int_gradW_μ₀ — closed
4. Picard sequence + contraction factor q — skeleton with sorry
5. picard_iterate_bundlesAs_VlasovMeasureCurve → ρ_lim — closed (depends on sorry in step 4)
6. h_int_ρ_lim + h_conv_cont_ρ_lim — closed
7. exists_vlasov_characteristicFlow_global_smallT → (charX, charV) — closed
8. Self-consistency h_self_consist — sorry
9. Bundle assembly (hflow_on, h_boundary, hM_ρ_bound, h_y_int_ρ, hconv_cont) — largely closed (hconv_cont still sorry)

### Lookup trail
- `VlasovMeasureCurve.extend_yIntegrable` — CharacteristicFlow.lean:3882
- `VlasovMeasureCurve.extend_hasMoment` — CharacteristicFlow.lean:3888
- `VlasovMeasureCurve.extend_convCont` — CharacteristicFlow.lean:3899
- `picard_iterate_bundlesAs_VlasovMeasureCurve` — CharacteristicFlow.lean:5884
- `convolveFunctionMeasure_lipschitz_in_x` — CharacteristicFlow.lean:75
- `norm_fst_le` — .lake/packages/mathlib/.../Normed/Group/Constructions.lean:238
- `LipschitzWith.dist_le_mul` — .lake/packages/mathlib/.../MetricSpace/Lipschitz.lean:50
- `Continuous.aestronglyMeasurable` — .lake/packages/mathlib/.../StronglyMeasurable/AEStronglyMeasurable.lean:215

### Build status
`lake build Vlasov.OT.CharacteristicFlow` — SUCCESS (no errors, 4 `declaration uses sorry` warnings, same as baseline)

### What didn't work
- Attempted to close `hq_lt : q < 1` but the relationship between gronwallBound and the hTL constraint depends on M in a way that requires a fixed-point analysis not available without the Picard sequence math.
- `hconv_cont` (universal in s) cannot be closed without h_self_consist.
