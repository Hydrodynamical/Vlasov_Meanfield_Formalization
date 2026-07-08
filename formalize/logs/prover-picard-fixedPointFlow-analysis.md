## 2026-05-29 (session 2) · picard_fixedPointFlow sub-sub-sorries · vlasovWellPosedness_local_picard_fixedPointFlow

**Result:** skipped — all 6 sub-sub-sorries are mutually blocked; no sorry count reduction achievable
**Iterations:** 0/8 (analysis only; no edits made)
**Sorry count:** 6 sub-sub-sorries in body → 6 (unchanged)
**Pre-flight (§3.5):** N/A (no Mathlib lemma citations written)

### Analysis: Why all 6 sub-sub-sorries are blocked

The 6 sorry's in `vlasovWellPosedness_local_picard_fixedPointFlow`'s body (L6149-6387) form a dependency chain that is mutually blocking:

**`hq_lt` (L6235)**: `gronwallBound 0 K (L * 2 * M_f₀) T < 1` where `K = max(1,L) = 1` (since `hTL : L*(T+1)^2 < 1` implies `L < 1`). This reduces to `L * 2 * M_f₀ * (exp(T)-1) < 1`. This is NOT provable from `hTL` because `M_f₀ = ∫ ‖y‖ ∂(spatialMarginal f₀)` can be arbitrarily large. The `q` definition (with `2*M` instead of `1`) is a parameterization bug: the true contraction RATIO is `L*(exp(T)-1)` (independent of M), not `L*2M*(exp(T)-1)`.

**Mathematical structural issue**: Even if `q` were redefined correctly as `gronwallBound 0 K L T = L*(exp(T)-1)`, the claim `L*(exp(T)-1) < 1` is STILL not provable from `hTL : L*(T+1)^2 < 1` alone for all T. Specifically, for T > 2.7 (approx), `exp(T)-1 > (T+1)^2`, so `L*(exp(T)-1) > L*(T+1)^2` is possible even with `L*(T+1)^2 < 1`. The Picard iteration's convergence requires an additional constraint (roughly `L*(exp(T)-1) < 1`), stronger than `hTL`.

**All downstream sorry's**: `h_self_consist` (#3), `hconv_cont` (#4), `h_aemeas_out` (#5), `h_int_conv_out` (#6) all depend on `hq_lt` and the Picard sequence (#2). Without the Picard sequence proved, `h_self_consist` cannot be established, and without `h_self_consist`, `hconv_cont` and `h_int_conv_out` cannot be proved for all `s`.

**`hconv_cont` and `h_int_conv_out` for `s ∈ Icc 0 T`**: These CAN be proved for `s ∈ Icc 0 T` via `h_self_consist` (which is itself sorry'd), but the universal `∀ s` claim requires `s ∉ Icc 0 T` to be handled too. For `s ∉ Icc 0 T`, AEMeasurability of `charX s` (from `h_aemeas_out`, also sorry'd) is needed plus a Gronwall-type moment bound for the extended flow. The `s ∉ Icc 0 T` case is genuinely hard.

**`h_aemeas_out`**: Requires `AEMeasurable (fun z => (charX s z, charV s z)) f₀`. This is Stage 1.8 territory: the flow map built via `Classical.choose` in `exists_vlasov_characteristicFlow_global_smallT` does not automatically carry measurability. Requires continuous dependence on initial data (Dobrushin-type) or a measurable selection theorem.

**Note on `h_int_conv_out` reordering**: Moving `h_aemeas_out` before `h_int_conv_out` (reordering in proof) would make `h_aemeas_out` available for proving `h_int_conv_out` for `s ∉ Icc 0 T`. But even with `h_aemeas_out`, integrability requires a moment bound `Integrable (fun z => ‖charX s z‖) f₀` for `s ∉ Icc 0 T`, which requires the flow's Gronwall growth bound extended past `[0,T]`. This is not directly available in scope without a separate lemma.

### Dependency graph
```
hTL → (fails to imply) → hq_lt
hq_lt → Picard sequence (#2) → h_self_consist (#3)
h_self_consist → h_int_conv_out (for s ∈ Icc 0 T) → h_int_conv_out (all s, needs more)
h_self_consist → hconv_cont (for s ∈ Icc 0 T) → hconv_cont (all s, needs h_aemeas_out)
h_aemeas_out → independent, Stage 1.8 hard
```

### Recommended fix path

1. **Fix `hTL` constraint or add auxiliary constraint**: Either strengthen `hTL` to `L * (exp(T)-1) < 1` (which implies Picard convergence directly) OR add a separate hypothesis. The current `L*(T+1)^2 < 1` is the constraint for per-z trajectory well-posedness (from `exists_vlasov_characteristicFlow_global_smallT`), not for the Picard W₁-contraction.

2. **Fix M choice**: The M-fixed-point at L6178 should pick `M` satisfying an additional selfconsistency condition so that `q = gronwallBound 0 1 (L*1) T = L*(exp(T)-1)` is the true contraction ratio and `D₀ = 2M` is the initial W₁ distance, with `q < 1` provable from the (strengthened) constraint.

3. **Prove Picard sequence (#2)**: Once `hq_lt` is fixed, the Picard sequence can be constructed inductively using `Phi_step` + `Phi_supW1_contraction` with proper M threading.

4. **Prove h_self_consist (#3)**: Via triangle inequality: `wasserstein1 (ρ_lim.ρ t) (spatialMarginal ...) ≤ wasserstein1 (ρ_lim.ρ t) ((x n).ρ t) + wasserstein1 ((x n).ρ t) (spatialMarginal ...)`. First term → 0 from `_h_tendsto`; second requires `(x n).ρ t = spatialMarginal (Phi(x n-1) t)` which follows from the Picard construction.

5. **Prove h_aemeas_out (#5)**: Needs continuous (or measurable) dependence of the characteristic flow on initial conditions. Approach: if `vlasovVectorField` is Lipschitz in z uniformly in t, then the flow is continuous in z, hence measurable. Alternatively, use a measurable selection theorem.

### What didn't work (analysis conclusions)
- `hq_lt`: Not provable from `hTL` alone due to M-dependence and insufficient constraint
- `h_self_consist`: Not provable from `_h_tendsto` alone without Picard construction structure
- `hconv_cont`/`h_int_conv_out`: Not provable universally without `h_self_consist` + AEMeasurability + extended flow moment bounds

---

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
