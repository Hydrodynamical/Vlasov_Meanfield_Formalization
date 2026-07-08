# Vlasov — the Lean package

The Lean 4 / Mathlib development for
[Mathematician in the Loop](../README.md): the mean-field derivation of the
Vlasov equation, formalized. Zero `sorry`; the three headline theorems carry
the axiom footprint `[propext, Classical.choice, Quot.sound]`.

## Build

```bash
lake build
```

The Lean toolchain is pinned by `lean-toolchain` (v4.29.1) and Mathlib by
`lake-manifest.json`. To check the axiom-footprint certificate:

```bash
lake env lean ../formalize/certification/footprint-check.lean
```

## Modules

| Module | Contents |
|---|---|
| [`Vlasov/Base/Geometry.lean`](Vlasov/Base/Geometry.lean) | phase-space geometry: `PhysSpace`, `PhaseSpace` |
| [`Vlasov/OT/Wasserstein.lean`](Vlasov/OT/Wasserstein.lean) | `wasserstein1` via the Kantorovich–Rubinstein dual, and its metric API |
| [`Vlasov/OT/Coupling.lean`](Vlasov/OT/Coupling.lean) | couplings, transport cost, the duality bridge `wasserstein1_eq_coupling` |
| [`Vlasov/OT/CharacteristicFlow.lean`](Vlasov/OT/CharacteristicFlow.lean) | characteristic flows; `vlasovWellPosedness`, `dobrushin`, `meanFieldLimit_coupling` |
| [`Vlasov/OT/WeakToLagrangian.lean`](Vlasov/OT/WeakToLagrangian.lean) | the superposition principle: `weak_isLagrangianVlasovSolutionOn` |
| [`Vlasov/Mathlib/ODE/PicardLindelof.lean`](Vlasov/Mathlib/ODE/PicardLindelof.lean) | Picard–Lindelöf supplement |
| [`Vlasov/Basic.lean`](Vlasov/Basic.lean) | particle systems, `empiricalMeasure`, weak solutions, `meanFieldLimit` |
