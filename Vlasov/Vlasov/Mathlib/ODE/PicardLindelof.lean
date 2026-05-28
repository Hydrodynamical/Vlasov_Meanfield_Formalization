/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Picard-Lindelöf with explicit confinement conjunct (vendored from Mathlib)

This file vendors two theorems from `Mathlib/Analysis/ODE/PicardLindelof.lean`
with one additional conjunct in the public conclusion.

The new conjunct exposes `FunSpace.compProj_mem_closedBall`'s guarantee at the
public theorem level: every flow trajectory `α x t` stays inside
`closedBall x₀ a` (the outer ball where the field is Lipschitz). The underlying
property is already proved upstream in Mathlib; in fact, the existing public
proof of `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`
already invokes `compProj_mem_closedBall hf.mul_max_le` internally (to
constrain the iterate to the Lipschitz region). We are only re-exporting that
invariant through the public conclusion.

**Intended upstreaming**: this file is structured as a near-mechanical patch
to `Mathlib/Analysis/ODE/PicardLindelof.lean`; the eventual Mathlib PR would
drop the `_confined` suffix and replace the two original theorems with their
strengthened forms (no API breaks for downstream consumers, since the
conclusion only grows).

**In-project consumer**: `Vlasov.OT.CharacteristicFlow` (where
`exists_vlasov_extend_one_window` threads the confinement conjunct through
to Helper 1, `vlasov_window_confinement`).
-/
