import Vlasov
open Lean Elab.Command

/-! Definitive whole-project sorry scan: lists every project declaration whose
    axiom footprint contains `sorryAx` (i.e. has a live sorry anywhere in its
    proof term). Uses cached `.olean`s — fast. -/
run_cmd liftCoreM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let projTags : List Name :=
    [`Vlasov.Base.Geometry, `Vlasov.OT.Wasserstein, `Vlasov.Basic,
     `Vlasov.OT.Coupling, `Vlasov.OT.CharacteristicFlow,
     `Vlasov.OT.WeakToLagrangian, `Vlasov.Mathlib.ODE.PicardLindelof]
  let projIdx := projTags.filterMap (fun m => mods.findIdx? (· == m))
  let mut sorried : Array Name := #[]
  let mut total := 0
  for mi in projIdx do
    let md := env.header.moduleData[mi]!
    for nm in md.constNames do
      if nm.isInternal then continue
      total := total + 1
      let ax ← Lean.collectAxioms nm
      if ax.contains ``sorryAx then
        sorried := sorried.push nm
  if sorried.isEmpty then
    logInfo s!"✓ SORRY-FREE: 0 of {total} project declarations depend on sorryAx."
  else
    logInfo s!"✗ {sorried.size} of {total} declarations depend on sorryAx:\n{String.intercalate "\n" (sorried.toList.map (·.toString))}"
