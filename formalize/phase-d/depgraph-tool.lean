import Vlasov
open Lean

namespace PhaseDDeps

/-- The project modules whose declarations we want the dependency graph for. -/
def projectModules : List Name :=
  [`Vlasov.Base.Geometry, `Vlasov.OT.Wasserstein,
   `Vlasov.Basic, `Vlasov.OT.Coupling, `Vlasov.OT.CharacteristicFlow,
   `Vlasov.Mathlib.ODE.PicardLindelof]

/-- Short tag for a module name (for compact output). -/
def modTag (n : Name) : String :=
  if n == `Vlasov.Base.Geometry then "GEOM"
  else if n == `Vlasov.OT.Wasserstein then "WASS"
  else if n == `Vlasov.Basic then "BASIC"
  else if n == `Vlasov.OT.Coupling then "COUP"
  else if n == `Vlasov.OT.CharacteristicFlow then "CHARFLOW"
  else if n == `Vlasov.Mathlib.ODE.PicardLindelof then "PICARD"
  else "OTHER"

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  -- module index for each project module
  let projIdx : List (Nat × Name) := projectModules.filterMap fun m =>
    (mods.findIdx? (· == m)).map (fun i => (i, m))
  let projIdxSet : List Nat := projIdx.map (·.1)
  -- helper: module tag for a declaration name (None if not in a tracked module)
  let modOf : Name → Option Name := fun nm =>
    match env.getModuleIdxFor? nm with
    | none => none
    | some mi =>
      let i := mi.toNat
      if projIdxSet.contains i then some mods[i]! else none
  let mut lines : Array String := #[]
  let mut count := 0
  for (mi, modName) in projIdx do
    let md := env.header.moduleData[mi]!
    for nm in md.constNames do
      if nm.isInternal then continue
      -- skip equation/match/proof auxiliaries
      let s := nm.toString
      if (s.splitOn "._").length > 1 then continue
      if (s.splitOn ".match_").length > 1 then continue
      if (s.splitOn ".eq_").length > 1 then continue
      let some info := env.find? nm | continue
      let usedT := info.type.getUsedConstants
      let usedV := (info.value?.map (·.getUsedConstants)).getD #[]
      let used := usedT ++ usedV
      -- project deps with their module tags, deduped
      let mut deps : Array String := #[]
      for u in used do
        if u == nm then continue
        match modOf u with
        | none => pure ()
        | some um =>
          let tag := s!"{modTag um}:{u}"
          if ¬ deps.contains tag then deps := deps.push tag
      lines := lines.push s!"{modTag modName}|{nm}|{String.intercalate "," deps.toList}"
      count := count + 1
  IO.FS.writeFile "phase_d_deps.txt" (String.intercalate "\n" lines.toList ++ "\n")
  logInfo s!"wrote {count} project declarations to phase_d_deps.txt"

end PhaseDDeps
