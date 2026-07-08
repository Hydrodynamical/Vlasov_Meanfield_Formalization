import Vlasov
open Lean Elab.Command

/-! Self-contained layer (PAPER.tex Def. 3.2) — a MEASUREMENT UNDER AN ASSERTED PARTITION,
with the partition's structural consequences machine-checked.

The reusability score is NOT a number the tool infers from declaration names — that would
be *spuriously* rigorous: a precise figure computed from a tunable heuristic, where the
precision hides the arbitrariness.  "Declaration `D` is general mathematics, not specific
to the Vlasov problem" is a statement about the relationship of `D` to a body of
mathematics *outside* the project (Mathlib, the literature) — not a property of the
elaboration environment, and so not decidable by any algorithm over `env`.  It is an
irreducible HUMAN JUDGEMENT.

So the partition is made honest by being **explicit, external, and auditable**:

  * `generalDecls` below is a hand-asserted, checked-in, per-declaration list — the claim
    "these are the general-mathematics declarations (optimal transport, ambient geometry,
    vendored general ODE), liftable as a standalone library; everything else is
    Vlasov-specific."  A referee contests it one declaration at a time; it is not buried
    in a regex.  This is the ONLY thing asserted rather than proved.

  * The tool then MACHINE-VERIFIES the structural consequences of that premise:
      (W) WELL-FORMED  — every asserted-general name is a real project declaration (no
                         stale / renamed / mistyped / duplicated entries).  `spec` is the
                         complement, so the partition is automatically total and disjoint;
                         the only failure mode is a stale assertion, which (W) catches.
      (D) DOWN-CLOSED  — every PROJECT dependency of a general declaration is itself
                         general.  Mathlib is the trusted base (exactly the role the kernel
                         plays for `#print axioms`), so down-closure is taken relative to
                         project declarations.  Down-closure-within-the-project and "no
                         general→specific edge" (the S2 back-edge count = 0) are the SAME
                         predicate, computed from `getUsedConstants`.

  * Two figures result, each reported "under the asserted partition P":
      POTENTIAL = |general| / |all|   — intrinsic to the dependency structure; independent
                  of how the files are organised.
      REALIZED  = |decls in self-contained general modules| / |all| — the fraction that
                  actually lives in a pure-general, import-clean sub-library you could lift
                  out and `import` as-is.  The in-environment proxy is module-purity +
                  import-fixpoint, below.  The EXTERNAL certification is the sibling package
                  `formalize/phase-d/ot-standalone/` actually building the realized modules
                  against Mathlib ALONE ("compiles in isolation", not "the import graph
                  looks clean").

Epistemic shape: identical to the rest of the project.  `#print axioms` is rigorous GIVEN
you trust the kernel; this score is rigorous GIVEN you accept `generalDecls` — and the
tagging is now inspectable and contestable rather than inferred.  Everything except
`generalDecls` is proved; `generalDecls` is asserted; nothing is dressed as more objective
than it is. -/

namespace ReuseScore

def projectModules : List Name :=
  [`Vlasov.Base.Geometry, `Vlasov.OT.Wasserstein, `Vlasov.OT.Coupling,
   `Vlasov.Basic, `Vlasov.OT.CharacteristicFlow, `Vlasov.OT.WeakToLagrangian,
   `Vlasov.Mathlib.ODE.PicardLindelof]

/-- Skip auto-generated / internal constants. -/
def isReal (nm : Name) : Bool :=
  ¬ nm.isInternal
  && (nm.toString.splitOn "._").length == 1
  && (nm.toString.splitOn ".match_").length == 1
  && (nm.toString.splitOn ".eq_").length == 1
  && (nm.toString.splitOn ".proof_").length == 1

/-- THE ASSERTED PARTITION — the one human judgement, contestable per-declaration.

The general-mathematics side: the optimal-transport core (`wassersteinCost*`,
`wasserstein1*`, `wassersteinBar*`, couplings `IsCoupling*`, and the dual / transport
attainment machinery), the ambient geometry (`PhysSpace`, `PhaseSpace`), and the vendored
general ODE lemmas (`IsPicardLindelof.*`).  Everything NOT listed here is asserted to be
Vlasov-specific (the kinetic development: vector fields, characteristic flow, Lagrangian /
Eulerian solutions, Gronwall coupling, Dobrushin, the mean-field limit).

A referee who disagrees edits THIS LIST and re-runs; the machine-checked verdicts (W)/(D)
and the two figures update accordingly. -/
def generalDecls : List Name :=
  [ `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined,
    `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_confined,
    `Vlasov.IsCoupling,
    `Vlasov.PhaseSpace,
    `Vlasov.PhysSpace,
    `Vlasov.cTransform_dual_witness,
    `Vlasov.exists_coupling_glue,
    `Vlasov.exists_finiteRange_map_cost_le,
    `Vlasov.exists_transport_min,
    `Vlasov.finiteRange_approxMap_measurable,
    `Vlasov.finiteRange_transportation_dual,
    `Vlasov.finiteTransport_dual_eps,
    `Vlasov.finiteTransport_dual_eps_plan,
    `Vlasov.integral_boundedContinuous_eq_of_integral_lipschitz_eq,
    `Vlasov.isClosed_transport_cone,
    `Vlasov.lintegral_ofReal_kept_cells_le,
    `Vlasov.lintegral_ofReal_ne_top_of_integrable_nonneg,
    `Vlasov.lintegral_ofReal_tail_tendsto_zero,
    `Vlasov.lipschitzWith_one_iff_oscillation,
    `Vlasov.measure_compl_biUnion_range_tendsto_zero,
    `Vlasov.transportProperCone,
    `Vlasov.wasserstein1,
    `Vlasov.wasserstein1_comm,
    `Vlasov.wasserstein1_coupling,
    `Vlasov.wasserstein1_coupling_eq,
    `Vlasov.wasserstein1_dual_lower_bound,
    `Vlasov.wasserstein1_eq_coupling,
    `Vlasov.wasserstein1_eq_iSup_lipschitz,
    `Vlasov.wasserstein1_eq_zero_iff_measure_eq,
    `Vlasov.wasserstein1_le_liminf_of_narrow,
    `Vlasov.wasserstein1_le_moments_sum,
    `Vlasov.wasserstein1_le_wasserstein1_coupling,
    `Vlasov.wasserstein1_lt_top_of_finite_moment,
    `Vlasov.wasserstein1_ne_top_of_finite_moment,
    `Vlasov.wasserstein1_self,
    `Vlasov.wasserstein1_triangle,
    `Vlasov.wassersteinCost,
    `Vlasov.wassersteinCost_comm,
    `Vlasov.wassersteinCost_coupling,
    `Vlasov.wassersteinCost_coupling_comm,
    `Vlasov.wassersteinCost_coupling_le_dual,
    `Vlasov.wassersteinCost_coupling_le_dual_of_finiteRange,
    `Vlasov.wassersteinCost_coupling_map_le,
    `Vlasov.wassersteinCost_coupling_triangle,
    `Vlasov.wassersteinCost_dual_le_add_map,
    `Vlasov.wassersteinCost_dual_lower_bound,
    `Vlasov.wassersteinCost_dual_singleMap_le,
    `Vlasov.wassersteinCost_self,
    `Vlasov.wassersteinCost_triangle ]

run_cmd liftCoreM do
  let env ← getEnv
  let mods := env.header.moduleNames
  -- per project module: (name, idx, real decls, project-module import indices)
  let mut modInfo : Array (Name × Nat × Array Name × Array Nat) := #[]
  let mut allSet : NameSet := {}
  for m in projectModules do
    match mods.findIdx? (· == m) with
    | none => pure ()
    | some mi =>
      let md := env.header.moduleData[mi]!
      let decls := md.constNames.filter isReal
      for nm in decls do allSet := allSet.insert nm
      let imps := md.imports.filterMap (fun im => mods.findIdx? (· == im.module))
                    |>.filter (fun j => projectModules.any (fun pm => mods.findIdx? (· == pm) == some j))
      modInfo := modInfo.push (m, mi, decls, imps)
  -- the asserted partition as a set
  let mut genSet : NameSet := {}
  for nm in generalDecls do genSet := genSet.insert nm
  -- (W) well-formedness: stale (asserted but not a real project decl) + duplicates
  let stale := generalDecls.filter (fun nm => ¬ allSet.contains nm)
  let dupCount := generalDecls.length - genSet.size
  -- general / specific over the actual project declarations (spec = complement → total+disjoint)
  let mut specSet : NameSet := {}
  let mut genN := 0; let mut total := 0
  for (_, _, decls, _) in modInfo do
    for nm in decls do
      total := total + 1
      if genSet.contains nm then genN := genN + 1
      else specSet := specSet.insert nm
  -- (D) down-closure / S2 back-edges: every PROJECT dependency of a general decl is general
  let mut backEdges := 0
  let mut backList : Array String := #[]
  for nm in genSet.toList do
    if allSet.contains nm then
      match env.find? nm with
      | none => pure ()
      | some info =>
        let used := info.type.getUsedConstants ++ (info.value?.map Expr.getUsedConstants).getD #[]
        let bad := used.filter (fun u => specSet.contains u)
        if bad.size > 0 then
          backEdges := backEdges + 1
          backList := backList.push s!"      {nm}  ->  {bad.toList}"
  -- REALIZED: a module is "pure-general" if all its real decls are general; "self-contained"
  -- if pure-general AND all its project imports are self-contained (import fixpoint).
  let isPure := fun (decls : Array Name) => decls.all (fun nm => genSet.contains nm)
  let mut clean : Array Bool := modInfo.map fun (_, _, ds, _) => isPure ds
  for _ in [0:modInfo.size] do
    let mut nxt := clean
    for i in [0:modInfo.size] do
      let (_, _, _, imps) := modInfo[i]!
      if clean[i]! then
        let importsClean := imps.all fun j =>
          match (modInfo.findIdx? fun (_, mj, _, _) => mj == j) with
          | some k => clean[k]!
          | none => true
        nxt := nxt.set! i importsClean
    clean := nxt
  let mut realizedN := 0
  for i in [0:modInfo.size] do
    let (_, _, ds, _) := modInfo[i]!
    if clean[i]! then realizedN := realizedN + ds.size
  -- interface: distinct general names consumed by the specific side
  let mut iface : NameSet := {}
  for nm in specSet.toList do
    match env.find? nm with
    | none => pure () | some info =>
      let used := info.type.getUsedConstants ++ (info.value?.map Expr.getUsedConstants).getD #[]
      for u in used do if genSet.contains u then iface := iface.insert u
  -- Q4 half A: reachability of each general decl from a target theorem (dead-code check).
  let targets : List Name :=
    [`Vlasov.vlasovWellPosedness, `Vlasov.dobrushin, `Vlasov.meanFieldLimit,
     `Vlasov.weak_isLagrangianVlasovSolutionOn]
  let mut reach : NameSet := {}
  for t in targets do reach := reach.insert t
  for _ in [0:total+5] do
    let before := reach.size
    for nm in reach.toList do
      match env.find? nm with
      | none => pure ()
      | some info =>
        let used := info.type.getUsedConstants ++ (info.value?.map Expr.getUsedConstants).getD #[]
        for u in used do if allSet.contains u then reach := reach.insert u
    if reach.size == before then break
  let unreached := genSet.toList.filter (fun nm => allSet.contains nm && ¬ reach.contains nm)
  let genSorted := ((genSet.toList.filter allSet.contains).map (·.toString)).toArray.qsort (· < ·) |>.toList
  let pc := fun (a b : Nat) =>
    let bp := a * 10000 / b          -- value in hundredths of a percent
    let frac := bp % 100
    let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
    s!"{bp / 100}.{fracStr}%"
  let wf := if stale.isEmpty && dupCount == 0 then "WELL-FORMED ✓" else "ILL-FORMED ✗"
  let dn := if backEdges == 0 then "DOWN-CLOSED ✓" else "NOT DOWN-CLOSED ✗"
  let mut perModLines : Array String := #[]
  for i in [0:modInfo.size] do
    let (m, _, ds, _) := modInfo[i]!
    let g := (ds.filter (fun nm => genSet.contains nm)).size
    let tag := if clean[i]! then "SELF-CONTAINED-GENERAL"
               else if ds.all (fun nm => genSet.contains nm) then "pure-general (imports not all general)"
               else "specific / mixed"
    perModLines := perModLines.push s!"    {m}: {ds.size} decls ({g} general) [{tag}]"
  let perMod := String.intercalate "\n" perModLines.toList
  let mut lines : List String :=
    [ "SELF-CONTAINED LAYER (PAPER Def. 3.2) — measurement under an asserted partition",
      s!"  asserted general declarations: {generalDecls.length} (distinct {genSet.size})",
      s!"  (W) partition well-formed:  {wf}   [stale asserted names: {stale.length}; duplicates: {dupCount}]",
      s!"  (D) down-closed (S2 back-edges general→specific, must be 0):  {dn}   [{backEdges}]",
      s!"  total project declarations: {total}",
      s!"  POTENTIAL (general fraction, under partition):    {genN}/{total} = {pc genN total}",
      s!"  REALIZED  (self-contained general modules):       {realizedN}/{total} = {pc realizedN total}",
      s!"  interface (distinct general names used by the specific side): {iface.size}",
      s!"  interface names: {iface.toList}",
      "  per module:", perMod ]
  let reachProj := (reach.toList.filter allSet.contains).length
  lines := lines ++ ["", s!"  Q4-A reachability from targets: {genN - unreached.length}/{genN} general reachable  ({reachProj}/{total} project decls reachable)"]
    ++ (if unreached.isEmpty then ["    (no dead code: every general declaration is reachable from a target)"]
        else ["    UNREACHED (dead code, fails Q4):"] ++ unreached.map (fun nm => s!"      {nm}"))
    ++ ["", s!"  L_gen --- the {genN} general declarations (sorted):"]
    ++ genSorted.map (fun s => s!"    {s}")
  if ¬ stale.isEmpty then
    lines := lines ++ ["  STALE asserted-general names (FIX THE LIST):"] ++ stale.map (fun nm => s!"      {nm}")
  if ¬ backList.isEmpty then
    lines := lines ++ ["  BACK-EDGES (general decl depending on a specific decl):"] ++ backList.toList
  logInfo (String.intercalate "\n" lines)

end ReuseScore
