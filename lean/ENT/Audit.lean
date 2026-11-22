module

import ENT.PaperStatements
import ENT.Supplement
import Lean.Util.CollectAxioms

/-! Check the transitive axioms of every public declaration in the ENT namespace. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let required := [`ENT.ent_conjecture, `ENT.iid_ent_conjecture_ae,
    `ENT.PaperStatements.paper_theorem_1_1,
    `ENT.PaperStatements.paper_theorem_1_1_canonical,
    `ENT.PaperStatements.stability_small, `ENT.PaperStatements.stability_large,
    `ENT.PaperStatements.stability_asymptotic, `ENT.PaperStatements.sharp_coefficient_limit,
    `ENT.PaperStatements.diagonal_density_curvature, `ENT.Quantitative.actual_curvature_ge_seven]
  for name in required do
    unless env.contains name do
      throwError "Missing theorem {name}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if `ENT |>.isPrefixOf name then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun ax => !allowed.contains ax
      unless bad.isEmpty do
        throwError "Unexpected transitive axioms in {name}: {bad}"
      count := count + 1
  logInfo m!"Checked the transitive axioms of {count} public ENT declarations."
