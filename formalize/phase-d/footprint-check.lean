import Vlasov
-- Axiom-footprint certificate for the three headline theorems. Run from the
-- Lean package directory:
--   cd Vlasov && lake env lean ../formalize/phase-d/footprint-check.lean
-- All three must print exactly: [propext, Classical.choice, Quot.sound]
#print axioms Vlasov.vlasovWellPosedness
#print axioms Vlasov.dobrushin
#print axioms Vlasov.weak_isLagrangianVlasovSolutionOn
