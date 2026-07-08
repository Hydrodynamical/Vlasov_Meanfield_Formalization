import Vlasov
-- Phase D footprint invariant check. Run after every move:
--   lake env lean formalize/phase-d/footprint-check.lean
-- Both must print exactly: [propext, Classical.choice, Quot.sound]
#print axioms Vlasov.vlasovWellPosedness
#print axioms Vlasov.dobrushin
