-- TODO(re-sync): the four `Vlasov/*.lean` files in this package are HAND-SYNCED
-- COPIES of the live OT-layer source (`Vlasov/Vlasov/{Base/Geometry, OT/Wasserstein,
-- OT/Coupling, Mathlib/ODE/PicardLindelof}.lean`). This package is the Q2 certificate
-- of Definition 3.2: it builds against Mathlib ALONE (zero kinetic files in scope).
-- If the live OT source is edited without re-copying the files here, this certificate
-- goes STALE. Re-sync (`cp` the four files), `lake build`, and `diff` against the live
-- source (should be empty) before trusting Q2.
import Vlasov.Base.Geometry
import Vlasov.OT.Wasserstein
import Vlasov.OT.Coupling
import Vlasov.Mathlib.ODE.PicardLindelof
