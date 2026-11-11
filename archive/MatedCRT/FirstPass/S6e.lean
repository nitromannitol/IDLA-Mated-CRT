import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.FirstPass.S6e.Final
import MatedCRT.FirstPass.S6e.Universal
import MatedCRT.FirstPass.S6e.C17Induction
import MatedCRT.FirstPass.S6e.DdSources
import MatedCRT.FirstPass.S6e.Walk
import MatedCRT.FirstPass.S6e.Inputs
import MatedCRT.FirstPass.S6e.Scales
import MatedCRT.FirstPass.S6e.Geometry
import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S6e.UniversalEvent
import MatedCRT.FirstPass.S6e.GeometryId
import MatedCRT.FirstPass.S6e.RadiusSelect

/-!
# FIRST PASS: the deterministic cutoffs, the final event and the universal event.

Aggregator of `FirstPass/S6e/`: `Cutoff` (D1, D3, D4 real analysis),
`Final` (D2, quantifier order and ProbTendsToOne), `Universal` (D3, rational reduction and measurability),
`Walk`, `Inputs`, `Scales`, `Geometry`, `Admissible` (B1, B2), `UniversalEvent` (the measurable universal event),
`GeometryId` (the geometric identification of the cell formulas, (2), (3), (9)), `RadiusSelect` (the selected radii
`R_j` of the first-good-radius choice over the A4 candidates; hR of C17; C17 with selected radii).
-/
