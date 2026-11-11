import MatedCRT.Proofs.Measurability.ConePairing
import HarmonicBalls.Defs.GFF

/-!
# FIRST PASS S2y, RadialProcCont250: almost sure continuity of the radial version

For a whole-plane GFF `(hC, hcirc)` the jointly measurable radial version `radialVersion hcirc ω` of the circle-average
process `s ↦ h_s(0)` (Duplantier–Sheffield, circle averages of the whole-plane GFF) is almost surely continuous on
`(0, ∞)`. The input is only the field `IsWholePlaneGFF.ae_continuousOn_circle` (joint continuity of the circle averages
on `(0, ∞) × ℂ` almost surely). The radial version agrees with `s ↦ h_s(0)` on `(0, ∞)` for each environment with
that continuity (`radialVersion_eq`, ConePairing.lean:199), which gives the claim by `ContinuousOn.congr`.

Nothing beyond `IsWholePlaneGFF` is assumed. This is the first of the two almost sure inputs of the radial process;
the second (the fourth-moment integrability on `(0, R]`) is not in this file.
-/

open MeasureTheory Filter Set
open _root_.HarmonicBalls

namespace MatedCRT
namespace RadialProcCont250

/-- **The radial version is almost surely continuous on `(0, ∞)`.** For a whole-plane GFF, almost surely the function
`s ↦ radialVersion hcirc ω s` is continuous on `Ioi 0`. -/
theorem ae_continuousOn_radialVersion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ContinuousOn (MatedCRT.CirclePairing.radialVersion hcirc ω) (Set.Ioi 0) := by
  filter_upwards [h.ae_continuousOn_circle] with ω hω
  have hc : ContinuousOn (fun s => hcirc ω s 0) (Set.Ioi 0) :=
    MatedCRT.CirclePairing.continuousOn_radial hω
  exact hc.congr fun s hs => MatedCRT.CirclePairing.radialVersion_eq hc (mem_Ioi.1 hs)

end RadialProcCont250
end MatedCRT

#print axioms MatedCRT.RadialProcCont250.ae_continuousOn_radialVersion
