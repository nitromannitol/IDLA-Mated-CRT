import MatedCRT.FirstPass.Derived.PaperBallClockPrefix
import LatticeProb.Prob.BrownianPathSpace

/-! # Exit clocks in complex and Euclidean coordinates -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open Set HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry
open scoped ENNReal NNReal

/-- The exit time is unchanged by reading a complex path in Euclidean coordinates.
The identity also covers paths that never leave the domain. -/
theorem continuousExitTime_complexToEuclideanPath
    (U : Set ℂ) (f : C(ℝ≥0, ℂ)) :
    continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
        (complexToEuclideanPath f) = pathExitTime U f := by
  have hm (t : ℝ≥0) :
      0 + complexToEuclideanPath f t ∉ Complex.orthonormalBasisOneI.repr.symm ⁻¹' U ↔
        f t ∉ U := by
    simp [complexToEuclideanPath]
  rw [continuousExitTime_eq_iInf]
  unfold pathExitTime
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro _ ⟨t, rfl, ht⟩
    exact iInf_le (fun s : {s : ℝ≥0 //
      0 + complexToEuclideanPath f s ∉ Complex.orthonormalBasisOneI.repr.symm ⁻¹' U} =>
      (s.1 : ℝ≥0∞)) ⟨t, (hm t).2 ht⟩
  · refine le_iInf fun t => ?_
    exact sInf_le ⟨t.1, rfl, (hm t.1).1 t.2⟩

end MatedCRT
end
