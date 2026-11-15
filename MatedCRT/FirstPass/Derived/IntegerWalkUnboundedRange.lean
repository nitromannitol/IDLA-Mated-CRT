import MatedCRT.FirstPass.Derived.IntegerWalkPositiveSpeedFiniteExit

/-! # Unbounded range of the embedded walk -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped ENNReal NNReal

/-- Almost every embedded walk has unbounded range at every positive speed. -/
theorem ae_unbounded_range_all_positive_speeds_integerWalk
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ v : ℝ, 0 < v → ¬ Bornology.IsBounded (Set.range (interpolatedWalk ε η v ξ)) := by
  filter_upwards [ae_pathExitTime_ne_top_all_positive_speeds_all_bounded_integerWalk
    h hε m hlf H hH hconn x] with ξ hξ
  intro v hv hbounded
  apply hξ v hv _ hbounded
  simp only [HarmonicBalls.pathExitTime, Set.mem_range_self, not_true_eq_false,
    and_false, exists_false, Set.ofPred_false, sInf_empty]

end MatedCRT
end
