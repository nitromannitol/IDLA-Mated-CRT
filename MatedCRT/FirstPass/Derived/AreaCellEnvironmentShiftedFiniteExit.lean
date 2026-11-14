import MatedCRT.FirstPass.Derived.AreaCellRecurrentShiftedFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellNonisolated
import MatedCRT.FirstPass.Derived.AreaCellLaw

/-! # Shifted finite exits for area-cell walks in an environment -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- Every shifted interpolation of a recurrent area-cell walk exits every
bounded set in finite time, simultaneously over valid representatives and
positive scales. -/
theorem MatedCRTEnv.ae_continuousExitTime_ne_top_all_bounded_all_shifts_areaCell
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (hm : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    (hc : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent) (x : ℤ) :
    ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      ∀ K : ℕ, ∀ (p : (areaCellConfig h hε (S.mult ε ω)).cells → Plane),
        (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ (a : ℝ≥0), 0 < a →
        ∀ U : Set Plane, Bornology.IsBounded U →
        BouRabeeGwynne.continuousExitTime U 0
          ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk p a
            (fun n => ξ (K + n))) ≠ ∞ := by
  exact ae_continuousExitTime_ne_top_all_bounded_all_shifts_areaCell_of_recurrent
    h hε (S.mult ε ω) hlf H hH hconn hc (S.areaCellConfig_exists_adj ω h hε)
    hrec x _ rfl (S.areaCellConfig_isSRWLaw ω h hε hm x)

end MatedCRT
end
