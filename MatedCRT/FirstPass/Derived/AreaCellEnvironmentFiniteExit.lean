import MatedCRT.FirstPass.Derived.AreaCellRecurrentSimultaneousFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellLaw

/-! # Finite exit for area-cell walks in a mated-CRT environment -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- An environment's recurrent area-cell walk exits every bounded set in finite
 time, simultaneously on one full-measure event. -/
theorem MatedCRTEnv.ae_continuousExitTime_ne_top_all_bounded_areaCell
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (hm : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    {σ : ℝ≥0} (hσ : 0 < σ)
    (hcell : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hadj : ∀ K : (areaCellConfig h hε (S.mult ε ω)).cells,
      ∃ K' : (areaCellConfig h hε (S.mult ε ω)).cells,
        (areaCellConfig h hε (S.mult ε ω)).Adj K K')
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent) (x : ℤ) :
    ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      ∀ U : Set ReflectedGMS.Plane, Bornology.IsBounded U →
        BouRabeeGwynne.continuousExitTime U 0
          ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
            (areaCellRepresentative h hε (S.mult ε ω)) σ ξ) ≠ ∞ := by
  exact ae_continuousExitTime_ne_top_all_bounded_areaCell_of_recurrent
    h hε (S.mult ε ω) hlf H hH hconn hσ hcell hadj hrec x _ rfl
    (S.areaCellConfig_isSRWLaw ω h hε hm x)

end MatedCRT
end
