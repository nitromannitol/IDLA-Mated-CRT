import MatedCRT.FirstPass.Derived.AreaCellEnvironmentFiniteExit
import LatticeProb.Euclidean.ParentBlockExitGeometry

/-! # Finite exit from parent-block interiors for area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open LatticeProb.ParentBlock
open scoped NNReal ENNReal

/-- A recurrent area-cell walk exits every parent-block interior in finite time,
simultaneously for all centers and nonnegative side lengths. -/
theorem MatedCRTEnv.ae_continuousExitTime_ne_top_all_parentBlock_interior
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
      ∀ (c : ℂ) (s : ℝ), 0 ≤ s →
        BouRabeeGwynne.continuousExitTime
          (Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock c s)) 0
          ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
            (areaCellRepresentative h hε (S.mult ε ω)) σ ξ) ≠ ∞ := by
  filter_upwards [S.ae_continuousExitTime_ne_top_all_bounded_areaCell ω h hε hlf hm
    H hH hconn hσ hcell hadj hrec x] with ξ hξ
  intro c s hs
  apply hξ
  exact (isCompact_parentBlock_preimage c hs).isBounded.subset
    (preimage_mono interior_subset)

end MatedCRT
end
