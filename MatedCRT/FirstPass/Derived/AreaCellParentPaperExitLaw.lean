import MatedCRT.FirstPass.Derived.AreaCellPaperHoldingExitLaw
import MatedCRT.FirstPass.Derived.AreaCellParentInteriorFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellNonisolated

/-! # Parent-block exit positions of area-cell walks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS HarmonicBalls
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain LatticeProb
open LatticeProb.ParentBlock LatticeProb.CellConfigWalk
open scoped NNReal ENNReal

/-- The area-cell walk and paper's constant-step walk have the same exit-position
law from a parent-block interior. -/
theorem MatedCRTEnv.areaCell_parentBlock_holding_exitPosition_law
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (hmult : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    {σ m : ℝ≥0} (hσ : 0 < σ) (hm : 0 < m)
    (hcell : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent)
    (x : ℤ) (c : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    let C := areaCellConfig h hε (S.mult ε ω)
    let e := euclideanCellEquiv h hε
    let p := areaCellRepresentative h hε (S.mult ε ω)
    let Q := srwLaw (S.mult ε ω) x
    let U := interior (parentBlock c a)
    (((Q.map (fun ξ n => e (ξ n))).map (fun ξ =>
      (C.interpolatedWalk p σ ξ)
        (LatticeProb.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (C.interpolatedWalk p σ ξ)).toNNReal)).map
      Complex.orthonormalBasisOneI.repr.symm) =
    Q.map (fun ξ => ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le ξ)
      (pathExitTime U ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le ξ)).toNNReal) := by
  have hfinite := S.ae_continuousExitTime_ne_top_all_parentBlock_interior ω h hε hlf
    hmult H hH hconn hσ hcell (S.areaCellConfig_exists_adj ω h hε) hrec x
  have hfinite' : ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map
      (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      LatticeProb.continuousExitTime
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock c a)) 0
        ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
          (areaCellRepresentative h hε (S.mult ε ω)) σ ξ) ≠ ∞ := by
    filter_upwards [hfinite] with ξ hξ
    exact hξ c a ha
  exact areaCell_holding_exitPosition_law h hε (S.mult ε ω) hrec
    (S.areaCellConfig_holding_pos ω h hε hcell) x (srwLaw (S.mult ε ω) x)
    (S.areaCellConfig_isSRWLaw ω h hε hmult x) hσ hm isOpen_interior hfinite'

end MatedCRT
end
