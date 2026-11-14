import MatedCRT.FirstPass.Derived.AreaCellBallTargets
import MatedCRT.FirstPass.Derived.AreaCellBallFrontier
import MatedCRT.FirstPass.Derived.AreaCellGraph
import MatedCRT.FirstPass.Derived.WalkSetDisconnectsBridge
import MatedCRT.FirstPass.Derived.SrwInnerTemplateProbability
import LatticeProb.Walk.RelabelledSeparationMeasure

/-! # Separation probabilities for area-parametrized cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS
open MatedCRTHarmonic.HarmonicInfinity
open MatedCRT.TemplateDisconnectionWalk

/-- Relabelling integer walks by their area cells preserves the probability of
separation before hitting a ball frontier, for any measure on walks. -/
theorem measure_areaCell_separation_eq {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hsymm : ∀ a b, m a b = m b a) (z : ℂ) (δ R : ℝ)
    (Q : Measure (ℕ → ℤ)) :
    (Q.map (fun ξ n => euclideanCellEquiv h hε (ξ n)))
      {ξ | GraphSeparates (areaCellConfig h hε m).graph
        (traceBefore id {K : (areaCellConfig h hε m).cells |
          ((K.1 : Set ReflectedGMS.Plane) ∩
            frontier (ball (Complex.orthonormalBasisOneI.repr z) R)).Nonempty} ξ)
        {K : (areaCellConfig h hε m).cells |
          ((K.1 : Set ReflectedGMS.Plane) ∩
            closedBall (Complex.orthonormalBasisOneI.repr z) δ).Nonempty}
        {K : (areaCellConfig h hε m).cells |
          ((K.1 : Set ReflectedGMS.Plane) ∩
            frontier (ball (Complex.orthonormalBasisOneI.repr z) R)).Nonempty}} =
      Q {ξ | walkSetDisconnectsBeforeHit m (cellVertices ε η (closedBall z δ))
        (cellVertices ε η (frontier (ball z R))) ξ} := by
  let _ : Countable (areaCellConfig h hε m).cells :=
    Countable.of_equiv ℤ (euclideanCellEquiv h hε)
  have ht := LatticeProb.measure_graphSeparates_traceBefore_map
    (areaCellGraphIso h hε m hsymm) (measurable_of_countable _) (measurable_of_countable _)
    {K : (areaCellConfig h hε m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩
        frontier (ball (Complex.orthonormalBasisOneI.repr z) R)).Nonempty}
    {K : (areaCellConfig h hε m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩
        closedBall (Complex.orthonormalBasisOneI.repr z) δ).Nonempty}
    {K : (areaCellConfig h hε m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩
        frontier (ball (Complex.orthonormalBasisOneI.repr z) R)).Nonempty} Q
  change (Q.map (fun ξ n => euclideanCellEquiv h hε (ξ n))) _ = _ at ht
  have hI : (areaCellGraphIso h hε m hsymm) ⁻¹'
      {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩
          frontier (ball (Complex.orthonormalBasisOneI.repr z) R)).Nonempty} =
      cellVertices ε η (frontier (ball z R)) := by
    change (euclideanCellEquiv h hε) ⁻¹' _ = _
    exact euclideanCellEquiv_preimage_meeting_ball_frontier h hε m z R
  have hA : (areaCellGraphIso h hε m hsymm) ⁻¹'
      {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩
          closedBall (Complex.orthonormalBasisOneI.repr z) δ).Nonempty} =
      cellVertices ε η (closedBall z δ) := by
    change (euclideanCellEquiv h hε) ⁻¹' _ = _
    exact euclideanCellEquiv_preimage_meeting_closedBall h hε m z δ
  rw [hI, hA] at ht
  refine ht.trans ?_
  congr 1
  ext ξ
  exact graphSeparates_traceBefore_iff_walkSetDisconnectsBeforeHit _ _ _ ξ

/-- The template-event estimate expressed in the area-cell graph. -/
theorem MatedCRTEnv.IsValid.ae_srw_templateProbability_le_areaCellSeparation
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
      (H : MatedCRTHarmonic.CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf)
        (0 : ℤ)), H.cell = cell ε (S.η ω) → ∀ (δ : ℝ), 0 < δ →
      (∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
        diam (cell ε (S.η ω) k) ≤ (templateRadius (templateScaleCount δ) : ℝ) / 2000) →
      ∀ (R : ℝ), R ≤ 1 →
        1 / 2 + 3 * ((templateRadius (templateScaleCount δ) : ℝ) / 2000) < R →
      ∀ (t : ℝ) (ht : 0 < t) (a : ℤ) {μ : Measure ℂ}
        (h : IsAreaParametrized μ (S.η ω)),
        srwLaw (S.mult ε ω) a
          {ξ | interpPathCM (vertexPoint ε (S.η ω)) ht.le ξ ∈ templateDisconnectionEvent δ} ≤
        ((srwLaw (S.mult ε ω) a).map (fun ξ n => euclideanCellEquiv h hε (ξ n)))
          {ξ | GraphSeparates (areaCellConfig h hε (S.mult ε ω)).graph
            (traceBefore id {K : (areaCellConfig h hε (S.mult ε ω)).cells |
              ((K.1 : Set ReflectedGMS.Plane) ∩
                frontier (ball (Complex.orthonormalBasisOneI.repr 0) R)).Nonempty} ξ)
            {K : (areaCellConfig h hε (S.mult ε ω)).cells |
              ((K.1 : Set ReflectedGMS.Plane) ∩
                closedBall (Complex.orthonormalBasisOneI.repr 0) δ).Nonempty}
            {K : (areaCellConfig h hε (S.mult ε ω)).cells |
              ((K.1 : Set ReflectedGMS.Plane) ∩
                frontier (ball (Complex.orthonormalBasisOneI.repr 0) R)).Nonempty}} := by
  filter_upwards [hS.ae_srw_templateProbability_le_innerDisconnection S hε] with ω hω
  intro hlf H hH δ hδ hdiam R hR hgap t ht a μ h
  rw [measure_areaCell_separation_eq h hε (S.mult ε ω) (S.mult_symm ε ω) 0 δ R]
  exact hω hlf H hH δ hδ hdiam R hR hgap t ht a

end MatedCRT
