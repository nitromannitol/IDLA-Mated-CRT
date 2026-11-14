import MatedCRT.FirstPass.Derived.AreaCellExitLawComparison

/-! # Template probabilities and area-cell exit laws -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity
open MatedCRT.TemplateDisconnectionWalk
open scoped NNReal ENNReal

/-- A template-event probability bound controls the distance between the
exit laws of area-cell walks on a common almost-sure environment event. -/
theorem MatedCRTEnv.IsValid.ae_levyProkhorovEDist_areaCell_exit_le_of_template
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (_hm : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (_hH : H.cell = cell ε (S.η ω))
    (_hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    {σ : ℝ≥0} (_hσ : 0 < σ)
    (_hcell : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (_hadj : ∀ K : (areaCellConfig h hε (S.mult ε ω)).cells,
      ∃ K' : (areaCellConfig h hε (S.mult ε ω)).cells,
        (areaCellConfig h hε (S.mult ε ω)).Adj K K')
    (_hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent)
    (ρ R d r : ℝ) (_hρ : ρ < 1) (_hρR : ρ ≤ R)
    (_hd : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ d) (_hgap : d < R - ρ)
    (W : Set Plane) (_hW : IsOpen W) (_hWb : Bornology.IsBounded W)
    (_hscale : ∀ z ∈ ball (Complex.orthonormalBasisOneI.repr 0) R, (σ : ℝ) • z ∈ W)
    (x y : ℤ)
    (_hxstart : (((euclideanCellEquiv h hε x).1 : Set Plane) ∩
      ball (Complex.orthonormalBasisOneI.repr 0) ρ).Nonempty)
    (_hystart : (((euclideanCellEquiv h hε y).1 : Set Plane) ∩
      ball (Complex.orthonormalBasisOneI.repr 0) ρ).Nonempty)
    (_hyB : (((euclideanCellEquiv h hε y).1 : Set Plane) ∩
      closedBall (Complex.orthonormalBasisOneI.repr 0) r).Nonempty)
    (_hr : 0 < r)
    (_htdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ (templateRadius (templateScaleCount r) : ℝ) / 2000)
    (_hρone : ρ ≤ 1)
    (_hρgap : 1 / 2 + 3 * ((templateRadius (templateScaleCount r) : ℝ) / 2000) < ρ)
    (t : ℝ) (ht : 0 < t) {δ : ℝ} (_hδ : 0 ≤ δ)
    (_htemplate : 1 - δ ≤ (srwLaw (S.mult ε ω) x
      {ξ | interpPathCM (vertexPoint ε (S.η ω)) ht.le ξ ∈ templateDisconnectionEvent r}).toReal),
    levyProkhorovEDist
      (((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))).map
        (fun ξ => ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
          (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)
          (BouRabeeGwynne.continuousExitTime W 0
            ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
              (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)).toNNReal))
      (((srwLaw (S.mult ε ω) y).map (fun ξ n => euclideanCellEquiv h hε (ξ n))).map
        (fun ξ => ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
          (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)
          (BouRabeeGwynne.continuousExitTime W 0
            ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
              (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)).toNNReal)) ≤ ENNReal.ofReal δ := by
  filter_upwards [hS.ae_srw_templateProbability_le_innerDisconnection S hε] with ω hω
  intro μ h hlf hm H hH hconn σ hσ hcell hadj hrec ρ R d r hρ hρR hd hgap
    W hW hWb hscale x y hxstart hystart hyB hr htdiam hρone hρgap t ht δ hδ htemplate
  apply S.levyProkhorovEDist_areaCell_exit_le ω h hε hlf hm H hH hconn hσ hcell hadj hrec
    ρ R d r hρ hρR hd hgap W hW hWb hscale x y hxstart hystart hyB hδ
  exact htemplate.trans (ENNReal.toReal_mono (measure_ne_top _ _)
    (hω hlf H hH r hr htdiam ρ hρone hρgap t ht x))

end MatedCRT
end
