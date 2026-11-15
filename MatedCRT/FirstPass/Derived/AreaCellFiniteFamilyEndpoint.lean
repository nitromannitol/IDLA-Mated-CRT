import MatedCRT.FirstPass.Derived.AreaCellEuclideanBrownianEndpoint
import MatedCRT.FirstPass.Derived.FiniteDomainBrownianEndpointComparison

/-! Uniform endpoint-law comparisons for families of paper walks. -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb BouRabeeGwynne Filter
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal Topology

/-- The Euclidean law of the totalized exit position of the interpolated walk. -/
def areaCellEuclideanExitProbability {η : ℝ → ℂ} {ε m : ℝ} (hm : 0 ≤ m)
    (mult : ℤ → ℤ → ℕ) (a : ℝ) {U : Set ℂ} (hU : IsOpen U) (x : ℤ) :
    ProbabilityMeasure (BouRabeeGwynne.Euc 2) := by
  let F : (ℕ → ℤ) → C(ℝ≥0, ℂ) := fun w => a • interpPathCM (vertexPoint ε η) hm w
  have hF : Measurable F := ((continuous_interpPathCM (vertexPoint ε η) hm).const_smul a).measurable
  have hE : Measurable (fun f : C(ℝ≥0, ℂ) => f (pathExitTime U f).toNNReal) :=
    ContinuousEval.continuous_eval.measurable.comp
      (measurable_id.prodMk (ENNReal.measurable_toNNReal.comp
        (ExitTimeCdf.measurable_pathExitTime hU)))
  let G := fun w => Complex.orthonormalBasisOneI.repr ((F w) (pathExitTime U (F w)).toNNReal)
  have hG : Measurable G := Complex.orthonormalBasisOneI.repr.continuous.measurable.comp (hE.comp hF)
  exact ⟨(srwLaw mult x).map G, (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance⟩

/-- Uniform stopped-curve convergence entails uniform convergence of the
corresponding totalized Euclidean exit-position laws. -/
theorem areaCell_finiteFamily_endpoint_hLP
    {J : Type*} {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    (W : J → Set ℂ) (hW : ∀ j, IsOpen (W j)) (K : J → Set (BouRabeeGwynne.Euc 2))
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) (hρ : BouRabeeGwynne.IsStandardBrownianLaw ρ)
    (V : ∀ _j, ℕ → Type*) (x : ∀ j n, V j n → ℤ)
    (ε m a : J → ℕ → ℝ) (hε : ∀ j n, 0 < ε j n) (hm : ∀ j n, 0 ≤ m j n)
    (mult : J → ℕ → ℤ → ℤ → ℕ)
    (hK : ∀ j n (v : V j n), Complex.orthonormalBasisOneI.repr
      (a j n • vertexPoint (ε j n) η (x j n v)) ∈ K j)
    (hc : ∀ j, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovEDist
        ((srwLaw (mult j n) (x j n v)).map (fun w => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath (a j n • interpPathCM (vertexPoint (ε j n) η) (hm j n) w))
            (pathExitTime (W j) (a j n • interpPathCM (vertexPoint (ε j n) η) (hm j n) w)).toNNReal)))
        (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' W j)
          (Complex.orthonormalBasisOneI.repr (a j n • vertexPoint (ε j n) η (x j n v))) ρ)
        < ENNReal.ofReal δ) :
    ∀ j, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist
        (areaCellEuclideanExitProbability (η := η) (ε := ε j n) (hm j n) (mult j n) (a j n) (hW j) (x j n v) : Measure (BouRabeeGwynne.Euc 2))
        (BrownianExitLawIdentification.stoppedBrownianEndpointProbability
          (Complex.orthonormalBasisOneI.repr '' W j)
          (Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenMap _ (hW j)) ρ hρ
          (⟨_, hK j n v⟩ : K j) : Measure (BouRabeeGwynne.Euc 2)) < δ := by
  intro j δ hδ
  filter_upwards [hc j δ hδ] with n hn v
  have hb := areaCell_paper_euclidean_exitPosition_le_sourceCurve h (hε j n)
    (mult j n) (hm j n) (a j n) (hW j) (x j n v) ρ
  have hlt := lt_of_le_of_lt hb (hn v)
  exact ENNReal.toReal_lt_of_lt_ofReal hlt

end MatedCRT
end
