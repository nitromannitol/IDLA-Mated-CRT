import MatedCRT.FirstPass.Derived.UniformStartGoodPackageInner
import LatticeProb.Bonanno.BouRabeeGwynne.EuclideanWienerLaw

/-!
# The uniform-start invariance principle from the cellwise comparison on the inner ball

`gms21UniformStartInput_of_cellwise_inner` is `gms21UniformStartInput_of_cellwise` with the cellwise Lévy-Prokhorov
comparison required only at the cells whose representative lies in the closed ball of radius `(ρ + R) / 2 < R`
instead of the whole ball of radius `R`.  The comparison on the inner ball is the form in which the Brownian
uniform-in-the-start estimates (a disc of radius strictly smaller than `R`) apply.  The comparison is the only
hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology

namespace MatedCRT

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison

/-- **The uniform-start invariance principle from the cellwise Lévy-Prokhorov comparison on the inner ball.** -/
theorem gms21UniformStartInput_of_cellwise_inner {𝒮 : SpaceFillingSLEModel}
    (hLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ →
      ∀ (e : ℕ → ℝ) (he : ∀ n, 0 < e n), Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω), ∀ᶠ n in atTop,
      ∀ v : (areaCellConfig h (he n) (S.mult (e n) ω)).cells,
        ‖Complex.orthonormalBasisOneI.repr.symm
          (areaCellRepresentative h (he n) (S.mult (e n) ω) v)‖ ≤ (ρ + R) / 2 →
          levyProkhorovEDist
            ((srwLaw (S.mult (e n) ω) ((euclideanCellEquiv h (he n)).symm v)).map
              (fun w : ℕ → ℤ => isometryEquiv 2
                (normalizedPrefixCurve
                  (complexToEuclideanPath (((1 : ℝ≥0) : ℝ) •
                    interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one w))
                  (pathExitTime (ball (0 : ℂ) R)
                    ⇑(((1 : ℝ≥0) : ℝ) • interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one w)).toNNReal)))
            (BouRabeeGwynne.stoppedBrownianLaw
              (Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R : Set (LatticeProb.Euc 2))
              (areaCellRepresentative h (he n) (S.mult (e n) ω) v)
              (BouRabeeGwynne.euclideanWienerLaw 2)) <
              ENNReal.ofReal ((κ / 2) / 3)) :
    GMS21UniformStartInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS R ρ hρ hρR κ hκ θ hθ
  exact UniformStartGood.exists_eps_uniformStart_bound_of_cellwise_inner hγ hγ2 hS hρR hκ _ rfl
    (BouRabeeGwynne.euclideanWienerLaw 2) (BouRabeeGwynne.isStandardBrownianLaw_euclideanWienerLaw 2)
    (hLP γ hγ hγ2 Ω S hS R ρ hρ hρR κ hκ) hθ

end MatedCRT
