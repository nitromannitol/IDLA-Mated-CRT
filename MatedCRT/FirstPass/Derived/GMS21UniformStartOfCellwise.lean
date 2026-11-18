import MatedCRT.FirstPass.Derived.UniformStartGoodPackage
import LatticeProb.Bonanno.BouRabeeGwynne.EuclideanWienerLaw

/-!
# The uniform-start invariance principle from the cellwise Lévy-Prokhorov comparison

`GMS21UniformStartInput 𝒮` ([GMS21, Theorem 3.4], uniform in the starting point) is derived from the cellwise
comparison of the stopped embedded walk with the stopped Brownian law: for every valid environment with
`0 < γ < 2`, all `0 < ρ < R`, `κ > 0` and every positive null sequence `e`, almost surely, for the area
parametrization of the curve, for all large `n` every cell of the mated-CRT map at mesh `e n` whose representative
lies in `ball 0 R` has Lévy-Prokhorov distance `< κ / 6` between the law of the stopped embedded walk from the cell
and the Brownian law started at the representative and stopped at its exit from `ball 0 R`.  The Brownian law is the
Euclidean Wiener law in dimension `2`.  The comparison is the only hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology

namespace MatedCRT

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison

/-- **The uniform-start invariance principle from the cellwise Lévy-Prokhorov comparison.** -/
theorem gms21UniformStartInput_of_cellwise {𝒮 : SpaceFillingSLEModel}
    (hLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ →
      ∀ (e : ℕ → ℝ) (he : ∀ n, 0 < e n), Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω), ∀ᶠ n in atTop,
      ∀ v : (areaCellConfig h (he n) (S.mult (e n) ω)).cells,
        areaCellRepresentative h (he n) (S.mult (e n) ω) v ∈
            (Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R : Set (LatticeProb.Euc 2)) →
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
  exact UniformStartGood.exists_eps_uniformStart_bound_of_cellwise hγ hγ2 hS hρR hκ _ rfl
    (BouRabeeGwynne.euclideanWienerLaw 2) (BouRabeeGwynne.isStandardBrownianLaw_euclideanWienerLaw 2)
    (hLP γ hγ hγ2 Ω S hS R ρ hρ hρR κ hκ) hθ

end MatedCRT
