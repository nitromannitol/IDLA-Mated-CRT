import MatedCRT.Proofs.Sec1.EnvironmentScaling.ReferenceConeRadialCircleFixed
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge

/-!
# The reference cone radial-circle identity, derived

At every fixed `t`, the circle average about `0` at radius `e^{-t}` of the circle-average
embedding of the `γ`-quantum cone (DMS Def 4.10), built from a whole-plane Gaussian free field `X`
and independent Brownian motions `B`, `B'`, is almost surely the radial process `A_t`
(Bonanno, `MatedCRTHarmonic.LQGCone.ae_circleAvg_coneField_exp`, copied into
Lattice-Probability). The frozen `MatedCRTHarmonic.MatedCRT.coneField` and `coneRadial` have the
same bodies as `MatedCRTHarmonic.CellScaling.coneField` and `coneRadial`, so they agree by `rfl`.
This supplies the hypothesis `hfix` of `referenceConeRadialCircleStep_of_fixedRadius`, hence
`ReferenceConeRadialCircleStep` and the canonical joint field-radius law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

theorem matedCRT_coneField_eq_cellScaling (X : LQGMetric.DistC) (A : ℝ → ℝ) :
    MatedCRTHarmonic.MatedCRT.coneField X A = MatedCRTHarmonic.CellScaling.coneField X A := rfl

theorem matedCRT_coneRadial_eq_cellScaling (γ α : ℝ) (b b' : ℝ≥0 → ℝ) :
    MatedCRTHarmonic.MatedCRT.coneRadial γ α b b' =
      MatedCRTHarmonic.CellScaling.coneRadial γ α b b' := rfl

/-- The circle average of the cone field at radius `e^{-t}` is the radial process at `t`, almost
surely, at every fixed `t` (frozen definitions). -/
theorem ae_circleAvg_matedCRT_coneField_exp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (γ : ℝ) {X : Ω → LQGMetric.DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hX : LQGMetric.IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) (t : ℝ) :
    ∀ᵐ ω ∂P, LQGMetric.circleAvg
        (MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))
        (Real.exp (-t)) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t :=
  MatedCRTHarmonic.LQGCone.ae_circleAvg_coneField_exp (α := γ) hX hB hB' hBB' t

/-- **`ReferenceConeRadialCircleStep`, derived** from the fixed-radius circle averages of the
cone field. -/
theorem referenceConeRadialCircleStep_derived (𝒮 : SpaceFillingSLEModel) :
    ReferenceConeRadialCircleStep 𝒮 :=
  referenceConeRadialCircleStep_of_fixedRadius (by
    intro γ Ω _ P _ X B B' hX hB hB' hBB' t
    exact ae_circleAvg_matedCRT_coneField_exp γ hX hB hB' hBB' t)

/-- The canonical joint field-radius law from the cone scaling input alone. -/
theorem canonicalConeDistributionRadiusLawStep_derived (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) : CanonicalConeDistributionRadiusLawStep 𝒮 :=
  canonicalConeDistributionRadiusLawStep_of_reference_circle 𝒮 hscale
    (referenceConeRadialCircleStep_derived 𝒮)

end MatedCRT.Sec1
