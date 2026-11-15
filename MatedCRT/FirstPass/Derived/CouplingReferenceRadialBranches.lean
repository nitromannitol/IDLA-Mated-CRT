import MatedCRT.FirstPass.Derived.ConeReferenceLaw
import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalConeIdentification
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.RadialProcess

/-! # Radial branches of the coupled reference cone -/

noncomputable section

open MarkovProcess HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- Continuous radial readout and matching paths identify both branches of
    the reference cone with the corresponding coupling radial branches. -/
theorem radialProcess_coneRefCircle_eq_referenceConeRadialPair
    (γ : ℝ) (c : ℝ → ℂ → ℝ) (W V F : C(ℝ≥0, ℝ)) (b b' : ℝ≥0 → ℝ)
    (hW : ∀ t, W t = b t) (hW0 : W 0 = 0) (hF0 : F 0 = 0)
    (hF : ∀ t, F t = MatedCRT.Sec1.referenceConeConditionedPath γ b' t)
    (hc : ∀ t : ℝ, c (Real.exp (-t)) 0 = MatedCRTHarmonic.GMCFacts.twoSided W V t) :
    radialProcess (coneRefCircle γ c F) = MatedCRT.Sec1.referenceConeRadialPair γ b b' := by
  rw [radialProcess_coneRefCircle]
  have hc1 : c 1 0 = 0 := by
    simpa [MatedCRTHarmonic.GMCFacts.twoSided_apply] using hc 0
  apply Prod.ext
  · funext t
    have ht := hc (t : ℝ)
    have hz : (-(t : ℝ)).toNNReal = 0 := Real.toNNReal_of_nonpos (neg_nonpos.mpr t.2)
    simp only [MatedCRTHarmonic.GMCFacts.twoSided_apply, Real.toNNReal_coe, hz,
      sub_self, add_zero, hW0, sub_zero, hW] at ht
    simp [coneRefRadial, MatedCRT.Sec1.referenceConeRadialPair, ht]
  · funext t
    have ht := congrFun (MatedCRT.Sec1.referenceConeRadialPair_outer_centered γ b b') t
    simp only [coneRefRadial, hF0, sub_zero, hc1, add_zero]
    rw [hF]
    linarith

end MatedCRT.FirstPass.Derived
