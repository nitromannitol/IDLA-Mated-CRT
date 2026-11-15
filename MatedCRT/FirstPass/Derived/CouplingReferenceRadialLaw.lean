import MatedCRT.FirstPass.Derived.CouplingReferenceRadialBranches

/-! # Radial branches under the coupled path laws -/

noncomputable section

open MeasureTheory ProbabilityTheory MarkovProcess HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- The common radial readout and coupled path laws identify both radial
branches on a single almost-sure event. -/
theorem ae_radialProcess_coneRefCircle_eq_referenceConeRadialPair
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {B B' : ℝ≥0 → Ω → ℝ}
    (W V F : Ω → C(ℝ≥0, ℝ)) (c : Ω → ℝ → ℂ → ℝ)
    (hWlaw : IsPreBrownianReal (fun t ω => W ω t) P)
    (hFmeas : Measurable F)
    (hFlaw : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F))
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    (hF : ∀ᵐ ω ∂P, ∀ t, F ω t = MatedCRT.Sec1.referenceConeConditionedPath γ (fun s => B' s ω) t)
    (hc : ∀ᵐ ω ∂P, ∀ t : ℝ,
      c ω (Real.exp (-t)) 0 = MatedCRTHarmonic.GMCFacts.twoSided (W ω) (V ω) t) :
    ∀ᵐ ω ∂P, radialProcess (coneRefCircle γ (c ω) (F ω)) =
      MatedCRT.Sec1.referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω) := by
  have hFzero : ∀ᵐ ω ∂P, F ω 0 = 0 := by
    have hs : MeasurableSet {w : C(ℝ≥0, ℝ) | w 0 = 0} :=
      measurableSet_eq_fun (continuous_eval_const (0 : ℝ≥0)).measurable measurable_const
    exact (ae_map_iff hFmeas.aemeasurable hs).mp
      (isBMConditionedPositive_ae_eval_zero hFlaw)
  filter_upwards [hW, hF, hc, hWlaw.eval_zero_ae_eq_zero, hFzero] with ω hw hf hr hz hfzero
  exact radialProcess_coneRefCircle_eq_referenceConeRadialPair γ (c ω) (W ω) (V ω)
    (F ω) (fun t => B t ω) (fun t => B' t ω) hw hz hfzero hf hr

end MatedCRT.FirstPass.Derived
