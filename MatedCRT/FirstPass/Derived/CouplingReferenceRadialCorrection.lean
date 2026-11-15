import MatedCRT.FirstPass.Derived.CouplingReferenceRadialLaw
import MatedCRT.FirstPass.Derived.ReferenceConeRadialCorrection
import LatticeProb.LQG.ConeSplicePairing

/-! # Radial correction for coupled cone paths -/

noncomputable section

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess
open scoped NNReal
open MatedCRTHarmonic MatedCRTHarmonic.GMCFacts

namespace MatedCRT.FirstPass.Derived

/-- The coupled cone and splice have locally integrable radial profiles and
    their difference is the reference correction on one common event. -/
theorem ae_coupled_radial_difference_eq_reference_correction
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : ProbabilityTheory.IsBrownianReal B P) (hB' : ProbabilityTheory.IsBrownianReal B' P)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    (W V F : Ω → C(ℝ≥0, ℝ)) (c : Ω → ℝ → ℂ → ℝ)
    (hFm : Measurable F)
    (hFlaw : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F))
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    (hF : ∀ᵐ ω ∂P, ∀ t, F ω t = MatedCRT.Sec1.referenceConeConditionedPath γ (fun s => B' s ω) t)
    (hc : ∀ᵐ ω ∂P, ∀ t : ℝ, c ω (Real.exp (-t)) 0 = twoSided (W ω) (V ω) t) :
    ∀ᵐ ω ∂P,
      LocallyIntegrable (fun z : ℂ => MatedCRTHarmonic.MatedCRT.coneRadial γ γ
        (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖)) volume ∧
      LocallyIntegrable (radialW (twoSided (W ω) (V ω))) volume ∧
      ∀ z : ℂ, MatedCRTHarmonic.MatedCRT.coneRadial γ γ
        (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖) -
        radialW (twoSided (W ω) (V ω)) z =
          γ * (-Real.log ‖z‖) + coneRefField (c ω) (F ω) z := by
  have hA : MatedCRTHarmonic.MoTPort.IsConeProcess γ (QuantumZipper.Qc γ)
      (fun t ω => MatedCRTHarmonic.LQGCone.motConeRadial γ γ
        (fun s => B s ω) (fun s => B' s ω) t) P :=
    MatedCRTHarmonic.LQGCone.isConeProcess_motConeRadial hB hB' hBB'
  have hLI : ∀ᵐ ω ∂P, LocallyIntegrable
      (fun z : ℂ => MatedCRTHarmonic.MatedCRT.coneRadial γ γ
        (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖)) volume := by
    filter_upwards [MatedCRTHarmonic.MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω
    refine hω.congr (Filter.Eventually.of_forall fun z => ?_)
    have he := MatedCRTHarmonic.LQGCone.coneRadial_eq_Q_add_motConeRadial γ γ
      (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖)
    exact he.symm
  have hFzero : ∀ᵐ ω ∂P, F ω 0 = 0 := by
    have hs : MeasurableSet {w : C(ℝ≥0, ℝ) | w 0 = 0} :=
      measurableSet_eq_fun (continuous_eval_const (0 : ℝ≥0)).measurable measurable_const
    exact (ae_map_iff hFm.aemeasurable hs).mp (isBMConditionedPositive_ae_eval_zero hFlaw)
  filter_upwards [hLI, LatticeProb.LQG.ae_locallyIntegrable_radialW_twoSided hB W V hW,
    hW, hF, hc, hB.eval_zero_ae_eq_zero, hFzero] with ω hcone hsplice hw hf hr hz hfzero
  have hwzero : W ω 0 = 0 := (hw 0).trans hz
  refine ⟨hcone, hsplice, radial_difference_eq_reference_correction γ _ _ _ _ _ hwzero hfzero ?_ ?_ hr⟩
  · intro t
    rw [← MatedCRT.Sec1.referenceConeRadialPair_inner γ (fun s => B s ω) (fun s => B' s ω) t]
    simp only [MatedCRT.Sec1.referenceConeRadialPair, hw]
  · intro t
    by_cases ht : t = 0
    · subst t
      simp [MatedCRTHarmonic.MatedCRT.coneRadial, hz, hfzero]
    · have ht' : 0 < t := bot_lt_iff_ne_bot.mpr ht
      rw [← MatedCRT.Sec1.referenceConeRadialPair_outer γ (fun s => B s ω) (fun s => B' s ω) t ht']
      have he := congrFun (MatedCRT.Sec1.referenceConeRadialPair_outer_centered γ
        (fun s => B s ω) (fun s => B' s ω)) t
      rw [← hf t] at he
      linarith

end MatedCRT.FirstPass.Derived
