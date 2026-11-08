import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapShiftIntegralDecoder
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapMeasureLaw
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapRestrictedComparison

/-! # Restricted measure-law domination from pinned field shifts -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped Topology ENNReal

namespace MatedCRT

/-- A pinned shift constant on an open set transfers domination of the
    modulo-constant pairing laws to mutual absolute continuity of the scaled LQG measure laws. -/
theorem restricted_lqg_shiftLaw_of_pairingLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ c : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμm : AEMeasurable μ P)
    (A : Set ℂ) (hA : IsOpen A)
    (hbuffer : ∀ n z, z ∈ A → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (g : ℂ → ℝ) (hg : Continuous g) (hpin : Real.circleAverage g 0 1 = 0)
    (hgA : ∀ z ∈ A, g z = c)
    (hpair : P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
        P.map (localModConstPairings α hC univ) ∧
      P.map (localModConstPairings α hC univ) ≪
        P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ)) :
    P.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict A) ≪
        P.map (fun ω => (μ ω).restrict A) ∧
      P.map (fun ω => (μ ω).restrict A) ≪
        P.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict A) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let b := ENNReal.ofReal (Real.exp (γ * c))
  let X : Ω → Measure ℂ := fun ω => b • (μ ω).restrict A
  let Y : Ω → Measure ℂ := fun ω => (μ ω).restrict A
  let Z := localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ
  let W := localModConstPairings α hC univ
  have hM (a : ℝ≥0∞) : Measurable (fun m : Measure ℂ => a • m.restrict A) :=
    (measurable_restricted_smul_measure A hA.measurableSet).comp
      (measurable_const.prodMk measurable_id)
  have hX : AEMeasurable X P := (hM b).comp_aemeasurable hμm
  have hY : AEMeasurable Y P := by
    simpa [Y, Function.comp_def] using (hM 1).comp_aemeasurable hμm
  have hlocY : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Y ω) := by
    filter_upwards [hμ] with ω hω
    let _ := hω.isLocallyFiniteMeasure
    dsimp [Y]
    infer_instance
  have hlocX : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (X ω) := by
    filter_upwards [hlocY] with ω hω
    let _ := hω
    let _ : IsFiniteMeasureOnCompacts (b • Y ω) :=
      IsFiniteMeasureOnCompacts.smul (Y ω) ENNReal.ofReal_ne_top
    change IsLocallyFiniteMeasure (b • Y ω)
    infer_instance
  have hZ : Measurable Z := measurable_pi_iff.mpr fun φ =>
    ((hGFF.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hW : Measurable W := measurable_pi_iff.mpr fun φ =>
    (hGFF.measurable_pairing φ.1 φ.2.1).sub_const _
  have hdec : ∀ U : Set ℂ, IsOpen U → ∃ d : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞,
      Measurable d ∧ (∀ᵐ ω ∂P, X ω U = d (Z ω)) ∧
      (∀ᵐ ω ∂P, Y ω U = d (W ω)) := by
    intro U hU
    obtain ⟨d, hdm, hde⟩ := exists_global_shifted_lqgOpenMass_decoder hGFF hμ A U hA hU hbuffer
    refine ⟨d, hdm, ?_, ?_⟩
    · filter_upwards [hde] with ω hω
      have hrestrict : ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))).restrict A =
          b • (μ ω).restrict A := by
        rw [restrict_withDensity hA.measurableSet, ← withDensity_const b]
        apply withDensity_congr_ae
        filter_upwards [ae_restrict_mem hA.measurableSet] with z hz
        simp [hgA z hz, b]
      have heq := hω g hg hpin
      have := congrArg (fun m : Measure ℂ => m U) hrestrict
      rw [Measure.restrict_apply hU.measurableSet] at this
      exact this.symm.trans heq.symm
    · filter_upwards [hde] with ω hω
      have heq := hω (fun _ => 0) continuous_const (by rw [Real.circleAverage_const])
      have hshift : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
        funext ω φ
        simp [addFunPairing]
      rw [hshift] at heq
      simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one] at heq
      change d (W ω) = ((μ ω).withDensity 1) (U ∩ A) at heq
      rw [withDensity_one] at heq
      rw [Measure.restrict_apply hU.measurableSet]
      exact heq.symm
  refine ⟨measureLaw_absolutelyContinuous_of_openMassDecoders
    hX hY hlocX hlocY hZ hW hpair.1 hdec, ?_⟩
  apply measureLaw_absolutelyContinuous_of_openMassDecoders hY hX hlocY hlocX hW hZ hpair.2
  intro U hU
  obtain ⟨d, hd, hx, hy⟩ := hdec U hU
  exact ⟨d, hd, hy, hx⟩

end MatedCRT
