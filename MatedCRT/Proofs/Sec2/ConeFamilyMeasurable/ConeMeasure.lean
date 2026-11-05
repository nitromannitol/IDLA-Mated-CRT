import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ConeVolumeGrowth
import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Measurability of the quantum-cone LQG measure -/

namespace MatedCRT

open MeasureTheory Filter Topology Set HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- A circle-average approximation of the cone LQG measure is measurable
up to a null set. -/
theorem IsConeField.aemeasurable_lqgApprox
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => lqgApprox γ (hcirc ω) r) P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_lqgApprox_decoder γ r
  have hp : Measurable (fun ω z => hcirc ω r z) :=
    Measurable.of_eval fun z => hcone.2.1.measurable_circle r z hr
  refine (hF.comp hp).aemeasurable.congr ?_
  filter_upwards [hcone.2.1.ae_continuousOn_circle] with ω hω
  have hc : Continuous (fun z => hcirc ω r z) :=
    hω.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, mem_univ z⟩)
  simpa only [Function.comp_apply, lqgApprox] using hFeq (fun z => hcirc ω r z) hc

/-- The LQG measure of a cone field is an almost-everywhere measurable
measure-valued random variable. -/
theorem IsConeField.aemeasurable_lqgMeasure
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) : AEMeasurable μ P := by
  classical
  let η : ℕ → Ω → Measure ℂ := fun n =>
    (hcone.aemeasurable_lqgApprox (dyadicScale_pos n)).mk _
  have hη (n : ℕ) : Measurable (η n) :=
    (hcone.aemeasurable_lqgApprox (dyadicScale_pos n)).measurable_mk
  have hηeq : ∀ᵐ ω ∂P, ∀ n, η n ω = lqgApprox γ (hcirc ω) (dyadicScale n) := by
    apply ae_all_iff.mpr
    intro n
    exact (hcone.aemeasurable_lqgApprox (dyadicScale_pos n)).ae_eq_mk.symm
  let A : Ω → Prop := fun ω => IsLQGLimit γ (hcirc ω) (μ ω) ∧
    ∀ n, η n ω = lqgApprox γ (hcirc ω) (dyadicScale n)
  have hgood : ∀ᵐ ω ∂P, A ω := hcone.2.2.and hηeq
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  let ν : Ω → Measure ℂ := fun ω => if ω ∈ N then 0 else μ ω
  have hA (ω : Ω) (hω : ω ∉ N) : A ω := by
    by_contra hn
    exact hω (hNsub hn)
  have hloc (ω : Ω) : IsLocallyFiniteMeasure (ν ω) := by
    by_cases hω : ω ∈ N
    · simp only [ν, hω, ite_true]
      infer_instance
    · simpa only [ν, hω, ite_false] using (hA ω hω).1.isLocallyFiniteMeasure
  have hopen (U : Set ℂ) (hU : IsOpen U) : Measurable (fun ω => ν ω U) := by
    obtain ⟨f, hf, hfc, hmass⟩ := exists_open_mass_test_functions hU
    let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
    let G : Ω → ℝ≥0∞ := fun ω => ⨆ i, Filter.liminf
      (fun n => ENNReal.ofReal (∫ z, f i z ∂(η n ω))) atTop
    have hG : Measurable G := by
      apply Measurable.iSup
      intro i
      apply Measurable.liminf
      intro n
      exact (((hf i).stronglyMeasurable.integral_kernel (κ := K)).measurable.comp (hη n)).ennreal_ofReal
    have heq : (fun ω => ν ω U) = (fun ω => if ω ∈ N then 0 else G ω) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp only [ν, hω, ite_true, Measure.coe_zero, Pi.zero_apply]
      · have ha := hA ω hω
        simp only [ν, hω, ite_false]
        rw [hmass (μ ω) ha.1.isLocallyFiniteMeasure]
        congr 1
        funext i
        apply (Filter.Tendsto.liminf_eq _).symm
        apply (ENNReal.continuous_ofReal.tendsto _).comp
        simpa only [ha.2] using ha.1.tendsto_integral (f i) (hf i) (hfc i)
    rw [heq]
    exact Measurable.ite hNmeas measurable_const hG
  have hν := measurable_measure_of_isOpen hloc hopen
  apply hν.aemeasurable.congr
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNnull)
  filter_upwards [hae] with ω hω
  simp only [ν, hω, ite_false]

/-- Volume growth and a measurable stopping time give a measurable stopped
cone family. -/
theorem aemeasurable_coneFamilyProcess
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ} (hT : AEMeasurable T P)
    (hf : ∀ᵐ ω ∂P, IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) :
    AEMeasurable (fun ω => familyProcess (Λ ω) (T ω)) P :=
  aemeasurable_coneFamilyProcess_of_volumeGrowth hγ hγ2 hcone h27 hcone.aemeasurable_lqgMeasure hT hf

end MatedCRT
