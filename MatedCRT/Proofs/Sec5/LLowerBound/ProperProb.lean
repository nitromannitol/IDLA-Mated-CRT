import MatedCRT.Proofs.Sec5.LLowerBound.SmallCells
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Measure

/-! Measurable exhaustion events for proper random curves. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Proper curves eventually avoid a fixed ball, with a time cutoff depending
only on the path. This event is closed in the compact-open path topology. -/
theorem isClosed_curve_escape (ρ T : ℝ) :
    IsClosed {f : C(ℝ, ℂ) | ∀ t : ℝ, T ≤ |t| → ρ ≤ ‖f t‖} := by
  have heq : {f : C(ℝ, ℂ) | ∀ t : ℝ, T ≤ |t| → ρ ≤ ‖f t‖} =
      ⋂ t : ℝ, ⋂ (_ : T ≤ |t|), {f : C(ℝ, ℂ) | ρ ≤ ‖f t‖} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_eval_const t).norm

/-- A measurable almost surely proper random curve has a deterministic time
cutoff which contains the preimage of a fixed ball with probability tending to
one as the cutoff tends to infinity. -/
theorem tendsto_measure_curve_escape {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (hp : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ)) (ρ : ℝ) :
    Tendsto (fun n : ℕ => P {ω | ∃ t : ℝ, (n : ℝ) ≤ |t| ∧ ‖η ω t‖ < ρ})
      atTop (𝓝 0) := by
  let E : ℕ → Set Ω := fun n => {ω | ∃ t : ℝ, (n : ℝ) ≤ |t| ∧ ‖η ω t‖ < ρ}
  apply tendsto_measure_zero_of_ae_eventually_not_mem P E
  · intro n
    have heq : E n = (η ⁻¹' {f : C(ℝ, ℂ) | ∀ t : ℝ, (n : ℝ) ≤ |t| → ρ ≤ ‖f t‖})ᶜ := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_compl_iff, mem_preimage, not_forall, not_le, exists_prop]
    rw [heq]
    exact (((isClosed_curve_escape ρ n).measurableSet.preimage hη).compl).nullMeasurableSet
  · filter_upwards [hp] with ω hω
    have hcomp : IsCompact ((η ω) ⁻¹' closedBall 0 ρ) :=
      (isProperMap_iff_tendsto_cocompact.2 ⟨(η ω).continuous, hω⟩).isCompact_preimage
        (isCompact_closedBall 0 ρ)
    obtain ⟨T, hT⟩ := hcomp.isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_nat_gt T
    filter_upwards [eventually_ge_atTop N] with n hn
    rintro ⟨t, htn, htρ⟩
    have htT : |t| ≤ T := by
      have h := hT (show t ∈ (η ω) ⁻¹' closedBall 0 ρ from by
        simpa [mem_closedBall, dist_zero_right] using htρ.le)
      simpa [Real.dist_eq] using h
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith

/-- The properness cutoff for the area-parametrized SLE curve is measurable
through the measurable continuous-path representative in the coupling. -/
theorem MatedCRTEnv.IsValid.tendsto_measure_curve_escape {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ρ : ℝ) :
    Tendsto (fun n : ℕ => S.P {ω | ∃ t : ℝ, (n : ℝ) ≤ |t| ∧ ‖S.η ω t‖ < ρ})
      atTop (𝓝 0) := by
  let _ : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  have hp : ∀ᵐ ω ∂S.P, Tendsto (η' ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [hS.ae_tendsto_cocompact, htie] with ω hω heq
    rw [heq.1]
    exact hω
  have h := _root_.MatedCRT.tendsto_measure_curve_escape S.P η' hC.measurable_curves.2.1 hp ρ
  have heq (n : ℕ) : S.P {ω | ∃ t : ℝ, (n : ℝ) ≤ |t| ∧ ‖S.η ω t‖ < ρ} =
      S.P {ω | ∃ t : ℝ, (n : ℝ) ≤ |t| ∧ ‖η' ω t‖ < ρ} := by
    apply measure_congr
    filter_upwards [htie] with ω hω
    simp only [hω.1]
  simpa only [← heq] using h

end MatedCRT
