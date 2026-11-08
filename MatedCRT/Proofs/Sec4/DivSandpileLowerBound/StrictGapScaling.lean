import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapCountable
import HarmonicBalls.Proofs.Sec5.ContinuityUnderMassScaling

/-! Samplewise exclusion of all but countably many mass shifts. -/

namespace MatedCRT

open Set MeasureTheory Metric _root_.HarmonicBalls

/-- If the confined regularization defects of a measure have countably many
mass parameters, then, at a fixed positive time, only countably many exponential
mass shifts produce such a defect. -/
theorem countable_regularization_defect_shifts
    {μ : Measure ℂ} {ρ t γ : ℝ} {z : ℂ} (ht : 0 < t) (hγ : γ ≠ 0)
    (hcount : {s : ℝ | 0 < s ∧ closure (cluster μ ρ z s) ⊆ ball 0 ρ ∧
      interior (closure (cluster μ ρ z s)) ≠ cluster μ ρ z s}.Countable) :
    {c : ℝ | closure (cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t) ⊆ ball 0 ρ ∧
      interior (closure (cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t)) ≠
        cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t}.Countable := by
  let f : ℝ → ℝ := fun c => (Real.exp (γ * c))⁻¹ * t
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (Real.exp (γ * a))⁻¹ = (Real.exp (γ * b))⁻¹ :=
      mul_right_cancel₀ ht.ne' hab
    have he : Real.exp (γ * a) = Real.exp (γ * b) := inv_injective h
    exact mul_left_cancel₀ hγ (Real.exp_injective he)
  apply (hcount.preimage hinj).mono
  intro c hc
  have hcluster := cluster_smul_measure (μ := μ) (R := ρ) (z := z)
    (c := Real.exp (γ * c)) (t := t) (Real.exp_pos _) ht.le
  change 0 < f c ∧ closure (cluster μ ρ z (f c)) ⊆ ball 0 ρ ∧
    interior (closure (cluster μ ρ z (f c))) ≠ cluster μ ρ z (f c)
  refine ⟨mul_pos (inv_pos.mpr (Real.exp_pos _)) ht, ?_⟩
  change closure (cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t) ⊆ ball 0 ρ ∧
    interior (closure (cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t)) ≠
      cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t at hc
  rw [hcluster] at hc
  exact hc

/-- The comparison estimate implies countability of the bad exponential
shifts for any fixed positive time. -/
theorem countable_regularization_defect_shifts_of_comparison
    {μ : Measure ℂ} {ρ t γ : ℝ} {z : ℂ} (ht : 0 < t) (hγ : γ ≠ 0)
    (hopen : ∀ s : ℝ, 0 < s → IsOpen (cluster μ ρ z s))
    (hcompare : ∀ s u : ℝ, 0 < s → s < u →
      closure (cluster μ ρ z u) ⊆ ball 0 ρ →
      interior (closure (cluster μ ρ z s)) ⊆ cluster μ ρ z u) :
    {c : ℝ | closure (cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t) ⊆ ball 0 ρ ∧
      interior (closure (cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t)) ≠
        cluster (ENNReal.ofReal (Real.exp (γ * c)) • μ) ρ z t}.Countable := by
  apply countable_regularization_defect_shifts ht hγ
  exact countable_open_cluster_regularization_defects
    (fun s => cluster μ ρ z s)
    (fun s => closure (cluster μ ρ z s) ⊆ ball 0 ρ) hopen hcompare

end MatedCRT
