import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeScalingPositivity

/-! Measurability of the cone harmonic-ball exit event.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Metric Set Topology TopologicalSpace _root_.HarmonicBalls

/-- Almost sure volume growth on positive integer-radius balls implies null
measurability of a cone harmonic-ball exit event. -/
theorem nullMeasurableSet_exit_of_integer_volumeGrowth
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hV : ∀ n : ℕ, ∀ᵐ ω ∂S.P, ∃ βminus βplus,
      VolumeGrowth (S.μ ω) ((n : ℝ) + 1) βminus βplus)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (ρ t : ℝ) (ht : 0 < t) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P := by
  obtain ⟨C₀, hcount, hdense⟩ := exists_countable_dense ℂ
  let C : Set ℂ := C₀ ∪ {0}
  have hC : C.Countable := hcount.union (countable_singleton 0)
  have hd : Dense C := hdense.mono subset_union_left
  have hzero : (0 : ℂ) ∈ C := Or.inr rfl
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) := by
    filter_upwards [hS.isLQGMeasure] with ω hω
    exact hω.isLocallyFiniteMeasure
  apply nullMeasurableSet_lt_clusterExitTime_of_membership S.P S.μ Λ hΛ hloc ?_ ρ t ht
  intro q hq z
  apply nullMeasurableSet_mem_coneFamily_of_dense_leastSupersolutions S.P S.μ Λ q hq hΛ
    hC hd hzero ?_ z
  intro n x _
  have hR : 0 < (n : ℝ) + 1 := by positivity
  by_cases hx : x ∈ closedBall (0 : ℂ) ((n : ℝ) + 1)
  · exact hS.aemeasurable_leastSupersolution_of_volumeGrowth _ _ 0 x hR hq
      (mem_ball_self hR) hx (hV n)
  · have heq : (fun ω => leastSupersolution (S.μ ω) ((n : ℝ) + 1) 0 q x) =
        fun _ => 0 := by
      funext ω
      exact leastSupersolution_eq_zero_of_notMem_closedBall (S.μ ω) _ _ 0 x hq.le hx
    rw [heq]
    exact aemeasurable_const

/-- Cone environment scaling and the local volume-growth estimate imply null
measurability of the cone harmonic-ball exit event. -/
theorem nullMeasurableSet_exit_of_cone_scaling
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hscale : ConeEnvironmentScalingStep 𝒮)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (ρ t : ℝ) (ht : 0 < t) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P := by
  apply nullMeasurableSet_exit_of_integer_volumeGrowth hS ?_ Λ hΛ ρ t ht
  intro n
  exact hS.ae_volumeGrowth_of_scaling hγ hγ' h27 hscale (by positivity)

end MatedCRT.Sec7
