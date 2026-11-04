import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RadialDriftReduction

/-! # Transfer of Brownian path events to the cone radial process -/

namespace MatedCRT

open Filter Set MeasureTheory HarmonicBalls MarkovProcess Topology
open scoped NNReal

/-- The positive-time part of the circle-average radial process, after
removing its linear drift, has the law of a standard Brownian path. -/
theorem IsQuantumCone.ae_radial_centered_of_brownian
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc)
    {E : Set (ℝ≥0 → ℝ)} (hE : MeasurableSet E)
    (hB : ∀ᵐ w ∂brownianMotion 0, (fun t : ℝ≥0 => w t) ∈ E) :
    ∀ᵐ ω ∂P, (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0 - γ * t) ∈ E := by
  obtain ⟨ν, hν, hlaw⟩ := hcone.radial_law
  let _ : IsProbabilityMeasure ν := hν.1
  let radial : Ω → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) := fun ω => radialProcess (hcirc ω)
  let center : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → (ℝ≥0 → ℝ) :=
    fun p t => p.1 t - γ * t
  let brown : ContinuousPath ℝ → (ℝ≥0 → ℝ) := fun w t => w t
  have hr : Measurable radial := by
    apply Measurable.prodMk <;> apply measurable_pi_iff.mpr <;> intro t
    · exact hcone.measurable_circle _ _ (Real.exp_pos _)
    · exact hcone.measurable_circle _ _ (Real.exp_pos _)
  have hc : Measurable center := by
    apply measurable_pi_iff.mpr
    intro t
    exact ((measurable_pi_apply t).comp measurable_fst).sub measurable_const
  have hb : Measurable brown := by
    apply measurable_pi_iff.mpr
    intro t
    exact ContinuousPath.measurable_coordinateProcess t
  have hmaps : P.map (center ∘ radial) = (brownianMotion 0).map brown := by
    rw [← Measure.map_map hc hr, hlaw]
    unfold quantumConeRadialLaw
    let shift : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun p t => p t - γ * t
    have hs : Measurable shift := by
      apply measurable_pi_iff.mpr
      intro t
      exact (measurable_pi_apply t).sub measurable_const
    have hid : center = shift ∘ Prod.fst := rfl
    rw [hid, ← Measure.map_map hs measurable_fst, Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    let drift : ContinuousPath ℝ → (ℝ≥0 → ℝ) := fun w t => w t + γ * t
    have hd : Measurable drift := by
      apply measurable_pi_iff.mpr
      intro t
      exact (ContinuousPath.measurable_coordinateProcess t).add measurable_const
    rw [Measure.map_map hs hd]
    congr 1
    funext w t
    simp [shift, drift, brown]
  have hBe : ∀ᵐ p ∂(brownianMotion 0).map brown, p ∈ E :=
    (MeasureTheory.ae_map_iff hb.aemeasurable hE).2 hB
  have hR : ∀ᵐ p ∂P.map (center ∘ radial), p ∈ E := hmaps ▸ hBe
  exact (MeasureTheory.ae_map_iff (hc.comp hr).aemeasurable hE).1 hR

/-- A discrete-time Brownian strong law transfers to integer logarithmic
times of the circle averages. -/
theorem IsQuantumCone.ae_radial_integer_sublinear_of_brownian
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc)
    (hB : ∀ᵐ w ∂brownianMotion 0, Tendsto
      (fun n : ℕ => w (n : ℝ≥0) / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (hcirc ω (Real.exp (-(n : ℝ))) 0 - γ * n) / n) atTop (𝓝 0) := by
  let E : Set (ℝ≥0 → ℝ) := {f | Tendsto (fun n : ℕ => f (n : ℝ≥0) / (n : ℝ)) atTop (𝓝 0)}
  have hE : MeasurableSet E := by
    apply MeasureTheory.measurableSet_tendsto_fun
    · intro n
      exact (measurable_pi_apply (n : ℝ≥0)).div_const _
    · exact measurable_const
  exact hcone.ae_radial_centered_of_brownian hE hB

end MatedCRT
