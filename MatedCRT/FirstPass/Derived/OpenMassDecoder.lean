import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.JointMeasureLaw

/-!
# The masses of countably many open sets are a measurable function of the circle average process

For a countable family `U i` of open sets there is one Borel function `F` of the circle average process
`(r, z) ↦ c r z` (product σ-algebra on `(0, ∞) × ℂ → ℝ`) whose value on the circle average process of every
continuous-on-`(0, ∞) × ℂ` pair `(c, μ)` with `IsLQGLimit γ c μ` is the vector of open-set masses
`i ↦ μ (U i)`.  The decoder is the supremum over test functions of the liminf over the dyadic scales of the
integrals against the approximating measures `lqgApprox`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- The masses of countably many open sets of the LQG limit measure are a Borel function of the circle
average process. -/
theorem exists_measurable_openMass_decoder {ι : Type} [Countable ι] (γ : ℝ) (U : ι → Set ℂ)
    (hU : ∀ i, IsOpen (U i)) :
    ∃ F : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ι → ℝ≥0∞, Measurable F ∧
      ∀ (c : ℝ → ℂ → ℝ) (μ : Measure ℂ),
        ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) → IsLQGLimit γ c μ →
          F (circleProcess c) = fun i => μ (U i) := by
  classical
  choose f hf hfc hmass using fun i : ι => exists_open_mass_test_functions (hU i)
  choose A hA hAeq using fun n : ℕ => exists_measurable_lqgApprox_decoder γ (dyadicScale n)
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  let profile (n : ℕ) (v : Ioi (0 : ℝ) × ℂ → ℝ) (z : ℂ) :=
    v (⟨dyadicScale n, dyadicScale_pos n⟩, z)
  have hp (n : ℕ) : Measurable (profile n) := by
    apply Measurable.of_eval
    intro z
    exact measurable_pi_apply _
  let F : (Ioi (0 : ℝ) × ℂ → ℝ) → ι → ℝ≥0∞ := fun v i =>
    ⨆ j : ℕ, Filter.liminf (fun n => ENNReal.ofReal (∫ z, f i j z ∂(A n (profile n v)))) atTop
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro i
    apply Measurable.iSup
    intro j
    apply Measurable.liminf
    intro n
    exact (((hf i j).stronglyMeasurable.integral_kernel (κ := K)).measurable.comp
      ((hA n).comp (hp n))).ennreal_ofReal
  refine ⟨F, hF, fun x m hxω hmω => ?_⟩
  funext i
  rw [hmass i m hmω.isLocallyFiniteMeasure]
  change (⨆ j : ℕ, Filter.liminf (fun n => ENNReal.ofReal
    (∫ z, f i j z ∂(A n (profile n (circleProcess x))))) atTop) = _
  apply iSup_congr
  intro j
  apply Filter.Tendsto.liminf_eq
  apply (ENNReal.continuous_ofReal.tendsto _).comp
  convert hmω.tendsto_integral (f i j) (hf i j) (hfc i j) using 1
  funext n
  have hcont : Continuous (fun z => x (dyadicScale n) z) :=
    hxω.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨dyadicScale_pos n, mem_univ z⟩)
  have heq : A n (profile n (circleProcess x)) = lqgApprox γ x (dyadicScale n) := by
    simpa only [profile, circleProcess, lqgApprox] using hAeq n (fun z => x (dyadicScale n) z) hcont
  rw [heq]

end MatedCRT.FirstPass.Derived
