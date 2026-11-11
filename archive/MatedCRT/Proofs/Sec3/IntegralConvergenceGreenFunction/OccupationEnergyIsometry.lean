import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PlanarBrownianIncrement
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Brownian occupation energy in Euclidean coordinates -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls
open scoped ENNReal

/-- Isometries preserve finite-dimensional Riesz energy under pushforward. -/
theorem HasFiniteDimensionalEnergy.map_isometry {E F : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure E} [SFinite μ] {d : ℝ} (hμ : HasFiniteDimensionalEnergy μ d)
    {f : E → F} (hf : Isometry f) : HasFiniteDimensionalEnergy (μ.map f) d := by
  intro δ hδ
  have hk := measurable_rieszEnergyKernel (E := F) (d - δ)
  have hm : Measurable f := hf.continuous.measurable
  calc
    (∫⁻ x, ∫⁻ y, rieszEnergyKernel (d - δ) x y ∂(μ.map f) ∂(μ.map f)) =
        ∫⁻ x, ∫⁻ y, rieszEnergyKernel (d - δ) (f x) (f y) ∂μ ∂μ := by
      rw [lintegral_map hk.lintegral_prod_right' hm]
      apply lintegral_congr
      intro x
      exact lintegral_map (hk.comp (measurable_const.prodMk measurable_id)) hm
    _ = ∫⁻ x, ∫⁻ y, rieszEnergyKernel (d - δ) x y ∂μ ∂μ := by
      simp only [rieszEnergyKernel, hf.dist_eq]
    _ < ⊤ := hμ δ hδ

/-- Almost surely the Brownian occupation measure has finite-dimensional
energy in the Euclidean coordinates used in Berestycki's GMC theorem. -/
theorem planarBrownianMotion_ae_euclidean_finiteDimensionalEnergy (z : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion z), ∀ T : ℝ,
      HasFiniteDimensionalEnergy
        (pathOccupationMeasure
          (fun t => Complex.orthonormalBasisOneI.repr (b t.toNNReal)) T) 2 := by
  filter_upwards [planarBrownianMotion_ae_finiteDimensionalEnergy z] with b hb T
  have hf : Isometry Complex.orthonormalBasisOneI.repr :=
    Complex.orthonormalBasisOneI.repr.isometry
  have hbmeas : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  have h := (hb T).map_isometry hf
  rw [pathOccupationMeasure, Measure.map_map hf.continuous.measurable hbmeas] at h
  simpa [pathOccupationMeasure, Function.comp_def] using h


/-- A finite-time occupation measure is carried by a measurable set when
the path remains there before the terminal time. -/
theorem pathOccupationMeasure_compl_eq_zero_of_before {E : Type*}
    [MeasurableSpace E] {b : ℝ → E} (hb : Measurable b) (T : ℝ)
    {D : Set E} (hD : MeasurableSet D)
    (hbefore : ∀ t ∈ Ico (0 : ℝ) T, b t ∈ D) :
    pathOccupationMeasure b T Dᶜ = 0 := by
  rw [pathOccupationMeasure, Measure.map_apply hb hD.compl]
  have hae : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), b t ∈ D := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne T)] with t ht hne
    exact hbefore t ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
  exact (ae_iff.mp hae)


/-- Brownian occupation up to a finite time no later than the exit time is
concentrated in the domain, including when the terminal time is the exit. -/
theorem continuousPath_occupation_compl_eq_zero_before_exit
    (b : MarkovProcess.ContinuousPath ℂ) (D : Set ℂ) (hD : MeasurableSet D)
    (T : ℝ) (hT : ENNReal.ofReal T ≤ b.exitTime D) :
    pathOccupationMeasure (fun t => b t.toNNReal) T Dᶜ = 0 := by
  apply pathOccupationMeasure_compl_eq_zero_of_before (by fun_prop) T hD
  intro t ht
  apply MarkovProcess.ContinuousPath.mem_of_lt_exitTime
  change ENNReal.ofReal t < b.exitTime D
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [ht.1, ht.2])).mpr ht.2) hT


/-- Simultaneously for all measurable Euclidean domains and finite horizons
up to exit, Brownian occupation is carried by the domain and has energy
dimension at least two. -/
theorem planarBrownianMotion_ae_euclidean_occupation_before_exit (z : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion z), ∀
      (D : Set (EuclideanSpace ℝ (Fin 2))) (_ : MeasurableSet D) (T : ℝ),
      ENNReal.ofReal T ≤ b.exitTime (Complex.orthonormalBasisOneI.repr ⁻¹' D) →
      HasFiniteDimensionalEnergy
        (pathOccupationMeasure (fun t => Complex.orthonormalBasisOneI.repr (b t.toNNReal)) T) 2 ∧
      pathOccupationMeasure (fun t => Complex.orthonormalBasisOneI.repr (b t.toNNReal)) T Dᶜ = 0 := by
  filter_upwards [planarBrownianMotion_ae_euclidean_finiteDimensionalEnergy z] with b hb D hD T hT
  refine ⟨hb T, ?_⟩
  apply pathOccupationMeasure_compl_eq_zero_of_before (by fun_prop) T hD
  intro t ht
  apply MarkovProcess.ContinuousPath.mem_of_lt_exitTime (Complex.orthonormalBasisOneI.repr ⁻¹' D) b
  change ENNReal.ofReal t < b.exitTime (Complex.orthonormalBasisOneI.repr ⁻¹' D)
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [ht.1, ht.2])).mpr ht.2) hT

end MatedCRT
