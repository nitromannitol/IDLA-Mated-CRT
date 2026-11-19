import MatedCRT.External.RevuzTimeChange
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import MatedCRT.FirstPass.Derived.BrownianTubeMarkov

/-!
# Lebesgue measure is invariant for planar Brownian motion

For every time `t` and Borel set `S ⊆ ℂ`, `∫ P_z[B_t ∈ S] dz = |S|`: Lebesgue measure is an invariant
measure of planar Brownian motion. This is the stationarity behind the Revuz measure
`revuz planarLaw A`, which is taken with respect to Lebesgue measure (Revuz–Yor (1999), Chapter X, §2).
The proof writes `P_z` as the translate by `z` of `P_0` and exchanges the two integrals.

With the simple Markov property at a deterministic time this gives the stationarity of the
Brownian path measure started from Lebesgue measure, `∫ P_z dz`: under it `B_t` has law Lebesgue
measure (`map_eval_bind_planarLaw`) and the law is invariant under the time shift `θ_t`
(`map_pathShift_bind_planarLaw`, `lintegral_pathShift_planarLaw`).
-/

open MeasureTheory Set MarkovProcess
open scoped ENNReal

namespace MatedCRT

/-- **Lebesgue measure is invariant for planar Brownian motion**: `∫ P_z[B_t ∈ S] dz = |S|`. -/
theorem lintegral_planarLaw_eval_mem (t : NNReal) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ z, planarLaw z {ω | ω t ∈ S} = volume S := by
  have hmeas : Measurable fun p : ℂ × ContinuousPath ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (p.2 t + p.1) :=
    (measurable_const.indicator hS).comp
      (((continuous_eval_const t).measurable.comp measurable_snd).add measurable_fst)
  have hpt : ∀ z : ℂ, planarLaw z {ω | ω t ∈ S} =
      ∫⁻ b, S.indicator (fun _ => (1 : ℝ≥0∞)) (b t + z) ∂HarmonicBalls.planarBrownianMotion 0 := by
    intro z
    have hT : MeasurableSet (StopAtExitCmp.translatePath z ⁻¹' {ω : ContinuousPath ℂ | ω t ∈ S}) :=
      ((continuous_eval_const t).measurable hS).preimage
        (StopAtExitCmp.translatePath z).continuous.measurable
    rw [planarLaw, StopAtExitCmp.planarBrownianMotion_apply_eq_translatePath z,
      ← lintegral_indicator_one hT]
    congr 1
  simp_rw [hpt]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hin : ∀ b : ContinuousPath ℂ,
      ∫⁻ z, S.indicator (fun _ => (1 : ℝ≥0∞)) (b t + z) = volume S := by
    intro b
    have := lintegral_add_left_eq_self (μ := (volume : Measure ℂ))
      (S.indicator fun _ => (1 : ℝ≥0∞)) (b t)
    rw [this]
    exact lintegral_indicator_one hS
  simp_rw [hin]
  rw [lintegral_const, measure_univ, mul_one]

/-- The planar Brownian laws form a measurable family of measures. -/
theorem measurable_planarLaw : Measurable planarLaw :=
  HarmonicBalls.planarBrownianMotion.measurable

/-- Under the path measure `∫ P_z dz` started from Lebesgue measure, `B_t` has law Lebesgue measure. -/
theorem map_eval_bind_planarLaw (t : NNReal) :
    ((volume : Measure ℂ).bind planarLaw).map (fun ω : ContinuousPath ℂ => ω t) = volume := by
  ext S hS
  rw [Measure.map_apply (continuous_eval_const t).measurable hS,
    Measure.bind_apply ((continuous_eval_const t).measurable hS) measurable_planarLaw.aemeasurable]
  exact lintegral_planarLaw_eval_mem t hS

theorem pathShift_eq_shift (t : NNReal) :
    (fun ω : ContinuousPath ℂ => LatticeProb.pathShift ω t) = ContinuousPath.shift t := by
  funext ω
  ext s
  simp [LatticeProb.pathShift_apply, ContinuousPath.shift_apply]

theorem measurable_pathShift_const (t : NNReal) :
    Measurable fun ω : ContinuousPath ℂ => LatticeProb.pathShift ω t := by
  rw [pathShift_eq_shift]
  exact ContinuousPath.measurable_shift_fixed t

/-- **Stationarity of planar Brownian motion started from Lebesgue measure**: the path measure
`∫ P_z dz` is invariant under the time shift `θ_t`. -/
theorem map_pathShift_bind_planarLaw (t : NNReal) :
    ((volume : Measure ℂ).bind planarLaw).map (fun ω => LatticeProb.pathShift ω t) =
      (volume : Measure ℂ).bind planarLaw := by
  rw [pathShift_eq_shift]
  ext B hB
  have hg : Measurable fun y => planarLaw y B :=
    HarmonicBalls.planarBrownianMotion.measurable_coe hB
  have h1 : ∀ z, planarLaw z (ContinuousPath.shift t ⁻¹' B) =
      ∫⁻ ω, planarLaw (ω t) B ∂planarLaw z := by
    intro z
    have := planarBrownian_inter_shift_preimage z t MeasurableSet.univ hB
    simpa [planarLaw] using this
  rw [Measure.map_apply (ContinuousPath.measurable_shift_fixed t) hB,
    Measure.bind_apply (ContinuousPath.measurable_shift_fixed t hB) measurable_planarLaw.aemeasurable,
    Measure.bind_apply hB measurable_planarLaw.aemeasurable]
  simp_rw [h1]
  have hgt : Measurable fun ω : ContinuousPath ℂ => planarLaw (ω t) B :=
    hg.comp (continuous_eval_const t).measurable
  rw [← Measure.lintegral_bind measurable_planarLaw.aemeasurable hgt.aemeasurable]
  have hm := lintegral_map hg (continuous_eval_const t).measurable
    (μ := (volume : Measure ℂ).bind planarLaw)
  rw [map_eval_bind_planarLaw] at hm
  exact hm.symm

/-- **Stationarity, integral form**: for a measurable functional `F ≥ 0` of the path,
`∫ E_z[F ∘ θ_t] dz = ∫ E_z[F] dz`. -/
theorem lintegral_pathShift_planarLaw (t : NNReal) {F : ContinuousPath ℂ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ z, ∫⁻ ω, F (LatticeProb.pathShift ω t) ∂planarLaw z = ∫⁻ z, ∫⁻ ω, F ω ∂planarLaw z := by
  have hFs : Measurable fun ω : ContinuousPath ℂ => F (LatticeProb.pathShift ω t) :=
    hF.comp (measurable_pathShift_const t)
  rw [← Measure.lintegral_bind measurable_planarLaw.aemeasurable hFs.aemeasurable,
    ← Measure.lintegral_bind measurable_planarLaw.aemeasurable hF.aemeasurable]
  have hm := lintegral_map hF (measurable_pathShift_const t)
    (μ := (volume : Measure ℂ).bind planarLaw)
  rw [map_pathShift_bind_planarLaw] at hm
  exact hm.symm

end MatedCRT
