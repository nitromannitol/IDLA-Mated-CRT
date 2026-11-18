import MatedCRT.FirstPass.Derived.PlanarBrownianOccupationMeasure
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller

/-!
# Stopped occupation of planar Brownian motion and its Gaussian marginals

The one-time marginal of planar Brownian motion from `z` at time `t` is the planar Gaussian law
`planarGaussian z t` (`map_eval_planarBrownianMotion`). Consequently, for an open set `D` and a
measurable `F ≥ 0`, the occupation integral of `F` along the path stopped at `t ∧ τ_D`, averaged
over the path, is at most the time integral over `(0, t]` of the Gaussian averages of `1_D F`
(`lintegral_stoppedOccupation_le_lintegral_planarGaussian`): before the exit time the path lies in
`D`, and Tonelli exchanges the path and time integrals.
-/

open MeasureTheory Set MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The marginal of planar Brownian motion from `x` at time `t` is the planar Gaussian law with
mean `x` and covariance `t · I₂`. -/
theorem map_eval_planarBrownianMotion (x : ℂ) (t : ℝ≥0) :
    (planarBrownianMotion x).map (fun b => b t) = planarGaussian x t := by
  have hmap := isFellerKernelSemigroup_planarHeatSemigroup.continuousProcess_map_eval_nnreal
    planarHeatSemigroup isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup t
  rw [← planarBrownianMotion_eq_continuousProcess] at hmap
  have hvalue := congrArg (fun ker : ProbabilityTheory.Kernel ℂ ℂ => ker x) hmap
  change (planarBrownianMotion.map (ContinuousPath.coordinateProcess t)) x = _ at hvalue
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_coordinateProcess t),
    planarHeatSemigroup_apply] at hvalue
  exact hvalue

/-- Stopped occupation bound: for an open `D`, a measurable `F ≥ 0` and `t : ℝ`,
`E_z ∫_{(0, t ∧ τ_D]} F(𝓑_s) ds ≤ ∫_{(0, t]} ∫ 1_D F d(planarGaussian z s) ds`. When `τ_D = ∞`
the left time interval is `(0, 0]`, which is empty. -/
theorem lintegral_stoppedOccupation_le_lintegral_planarGaussian {D : Set ℂ} (hD : IsOpen D)
    (z : ℂ) {F : ℂ → ℝ≥0∞} (hF : Measurable F) (t : ℝ) :
    ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime D b).toReal), F (b s.toNNReal))
        ∂(planarBrownianMotion z) ≤
      ∫⁻ s in Ioc 0 t, ∫⁻ y, D.indicator F y ∂(planarGaussian z s.toNNReal) := by
  have hFD : Measurable (D.indicator F) := hF.indicator hD.measurableSet
  have hpt : ∀ b : ContinuousPath ℂ,
      ∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime D b).toReal), F (b s.toNNReal) ≤
        ∫⁻ s in Ioc 0 t, D.indicator F (b s.toNNReal) := by
    intro b
    rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
    calc ∫⁻ s in Ioo 0 (min t (ContinuousPath.exitTime D b).toReal), F (b s.toNNReal)
        = ∫⁻ s in Ioo 0 (min t (ContinuousPath.exitTime D b).toReal),
            D.indicator F (b s.toNNReal) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
          have hlt : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b := by
            rcases eq_or_ne (ContinuousPath.exitTime D b) ⊤ with h | h
            · rw [h]
              exact ENNReal.coe_lt_top
            · exact (ENNReal.ofReal_lt_iff_lt_toReal hs.1.le h).2
                (hs.2.trans_le (min_le_right _ _))
          rw [indicator_of_mem (ContinuousPath.mem_of_lt_exitTime D b _ hlt)]
      _ ≤ ∫⁻ s in Ioc 0 t, D.indicator F (b s.toNNReal) :=
          lintegral_mono_set fun s hs => ⟨hs.1, hs.2.le.trans (min_le_left _ _)⟩
  calc _ ≤ ∫⁻ b, (∫⁻ s in Ioc 0 t, D.indicator F (b s.toNNReal)) ∂(planarBrownianMotion z) :=
        lintegral_mono hpt
    _ = ∫⁻ s in Ioc 0 t, ∫⁻ b, D.indicator F (b s.toNNReal) ∂(planarBrownianMotion z) :=
        lintegral_lintegral_swap (hFD.comp measurable_eval_toNNReal).aemeasurable
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
        rw [← map_eval_planarBrownianMotion z s.toNNReal,
          lintegral_map hFD (g := fun b : ContinuousPath ℂ => b s.toNNReal)
            (ContinuousPath.measurable_coordinateProcess _)]

end MatedCRT.KilledOccupation
