import MatedCRT.FirstPass.Derived.OccupationIntegralInMeasure
import MatedCRT.FirstPass.Derived.LQGApproxClockRevuz

/-!
# Occupation integrals of the approximating Liouville clocks converge in measure

For circle averages `hE` continuous at the dyadic scales, `F` the LQG clock (`IsLQGClock`, convergence in
probability of the approximating clocks, uniformly on compact time intervals) and `G` a PCAF version of `F`, the
occupation integrals `∫ f d(occupation measure of the clock at scale ε_k)` converge in `P_z`-measure, for every
start `z`, to the occupation integral of `G`, for every nonnegative continuous `f`.
-/

open MeasureTheory MarkovProcess Set Filter Topology
open HarmonicBalls (lqgClockApprox IsLQGClock planarBrownianMotion)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Occupation integrals of the approximating Liouville clocks converge in measure** to the occupation integral
of the LQG clock, under planar Brownian motion from every start `z`. -/
theorem tendstoInMeasure_integral_occupationMeasure_lqgClock {γ : ℝ} {hE : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (z : ℂ) (hF : IsLQGClock planarBrownianMotion γ hE z F)
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hG : IsPCAF planarLaw G)
    (hGF : ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t)
    {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    TendstoInMeasure (planarLaw z)
      (fun k b => ∫ x, f x ∂occupationMeasure
        (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b) atTop
      (fun b => ∫ x, f x ∂occupationMeasure (fun t => G t b) b) := by
  have hε0 : ∀ k : ℕ, 0 ≤ HarmonicBalls.dyadicScale k := fun k => (HarmonicBalls.dyadicScale_pos k).le
  have hP : ∀ k, IsPCAF planarLaw (lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k)) := fun k =>
    isPCAF_lqgClockApproxNN (hε0 k) (hcont k)
  refine tendstoInMeasure_integral_occupationMeasure (A := fun k => lqgClockApproxNN γ hE
      (HarmonicBalls.dyadicScale k)) (fun k => ?_) ?_ ?_ hf
    (fun k => (aemeasurable_integral_occupationMeasure (hP k) z hf hf0).aestronglyMeasurable)
  · exact ((hP k).path z).mono fun b hb => ⟨hb.2.1, hb.2.2⟩
  · exact (hG.path z).mono fun b hb => ⟨hb.2.1, hb.2.2⟩
  · intro η hη
    have hN : planarLaw z {b : ContinuousPath ℂ | ¬ ∀ t, (G t b : ℝ) = F b t} = 0 :=
      ae_iff.1 hGF
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) (hF 1 η hη)
      (fun k => bot_le) (fun k => ?_)
    calc planarLaw z {b | ∃ t : ℝ≥0, t ≤ 1 ∧
          η ≤ |(lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b : ℝ) - (G t b : ℝ)|}
        ≤ planarLaw z ({b | ∃ t ≤ (1 : ℝ≥0), η ≤
            |lqgClockApprox γ hE (HarmonicBalls.dyadicScale k) b t - F b t|} ∪
            {b : ContinuousPath ℂ | ¬ ∀ t, (G t b : ℝ) = F b t}) := by
          refine measure_mono fun b hb => ?_
          by_cases hbN : ∀ t, (G t b : ℝ) = F b t
          · left
            obtain ⟨t, ht, h⟩ := hb
            refine ⟨t, ht, ?_⟩
            rwa [coe_lqgClockApproxNN (hε0 k), hbN t] at h
          · right
            exact hbN
      _ ≤ _ + 0 := (measure_union_le _ _).trans (add_le_add_right hN.le _)
      _ = _ := add_zero _

end MatedCRT.FirstPass.Derived
