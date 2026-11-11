import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.JointL1Convergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ConditionalMassBound

/-! # Joint convergence of conditional chaos masses -/

namespace MatedCRT

open MeasureTheory Filter Topology

/-- Conditional L¹ convergence of nonnegative masses with a common conditional
mean gives joint L¹ convergence when that mean is integrable over paths.
Joint measurability of the error remains an explicit hypothesis. -/
theorem tendsto_integral_norm_prod_of_conditional_mass_L1
    {B Ω ι : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    (Q : Measure B) (P : Measure Ω) [SFinite Q] [SFinite P]
    (l : Filter ι) [l.IsCountablyGenerated]
    (f : ι → B → Ω → ℝ) (g : B → Ω → ℝ) (m : B → ℝ)
    (hm : Integrable m Q)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable
      (fun p : B × Ω => f i p.1 p.2 - g p.1 p.2) (Q.prod P))
    (hg : ∀ᵐ b ∂Q, Integrable (g b) P ∧ (∀ᵐ ω ∂P, 0 ≤ g b ω) ∧
      (∫ ω, g b ω ∂P) = m b)
    (hf : ∀ᶠ i in l, ∀ᵐ b ∂Q, Integrable (f i b) P ∧
      (∀ᵐ ω ∂P, 0 ≤ f i b ω) ∧ (∫ ω, f i b ω ∂P) = m b)
    (hlim : ∀ᵐ b ∂Q, Tendsto
      (fun i => ∫ ω, |f i b ω - g b ω| ∂P) l (𝓝 0)) :
    (∀ᶠ i in l, Integrable (fun p : B × Ω => f i p.1 p.2 - g p.1 p.2)
      (Q.prod P)) ∧ Tendsto
      (fun i => ∫ p, ‖f i p.1 p.2 - g p.1 p.2‖ ∂(Q.prod P)) l (𝓝 0) := by
  apply tendsto_integral_norm_prod_of_conditional_L1 Q P l
    (fun i p => f i p.1 p.2 - g p.1 p.2) (fun b => 2 * m b)
  · exact hm.const_mul 2
  · exact hmeas
  · filter_upwards [hf] with i hi
    filter_upwards [hi, hg] with b hb hgb
    exact hb.1.sub hgb.1
  · filter_upwards [hf] with i hi
    filter_upwards [hi, hg] with b hb hgb
    simpa only [Real.norm_eq_abs] using
      integral_abs_sub_le_twice_mean P (f i b) (g b) (m b)
        hb.1 hgb.1 hb.2.1 hgb.2.1 hb.2.2 hgb.2.2
  · simpa only [Real.norm_eq_abs] using hlim

end MatedCRT
