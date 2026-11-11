import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # From conditional to joint L¹ convergence -/

namespace MatedCRT

open MeasureTheory Filter Topology

/-- Conditional L¹ convergence with an integrable pathwise bound yields
joint L¹ convergence. The product measurability hypothesis is explicit: it
is needed both for Fubini and for measurability of the conditional error. -/
theorem tendsto_integral_norm_prod_of_conditional_L1
    {B Ω ι : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    (Q : Measure B) (P : Measure Ω) [SFinite Q] [SFinite P]
    (l : Filter ι) [l.IsCountablyGenerated] (F : ι → B × Ω → ℝ) (bound : B → ℝ)
    (hbound : Integrable bound Q)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (F i) (Q.prod P))
    (hslice : ∀ᶠ i in l, ∀ᵐ b ∂Q, Integrable (fun ω => F i (b, ω)) P)
    (hdom : ∀ᶠ i in l, ∀ᵐ b ∂Q, (∫ ω, ‖F i (b, ω)‖ ∂P) ≤ bound b)
    (hlim : ∀ᵐ b ∂Q, Tendsto (fun i => ∫ ω, ‖F i (b, ω)‖ ∂P) l (𝓝 0)) :
    (∀ᶠ i in l, Integrable (F i) (Q.prod P)) ∧
      Tendsto (fun i => ∫ p, ‖F i p‖ ∂(Q.prod P)) l (𝓝 0) := by
  let e : ι → B → ℝ := fun i b => ∫ ω, ‖F i (b, ω)‖ ∂P
  have hemeas : ∀ᶠ i in l, AEStronglyMeasurable (e i) Q := by
    filter_upwards [hmeas] with i hi
    exact hi.norm.integral_prod_right'
  have hedomb : ∀ᶠ i in l, ∀ᵐ b ∂Q, ‖e i b‖ ≤ bound b := by
    filter_upwards [hdom] with i hi
    filter_upwards [hi] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hb
  have heint : ∀ᶠ i in l, Integrable (e i) Q := by
    filter_upwards [hemeas, hedomb] with i hi hd
    exact hbound.mono' hi hd
  have hprod : ∀ᶠ i in l, Integrable (F i) (Q.prod P) := by
    filter_upwards [hmeas, hslice, heint] with i hi hs he
    exact (integrable_prod_iff hi).2 ⟨hs, he⟩
  have hconv : Tendsto (fun i => ∫ b, e i b ∂Q) l (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence bound hemeas hedomb hbound hlim
  refine ⟨hprod, ?_⟩
  apply hconv.congr'
  filter_upwards [hprod] with i hi
  exact (integral_prod (fun p => ‖F i p‖) hi.norm).symm

end MatedCRT
