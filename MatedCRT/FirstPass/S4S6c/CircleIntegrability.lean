import MatedCRT.FirstPass.S4S6c.GoodAnnulusKernel

/-!
# Integrability of the corrected kernel on the good annulus times the circle (q2, task fp-S4S6c)

Ingredients of the joint integrability needed for the Fubini interchange in `CircleSwap.lean` (LEMMA68 Lemma 1, eq (6)):
* `ae_circleMap_ne`: for a fixed point `u`, almost every parameter `θ ∈ (0, 2π]` has `circleMap z t θ ≠ u`;
* `intervalIntegrable_kernel_slice`: for fixed `u`, `θ ↦ log(R/|u - circleMap z t θ|) + 1` is interval integrable;
* `measurable_kernel_circle`: `(u, θ) ↦ log(R/|u - circleMap z t θ|) + 1` is measurable on `ℂ × ℝ`.
The remaining step, integrability of `u ↦ ∫ |K(u, circleMap θ)| dθ` on the annulus, is open (see the round report).
-/

open MeasureTheory Real Set

namespace MatedCRT

/-- For a fixed point `u`, almost every `θ ∈ (0, 2π]` has `circleMap z t θ ≠ u`. -/
theorem ae_circleMap_ne {z u : ℂ} {t : ℝ} (ht : t ≠ 0) :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc 0 (2 * π) → circleMap z t θ ≠ u := by
  have hnull : volume {θ : ℝ | θ ∈ Set.uIoc 0 (2 * π) ∧ circleMap z t θ = u} = 0 := by
    apply Set.Subsingleton.measure_zero _ volume
    intro a ha b hb
    exact injOn_circleMap_of_abs_sub_le ht (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
      ha.1 hb.1 (ha.2.trans hb.2.symm)
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro θ hθ
  simp only [Set.mem_ofPred_eq, not_imp, ne_eq, not_not] at hθ
  exact hθ

/-- For fixed `u`, the kernel `θ ↦ log(R/|u - circleMap z t θ|) + 1` is interval integrable over `[0, 2π]`. -/
theorem intervalIntegrable_kernel_slice {z u : ℂ} {R t : ℝ} (hR : 0 < R) (ht : t ≠ 0) :
    IntervalIntegrable (fun θ : ℝ => Real.log (R / ‖u - circleMap z t θ‖) + 1) volume 0 (2 * π) := by
  have h1 : IntervalIntegrable (fun θ : ℝ => (Real.log R + 1) - Real.log ‖circleMap z t θ - u‖)
      volume 0 (2 * π) :=
    intervalIntegrable_const.sub (circleIntegrable_log_norm_sub_const (c := z) (a := u) t)
  refine h1.congr_ae ?_
  filter_upwards [(ae_restrict_iff' measurableSet_uIoc).2 (ae_circleMap_ne (z := z) (u := u) ht)]
    with θ hne
  have huv : ‖u - circleMap z t θ‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    exact hne.symm
  rw [Real.log_div hR.ne' huv, norm_sub_rev]
  ring

/-- The kernel `(u, θ) ↦ log(R/|u - circleMap z t θ|) + 1` is measurable on `ℂ × ℝ`. -/
theorem measurable_kernel_circle (z : ℂ) (R t : ℝ) :
    Measurable (fun p : ℂ × ℝ => Real.log (R / ‖p.1 - circleMap z t p.2‖) + 1) := by
  have hc : Continuous (fun p : ℂ × ℝ => circleMap z t p.2) := by
    unfold circleMap
    fun_prop
  have hn : Continuous (fun p : ℂ × ℝ => ‖p.1 - circleMap z t p.2‖) :=
    continuous_norm.comp (continuous_fst.sub hc)
  exact ((measurable_const.div hn.measurable).log).add_const 1

end MatedCRT
