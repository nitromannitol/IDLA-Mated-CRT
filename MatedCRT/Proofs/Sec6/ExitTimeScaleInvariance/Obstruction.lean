import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# E-A10: why Lemma 2.18 cannot give the scale-invariant exit-time bound of Lemma 6.8, Step 4

Two elementary facts behind the verdict (b) of ESCALATIONS "E-A10 resolution (c4)".

* `log_one_div_le_of_mem_thickening_ball`: on `B_{t}(B_s(y))` the kernel of Lemma 2.18 (BG20 Proposition 5.1, line 921)
  satisfies `log (1/|v - u|) ≥ log (1/(2(s + t)))`. So the bound that Lemma 2.18 gives for the exit time from
  `B' = B_{𝐫_z/4}(η(b))` (Step 4, line 2600) is at least `C ε⁻¹ (log (1/(2(𝐫_z/4 + ε^α))) + 1) μ_h(B_{ε^α}(B'))`,
  while Step 3 (line 2547) gives `E[V | h, η] ≤`-order `ε⁻¹ μ_h(B')` at best; the Paley-Zygmund ratio of line 2528
  obtained from Steps 3-4 is therefore `O(log⁻² (1/𝐫_z))`, never an `r`-independent `s₂`.
* `log_div_add_log_le_log_one_div_scaled`: the only exact symmetry of the quantum-cone mated-CRT environment that
  rescales space is the quantum-cone scaling about the origin (DMS14 Proposition 4.13(i), `QuantumConeScalingInput`).
  If `λ > 0` maps `B_s(y)` into `B_ρ` (`λ (|y| + s) ≤ ρ`), then for `u ≠ v` in it the kernel of Lemma 2.18 for the
  rescaled environment, `log (1/(λ |u - v|))`, still exceeds the scale-invariant `log (s/|u - v|)` by
  `log ((|y| + s)/(ρ s))`. In Step 4 the balls lie outside `Θ̄ ⊇ B_{s₀}` and have radius `≤ √δ`, so the loss is at least
  `log (s₀/(ρ √δ)) → ∞`: rescaling about the origin does not remove it.
-/

namespace MatedCRT

open Metric

/-- Scaling about the origin does not remove the logarithmic loss: if `λ (|y| + s) ≤ ρ` (the dilation `z ↦ λ z` maps
`B_s(y)` into `B_ρ`), then `log (s/|u - v|) + log ((|y| + s)/(ρ s)) ≤ log (1/(λ |u - v|))` for `u ≠ v`. -/
theorem log_div_add_log_le_log_one_div_scaled {lam ρ s : ℝ} {y u v : ℂ} (hlam : 0 < lam) (hρ : 0 < ρ)
    (hs : 0 < s) (huv : u ≠ v) (hmap : lam * (‖y‖ + s) ≤ ρ) :
    Real.log (s / ‖u - v‖) + Real.log ((‖y‖ + s) / (ρ * s)) ≤ Real.log (1 / (lam * ‖u - v‖)) := by
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  have hys : 0 < ‖y‖ + s := by positivity
  have h1 : 0 < s / ‖u - v‖ := div_pos hs hd
  have h2 : 0 < (‖y‖ + s) / (ρ * s) := div_pos hys (mul_pos hρ hs)
  rw [← Real.log_mul h1.ne' h2.ne']
  refine Real.log_le_log (mul_pos h1 h2) ?_
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hd (mul_pos hρ hs)) (mul_pos hlam hd)]
  calc s * (‖y‖ + s) * (lam * ‖u - v‖) = (s * ‖u - v‖) * (lam * (‖y‖ + s)) := by ring
    _ ≤ (s * ‖u - v‖) * ρ := mul_le_mul_of_nonneg_left hmap (mul_pos hs hd).le
    _ = 1 * (‖u - v‖ * (ρ * s)) := by ring

/-- On the `t`-neighbourhood of `B_s(y)` the kernel of Lemma 2.18 is at least `log (1/(2(s + t)))`:
`|v - u| < 2(s + t)` there. -/
theorem log_one_div_le_of_mem_thickening_ball {t s : ℝ} {y u v : ℂ} (hu : u ∈ thickening t (ball y s))
    (hv : v ∈ thickening t (ball y s)) (huv : u ≠ v) :
    Real.log (1 / (2 * (s + t))) ≤ Real.log (1 / ‖v - u‖) := by
  obtain ⟨a, ha, hua⟩ := mem_thickening_iff.mp hu
  obtain ⟨b, hb, hvb⟩ := mem_thickening_iff.mp hv
  rw [mem_ball] at ha hb
  have hd : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv.symm)
  have hlt : ‖v - u‖ < 2 * (s + t) := by
    rw [← dist_eq_norm]
    have h1 := dist_triangle v b u
    have h2 := dist_triangle b y u
    have h3 := dist_triangle y a u
    have h4 := dist_comm y a
    have h5 := dist_comm a u
    linarith
  exact Real.log_le_log (one_div_pos.mpr (hd.trans hlt)) (one_div_le_one_div_of_le hd hlt.le)

end MatedCRT
