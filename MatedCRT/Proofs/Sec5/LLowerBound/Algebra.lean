import MatedCRT.Draft.Section5

/-! # Absorbing the constant in Lemma 5.4

The final deterministic step in the proof at lines 2045-2050: a lower bound
of order `ε⁻¹` for the Green sum and an upper bound of order `ε⁻¹/²` for the
diagonal give the asserted power-law ratio. -/

namespace MatedCRT

open Filter Topology

/-- The constant in the lower bound may be absorbed by reducing the exponent
from `1/2` to `1/4`. -/
theorem eventually_green_ratio_lower_bound {C : ℝ} (hC : 0 < C) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ N D : ℝ,
      C * ε⁻¹ ≤ N → 0 < D → D ≤ ε ^ (-(1 / 2 : ℝ)) →
      ε ^ (-(1 / 4 : ℝ)) ≤ N / D := by
  have ht : Tendsto (fun ε : ℝ => ε ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 / 4 : ℝ))) :=
      ((Real.continuousAt_rpow_const 0 (1 / 4 : ℝ) (Or.inr (by norm_num))).tendsto).mono_left
        nhdsWithin_le_nhds
    simpa using h
  filter_upwards [self_mem_nhdsWithin, ht.eventually (Iio_mem_nhds hC)] with ε hε hsmall N D hN hD hupper
  have hpow : 0 ≤ ε ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hε.le _
  have heq : ε ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 2 : ℝ)) =
      ε ^ (1 / 4 : ℝ) * ε⁻¹ := by
    rw [← Real.rpow_add hε, ← Real.rpow_neg_one ε, ← Real.rpow_add hε]
    congr 1
    norm_num
  apply (le_div_iff₀ hD).2
  calc
    ε ^ (-(1 / 4 : ℝ)) * D ≤ ε ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hupper hpow
    _ = ε ^ (1 / 4 : ℝ) * ε⁻¹ := heq
    _ ≤ C * ε⁻¹ := mul_le_mul_of_nonneg_right hsmall.le (inv_nonneg.mpr hε.le)
    _ ≤ N := hN

end MatedCRT
