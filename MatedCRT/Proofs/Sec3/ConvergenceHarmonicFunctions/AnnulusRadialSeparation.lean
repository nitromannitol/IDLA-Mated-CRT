import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusBarriers

/-! # Outward radial segments for annulus separation -/

namespace MatedCRT

open Metric Set

/-- Every point admits a unit outward direction from a prescribed center.
Along this ray, both the displacement from the starting point and the
distance from the center increase exactly by the ray parameter. -/
theorem exists_outward_unit_direction (z x : ℂ) :
    ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ t : ℝ, 0 ≤ t →
      dist (x + t • e) x = t ∧ dist (x + t • e) z = dist x z + t := by
  by_cases hx : x = z
  · subst x
    refine ⟨1, norm_one, ?_⟩
    intro t ht
    constructor
    · simp [dist_eq_norm, abs_of_nonneg ht]
    · simp [dist_eq_norm, abs_of_nonneg ht]
  · let e : ℂ := ‖x - z‖⁻¹ • (x - z)
    have hne : x - z ≠ 0 := sub_ne_zero.mpr hx
    have he : ‖e‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hne
    have hrepr : ‖x - z‖ • e = x - z := by
      change (‖x - z‖ : ℝ) • ((‖x - z‖⁻¹ : ℝ) • (x - z)) = x - z
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul]
    refine ⟨e, he, ?_⟩
    intro t ht
    constructor
    · simp [dist_eq_norm, abs_of_nonneg ht, he]
    · rw [dist_eq_norm, dist_eq_norm]
      have hrew : x + t • e - z = (‖x - z‖ + t) • e := by
        rw [add_smul, hrepr]
        abel
      rw [hrew, norm_smul_of_nonneg (add_nonneg (norm_nonneg _) ht), he, mul_one]

/-- If the initial point is within `gap` of the disk boundary, an outward
segment starting farther than `gap + margin` from it stays at distance
greater than `margin` from every point of the disk. -/
theorem exists_outward_annulus_segment_avoiding_disk
    (z x : ℂ) (radius gap margin inner outer : ℝ)
    (hnear : radius - dist x z ≤ gap) (hinner : gap + margin < inner)
    (hinner0 : 0 ≤ inner) (houter : inner ≤ outer) :
    ∃ e : ℂ, ‖e‖ = 1 ∧
      x + inner • e ∈ sphere x inner ∧ x + outer • e ∈ sphere x outer ∧
      (∀ t ∈ Icc inner outer, dist (x + t • e) x = t) ∧
      (∀ t ∈ Icc inner outer, ∀ y ∈ ball z radius, margin < dist (x + t • e) y) := by
  obtain ⟨e, he, hray⟩ := exists_outward_unit_direction z x
  refine ⟨e, he, ?_, ?_, ?_, ?_⟩
  · exact mem_sphere.mpr (hray inner hinner0).1
  · exact mem_sphere.mpr (hray outer (hinner0.trans houter)).1
  · intro t ht
    exact (hray t (hinner0.trans ht.1)).1
  · intro t ht y hy
    have hd := (hray t (hinner0.trans ht.1)).2
    have htri := dist_triangle (x + t • e) y z
    have hy' : dist y z < radius := mem_ball.mp hy
    have htlo : inner ≤ t := ht.1
    linarith

end MatedCRT
