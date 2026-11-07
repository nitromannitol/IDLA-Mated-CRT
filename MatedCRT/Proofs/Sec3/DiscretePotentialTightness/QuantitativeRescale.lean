import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Convergence
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.QuantitativeInterior

/-! Transfer quantitative vertex estimates to the rescaled functions. -/

namespace MatedCRT.Tightness

open Filter Topology Set Metric

/-- A fixed-scale vertex modulus transfers uniformly to rescaled functions
on a bounded set. The cell diameter is taken small after fixing the scale. -/
theorem rescale_modulus_of_vertex_modulus
    {K : Set ℂ} {η : ℝ → ℂ} {ε mε : ℕ → ℝ} {u : ℕ → ℤ → ℝ}
    {Cm δ B : ℝ} (hK : Bornology.IsBounded K)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 ≤ Cm) (hδ : 0 < δ)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hV : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (ε n) η K,
      ∀ b ∈ cellVertices (ε n) η K,
      ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ≤ δ →
        ε n * |u n a - u n b| ≤ B) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ / 2 →
      |rescale (mε n) (ε n) η (u n) x - rescale (mε n) (ε n) η (u n) y| ≤ Cm * B := by
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hη hp hK (s := δ / 4) (by positivity)
  filter_upwards [hV, hm, hε0.eventually (gt_mem_nhds hε₀)] with n hn hmn hεn x hx y hy hxy
  have hxa : x ∈ cell (ε n) η (vertexOf (ε n) η x) := mem_cell_vertexOf hη hp hsurj (hε n) x
  have hyb : y ∈ cell (ε n) η (vertexOf (ε n) η y) := mem_cell_vertexOf hη hp hsurj (hε n) y
  have haK : vertexOf (ε n) η x ∈ cellVertices (ε n) η K := ⟨x, hxa, hx⟩
  have hbK : vertexOf (ε n) η y ∈ cellVertices (ε n) η K := ⟨y, hyb, hy⟩
  have h1 : ‖vertexPoint (ε n) η (vertexOf (ε n) η x) - x‖ < δ / 4 := by
    rw [norm_sub_rev]; exact hcell (ε n) (hε n) hεn _ haK x hxa
  have h2 : ‖y - vertexPoint (ε n) η (vertexOf (ε n) η y)‖ < δ / 4 :=
    hcell (ε n) (hε n) hεn _ hbK y hyb
  have hab : ‖vertexPoint (ε n) η (vertexOf (ε n) η x) - vertexPoint (ε n) η (vertexOf (ε n) η y)‖ ≤ δ := by
    calc _ = ‖(vertexPoint (ε n) η (vertexOf (ε n) η x) - x) + (x - y) +
          (y - vertexPoint (ε n) η (vertexOf (ε n) η y))‖ := by congr 1; ring
      _ ≤ ‖vertexPoint (ε n) η (vertexOf (ε n) η x) - x‖ + ‖x - y‖ +
          ‖y - vertexPoint (ε n) η (vertexOf (ε n) η y)‖ := norm_add₃_le
      _ ≤ δ := by linarith
  have hv := hn _ haK _ hbK hab
  change |(mε n)⁻¹ * u n (vertexOf (ε n) η x) -
    (mε n)⁻¹ * u n (vertexOf (ε n) η y)| ≤ Cm * B
  rw [← mul_sub, abs_mul, abs_of_nonneg hmn.1]
  calc (mε n)⁻¹ * |u n (vertexOf (ε n) η x) - u n (vertexOf (ε n) η y)|
      ≤ (Cm * ε n) * |u n (vertexOf (ε n) η x) - u n (vertexOf (ε n) η y)| :=
        mul_le_mul_of_nonneg_right hmn.2 (abs_nonneg _)
    _ = Cm * (ε n * |u n (vertexOf (ε n) η x) - u n (vertexOf (ε n) η y)|) := by ring
    _ ≤ Cm * B := mul_le_mul_of_nonneg_left hv hCm

/-- The two-power vertex estimate transfers at every fixed small radius,
with a single eventual index for all pairs in the bounded set. -/
theorem rescale_two_power_modulus
    {K : Set ℂ} {η : ℝ → ℂ} {ε mε : ℕ → ℝ} {u : ℕ → ℤ → ℝ}
    {Cm R₀ A C C₁ ξ q : ℝ} (hK : Bornology.IsBounded K)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 ≤ Cm)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hV : ∀ R : ℝ, 0 < R → R < R₀ → ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) η K, ∀ b ∈ cellVertices (ε n) η K,
        ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ≤ (R / 2) * (R / 2) →
        ε n * |u n a - u n b| ≤ A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) :
    ∀ R : ℝ, 0 < R → R < R₀ → ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
      |rescale (mε n) (ε n) η (u n) x - rescale (mε n) (ε n) η (u n) y| ≤
        Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by
  intro R hR hRlt
  exact rescale_modulus_of_vertex_modulus hK hη hp hsurj hε hε0 hCm
    (mul_pos (half_pos hR) (half_pos hR)) hm (hV R hR hRlt)

end MatedCRT.Tightness
