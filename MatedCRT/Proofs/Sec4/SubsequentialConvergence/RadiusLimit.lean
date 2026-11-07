import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.QuantitativeRescale
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.QuantitativeInteriorRadius

/-! Transfer the radius-dependent vertex estimate to pointwise limits. -/

namespace MatedCRT.Tightness

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- At each fixed radius, the two-power vertex estimate passes to any
pointwise limit of the rescaled functions. -/
theorem limit_two_power_modulus_of_vertex_modulus
    {K : Set ℂ} {η : ℝ → ℂ} {ε mε : ℕ → ℝ} {u : ℕ → ℤ → ℝ}
    {f : ℂ → ℝ} {Cm R₀ A C C₁ ξ q : ℝ} (hK : Bornology.IsBounded K)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 ≤ Cm)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hV : ∀ R : ℝ, 0 < R → R < R₀ → ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) η K, ∀ b ∈ cellVertices (ε n) η K,
        ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ≤ (R / 2) * (R / 2) →
        ε n * |u n a - u n b| ≤ A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q)
    (hconv : ∀ x ∈ K, Tendsto (fun n => rescale (mε n) (ε n) η (u n) x)
      atTop (𝓝 (f x))) :
    ∀ R : ℝ, 0 < R → R < R₀ → ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
      |f x - f y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by
  intro R hR hRlt x hx y hy hxy
  have hlim := ((hconv x hx).sub (hconv y hy)).abs
  apply le_of_tendsto hlim
  filter_upwards [rescale_two_power_modulus hK hη hp hsurj hε hε0 hCm hm hV R hR hRlt] with n hn
  exact hn x hx y hy hxy

/-- The exit-potential estimates yield a limit modulus whose scale is
explicitly controlled by the compact set’s separation from the boundary. -/
theorem limit_two_power_modulus_of_exit_estimates {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ}
    {μ : Measure ℂ} {D K : Set ℂ} {ρ C ξ A β α C₁ q Cm : ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hCm : 0 ≤ Cm)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hadj : ∀ n j k, m n j k ≠ 0 → (cell (ε n) η j ∩ cell (ε n) η k).Nonempty)
    (hsucc : ∀ n k, m n k (k + 1) ≠ 0) (hDo : IsOpen D) (hDρ : D ⊆ ball 0 ρ) (hK : IsCompact K)
    (hC : 0 ≤ C) (hlap : ∀ n, ∀ a ∈ interiorCellVertices (ε n) η D, |mLaplacian (m n) (u n) a| ≤ C)
    (hbd : ∀ n, ∀ a ∈ cellVertices (ε n) η D, |u n a| ≤ C / ε n)
    (hξ : 0 < ξ) (hA : 0 ≤ A) (hβ : 0 < β) (hα : 0 < α) (hC₁ : 0 ≤ C₁)
    (hH : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (ε n) η (ball x r), matedLaplacian (m n) f a = 0) →
      ∀ a ∈ interiorCellVertices (ε n) η (ball x r), ∀ b ∈ cellVertices (ε n) η (ball x r),
        |f a - f b| * infDist (vertexPoint (ε n) η a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices (ε n) η (ball x r), |f a'|) *
            max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ)
    (hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (ε n) η D',
      expectedExitTime (m n) (interiorCellVertices (ε n) η D') a ≤
        ENNReal.ofReal (C₁ * (ε n)⁻¹) * largestExitTimeRV μ (thickening (ε n ^ α) D'))
    {r0 R₁ : ℝ} (hr0D : cthickening r0 K ⊆ D)
    (hM₁ : ∀ R : ℝ, 0 < R → R < R₁ →
      ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV μ (ball y R) ≤ ENNReal.ofReal (R ^ q))
    {f : ℂ → ℝ} (hconv : ∀ x ∈ K, Tendsto
      (fun n => rescale (mε n) (ε n) η (u n) x) atTop (𝓝 (f x))) :
    ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) → ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
      |f x - f y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by
  apply limit_two_power_modulus_of_vertex_modulus hK.isBounded hη hp hsurj hε hε0 hCm hm
    (interior_vertex_two_power_estimate_at_radius hε hε0 hη hp hadj hsucc hDo hDρ hK
      hC hlap hbd hξ hA hβ hα hC₁ hH hQ hr0D hM₁) hconv

/-- A pair of points whose distances to the ball boundary exceed `r` has
its closed `r`-neighborhood inside the ball. -/
theorem cthickening_pair_subset_ball {x y : ℂ} {r ρ : ℝ} (hr : 0 ≤ r)
    (hx : dist x 0 + r < ρ) (hy : dist y 0 + r < ρ) :
    cthickening r ({x, y} : Set ℂ) ⊆ ball 0 ρ := by
  rw [show ({x, y} : Set ℂ) = {x} ∪ {y} by ext z; simp [or_comm],
    cthickening_union, cthickening_singleton x hr, cthickening_singleton y hr]
  rintro z (hz | hz)
  · rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith [dist_triangle z x 0]
  · rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith [dist_triangle z y 0]

/-- A separation-dependent limit estimate for a pair of points in a ball. -/
theorem limit_two_power_modulus_for_pair_in_ball {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ}
    {μ : Measure ℂ} {x y : ℂ} {ρ C ξ A β α C₁ q Cm : ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hCm : 0 ≤ Cm)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hadj : ∀ n j k, m n j k ≠ 0 → (cell (ε n) η j ∩ cell (ε n) η k).Nonempty)
    (hsucc : ∀ n k, m n k (k + 1) ≠ 0) 
    (hC : 0 ≤ C) (hlap : ∀ n, ∀ a ∈ interiorCellVertices (ε n) η (ball 0 ρ), |mLaplacian (m n) (u n) a| ≤ C)
    (hbd : ∀ n, ∀ a ∈ cellVertices (ε n) η (ball 0 ρ), |u n a| ≤ C / ε n)
    (hξ : 0 < ξ) (hA : 0 ≤ A) (hβ : 0 < β) (hα : 0 < α) (hC₁ : 0 ≤ C₁)
    (hH : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (ε n) η (ball x r), matedLaplacian (m n) f a = 0) →
      ∀ a ∈ interiorCellVertices (ε n) η (ball x r), ∀ b ∈ cellVertices (ε n) η (ball x r),
        |f a - f b| * infDist (vertexPoint (ε n) η a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices (ε n) η (ball x r), |f a'|) *
            max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ)
    (hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (ε n) η D',
      expectedExitTime (m n) (interiorCellVertices (ε n) η D') a ≤
        ENNReal.ofReal (C₁ * (ε n)⁻¹) * largestExitTimeRV μ (thickening (ε n ^ α) D'))
    {r0 R₁ : ℝ} (hr0 : 0 ≤ r0)
    (hx : dist x 0 + r0 < ρ) (hy : dist y 0 + r0 < ρ)
    (hM₁ : ∀ R : ℝ, 0 < R → R < R₁ →
      ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV μ (ball y R) ≤ ENNReal.ofReal (R ^ q))
    {f : ℂ → ℝ} (hconv : ∀ z ∈ ball (0 : ℂ) ρ, Tendsto
      (fun n => rescale (mε n) (ε n) η (u n) z) atTop (𝓝 (f z))) :
    ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) →
      ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
      |f x - f y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by
  have hpair : ({x, y} : Set ℂ) ⊆ ball 0 ρ := by
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> rw [mem_ball] <;> linarith
  intro R hR hRlt hxy
  apply limit_two_power_modulus_of_exit_estimates hε hε0 hη hp hsurj hCm hm
    hadj hsucc isOpen_ball Subset.rfl (isCompact_singleton.insert x)
    hC hlap hbd hξ hA hβ hα hC₁ hH hQ
    (cthickening_pair_subset_ball hr0 hx hy) hM₁
    (fun z hz => hconv z (hpair hz)) R hR hRlt x (by simp) y (by simp) hxy

end MatedCRT.Tightness
