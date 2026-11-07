import MatedCRT.Proofs.Sec4.SubsequentialConvergence.RadiusLimit

/-! Separation-dependent limit estimates with eventual data bounds. -/

namespace MatedCRT.Tightness

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Eventual Laplacian and vertex bounds suffice for the two-point limit estimate. -/
theorem limit_two_power_modulus_for_pair_of_eventual_exit_estimates {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ}
    {μ : Measure ℂ} {x y : ℂ} {ρ C ξ A β α C₁ q Cm : ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hCm : 0 ≤ Cm)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hadj : ∀ n j k, m n j k ≠ 0 → (cell (ε n) η j ∩ cell (ε n) η k).Nonempty)
    (hsucc : ∀ n k, m n k (k + 1) ≠ 0) 
    (hC : 0 ≤ C) (hdata : ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) η (ball 0 ρ), |mLaplacian (m n) (u n) a| ≤ C) ∧
      (∀ a ∈ cellVertices (ε n) η (ball 0 ρ), |u n a| ≤ C / ε n))
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
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdata
  let shift : ℕ → ℕ := fun n => n + N
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_right h N
  have hs := hshift.tendsto_atTop
  apply limit_two_power_modulus_for_pair_in_ball
    (m := fun n => m (shift n)) (ε := fun n => ε (shift n))
    (mε := fun n => mε (shift n)) (u := fun n => u (shift n))
    (μ := μ) (ρ := ρ) (β := β) (α := α)
    (Cm := Cm) (C := C) (ξ := ξ) (A := A) (C₁ := C₁) (q := q)
    (fun n => hε _) (hε0.comp hs) hη hp hsurj hCm (hs.eventually hm)
    (fun n => hadj _) (fun n => hsucc _) hC
    (fun n => (hN (shift n) (Nat.le_add_left N n)).1)
    (fun n => (hN (shift n) (Nat.le_add_left N n)).2)
    hξ hA hβ hα hC₁ (hs.eventually hH) (hs.eventually hQ) hr0 hx hy hM₁
  intro z hz
  exact (hconv z hz).comp hs

end MatedCRT.Tightness
