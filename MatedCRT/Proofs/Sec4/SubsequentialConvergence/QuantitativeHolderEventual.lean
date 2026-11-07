import MatedCRT.Proofs.Sec4.SubsequentialConvergence.QuantitativeHolder

/-! Hölder regularity with eventual pathwise data bounds. -/

namespace MatedCRT.Tightness

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The quantitative estimates in Lemma 3.1 give Hölder continuity of a
pointwise rescaled limit on each compact subset of the domain. -/
theorem holderOn_rescale_limit_of_eventual_exit_estimates
    {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ}
    {μ : Measure ℂ} {D K : Set ℂ} {ρ β α : ℝ} {Cm C ξ A C₁ q : ℝ≥0}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ (Cm : ℝ) * ε n)
    (hadj : ∀ n j k, m n j k ≠ 0 → (cell (ε n) η j ∩ cell (ε n) η k).Nonempty)
    (hsucc : ∀ n k, m n k (k + 1) ≠ 0) (hDo : IsOpen D) (hDρ : D ⊆ ball 0 ρ)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hdata : ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) η D, |mLaplacian (m n) (u n) a| ≤ C) ∧
      (∀ a ∈ cellVertices (ε n) η D, |u n a| ≤ (C : ℝ) / ε n))
    (hξ : 0 < ξ) (hξ2 : ξ ≤ 2) (hβ : 0 < β) (hα : 0 < α) (hq : 0 < q)
    (hH : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (ε n) η (ball x r), matedLaplacian (m n) f a = 0) →
      ∀ a ∈ interiorCellVertices (ε n) η (ball x r), ∀ b ∈ cellVertices (ε n) η (ball x r),
        |f a - f b| * infDist (vertexPoint (ε n) η a) (frontier (ball x r)) ^ (ξ : ℝ) ≤
          A * (⨆ a' : cellVertices (ε n) η (ball x r), |f a'|) *
            max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ (ξ : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (ε n) η D',
      expectedExitTime (m n) (interiorCellVertices (ε n) η D') a ≤
        ENNReal.ofReal (C₁ * (ε n)⁻¹) * largestExitTimeRV μ (thickening (ε n ^ α) D'))
    (hM : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, 0 < R → R < R₁ →
      ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV μ (ball y R) ≤ ENNReal.ofReal (R ^ (q : ℝ)))
    {f : ℂ → ℝ} (hconv : ∀ x ∈ K, Tendsto (fun n => rescale (mε n) (ε n) η (u n) x)
      atTop (𝓝 (f x))) : IsHolderContinuousOn f K := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdata
  let shift : ℕ → ℕ := fun n => n + N
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_right h N
  have hs := hshift.tendsto_atTop
  apply holderOn_rescale_limit_of_exit_estimates
    (m := fun n => m (shift n)) (ε := fun n => ε (shift n))
    (mε := fun n => mε (shift n)) (u := fun n => u (shift n))
    (μ := μ) (D := D) (ρ := ρ) (β := β) (α := α)
    (Cm := Cm) (C := C) (ξ := ξ) (A := A) (C₁ := C₁) (q := q)
    (fun n => hε _) (hε0.comp hs) hη hp hsurj (hs.eventually hm)
    (fun n => hadj _) (fun n => hsucc _) hDo hDρ hK hKD
    (fun n => (hN (shift n) (Nat.le_add_left N n)).1)
    (fun n => (hN (shift n) (Nat.le_add_left N n)).2)
    hξ hξ2 hβ hα hq (hs.eventually hH) (hs.eventually hQ) hM
  intro x hx
  exact (hconv x hx).comp hs

end MatedCRT.Tightness
