import MatedCRT.Proofs.LBM.DirichletDiscHolder
import MatedCRT.Defs.Notation

/-! An interior Hölder estimate from a uniform small-distance estimate. -/

namespace MatedCRT

open Metric Set Filter Topology
open scoped NNReal

/-- A uniform power-law estimate at small distances and a uniform oscillation
bound imply a Hölder estimate at every distance. This is the analytic
passage needed to use the estimate in the proof of Lemma 3.1. -/
theorem holderOn_of_small_distance_and_oscillation
    {f : ℂ → ℝ} {K : Set ℂ} {C M χ δ : ℝ≥0}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hδ : 0 < δ)
    (hlocal : ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      dist (f x) (f y) ≤ C * dist x y ^ (χ : ℝ))
    (hbound : ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ M) :
    IsHolderContinuousOn f K := by
  let D : ℝ := (M : ℝ) / (δ : ℝ) ^ (χ : ℝ)
  have hδr : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hp : 0 < (δ : ℝ) ^ (χ : ℝ) := Real.rpow_pos_of_pos hδr _
  have hD : 0 ≤ D := div_nonneg (NNReal.coe_nonneg M) hp.le
  refine ⟨C + Real.toNNReal D, χ, hχ, hχ1, holderOnWith_of_dist_le ?_⟩
  intro x hx y hy
  have hdist : 0 ≤ dist x y ^ (χ : ℝ) := Real.rpow_nonneg dist_nonneg _
  have hco : ((C + Real.toNNReal D : ℝ≥0) : ℝ) = (C : ℝ) + D := by simp [hD]
  rw [hco]
  by_cases hsmall : dist x y < δ
  · have h := hlocal x hx y hy hsmall
    nlinarith [mul_nonneg hD hdist]
  · have hfar : (δ : ℝ) ≤ dist x y := le_of_not_gt hsmall
    have hp' : (δ : ℝ) ^ (χ : ℝ) ≤ dist x y ^ (χ : ℝ) :=
      Real.rpow_le_rpow hδr.le hfar (NNReal.coe_nonneg χ)
    have hmul : D * (δ : ℝ) ^ (χ : ℝ) = (M : ℝ) := by
      dsimp [D]
      exact div_mul_cancel₀ _ (ne_of_gt hp)
    have hb := hbound x hx y hy
    have hC : 0 ≤ (C : ℝ) := NNReal.coe_nonneg C
    nlinarith [mul_nonneg hC hdist, mul_nonneg hD (sub_nonneg.mpr hp')]

/-- The fixed-distance asymptotic estimates in the proof of Lemma 3.1 pass
to a pointwise subsequential limit and yield Hölder continuity. The eventual
index may depend on the two points and on the distance threshold. -/
theorem holderOn_of_eventual_small_distance_and_oscillation
    {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {K : Set ℂ} {C M χ δ : ℝ≥0}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hδ : 0 < δ)
    (hconv : ∀ x ∈ K, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hlocal : ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → ∀ᶠ n in atTop,
      dist (F n x) (F n y) ≤ C * dist x y ^ (χ : ℝ))
    (hbound : ∀ x ∈ K, ∀ y ∈ K, ∀ᶠ n in atTop,
      dist (F n x) (F n y) ≤ M) :
    IsHolderContinuousOn f K := by
  apply holderOn_of_small_distance_and_oscillation hχ hχ1 hδ
  · intro x hx y hy hxy
    exact le_of_tendsto ((hconv x hx).dist (hconv y hy)) (hlocal x hx y hy hxy)
  · intro x hx y hy
    exact le_of_tendsto ((hconv x hx).dist (hconv y hy)) (hbound x hx y hy)

end MatedCRT
