import MatedCRT.FirstPass.Derived.ExitTimeLogIntegral
import MatedCRT.FirstPass.Derived.ExitTimeMomentKhasminskii

/-!
# Moments of exit times against the logarithmic integral (BG20 (5.1), deterministic part)

Berestycki-Gwynne (arXiv:2003.10320), proof of Proposition 5.1. On the events of the Green kernel upper
bound (Lemma 5.4), the near-vertex count (5.41), the crude Green function bound (Lemma 5.6) and the upper
half of the cell-sum comparison (A.21) for `D`, every interior vertex `y` of `D` satisfies (5.45); the
comparison of `ExitTimeLogIntegral` bounds it by `c ε⁻¹ sup_{z ∈ D} ∫_{B_{ε^α}(D)} (log(1/|z-w|) + 1) dμ`,
and the Khasminskii bound (Lemma 5.9) turns this first-moment bound into the `N`-th moment bound (5.1):
`E^a[τ^N] ≤ N! c^N ε^{-N} (sup_{z ∈ D} ∫ ...)^N` with `c = 2 (1 - log 2)⁻¹ + 6 C`.
-/

open HarmonicBalls

namespace MatedCRT

open Set Metric MeasureTheory Filter LatticeProb.TruncatedLog
open scoped ENNReal

namespace ExitTimeMomentLogIntegral

/-- The constant `2 (1 - log 2)⁻¹ + 6 C` is nonnegative for `C ≥ 0`. -/
theorem logIntegralConst_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ 2 * (1 - Real.log 2)⁻¹ + 6 * C := by
  have hlog2 : 0 < 1 - Real.log 2 := by have := Real.log_two_lt_d9; linarith
  exact add_nonneg (mul_nonneg zero_le_two (inv_nonneg.2 hlog2.le)) (mul_nonneg (by norm_num) hC)

/-- **BG20 (5.1), deterministic form.** On the events of Lemma 5.4, (5.41) (for every interior vertex),
Lemma 5.6 and the upper half of (A.21) for `D ⊆ B_ρ`, `ρ ≤ 1`, with `α ≤ α₁`, `K M ≤ ε^{-1+α}`,
`μ(D) ≥ ε^α` and no atoms of `μ`, the `N`-th moment of the exit time from the interior vertices of `D`
is at most `N! c^N ε^{-N} (sup_{z ∈ D} ∫_{B_{ε^α}(D)} (log(1/|z-w|) + 1) dμ(w))^N`, from every vertex `a`. -/
theorem exitTimeMoment_le_logIntegral {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε β C ρ K M α α₁ b : ℝ} {η : ℝ → ℂ} {μ : Measure ℂ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {D : Set ℂ} (hDρ : D ⊆ ball 0 ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C) (h1 : 1 ≤ ε ^ (-β))
    (hbd : C * (Real.log (ε ^ (-β)) + 1) ≤ ε ^ (-b)) (hlip : C * ε ^ (-β) ≤ ε ^ (-b))
    (hev : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      ε ^ β ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ →
      greenKernel m (interiorCellVertices ε η (ball 0 ρ)) a b ≤
        C * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) + C)
    (hY : ∀ y ∈ interiorCellVertices ε η D, ∀ s : Finset ℤ,
      (s : Set ℤ) ⊆ cellVertices ε η (ball (vertexPoint ε η y) (ε ^ β)) → (s.card : ℝ) ≤ K)
    (hM0 : 0 ≤ M)
    (hM : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      greenFn m (interiorCellVertices ε η (ball 0 ρ)) a b ≤ M)
    (hdeg : ∀ b ∈ interiorCellVertices ε η D, 0 < mdeg m b)
    (hA5 : ∀ g : ℂ → ℝ, (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) →
      (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
      ∀ w : ℤ → ℂ, (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ D) →
      ∑' k : cellVertices ε η D, (matedDeg m k : ℝ) * g (w k) ≤
        6 * ε⁻¹ * ∫ x in thickening (ε ^ α₁) D, g x ∂μ + ε ^ (-1 + α₁))
    (hαα₁ : α ≤ α₁) (hKM : K * M ≤ ε ^ (-1 + α)) (hatom : ∀ z : ℂ, μ {z} = 0)
    (hμD : ENNReal.ofReal (ε ^ α) ≤ μ D) (N : ℕ) (a : ℤ) :
    exitTimeMoment m (interiorCellVertices ε η D) a N ≤
      ENNReal.ofReal (N.factorial * (2 * (1 - Real.log 2)⁻¹ + 6 * C) ^ N * ε ^ (-(N : ℝ))) *
        (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
          ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) ^ N := by
  set c := 2 * (1 - Real.log 2)⁻¹ + 6 * C
  have hc : 0 ≤ c := logIntegralConst_nonneg hC
  have hbound : ∀ y ∈ interiorCellVertices ε η D,
      expectedExitTime m (interiorCellVertices ε η D) y ≤ ENNReal.ofReal (c * ε⁻¹) *
        ⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
          ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ := fun y hy => by
    have hz := InteriorCellGeometry.vertexPoint_mem_of_mem_interiorCellVertices hε.le hη hy
    refine (ExitTimeIntegralBound.expectedExitTime_le_integral_truncLogKernel hlf hcons hε hη hp hDρ
      hC h1 hbd hlip hev hy (hY y hy) hM0 hM hdeg hA5).trans ?_
    refine (ExitTimeLogIntegral.ofReal_exitBound_le_logIntegral hC hε hε1 hαα₁ hKM
      (hDρ.trans (ball_subset_ball hρ1)) hz (hatom _) hμD).trans ?_
    gcongr
    exact le_iSup₂ (f := fun z (_ : z ∈ D) => ∫⁻ w in thickening (ε ^ α) D,
      ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) _ hz
  refine (exitTimeMoment_le_factorial_mul_pow m _ hbound N a).trans (le_of_eq ?_)
  rw [mul_pow, ← mul_assoc, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [mul_pow, Real.rpow_neg hε.le, Real.rpow_natCast, inv_pow]
  ring

end ExitTimeMomentLogIntegral

end MatedCRT
