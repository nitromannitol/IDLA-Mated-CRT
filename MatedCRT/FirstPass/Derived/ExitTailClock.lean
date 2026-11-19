import MatedCRT.FirstPass.Derived.ExitTailAllRadii
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow

/-!
# From the exit step of the embedded walk to the exit time of the interpolated walk

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Section 6.4 and eq. (1.8): the clock `t ↦ m_ε t` of the interpolated walk.

If `ε m_ε ≥ c₀` and `N ≥ K / c₀`, then `N m_ε ≥ K ε⁻¹`: a walk whose interpolation stays in `B_r` for the times
`t ≤ N` has not exited `B_r` by step `K ε⁻¹`.  Hence the exit tail `exitTail_allRadii` (at step `K ε⁻¹`)
bounds the quenched probability that the interpolated walk of `S` stays in `B_r` up to the time `N`:
outside an event of probability at most `2 θ`, it is at most `θ`, uniformly in the starting vertex of
`B_r`.

* `exitTail_clock`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter HarmonicBalls
open scoped ENNReal Topology NNReal

namespace MatedCRT
namespace ExitTailClock

/-- If a path stays in `A` up to step `m` then its exit time from `A` is larger than `m`. -/
theorem coe_lt_vExitTime_of_forall_mem {A : Set ℤ} {x : ℕ → ℤ} {m : ℕ} (h : ∀ n ≤ m, x n ∈ A) :
    (m : ℕ∞) < vExitTime A x := by
  classical
  unfold vExitTime
  split_ifs with hex
  · exact_mod_cast (Nat.lt_find_iff hex m).2 fun n hn => not_not.2 (h n hn)
  · exact ENat.natCast_lt_top m

/-- A path whose interpolation stays in `B_r` up to time `N` has not exited `B_r` by step `K ε⁻¹` when
`K ε⁻¹ ≤ N m_ε`. -/
theorem lt_embeddedExitTime_of_stay {ε mε K : ℝ} {N : ℕ} {r : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hm : 0 < mε) (hKN : K * ε⁻¹ ≤ N * mε) (η : ℝ → ℂ) (x : ℕ → ℤ)
    (hx : ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) → interpolatedWalk ε η mε x t ∈ ball (0 : ℂ) r) :
    ENNReal.ofReal (K * ε⁻¹) < (embeddedExitTime ε η (ball 0 r) x : ℝ≥0∞) := by
  have hKε : 0 ≤ K * ε⁻¹ := mul_nonneg hK (inv_nonneg.2 hε.le)
  set m : ℕ := ⌊K * ε⁻¹⌋₊ with hmdef
  have hmem : ∀ n ≤ m, x n ∈ {k : ℤ | vertexPoint ε η k ∈ ball (0 : ℂ) r} := by
    intro n hn
    have hn1 : (n : ℝ) ≤ K * ε⁻¹ := (Nat.cast_le.2 hn).trans (Nat.floor_le hKε)
    have hn2 : (n : ℝ) ≤ N * mε := hn1.trans hKN
    have ht : ((n : ℝ) / mε).toNNReal ≤ (N : ℝ≥0) := by
      rw [Real.toNNReal_le_iff_le_coe, div_le_iff₀ hm]
      simpa using hn2
    have := hx _ ht
    rwa [interpolatedWalk_natCast_div hm η x n] at this
  have hlt : (m : ℕ∞) < embeddedExitTime ε η (ball 0 r) x :=
    coe_lt_vExitTime_of_forall_mem hmem
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ embeddedExitTime ε η (ball 0 r) x := by
    rw [Nat.cast_succ]
    exact Order.add_one_le_of_lt hlt
  have h2 : (((m + 1 : ℕ) : ℕ∞) : ℝ≥0∞) ≤ (embeddedExitTime ε η (ball 0 r) x : ℝ≥0∞) :=
    ENat.toENNReal_le.2 h1
  rw [ENat.toENNReal_coe] at h2
  refine lt_of_lt_of_le ?_ h2
  rw [← ENNReal.ofReal_natCast]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by exact_mod_cast Nat.lt_floor_add_one _)

end ExitTailClock

/-- **Exit tail of the interpolated walk from `B_r`, uniform in the start** (Berestycki-Gwynne, Section 6.4 and
(1.8)).  If `ε m_ε ≥ c₀` for small `ε` (`hc0`), then for every `r > 0` and `θ > 0` there are `N ∈ ℕ` and
`ε₂ > 0` such that for `ε < ε₂`, with probability at least `1 - 2 θ`, from every vertex `k` with `η(ε k) ∈ B_r`
the interpolated walk stays in `B_r` for all times `t ≤ N` with quenched probability at most `θ`. -/
theorem exitTail_clock {𝒮 : SpaceFillingSLEModel} (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {θ : ℝ} (hθ : 0 < θ) {r : ℝ} (hr : 0 < r) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ)
    (hc0 : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε) :
    ∃ N : ℕ, ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₂ →
      S.P {ω | ∃ k : ℤ, vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) r ∧
        ENNReal.ofReal θ < srwLaw (S.mult ε ω) k
          {x | ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) →
            interpolatedWalk ε (S.η ω) (S.mε ε) x t ∈ ball (0 : ℂ) r}}
        ≤ ENNReal.ofReal (2 * θ) := by
  obtain ⟨c₀, hc₀, ε₁, hε₁, hcε⟩ := hc0
  obtain ⟨K, hK, ε₀, hε₀, hmain⟩ := exitTail_allRadii hEnvS h214 h217 hγ hγ2 hθ hr Ω S hS
  refine ⟨⌈K / c₀⌉₊, min ε₀ ε₁, lt_min hε₀ hε₁, fun ε hε hεlt => ?_⟩
  have hc := hcε ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
  have hm : 0 < S.mε ε := by
    by_contra hneg
    have : ε * S.mε ε ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (not_lt.1 hneg)
    linarith
  have hKN : K * ε⁻¹ ≤ (⌈K / c₀⌉₊ : ℝ) * S.mε ε := by
    have h1 : ε⁻¹ ≤ S.mε ε / c₀ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hε hc₀]
      linarith
    calc K * ε⁻¹ ≤ K * (S.mε ε / c₀) := mul_le_mul_of_nonneg_left h1 hK.le
      _ = K / c₀ * S.mε ε := by ring
      _ ≤ (⌈K / c₀⌉₊ : ℝ) * S.mε ε :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) hm.le
  refine le_trans (measure_mono ?_) (hmain ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)))
  rintro ω ⟨k, hk1, hk2⟩
  refine ⟨k, hk1, lt_of_lt_of_le hk2 (measure_mono fun x hx => ?_)⟩
  exact ExitTailClock.lt_embeddedExitTime_of_stay hε hK.le hm hKN (S.η ω) x hx

end MatedCRT
