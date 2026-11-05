import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability

/-! # The interpolated walk is a continuous path -/

namespace MatedCRT

open Set Filter Topology
open scoped NNReal

/-- The linear interpolation `s ↦ (1 - θ) a_⌊s⌋ + θ a_{⌊s⌋+1}`, `θ = s - ⌊s⌋`, of a sequence. -/
noncomputable def seqInterpolation (a : ℕ → ℂ) (s : ℝ) : ℂ :=
  ((1 - (s - ⌊s⌋₊) : ℝ) : ℂ) * a ⌊s⌋₊ + ((s - ⌊s⌋₊ : ℝ) : ℂ) * a (⌊s⌋₊ + 1)

/-- The affine piece through `a n` and `a (n + 1)`. -/
noncomputable def seqPiece (a : ℕ → ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ((1 - (s - n) : ℝ) : ℂ) * a n + ((s - n : ℝ) : ℂ) * a (n + 1)

theorem continuous_seqPiece (a : ℕ → ℂ) (n : ℕ) : Continuous (seqPiece a n) := by
  unfold seqPiece
  fun_prop

theorem seqInterpolation_eq_of_floor (a : ℕ → ℂ) {s : ℝ} {n : ℕ} (h : ⌊s⌋₊ = n) :
    seqInterpolation a s = seqPiece a n s := by
  unfold seqInterpolation seqPiece
  rw [h]

theorem seqInterpolation_natCast (a : ℕ → ℂ) (n : ℕ) :
    seqInterpolation a (n + 1 : ℕ) = seqPiece a n (n + 1 : ℕ) := by
  unfold seqInterpolation seqPiece
  rw [Nat.floor_natCast]
  push_cast
  simp

theorem eventuallyEq_seqInterpolation_right (a : ℕ → ℂ) (s₀ : ℝ) :
    seqInterpolation a =ᶠ[𝓝[≥] s₀] seqPiece a ⌊s₀⌋₊ := by
  have hlt : s₀ < (⌊s₀⌋₊ : ℝ) + 1 := by
    rcases le_or_gt 0 s₀ with h | h
    · exact Nat.lt_floor_add_one s₀
    · rw [Nat.floor_of_nonpos h.le]; simp; linarith
  filter_upwards [Ico_mem_nhdsGE hlt] with s hs
  apply seqInterpolation_eq_of_floor
  rcases le_or_gt 0 s with h0 | h0
  · rw [Nat.floor_eq_iff h0]
    refine ⟨?_, hs.2⟩
    rcases le_or_gt 0 s₀ with h | h
    · exact (Nat.floor_le h).trans hs.1
    · rw [Nat.floor_of_nonpos h.le]; simpa using h0
  · rw [Nat.floor_of_nonpos h0.le, Nat.floor_of_nonpos (hs.1.trans h0.le)]

theorem eventuallyEq_seqInterpolation_left (a : ℕ → ℂ) (s₀ : ℝ) :
    seqInterpolation a =ᶠ[𝓝[≤] s₀] seqPiece a (⌈s₀⌉₊ - 1) := by
  rcases Nat.eq_zero_or_pos ⌈s₀⌉₊ with hc | hc
  · -- `s₀ ≤ 0`
    have hs₀ : s₀ ≤ 0 := Nat.ceil_eq_zero.1 hc
    rw [hc]
    filter_upwards [self_mem_nhdsWithin] with s hs
    apply seqInterpolation_eq_of_floor
    exact Nat.floor_of_nonpos ((show s ≤ s₀ from hs).trans hs₀)
  · set n := ⌈s₀⌉₊ with hn
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hs₀pos : 0 ≤ s₀ := by
      by_contra h
      have h' := Nat.ceil_eq_zero.2 (not_le.mp h).le
      rw [← hn] at h'
      omega
    have hlow : (n : ℝ) - 1 < s₀ := by
      have := Nat.ceil_lt_add_one hs₀pos
      linarith
    have hup : s₀ ≤ n := Nat.le_ceil s₀
    filter_upwards [Ioc_mem_nhdsLE hlow] with s hs
    have hs0 : 0 ≤ s := by
      have : (0 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hc
        linarith
      linarith [hs.1]
    rcases lt_or_eq_of_le (hs.2.trans hup) with hlt | heq
    · apply seqInterpolation_eq_of_floor
      rw [Nat.floor_eq_iff hs0, hn1]
      exact ⟨hs.1.le, by linarith⟩
    · have hn' : n = (n - 1) + 1 := by omega
      rw [heq]
      have h := seqInterpolation_natCast a (n - 1)
      rwa [← hn'] at h

theorem continuous_seqInterpolation (a : ℕ → ℂ) : Continuous (seqInterpolation a) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · have h := (eventuallyEq_seqInterpolation_left a s₀)
    have hval : seqInterpolation a s₀ = seqPiece a (⌈s₀⌉₊ - 1) s₀ :=
      h.eq_of_nhdsWithin (mem_Iic.2 le_rfl)
    exact ((continuous_seqPiece a _).continuousAt.continuousWithinAt).congr_of_eventuallyEq h hval
  · have h := (eventuallyEq_seqInterpolation_right a s₀)
    have hval : seqInterpolation a s₀ = seqPiece a ⌊s₀⌋₊ s₀ :=
      h.eq_of_nhdsWithin (mem_Ici.2 le_rfl)
    exact ((continuous_seqPiece a _).continuousAt.continuousWithinAt).congr_of_eventuallyEq h hval

/-- **The interpolated walk is continuous.** -/
theorem continuous_interpolatedWalk (ε mε : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ) :
    Continuous (interpolatedWalk ε η mε x) := by
  have h : interpolatedWalk ε η mε x =
      fun t : ℝ≥0 => seqInterpolation (fun n => vertexPoint ε η (x n)) (mε * t) := by
    funext t
    rfl
  rw [h]
  exact (continuous_seqInterpolation _).comp (continuous_const.mul NNReal.continuous_coe)

end MatedCRT
