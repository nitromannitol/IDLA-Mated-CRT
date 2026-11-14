import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import MatedCRT.Defs.RandomWalk

/-!
# A sticky time window of the interpolated walk contains a window of steps

Let `v : ℤ → ℂ` label the vertices and let `f = interpPathCM v hm x` be the walk `x` run at speed `m > 0` and
linearly interpolated.  Suppose that for some `s` the path `f` stays in `B(0, ρ)` up to time `s + a` and moves
less than `δ` away from `f s` during `[s, s + a]` (a *sticky window*, the sets `stickyOpen` of the library).
If `2 b ≤ m a`, then the first integer step `j = ⌈m s⌉` has the following two properties:

* the walk `x` has not left a set `A` before step `j + b`, whenever `A` contains every vertex labelled in
  `B(0, ρ)`;
* all labels `v (x i)`, `j ≤ i < j + 2 b`, lie within `2 δ` of each other.

This is the negation of the event of Proposition 6.14 of Berestycki-Gwynne at threshold `2 δ`, which is how the
event-level absence of sticking (`MatedCRT.NoStickingEvent.limLimSmall_noSticking`, windows counted in steps)
yields the absence of sticking of the time-scaled limit (Proposition 6.1, last claim).
-/

set_option autoImplicit false

open Metric
open scoped NNReal

namespace MatedCRT
namespace StickyWindowWalk

/-- The interpolated path takes the value `v (x n)` at the time `n / m`. -/
theorem interpPathCM_natCast_div (v : ℤ → ℂ) {m : ℝ} (hm : 0 < m) (x : ℕ → ℤ) (n : ℕ) :
    interpPathCM v hm.le x (Real.toNNReal ((n : ℝ) / m)) = v (x n) := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
  have h1 : m * ((n : ℝ) / m) = n := by field_simp
  simp only [interpPathCM_apply, interpPathFn, Real.coe_toNNReal _ h0, h1]
  simp [linInterp]

/-- **A sticky time window contains a window of steps.**  See the module docstring. -/
theorem exists_stepWindow (v : ℤ → ℂ) {m : ℝ} (hm : 0 < m) (x : ℕ → ℤ) {ρ δ : ℝ} {a s : ℝ≥0} {b : ℕ}
    (hb : 2 * (b : ℝ) ≤ m * a) (A : Set ℤ) (hA : ∀ w : ℤ, v w ∈ ball (0 : ℂ) ρ → w ∈ A)
    (hin : ∀ u : ℝ≥0, u ≤ s + a → interpPathCM v hm.le x u ∈ ball (0 : ℂ) ρ)
    (hstill : ∀ u : ℝ≥0, s ≤ u → u ≤ s + a →
      dist (interpPathCM v hm.le x u) (interpPathCM v hm.le x s) < δ) :
    ∃ j : ℕ, ((j + b : ℕ) : ℕ∞) ≤ vExitTime A x ∧
      ∀ i₁ i₂ : ℕ, j ≤ i₁ → i₁ ≤ i₂ → i₂ < j + 2 * b → ‖v (x i₂) - v (x i₁)‖ < 2 * δ := by
  have hms : (0 : ℝ) ≤ m * s := mul_nonneg hm.le s.2
  have hj1 : m * (s : ℝ) ≤ (⌈m * (s : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hj2 : ((⌈m * (s : ℝ)⌉₊ : ℕ) : ℝ) < m * (s : ℝ) + 1 := Nat.ceil_lt_add_one hms
  set j : ℕ := ⌈m * (s : ℝ)⌉₊ with hj
  -- every step `n` in `[j, j + 2 b)` is the lattice time of a time in `[s, s + a]`
  have key : ∀ n : ℕ, j ≤ n → n < j + 2 * b →
      v (x n) ∈ ball (0 : ℂ) ρ ∧ dist (v (x n)) (interpPathCM v hm.le x s) < δ := by
    intro n hjn hn
    have hn1 : (n : ℝ) + 1 ≤ (j : ℝ) + 2 * b := by exact_mod_cast hn
    have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
    have hnle : (n : ℝ) ≤ m * ((s : ℝ) + a) := by
      have : (n : ℝ) ≤ m * (s : ℝ) + m * a := by linarith
      linarith [mul_add m (s : ℝ) (a : ℝ)]
    have hs_le : s ≤ Real.toNNReal ((n : ℝ) / m) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity), le_div_iff₀ hm]
      linarith [mul_comm m (s : ℝ)]
    have hu_le : Real.toNNReal ((n : ℝ) / m) ≤ s + a := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity), NNReal.coe_add, div_le_iff₀ hm]
      linarith [mul_comm m ((s : ℝ) + a)]
    refine ⟨?_, ?_⟩
    · have := hin _ hu_le
      rwa [interpPathCM_natCast_div v hm x n] at this
    · have := hstill _ hs_le hu_le
      rwa [interpPathCM_natCast_div v hm x n] at this
  refine ⟨j, ?_, ?_⟩
  · classical
    unfold vExitTime
    split_ifs with h
    · have hle : j + b ≤ Nat.find h := by
        by_contra hlt
        have hlt' : Nat.find h < j + b := not_le.1 hlt
        have hnb : Nat.find h < j + 2 * b := by omega
        -- the first exit time is `≥ j`: otherwise it is before the window, where nothing is known
        by_cases hjl : j ≤ Nat.find h
        · exact (Nat.find_spec h) (hA _ (key _ hjl hnb).1)
        · -- before the window use the sticky window's start: times `n < j` lie before `s + a`
          have hnj : Nat.find h < j := not_le.1 hjl
          have hn1 : ((Nat.find h : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hnj
          have hnle : ((Nat.find h : ℕ) : ℝ) ≤ m * ((s : ℝ) + a) := by
            have : ((Nat.find h : ℕ) : ℝ) ≤ m * (s : ℝ) + m * a := by
              have := mul_nonneg hm.le a.2
              linarith
            linarith [mul_add m (s : ℝ) (a : ℝ)]
          have hu_le : Real.toNNReal (((Nat.find h : ℕ) : ℝ) / m) ≤ s + a := by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity), NNReal.coe_add,
              div_le_iff₀ hm]
            linarith [mul_comm m ((s : ℝ) + a)]
          have := hin _ hu_le
          rw [interpPathCM_natCast_div v hm x _] at this
          exact (Nat.find_spec h) (hA _ this)
      exact_mod_cast hle
    · exact le_top
  · intro i₁ i₂ h1 h12 h2
    have a1 := key i₁ h1 (by omega)
    have a2 := key i₂ (h1.trans h12) h2
    rw [dist_eq_norm] at a1 a2
    calc ‖v (x i₂) - v (x i₁)‖
        = ‖(v (x i₂) - interpPathCM v hm.le x s) - (v (x i₁) - interpPathCM v hm.le x s)‖ := by
          congr 1; ring
      _ ≤ ‖v (x i₂) - interpPathCM v hm.le x s‖ + ‖v (x i₁) - interpPathCM v hm.le x s‖ := norm_sub_le _ _
      _ < δ + δ := add_lt_add a2.2 a1.2
      _ = 2 * δ := by ring

end StickyWindowWalk
end MatedCRT
