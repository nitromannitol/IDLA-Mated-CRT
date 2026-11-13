import MatedCRT.FirstPass.Derived.ExitCouplingEvents

/-!
# Oscillation of the interpolated walk from the absence of short travel

Deterministic bridge between the integer-time form of "no short travel" (Berestycki–Gwynne (2020),
Proposition 6.5: no two vertices visited in fewer than `g` steps before the exit time are at embedded
distance more than `D`) and the oscillation event of `walkGood` for the linearly interpolated walk of
speed `m` (Proposition 6.12, Step 2): the interpolated walk has oscillation at most `D` over windows of
length at most `ρ` when `m ρ + 2 ≤ g`.  The probabilistic form bounds the complement of `walkGood`
by the exit-time tail and the short-travel probability.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingOscillation

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingEvents

/-- Linear interpolation of `a` at `s ≥ 0` lies in the closed ball `B(q, D)` when the node `a ⌊s⌋₊`
does and, if the interpolation weight is nonzero, so does the next node. -/
lemma dist_linInterp_le {a : ℕ → ℂ} {s : ℝ} (hs : 0 ≤ s) {q : ℂ} {D : ℝ}
    (h0 : dist (a ⌊s⌋₊) q ≤ D) (h1 : s - ⌊s⌋₊ ≠ 0 → dist (a (⌊s⌋₊ + 1)) q ≤ D) :
    dist (linInterp a s) q ≤ D := by
  have hn0 : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs
  have hn1 : s < ⌊s⌋₊ + 1 := Nat.lt_floor_add_one s
  unfold linInterp
  by_cases hθ : s - ⌊s⌋₊ = 0
  · rw [hθ]
    simpa using h0
  · have hθpos : 0 < s - ⌊s⌋₊ := lt_of_le_of_ne (by linarith) (Ne.symm hθ)
    have hmem := (convex_closedBall q D) (Metric.mem_closedBall.2 h0)
      (Metric.mem_closedBall.2 (h1 hθ)) (a := 1 - (s - ⌊s⌋₊)) (b := s - ⌊s⌋₊) (by linarith)
      hθpos.le (by ring)
    rw [Metric.mem_closedBall] at hmem
    simpa [Complex.real_smul] using hmem

/-- **Oscillation of the interpolated walk.**  If any two vertices visited at steps `i < j < i + g`,
`j ≤ N`, are at embedded distance at most `D`, and `m ρ + 2 ≤ g`, then the interpolated walk of speed
`m` has oscillation at most `D` over rescaled times `s, t` with `m s, m t ≤ N` and `|s - t| ≤ ρ`. -/
lemma dist_interpPathFn_le_of_close {v : ℤ → ℂ} {m : ℝ≥0} {X : ℕ → ℤ} {N g : ℕ} {D ρ : ℝ}
    (hρ : 0 ≤ ρ) (hD : 0 ≤ D) (hg : (m : ℝ) * ρ + 2 ≤ g)
    (h : ∀ i j : ℕ, i < j → j < i + g → j ≤ N → dist (v (X i)) (v (X j)) ≤ D)
    {s t : ℝ≥0} (hs : (m : ℝ) * s ≤ N) (ht : (m : ℝ) * t ≤ N) (hst : dist s t ≤ ρ) :
    dist (interpPathFn v m X s) (interpPathFn v m X t) ≤ D := by
  wlog hle : s ≤ t generalizing s t
  · rw [dist_comm]
    exact this ht hs (by rwa [dist_comm]) (le_of_not_ge hle)
  have hc : ∀ i j : ℕ, i ≤ j → j < i + g → j ≤ N → dist (v (X i)) (v (X j)) ≤ D := by
    intro i j hij hjg hjN
    rcases hij.eq_or_lt with rfl | hlt
    · rw [dist_self]
      exact hD
    · exact h i j hlt hjg hjN
  have hc' : ∀ i j : ℕ, j ≤ i → i < j + g → i ≤ N → dist (v (X i)) (v (X j)) ≤ D := by
    intro i j hji hig hiN
    rw [dist_comm]
    exact hc j i hji hig hiN
  have hm0 : (0 : ℝ) ≤ m := m.coe_nonneg
  have hg2 : 2 ≤ g := by
    have : (2 : ℝ) ≤ g := by nlinarith [mul_nonneg hm0 hρ]
    exact_mod_cast this
  have hts : (t : ℝ) - s ≤ ρ := by
    rw [NNReal.dist_eq] at hst
    have := (abs_le.1 hst).1
    linarith
  have hab : (m : ℝ) * s ≤ m * t := mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hm0
  have hbd : (m : ℝ) * t ≤ m * s + m * ρ := by
    have := mul_le_mul_of_nonneg_left hts hm0
    linarith
  have ha0 : 0 ≤ (m : ℝ) * s := by positivity
  have hb0 : 0 ≤ (m : ℝ) * t := by positivity
  have hia : (⌊(m : ℝ) * s⌋₊ : ℝ) ≤ m * s := Nat.floor_le ha0
  have hai : (m : ℝ) * s < ⌊(m : ℝ) * s⌋₊ + 1 := Nat.lt_floor_add_one _
  have hjb : (⌊(m : ℝ) * t⌋₊ : ℝ) ≤ m * t := Nat.floor_le hb0
  have hbj : (m : ℝ) * t < ⌊(m : ℝ) * t⌋₊ + 1 := Nat.lt_floor_add_one _
  have hij : ⌊(m : ℝ) * s⌋₊ ≤ ⌊(m : ℝ) * t⌋₊ := Nat.floor_mono hab
  have hjN : ⌊(m : ℝ) * t⌋₊ ≤ N := by exact_mod_cast hjb.trans ht
  have hjg1 : ⌊(m : ℝ) * t⌋₊ + 1 < ⌊(m : ℝ) * s⌋₊ + g := by
    have : (⌊(m : ℝ) * t⌋₊ : ℝ) + 1 < ⌊(m : ℝ) * s⌋₊ + g := by linarith
    exact_mod_cast this
  have hA : dist (linInterp (fun k => v (X k)) ((m : ℝ) * s)) (v (X ⌊(m : ℝ) * t⌋₊)) ≤ D := by
    apply dist_linInterp_le ha0
    · exact hc _ _ hij (by omega) hjN
    · intro hθ
      have hiN : ⌊(m : ℝ) * s⌋₊ + 1 ≤ N := by
        have h1 : (⌊(m : ℝ) * s⌋₊ : ℝ) < m * s := lt_of_le_of_ne hia (fun h => hθ (by linarith))
        have h2 : (⌊(m : ℝ) * s⌋₊ : ℝ) < N := h1.trans_le hs
        exact_mod_cast h2
      by_cases hle' : ⌊(m : ℝ) * s⌋₊ + 1 ≤ ⌊(m : ℝ) * t⌋₊
      · exact hc _ _ hle' (by omega) hjN
      · exact hc' _ _ (by omega) (by omega) hiN
  have hB : dist (linInterp (fun k => v (X k)) ((m : ℝ) * t))
      (linInterp (fun k => v (X k)) ((m : ℝ) * s)) ≤ D := by
    apply dist_linInterp_le hb0
    · rw [dist_comm]
      exact hA
    · intro hθ
      have hj1N : ⌊(m : ℝ) * t⌋₊ + 1 ≤ N := by
        have h1 : (⌊(m : ℝ) * t⌋₊ : ℝ) < m * t := lt_of_le_of_ne hjb (fun h => hθ (by linarith))
        have h2 : (⌊(m : ℝ) * t⌋₊ : ℝ) < N := h1.trans_le ht
        exact_mod_cast h2
      rw [dist_comm]
      apply dist_linInterp_le ha0
      · exact hc _ _ (by omega) (by omega) hj1N
      · intro _
        exact hc _ _ (by omega) (by omega) hj1N
  show dist (linInterp (fun k => v (X k)) ((m : ℝ) * s)) (linInterp (fun k => v (X k)) ((m : ℝ) * t)) ≤ D
  rw [dist_comm]
  exact hB

/-- **Walks with oscillation.**  The complement of the good walks `walkGood v m A' A ρ D z` has
probability at most `p₁ + p₂` where `p₁` bounds a slow exit from `A'` and `p₂` bounds the event that two
vertices visited at steps `i < j < i + g` before the exit time from `A` are at embedded distance more than
`D` (no short travel, Proposition 6.5), if `m ρ + 2 ≤ g`. -/
theorem srwLaw_walkGood_compl_le_of_shortTravel (mult : ℤ → ℤ → ℕ) (z : ℤ) (v : ℤ → ℂ) {m : ℝ≥0}
    (hm : 0 < m) (A' A : Set ℤ) (ρ : ℝ≥0) {D : ℝ} (hD : 0 ≤ D) {g : ℕ}
    (hg : (m : ℝ) * ρ + 2 ≤ g) {p₁ p₂ : ℝ≥0∞}
    (hfin : srwLaw mult z {X | vExitTime A X = ⊤} = 0)
    (hT : srwLaw mult z {X | ρ < ((vExitTime A' X).toNat : ℝ≥0) / m} ≤ p₁)
    (hshort : srwLaw mult z {X | ∃ i j : ℕ, i < j ∧ j < i + g ∧ (j : ℕ∞) ≤ vExitTime A X ∧
      D < dist (v (X i)) (v (X j))} ≤ p₂) :
    srwLaw mult z (walkGood v m A' A ρ D z)ᶜ ≤ p₁ + p₂ := by
  refine srwLaw_walkGood_compl_le mult z v m A' A ρ D hfin hT (le_trans (measure_mono ?_) hshort)
  intro X hX
  obtain ⟨s, t, hs, ht, hst, hlt⟩ := hX
  by_contra hno
  have hno' : ∀ i j : ℕ, i < j → j < i + g → (j : ℕ∞) ≤ vExitTime A X →
      dist (v (X i)) (v (X j)) ≤ D := by
    intro i j hij hjg hjT
    by_contra hcon
    exact hno ⟨i, j, hij, hjg, hjT, not_le.1 hcon⟩
  have hNle : ∀ j : ℕ, j ≤ (vExitTime A X).toNat → (j : ℕ∞) ≤ vExitTime A X := by
    intro j hj
    by_cases hv : vExitTime A X = ⊤
    · rw [hv]
      exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hv
      have hTk : (vExitTime A X).toNat = k := by rw [← hk]; simp
      rw [← hk]
      exact_mod_cast hTk ▸ hj
  have hmN : ∀ u : ℝ≥0, u ≤ ((vExitTime A X).toNat : ℝ≥0) / m →
      (m : ℝ) * u ≤ ((vExitTime A X).toNat : ℝ) := by
    intro u hu
    have := (le_div_iff₀ hm).1 hu
    have h2 : (u : ℝ) * m ≤ ((vExitTime A X).toNat : ℝ) := by exact_mod_cast this
    linarith
  have hgood := dist_interpPathFn_le_of_close (v := v) (m := m) (X := X) (N := (vExitTime A X).toNat)
    (g := g) (D := D) (ρ := ρ) ρ.coe_nonneg hD hg
    (fun i j hij hjg hjN => hno' i j hij hjg (hNle j hjN)) (hmN s hs) (hmN t ht) hst
  exact absurd hlt (not_lt.2 hgood)

end ExitCouplingOscillation
end MatedCRT
