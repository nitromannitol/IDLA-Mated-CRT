import MatedCRT.FirstPass.Derived.ConeConfigReconstructionMap

/-!
# The labels of the reconstruction

The true data of a quantum-time curve `ξ` at mesh `1/n` with phase `θ` (`phaseData`) have the vertex points
`ξ((k + θ)/n)` and the frontier-side multiplicities of the cells of `t ↦ ξ(t + θ/n)`. With the quantum times
`C₋ < C₊` of the inner endpoints of the two blocks, the true label `k` of a cell of the negative block becomes the
synthetic label `k - ⌊n C₋ - θ⌋ ≤ 0`, and that of a cell of the positive block the synthetic label
`k - ⌊n C₊ - θ⌋ + 2` (`reconLabel`). With the residues `fract(n C_± - θ)` the relative quantum times of the synthetic
cell are `(k - 1 + θ)/n - C_±` and `(k + θ)/n - C_±` (`reconRelLeft_reconLabel_neg`, …).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace MatedCRT

/-- **The true data** at mesh `1/n` with phase `θ`: the points `ξ((k + θ)/n)` and the frontier-side multiplicities of
the cells of `t ↦ ξ(t + θ/n)`. -/
def phaseData (n : ℕ) (θ : ℝ) (ξ : C(ℝ, ℂ)) : (ℤ → ℂ) × (ℤ → ℤ → ℕ) :=
  (fun k => ξ (((k : ℝ) + θ) / n), fun j k => cellSideMult (1 / (n : ℝ)) (fun t => ξ (t + θ / n)) j k)

/-- The residues `fract(n C_i - θ)` of the two offsets `C = (C₋, C₊)`. -/
def offsetResiduesOf (n : ℕ) (θ : ℝ) (C : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => Int.fract ((n : ℝ) * C i - θ)

theorem offsetResiduesOf_apply (n : ℕ) (θ : ℝ) (C : Fin 2 → ℝ) (i : Fin 2) :
    offsetResiduesOf n θ C i = Int.fract ((n : ℝ) * C i - θ) :=
  rfl

/-- **The synthetic label of the true label `k`**: `k - ⌊n C₋ - θ⌋` if the vertex `(k + θ)/n` is at most `C₋`, and
`k - ⌊n C₊ - θ⌋ + 2` otherwise. -/
def reconLabel (n : ℕ) (θ : ℝ) (C : Fin 2 → ℝ) (k : ℤ) : ℤ :=
  if ((k : ℝ) + θ) / n ≤ C 0 then k - ⌊(n : ℝ) * C 0 - θ⌋ else k - ⌊(n : ℝ) * C 1 - θ⌋ + 2

theorem shift_sub_fract_div {n : ℕ} (hn : 0 < n) (θ c : ℝ) (k : ℤ) (s : ℝ) :
    (((k - ⌊(n : ℝ) * c - θ⌋ : ℤ) : ℝ) - s - Int.fract ((n : ℝ) * c - θ)) / n = ((k : ℝ) - s + θ) / n - c := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Int.fract]
  push_cast
  field_simp
  ring

theorem reconLabel_le_zero_iff {n : ℕ} (hn : 0 < n) {θ : ℝ} {C : Fin 2 → ℝ} {k : ℤ}
    (hk : ((k : ℝ) + θ) / n ≤ C 0) : reconLabel n θ C k = k - ⌊(n : ℝ) * C 0 - θ⌋ ∧
      reconLabel n θ C k ≤ 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : reconLabel n θ C k = k - ⌊(n : ℝ) * C 0 - θ⌋ := if_pos hk
  refine ⟨hl, ?_⟩
  rw [hl, sub_nonpos]
  apply Int.le_floor.2
  rw [div_le_iff₀ hn'] at hk
  linarith

theorem reconLabel_of_lt {n : ℕ} {θ : ℝ} {C : Fin 2 → ℝ} {k : ℤ} (hk : C 0 < ((k : ℝ) + θ) / n) :
    reconLabel n θ C k = k - ⌊(n : ℝ) * C 1 - θ⌋ + 2 :=
  if_neg (not_le.2 hk)

/-- In the positive block (`C₊ ≤ (k - 1 + θ)/n`) the synthetic label is at least `3`. -/
theorem three_le_reconLabel {n : ℕ} (hn : 0 < n) {θ : ℝ} {C : Fin 2 → ℝ} (hC : C 0 < C 1) {k : ℤ}
    (hk : C 1 ≤ ((k : ℝ) - 1 + θ) / n) : 3 ≤ reconLabel n θ C k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : C 0 < ((k : ℝ) + θ) / n := by
    have : ((k : ℝ) - 1 + θ) / n < ((k : ℝ) + θ) / n := by
      apply div_lt_div_of_pos_right _ hn'; linarith
    linarith
  rw [reconLabel_of_lt hlt]
  have h1 : ⌊(n : ℝ) * C 1 - θ⌋ ≤ k - 1 := by
    apply Int.floor_le_iff.2
    rw [le_div_iff₀ hn'] at hk
    push_cast
    linarith
  omega

theorem reconRelRight_reconLabel_neg {n : ℕ} (hn : 0 < n) {θ : ℝ} {C : Fin 2 → ℝ} {k : ℤ}
    (hk : ((k : ℝ) + θ) / n ≤ C 0) :
    reconRelRight n (offsetResiduesOf n θ C) (reconLabel n θ C k) = ((k : ℝ) + θ) / n - C 0 := by
  obtain ⟨hl, hl0⟩ := reconLabel_le_zero_iff hn hk
  rw [reconRelRight, if_pos hl0, hl, offsetResiduesOf_apply]
  simpa using shift_sub_fract_div hn θ (C 0) k 0

theorem reconRelLeft_reconLabel_neg {n : ℕ} (hn : 0 < n) {θ : ℝ} {C : Fin 2 → ℝ} {k : ℤ}
    (hk : ((k : ℝ) + θ) / n ≤ C 0) :
    reconRelLeft n (offsetResiduesOf n θ C) (reconLabel n θ C k) = ((k : ℝ) - 1 + θ) / n - C 0 := by
  obtain ⟨hl, hl0⟩ := reconLabel_le_zero_iff hn hk
  rw [reconRelLeft, if_pos hl0, hl, offsetResiduesOf_apply]
  exact shift_sub_fract_div hn θ (C 0) k 1

theorem reconRelRight_reconLabel_pos {n : ℕ} (hn : 0 < n) {θ : ℝ} {C : Fin 2 → ℝ} (hC : C 0 < C 1) {k : ℤ}
    (hk : C 1 ≤ ((k : ℝ) - 1 + θ) / n) :
    reconRelRight n (offsetResiduesOf n θ C) (reconLabel n θ C k) = ((k : ℝ) + θ) / n - C 1 := by
  have h3 := three_le_reconLabel hn hC hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : C 0 < ((k : ℝ) + θ) / n := by
    have : ((k : ℝ) - 1 + θ) / n < ((k : ℝ) + θ) / n := by
      apply div_lt_div_of_pos_right _ hn'; linarith
    linarith
  have hl0 : ¬ (reconLabel n θ C k ≤ 0) := by omega
  rw [reconRelRight, if_neg hl0, reconLabel_of_lt hlt, offsetResiduesOf_apply]
  have := shift_sub_fract_div hn θ (C 1) k 0
  simp only [sub_zero] at this
  rw [← this]
  congr 1
  push_cast
  ring

theorem reconRelLeft_reconLabel_pos {n : ℕ} (hn : 0 < n) {θ : ℝ} {C : Fin 2 → ℝ} (hC : C 0 < C 1) {k : ℤ}
    (hk : C 1 ≤ ((k : ℝ) - 1 + θ) / n) :
    reconRelLeft n (offsetResiduesOf n θ C) (reconLabel n θ C k) = ((k : ℝ) - 1 + θ) / n - C 1 := by
  have h3 := three_le_reconLabel hn hC hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : C 0 < ((k : ℝ) + θ) / n := by
    have : ((k : ℝ) - 1 + θ) / n < ((k : ℝ) + θ) / n := by
      apply div_lt_div_of_pos_right _ hn'; linarith
    linarith
  have hl0 : ¬ (reconLabel n θ C k ≤ 0) := by omega
  rw [reconRelLeft, if_neg hl0, reconLabel_of_lt hlt, offsetResiduesOf_apply,
    ← shift_sub_fract_div hn θ (C 1) k 1]
  congr 1
  push_cast
  ring

end MatedCRT
