import MatedCRT.Proofs.Sandpile.Comparison

/-! Finite-support stabilizing witnesses from the discrete obstacle problem. -/

namespace MatedCRT.Sandpile

open Set Finset Classical

variable {m : ℤ → ℤ → ℕ} {M : ℝ} {V : Set ℤ} {φ : ℤ → ℝ}

/-- If the obstacle cluster is contained in the graph interior of its domain,
the stopped obstacle odometer is a finite-support global stabilizer. -/
theorem finite_witness_of_obstacle_interior
    (hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ ((mdeg m 0 : ℝ)⁻¹ * M))
    (hint : discreteCluster (vClosure m V)
      (discreteLeastSupersolution m V (vClosure m V) (fun a => (mdeg m a : ℝ)⁻¹) φ) φ ⊆
        vInterior m V) :
    ∃ v : ℤ → ℝ, v ∈ admissible m M ∧ (Function.support v).Finite := by
  classical
  let r : ℤ → ℝ := fun a => (mdeg m a : ℝ)⁻¹
  let w := discreteLeastSupersolution m V (vClosure m V) r φ
  let v : ℤ → ℝ := fun a => if a ∈ vClosure m V then w a - φ a else 0
  have hvnonneg : ∀ a, 0 ≤ v a := by
    intro a
    dsimp [v]
    split_ifs with ha
    · exact sub_nonneg.2 (hS.obstacle_le_w a ha)
    · exact le_rfl
  have hsupport : Function.support v ⊆ vInterior m V := by
    intro a ha
    by_cases haW : a ∈ vClosure m V
    · apply hint
      refine ⟨haW, ?_⟩
      have hpos : 0 < v a := lt_of_le_of_ne (hvnonneg a) (Ne.symm ha)
      simp only [v, ite_eq_left haW] at hpos
      linarith
    · simp [Function.mem_support, v, haW] at ha
  have hvlocal : ∀ a ∈ V, mLaplacian m v a + (mdeg m 0 : ℝ)⁻¹ * M * diracZero a ≤ r a := by
    intro a ha
    have haW : a ∈ vClosure m V := Or.inl ha
    have hsum : lapSum hS.hlf v a = lapSum hS.hlf (fun b => w b - φ b) a := by
      unfold lapSum
      apply Finset.sum_congr rfl
      intro b hb
      have hbW := mem_vClosure_of_mem_nbrs hS.hlf ha hb
      simp [v, haW, hbW]
    have hΔ : mLaplacian m v a = mLaplacian m w a - mLaplacian m φ a := by
      simp only [mLaplacian_eq_div hS.hlf]
      rw [hsum, lapSum_sub, sub_div]
    rw [hΔ, hS.obstacle_laplacian a ha]
    have hbound := hS.lap_w_le a ha
    dsimp [w, r] at *
    by_cases ha0 : a = 0 <;> simp [diracZero, ha0] at * <;> linarith
  have hvadm : v ∈ admissible m M := by
    refine ⟨hvnonneg, fun a => ?_⟩
    by_cases ha : a ∈ V
    · exact hvlocal a ha
    · have ha0 : a ≠ 0 := fun e => ha (e ▸ hS.origin_mem)
      have hva : v a = 0 := by
        by_contra hn
        exact ha (hsupport hn).1
      have hsum : lapSum hS.hlf v a = 0 := by
        unfold lapSum
        apply Finset.sum_eq_zero
        intro b hb
        have hvb : v b = 0 := by
          by_contra hn
          have hba : m b a ≠ 0 := by rw [hS.symm]; exact (mem_nbrs hS.hlf).1 hb
          exact ha ((hsupport hn).2 a hba)
        simp [hva, hvb]
      have hlap : mLaplacian m v a = 0 := by
        rw [mLaplacian_eq_div hS.hlf, hsum, zero_div]
      simp only [hlap, diracZero, ite_eq_right ha0, mul_zero, add_zero]
      exact inv_nonneg.2 (Nat.cast_nonneg _)
  exact ⟨v, hvadm, hS.finite.subset fun a ha => (hsupport ha).1⟩

end MatedCRT.Sandpile
