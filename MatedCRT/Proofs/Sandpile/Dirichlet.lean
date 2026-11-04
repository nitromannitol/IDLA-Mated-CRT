import MatedCRT.Proofs.Sandpile.Comparison

/-! Dirichlet problems on finite connected sets of general multigraphs. -/

namespace MatedCRT.Sandpile

open Set Classical

variable {m : ℤ → ℤ → ℕ} {V : Set ℤ}

/-- The finite Dirichlet problem, using the minimum principle and the
finite-dimensional restricted Laplacian of `Sec4/GreenLaplacian.lean`. -/
theorem exists_dirichlet_laplacian (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hV : V.Finite) (hconn : IsVConnected m V)
    (hbd : (vBoundary m V).Nonempty) (r : ℤ → ℝ) :
    ∃ v : ℤ → ℝ, (∀ a ∉ V, v a = 0) ∧ ∀ a ∈ V, mLaplacian m v a = r a := by
  have hinj : Function.Injective (restrictedLaplacian m hlf V) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    let v := extendByZero V x
    have hlap : ∀ a ∈ V, mLaplacian m v a = 0 := fun a ha => congrFun hx ⟨a, ha⟩
    have hboundary : ∀ a ∈ vBoundary m V, v a = 0 := fun a ha => extendByZero_of_not_mem ha.1
    have hsum : ∀ a ∈ V, lapSum hlf v a = 0 := by
      intro a ha
      rw [← mLaplacian_mul_mdeg hlf, hlap a ha, zero_mul]
    have hv : ∀ a ∈ V, 0 ≤ v a := nonneg_of_lapSum_nonpos hlf hsymm hV hconn hbd
      (fun a ha => (hsum a ha).le) (fun a ha => (hboundary a ha).ge)
    have hvneg : ∀ a ∈ V, 0 ≤ -v a := by
      apply nonneg_of_lapSum_nonpos hlf hsymm hV hconn hbd (v := fun a => -v a)
      · intro a ha
        have heq : (fun b => -v b) = fun b => (0 : ℝ) - v b := by funext b; simp
        simp only [heq, lapSum_sub, lapSum_zero, hsum a ha, sub_self, le_refl]
      · intro a ha
        simp [hboundary a ha]
    funext a
    have hzero : v a = 0 := by linarith [hv a a.2, hvneg a a.2]
    change x a = 0
    simpa [v, extendByZero_coe] using hzero
  have := hV.to_subtype
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.1 hinj) fun a => r a
  exact ⟨extendByZero V x, fun a ha => extendByZero_of_not_mem ha, fun a ha => congrFun hx ⟨a, ha⟩⟩

/-- A finite connected domain with nonempty boundary admits the point-source
obstacle required by Appendix A, on any locally finite symmetric multigraph. -/
theorem exists_point_source_obstacle (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hV : V.Finite) (hconn : IsVConnected m V)
    (hbd : (vBoundary m V).Nonempty) (h0 : (0 : ℤ) ∈ V) {M : ℝ} (hM : 0 < M) :
    ∃ φ : ℤ → ℝ, IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ
      ((mdeg m 0 : ℝ)⁻¹ * M) := by
  let t : ℝ := (mdeg m 0 : ℝ)⁻¹ * M
  have ht : 0 < t := mul_pos (inv_pos.2 (by exact_mod_cast hdeg 0)) hM
  obtain ⟨φ, hφ0, hφlap⟩ := exists_dirichlet_laplacian hlf hsymm hV hconn hbd
    (fun a => t * if a = 0 then 1 else 0)
  have hsum : ∀ a ∈ V, 0 ≤ lapSum hlf φ a := by
    intro a ha
    rw [← mLaplacian_mul_mdeg hlf, hφlap a ha]
    have hδ : 0 ≤ (if a = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg ht.le hδ) (Nat.cast_nonneg _)
  have hφnonpos : ∀ a ∈ V, φ a ≤ 0 := by
    have hneg : ∀ a ∈ V, 0 ≤ -φ a := by
      apply nonneg_of_lapSum_nonpos hlf hsymm hV hconn hbd (v := fun a => -φ a)
      · intro a ha
        have heq : (fun b => -φ b) = fun b => (0 : ℝ) - φ b := by funext b; simp
        rw [heq, lapSum_sub, lapSum_zero, zero_sub]
        exact neg_nonpos.2 (hsum a ha)
      · intro a ha
        simp [hφ0 a ha.1]
    intro a ha
    linarith [hneg a ha]
  refine ⟨φ, ?_⟩
  refine ⟨hsymm, hloop, hlf, inferInstance, hV, hconn, h0, ?_, ?_, ?_, ?_, ht⟩
  · intro a ha
    exact inv_pos.2 (by exact_mod_cast hdeg a)
  · intro a ha
    rcases ha with ha | ha
    · exact hφnonpos a ha
    · rw [hφ0 a ha.1]
  · intro a ha
    by_cases ha0 : a = 0 <;> simpa [t, ha0] using hφlap a ha
  · intro a ha
    exact hφ0 a ha.1

end MatedCRT.Sandpile
