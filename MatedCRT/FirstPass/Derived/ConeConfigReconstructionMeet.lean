import MatedCRT.FirstPass.Derived.CellSideMult

/-!
# Cells with a nonzero frontier-side multiplicity meet

If `cellSideMult ε g j k ≠ 0`, the images under `g` of the cells `[ε(j - 1), εj]` and
`[ε(k - 1), εk]` intersect: consecutive cells share an endpoint, and for separated cells a branch
time of a shared frontier side gives, through the contact relation, a continuum in the intersection
of the images.
-/

set_option autoImplicit false

open Set Filter

namespace MatedCRT

/-- A nonzero side count forces a branch time. -/
theorem cellSideBranchTimes_nonempty_of_cellSideCount_ne_zero {a b c d : ℝ} {g : ℝ → ℂ}
    (h : cellSideCount a b c d g ≠ 0) : (cellSideBranchTimes a b c d g).Nonempty := by
  by_contra hne
  apply h
  have h2 : ¬ ∃ u ∈ cellSideBranchTimes a b c d g, ∃ v ∈ cellSideBranchTimes a b c d g, u ≠ v :=
    fun ⟨u, hu, _⟩ => hne ⟨u, hu⟩
  simp only [cellSideCount, ite_eq_right hne, ite_eq_right h2]

/-- A branch time of the shared sides gives intersecting images of the two cell intervals. -/
theorem inter_nonempty_of_cellSideBranchTimes_nonempty {a b c d : ℝ} {g : ℝ → ℂ}
    (h : (cellSideBranchTimes a b c d g).Nonempty) :
    ((g '' Icc a b) ∩ (g '' Icc c d)).Nonempty := by
  obtain ⟨u, hu, s, hs, t, ht, -, -, hst⟩ := h
  obtain ⟨p₁, hp₁a, hp₁s⟩ := exists_rat_btwn hs.1
  obtain ⟨p₂, hsp₂, hp₂b⟩ := exists_rat_btwn (show s < b from hs.2)
  obtain ⟨q₁, hq₁c, hq₁t⟩ := exists_rat_btwn ht.1
  obtain ⟨q₂, htq₂, hq₂d⟩ := exists_rat_btwn (show t < d from ht.2)
  have hbc : b < c := hu.1.trans hu.2
  have hcd : c < d := ht.1.trans ht.2
  have hdisj : Disjoint (Ioo (p₁ : ℝ) p₂) (Ioo (q₁ : ℝ) q₂) := by
    refine disjoint_left.2 fun x hx hx' => ?_
    linarith [hx.2, hx'.1]
  have hP : Icc (p₁ : ℝ) p₂ ⊆ Ioo a d := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hQ : Icc (q₁ : ℝ) q₂ ⊆ Ioo a d := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨K, hK, -, hKc, -⟩ := hst p₁ p₂ q₁ q₂ ⟨hp₁s, hsp₂⟩ ⟨hq₁t, htq₂⟩ hdisj hP hQ
  obtain ⟨z, hz⟩ := hKc.nonempty
  obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩ := hK hz
  exact ⟨g x, ⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩,
    ⟨y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, hyx⟩⟩

/-- **Cells with a nonzero frontier-side multiplicity meet**: the images of the two cell intervals
under the curve intersect. -/
theorem cellSideMult_ne_zero_inter_nonempty {ε : ℝ} {g : ℝ → ℂ} {j k : ℤ}
    (h : cellSideMult ε g j k ≠ 0) :
    ((g '' Icc (ε * ((j : ℝ) - 1)) (ε * j)) ∩ (g '' Icc (ε * ((k : ℝ) - 1)) (ε * k))).Nonempty := by
  unfold cellSideMult at h
  by_cases h1 : ε ≤ 0 ∨ j = k
  · rw [ite_eq_left h1] at h
    exact absurd rfl h
  rw [ite_eq_right h1] at h
  have hε : 0 < ε := not_le.1 fun hle => h1 (Or.inl hle)
  by_cases h2 : |j - k| = 1
  · rcases abs_eq (zero_le_one : (0 : ℤ) ≤ 1) |>.1 h2 with hjk | hjk
    · have hj : (j : ℝ) = k + 1 := by exact_mod_cast (by omega : j = k + 1)
      refine ⟨g (ε * k), ⟨ε * (j - 1), ?_, ?_⟩, ⟨ε * k, ⟨by nlinarith, le_rfl⟩, rfl⟩⟩
      · exact ⟨le_rfl, by nlinarith⟩
      · rw [hj]; ring_nf
    · have hk : (k : ℝ) = j + 1 := by exact_mod_cast (by omega : k = j + 1)
      refine ⟨g (ε * j), ⟨ε * j, ⟨by nlinarith, le_rfl⟩, rfl⟩, ⟨ε * (k - 1), ?_, ?_⟩⟩
      · exact ⟨le_rfl, by nlinarith⟩
      · rw [hk]; ring_nf
  rw [ite_eq_right h2] at h
  have key := inter_nonempty_of_cellSideBranchTimes_nonempty
    (cellSideBranchTimes_nonempty_of_cellSideCount_ne_zero h)
  rcases le_total j k with hjk | hjk
  · rwa [min_eq_left hjk, max_eq_right hjk] at key
  · rw [min_eq_right hjk, max_eq_left hjk] at key
    rwa [inter_comm]

end MatedCRT
