import MatedCRT.Defs.Setting

/-!
# Families of harmonic balls of the quantum cone: uniqueness and gluing

Condition (c) of Theorem 2.3 (the obstacle characterization, `SatisfiesObstacleCharacterization`) determines each
bounded `Λ_t`: if `Λ_t ⊆ B_r` then `Λ_t = int cl {w̄^{B_ρ}_t > -t G_{B_ρ}(0, ·)}` for every `ρ > r`, a set which only
depends on `μ`, `ρ` and `t`. Hence two families satisfying (b) (boundedness) and (c) agree wherever both are defined
(`IsConeHarmonicBallFamilyOn.eqOn`, `IsConeHarmonicBallFamily.eqOn`), and families defined on intervals
`(0, S_n)` with `sup_n S_n = ∞` glue to a family defined for all `t > 0` (`exists_isConeHarmonicBallFamily_of_seq`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Two families of harmonic balls with the properties of Theorem 2.3 on `(0, T)` and `(0, T')` agree on
`(0, min T T')` (condition (c) and boundedness). -/
theorem IsConeHarmonicBallFamilyOn.eqOn {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {T T' : ℝ}
    (h : IsConeHarmonicBallFamilyOn μ Λ T) (h' : IsConeHarmonicBallFamilyOn μ Λ' T') :
    EqOn Λ' Λ (Ioo 0 (min T T')) := by
  intro t ht
  have htT : t ∈ Ioo 0 T := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have htT' : t ∈ Ioo 0 T' := ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  obtain ⟨r, hr⟩ := (h.2.1.isBounded t htT).subset_ball 0
  obtain ⟨r', hr'⟩ := (h'.2.1.isBounded t htT').subset_ball 0
  have hR : 0 < max (max r r') 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hrR : r ≤ max (max r r') 1 := (le_max_left r r').trans (le_max_left _ _)
  have hr'R : r' ≤ max (max r r') 1 := (le_max_right r r').trans (le_max_left _ _)
  rw [(h.2.2 t _ htT hR (hr.trans (ball_subset_ball hrR)) _ (lt_add_one _)).1,
    (h'.2.2 t _ htT' hR (hr'.trans (ball_subset_ball hr'R)) _ (lt_add_one _)).1]

/-- **Uniqueness in Theorem 2.3**: two families of harmonic balls with the properties (a)-(c) agree. -/
theorem IsConeHarmonicBallFamily.eqOn {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ}
    (h : IsConeHarmonicBallFamily μ Λ) (h' : IsConeHarmonicBallFamily μ Λ') : EqOn Λ' Λ (Ioi 0) := by
  intro t ht
  obtain ⟨r, hr⟩ := (h.2.1.isBounded t ht).subset_ball 0
  obtain ⟨r', hr'⟩ := (h'.2.1.isBounded t ht).subset_ball 0
  have hR : 0 < max (max r r') 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hrR : r ≤ max (max r r') 1 := (le_max_left r r').trans (le_max_left _ _)
  have hr'R : r' ≤ max (max r r') 1 := (le_max_right r r').trans (le_max_left _ _)
  rw [(h.2.2 t _ ht hR (hr.trans (ball_subset_ball hrR)) _ (lt_add_one _)).1,
    (h'.2.2 t _ ht hR (hr'.trans (ball_subset_ball hr'R)) _ (lt_add_one _)).1]

/-- **Gluing.** Families of harmonic balls with the properties of Theorem 2.3 on intervals `(0, S_n)` with
`sup_n S_n = ∞` glue to a family with the properties (a)-(c) for all `t > 0`. -/
theorem exists_isConeHarmonicBallFamily_of_seq {μ : Measure ℂ} {S : ℕ → ℝ} {Λ : ℕ → ℝ → Set ℂ}
    (hfam : ∀ n, IsConeHarmonicBallFamilyOn μ (Λ n) (S n)) (hunb : ∀ M : ℝ, ∃ n, M < S n) :
    ∃ Λ' : ℝ → Set ℂ, IsConeHarmonicBallFamily μ Λ' := by
  classical
  let N : ℝ → ℕ := fun t => Nat.find (hunb t)
  have hN : ∀ t, t < S (N t) := fun t => Nat.find_spec (hunb t)
  let Λ' : ℝ → Set ℂ := fun t => Λ (N t) t
  have hmem : ∀ t, 0 < t → t ∈ Ioo 0 (S (N t)) := fun t ht => ⟨ht, hN t⟩
  have hagree : ∀ n t, t ∈ Ioo 0 (S n) → Λ' t = Λ n t := fun n t ht =>
    (hfam n).eqOn (hfam (N t)) ⟨ht.1, lt_min ht.2 (hN t)⟩
  refine ⟨Λ', fun t ht => (hfam (N t)).1 t (hmem t ht), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun t ht => (hfam (N t)).2.1.measure_eq t (hmem t ht)
  · exact fun t ht => (hfam (N t)).2.1.measure_frontier t (hmem t ht)
  · exact fun t ht => (hfam (N t)).2.1.isRegularOpen t (hmem t ht)
  · exact fun t ht => (hfam (N t)).2.1.isBounded t (hmem t ht)
  · exact fun t ht => (hfam (N t)).2.1.isConnected t (hmem t ht)
  · exact fun t ht => (hfam (N t)).2.1.mem t (hmem t ht)
  · intro s hs t ht hst
    rw [hagree (N t) s ⟨hs, lt_of_le_of_lt hst (hN t)⟩]
    exact (hfam (N t)).2.1.monotoneOn ⟨hs, lt_of_le_of_lt hst (hN t)⟩ (hmem t ht) hst
  · intro t ht ε hε
    have h1 := (hfam (N t)).2.1.hausdorffContinuousOn t (hmem t ht) ε hε
    rw [isOpen_Ioo.nhdsWithin_eq (hmem t ht)] at h1
    have h2 : Ioo 0 (S (N t)) ∈ 𝓝 t := isOpen_Ioo.mem_nhds (hmem t ht)
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with s hs hs2
    rw [hagree (N t) s hs2]
    exact hs
  · apply Subset.antisymm
    · intro x hx
      rw [← (hfam 0).2.1.iInter_eq]
      simp only [mem_iInter] at hx ⊢
      intro t ht
      rw [← hagree 0 t ht]
      exact hx t ht.1
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      simp only [mem_iInter]
      intro t ht
      exact (hfam (N t)).2.1.mem t (hmem t ht)
  · exact fun t r ht hr hsub ρ hρ => (hfam (N t)).2.2 t r (hmem t ht) hr hsub ρ hρ

end MatedCRT
