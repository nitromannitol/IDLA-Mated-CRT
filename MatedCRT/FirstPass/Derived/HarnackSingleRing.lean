import MatedCRT.FirstPass.Derived.HarnackFromSeparation

/-!
# Separation of a vertex from far vertices by a ring of the walk

Deterministic part of Berestycki–Gwynne (2020), Lemma 3.9 / display (3.21): if the trace of a walk disconnects the
vertices whose cells meet a small circle `∂B_{r₁}(c)` from those whose cells meet a larger circle `∂B_{r₂}(c)`, then it
disconnects every vertex with a cell point in the closed disc `B̄_{r₁}(c)` from every vertex with a cell point outside
the open disc `B_{r₂}(c)`.  The proof is topological: cells are connected and the cells of consecutive vertices of a
walk meet, so a walk from the inner disc to the outer region meets a cell crossing each intermediate circle.
-/

set_option autoImplicit false

namespace MatedCRT

open Set Metric
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov

/-- A connected set with points at distance `≤ r` and `≥ r` from `c` has a point at distance exactly `r`. -/
theorem exists_dist_eq_of_isPreconnected {C : Set ℂ} (hC : IsPreconnected C) {c : ℂ} {r : ℝ}
    (h₁ : ∃ x ∈ C, dist x c ≤ r) (h₂ : ∃ x ∈ C, r ≤ dist x c) : ∃ x ∈ C, dist x c = r := by
  obtain ⟨x₁, hx₁, hx₁'⟩ := h₁
  obtain ⟨x₂, hx₂, hx₂'⟩ := h₂
  have hD : IsPreconnected ((fun x => dist x c) '' C) :=
    hC.image _ (continuous_id.dist continuous_const).continuousOn
  obtain ⟨w, hw, hw'⟩ := hD.Icc_subset ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩ ⟨hx₁', hx₂'⟩
  exact ⟨w, hw, hw'⟩

/-- **Crossing lemma.** A walk whose consecutive cells meet, from a vertex with a cell point at distance `≤ r` from
`c` to a vertex with a cell point at distance `≥ r`, visits a vertex whose cell meets the circle `∂B_r(c)`. -/
theorem exists_mem_support_cell_dist_eq {Γ : SimpleGraph ℤ} {J : ℤ → Set ℂ}
    (hJ : ∀ k, IsPreconnected (J k)) (hΓ : ∀ j k, Γ.Adj j k → (J j ∩ J k).Nonempty) {c : ℂ} {r : ℝ} :
    ∀ {u v : ℤ} (w : Γ.Walk u v), (∃ x ∈ J u, dist x c ≤ r) → (∃ x ∈ J v, r ≤ dist x c) →
      ∃ k ∈ w.support, ∃ x ∈ J k, dist x c = r := by
  intro u v w
  induction w with
  | nil =>
    intro h₁ h₂
    exact ⟨_, by simp, exists_dist_eq_of_isPreconnected (hJ _) h₁ h₂⟩
  | @cons u v' v' h p ih =>
    intro h₁ h₂
    by_cases hbig : ∃ x ∈ J u, r ≤ dist x c
    · exact ⟨u, by simp, exists_dist_eq_of_isPreconnected (hJ u) h₁ hbig⟩
    · push Not at hbig
      obtain ⟨x, hx1, hx2⟩ := hΓ _ _ h
      obtain ⟨k, hk, hk'⟩ := ih ⟨x, hx2, (hbig x hx1).le⟩ h₂
      exact ⟨k, by simp [hk], hk'⟩

/-- **Separation by a ring.** If `U₀ ⊆ U` separates the vertices whose cells meet `∂B_{r₁}(c)` from those whose cells
meet `∂B_{r₂}(c)`, `r₁ ≤ r₂`, then `U` separates every vertex `y` with a cell point in `B̄_{r₁}(c)` from every vertex
of `I`, as soon as each vertex of `I` has a cell point outside `B_{r₂}(c)`. -/
theorem graphSeparates_of_two_spheres {Γ : SimpleGraph ℤ} {J : ℤ → Set ℂ}
    (hJ : ∀ k, IsPreconnected (J k)) (hΓ : ∀ j k, Γ.Adj j k → (J j ∩ J k).Nonempty) {c : ℂ} {r₁ r₂ : ℝ}
    (hr : r₁ ≤ r₂) {S T U₀ U I : Set ℤ} (hS : ∀ k, ∀ x ∈ J k, dist x c = r₁ → k ∈ S)
    (hT : ∀ k, ∀ x ∈ J k, dist x c = r₂ → k ∈ T) (hU : U₀ ⊆ U) {y : ℤ} (hy : ∃ x ∈ J y, dist x c ≤ r₁)
    (hI : ∀ k ∈ I, ∃ x ∈ J k, r₂ ≤ dist x c) (hsep : GraphSeparates Γ U₀ S T) :
    GraphSeparates Γ U {y} I := by
  intro y' hy' k hk w
  rw [Set.mem_singleton_iff] at hy'
  subst hy'
  obtain ⟨u, hu, x₂, hx₂, hx₂'⟩ := exists_mem_support_cell_dist_eq hJ hΓ (r := r₂) w
    (hy.imp fun x hx => ⟨hx.1, hx.2.trans hr⟩) (hI k hk)
  obtain ⟨s, hs, x₁, hx₁, hx₁'⟩ := exists_mem_support_cell_dist_eq hJ hΓ (r := r₁) (w.takeUntil u hu) hy
    ⟨x₂, hx₂, by rw [hx₂']; exact hr⟩
  obtain ⟨v, hv, hvU⟩ := hsep s (hS s x₁ hx₁ hx₁') u (hT u x₂ hx₂ hx₂') ((w.takeUntil u hu).dropUntil s hs)
  exact ⟨v, SimpleGraph.Walk.support_takeUntil_subset_support w hu
    (SimpleGraph.Walk.support_dropUntil_subset_support _ hs hv), hU hvU⟩

/-- The vertices visited before time `n` belong to the trace before the first visit to `I`, if none of them is in
`I`. -/
theorem subset_traceBefore_of_forall_not_mem {I : Set ℤ} {ξ : ℕ → ℤ} {n : ℕ} (hn : ∀ j < n, ξ j ∉ I) :
    {v | ∃ m < n, ξ m = v} ⊆ traceBefore (id : ℤ → ℤ) I ξ := by
  rintro v ⟨m, hm, rfl⟩
  refine ⟨m, ?_, rfl⟩
  have h : ¬ hitTime ((id : ℤ → ℤ) ⁻¹' I) ξ ≤ (m : ℕ∞) := by
    rw [hitTime_le_coe_iff]
    rintro ⟨j, hj, hj'⟩
    exact hn j (lt_of_le_of_lt hj hm) hj'
  exact lt_of_not_ge h

/-- **Separation of the trace by the walk's ring.** If the walk `ξ` avoids `I` before time `n` and its first `n`
vertices separate the vertices meeting `∂B_{r₁}(c)` from those meeting `∂B_{r₂}(c)`, then the trace before the first
visit to `I` separates `y` (with a cell point in `B̄_{r₁}(c)`) from `I` (every vertex of which has a cell point
outside `B_{r₂}(c)`). -/
theorem graphSeparates_traceBefore_of_two_spheres {Γ : SimpleGraph ℤ} {J : ℤ → Set ℂ}
    (hJ : ∀ k, IsPreconnected (J k)) (hΓ : ∀ j k, Γ.Adj j k → (J j ∩ J k).Nonempty) {c : ℂ} {r₁ r₂ : ℝ}
    (hr : r₁ ≤ r₂) {S T I : Set ℤ} (hS : ∀ k, ∀ x ∈ J k, dist x c = r₁ → k ∈ S)
    (hT : ∀ k, ∀ x ∈ J k, dist x c = r₂ → k ∈ T) {y : ℤ} (hy : ∃ x ∈ J y, dist x c ≤ r₁)
    (hI : ∀ k ∈ I, ∃ x ∈ J k, r₂ ≤ dist x c) {ξ : ℕ → ℤ} {n : ℕ} (hn : ∀ j < n, ξ j ∉ I)
    (hsep : GraphSeparates Γ {v | ∃ m < n, ξ m = v} S T) :
    GraphSeparates Γ (traceBefore (id : ℤ → ℤ) I ξ) {y} I :=
  graphSeparates_of_two_spheres hJ hΓ hr hS hT (subset_traceBefore_of_forall_not_mem hn) hy hI hsep

end MatedCRT
