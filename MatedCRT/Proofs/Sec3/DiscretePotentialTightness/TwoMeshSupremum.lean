import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.ThresholdReconstruction

/-! # Measurable suprema of two-mesh cell values -/

namespace MatedCRT

open Set MeasureTheory

/-- The supremum of a bounded nonnegative two-cell observable on a compact
    set has a measurable version on the common cell-selection event. -/
theorem exists_measurable_two_mesh_supremum
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (v : Ω → ℤ → ℤ → ℝ) (hv : ∀ a b, Measurable fun ω => v ω a b)
    (C : ℝ) (hC : 0 ≤ C) (hvbound : ∀ ω a b, 0 ≤ v ω a b ∧ v ω a b ≤ C)
    (ε δ : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hε : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty)
    (hδ : ∀ k : ℤ, (Icc (δ * (k - 1)) (δ * k)).Nonempty) :
    ∃ g : Ω → ℝ, Measurable g ∧ ∀ ω,
      (∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) →
      (∃ M : ℤ, ∀ j < M, ∀ x ∈ K, x ∉ cell δ (η ω) j) →
      (∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x)) →
      (∀ x ∈ K, x ∈ cell δ (η ω) (vertexOf δ (η ω) x)) →
      g ω = sSup (insert 0 {r | ∃ x ∈ K,
        r = v ω (vertexOf ε (η ω) x) (vertexOf δ (η ω) x)}) := by
  classical
  let P : Ω → Prop := fun ω =>
    (∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
    (∃ M : ℤ, ∀ j < M, ∀ x ∈ K, x ∉ cell δ (η ω) j) ∧
    (∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x)) ∧
    (∀ x ∈ K, x ∈ cell δ (η ω) (vertexOf δ (η ω) x))
  let S : Ω → Set ℝ := fun ω => insert 0 {r | ∃ x ∈ K,
    r = v ω (vertexOf ε (η ω) x) (vertexOf δ (η ω) x)}
  let f : Ω → ℝ := fun ω => sSup (S ω)
  have hS : ∀ ω, BddAbove (S ω) := by
    intro ω
    refine ⟨C, ?_⟩
    intro r hr
    rcases (mem_insert_iff.mp hr) with rfl | ⟨x, hx, rfl⟩
    · exact hC
    · exact (hvbound ω _ _).2
  have hf : ∀ ω, 0 ≤ f ω ∧ f ω ≤ C := by
    intro ω
    constructor
    · exact le_csSup (hS ω) (mem_insert 0 _)
    · apply csSup_le
      · exact ⟨0, mem_insert 0 _⟩
      · intro r hr
        rcases (mem_insert_iff.mp hr) with rfl | ⟨x, hx, rfl⟩
        · exact hC
        · exact (hvbound ω _ _).2
  have hevent : ∀ q : ℚ, ∃ A : Set Ω, MeasurableSet A ∧ ∀ ω, P ω →
      (ω ∈ A ↔ ∃ x ∈ K, (q : ℝ) < v ω (vertexOf ε (η ω) x) (vertexOf δ (η ω) x)) := by
    intro q
    obtain ⟨A, hAm, hA⟩ := exists_measurable_two_mesh_cell_values_event η hη v hv ε δ q K hK hε hδ
    exact ⟨A, hAm, fun ω hP => hA ω hP.1 hP.2.1 hP.2.2.1 hP.2.2.2⟩
  choose A hAm hA using hevent
  let B : ℚ → Set Ω := fun q => if (q : ℝ) < 0 then univ else A q
  have hBm : ∀ q, MeasurableSet (B q) := by
    intro q
    dsimp only [B]
    split_ifs
    · exact MeasurableSet.univ
    · exact hAm q
  have hB : ∀ ω, P ω → ∀ q, (ω ∈ B q ↔ (q : ℝ) < f ω) := by
    intro ω hP q
    by_cases hq : (q : ℝ) < 0
    · change ω ∈ (if (q : ℝ) < 0 then univ else A q) ↔ (q : ℝ) < f ω
      split_ifs
      exact iff_of_true (mem_univ ω) (hq.trans_le (hf ω).1)
    · have hq0 : 0 ≤ (q : ℝ) := le_of_not_gt hq
      have hs := lt_csSup_iff (a := (q : ℝ)) (hS ω) (show (S ω).Nonempty from ⟨0, mem_insert 0 _⟩)
      have heq : ((q : ℝ) < f ω) ↔ ∃ x ∈ K,
          (q : ℝ) < v ω (vertexOf ε (η ω) x) (vertexOf δ (η ω) x) := by
        rw [hs]
        simp only [S, mem_insert_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨r, rfl | ⟨x, hx, rfl⟩, hr⟩
          · exact (not_lt_of_ge hq0 hr).elim
          · exact ⟨x, hx, hr⟩
        · rintro ⟨x, hx, hxv⟩
          exact ⟨_, Or.inr ⟨x, hx, rfl⟩, hxv⟩
      change ω ∈ (if (q : ℝ) < 0 then univ else A q) ↔ (q : ℝ) < f ω
      split_ifs
      exact (hA q ω hP).trans heq.symm
  obtain ⟨g, hgm, hg⟩ := exists_measurable_version_of_thresholds P f C hC
    (fun ω _ => hf ω) B hBm hB
  exact ⟨g, hgm, fun ω h₁ h₂ h₃ h₄ => hg ω ⟨h₁, h₂, h₃, h₄⟩⟩

end MatedCRT
