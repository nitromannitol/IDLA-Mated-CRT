import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells
import MatedCRT.Defs.Setting

/-! A cell of an area-parametrized proper curve has a representative whose
least containing cell is the cell itself. -/

namespace MatedCRT

open Filter Topology Set MeasureTheory

theorem exists_vertexOf_eq_of_area_parametrized {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (a : ℤ) : ∃ x ∈ cell ε η a, vertexOf ε η x = a := by
  let p : ℝ := ε * ((a : ℝ) - 1)
  let q : ℝ := ε * (a : ℝ)
  have hpq : p < q := by dsimp [p, q]; nlinarith
  have hbounded : Bornology.IsBounded (cell ε η a) :=
    (isCompact_Icc.image hη.1).isBounded
  obtain ⟨T, hT⟩ := Tightness.exists_time_bound hη.1 hp hbounded
  let s : ℝ := min (-T - 1) (p - 1)
  have hsp : s < p := by dsimp [s]; linarith [min_le_right (-T - 1) (p - 1)]
  have htime : ∀ v, η v ∈ cell ε η a → s ≤ v := by
    intro v hv
    have ht := hT v hv
    have hs : s ≤ -T - 1 := min_le_left _ _
    linarith [neg_abs_le v]
  have hex : ∃ x ∈ cell ε η a, ∀ b : ℤ, b < a → x ∉ cell ε η b := by
    by_contra h
    push Not at h
    have hBA : cell ε η a ⊆ η '' Icc s p := by
      intro x hx
      obtain ⟨b, hba, hxb⟩ := h x hx
      obtain ⟨v, hv, hvx⟩ := hxb
      have hcast : (b : ℝ) ≤ (a : ℝ) - 1 := by
        have hi : b ≤ a - 1 := by omega
        exact_mod_cast hi
      have hmul := mul_le_mul_of_nonneg_left hcast hε.le
      have hvle : v ≤ p := hv.2.trans hmul
      refine ⟨v, ⟨htime v ?_, hvle⟩, hvx⟩
      rwa [hvx]
    have hwhole : η '' Icc s q ⊆ η '' Icc s p := by
      rintro x ⟨v, ⟨hsv, hvq⟩, rfl⟩
      by_cases hvp : v ≤ p
      · exact ⟨v, ⟨hsv, hvp⟩, rfl⟩
      · apply hBA
        exact ⟨v, ⟨le_of_not_ge hvp, hvq⟩, rfl⟩
    have hm : μ (η '' Icc s q) ≤ μ (η '' Icc s p) := measure_mono hwhole
    rw [hη.2.2.2 s q (lt_trans hsp hpq), hη.2.2.2 s p hsp] at hm
    have hm' := (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ p - s)).1 hm
    linarith
  obtain ⟨x, hx, hmin⟩ := hex
  refine ⟨x, hx, ?_⟩
  have hleast : IsLeast {k : ℤ | x ∈ cell ε η k} a := by
    refine ⟨hx, ?_⟩
    intro b hb
    by_contra hba
    exact hmin b (lt_of_not_ge hba) hb
  exact hleast.csInf_eq

theorem exists_rescale_eq_at_cell_of_area_parametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    {ε : ℝ} (hη : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (a : ℤ) (mε : ℝ) (u : ℤ → ℝ) :
    ∃ x ∈ cell ε η a, rescale mε ε η u x = mε⁻¹ * u a := by
  obtain ⟨x, hx, hxa⟩ := exists_vertexOf_eq_of_area_parametrized hη hp hε a
  exact ⟨x, hx, by simp [rescale, hxa]⟩

end MatedCRT
