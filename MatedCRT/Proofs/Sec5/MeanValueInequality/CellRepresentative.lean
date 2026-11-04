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

/-- Transfer two uniform approximation bounds and a continuum lower bound
to a lower bound for the corresponding weighted sum at a graph vertex. -/
theorem weighted_vertex_lower_of_uniform_bounds {μ : Measure ℂ} {η : ℝ → ℂ}
    {ε : ℝ} (hη : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (a : ℤ) (mε t L e₁ e₂ : ℝ) (u v : ℤ → ℝ) (f g : ℂ → ℝ) (O : Set ℂ)
    (ht : 0 ≤ t) (hcell : cell ε η a ⊆ O)
    (hf : ∀ x ∈ O, |rescale mε ε η u x - f x| ≤ e₁)
    (hg : ∀ x ∈ O, |rescale mε ε η v x - g x| ≤ e₂)
    (hlower : ∀ x ∈ O, L ≤ f x + t * g x) :
    L - e₁ - t * e₂ ≤ mε⁻¹ * (u a + t * v a) := by
  obtain ⟨x, hx, hxa⟩ := exists_vertexOf_eq_of_area_parametrized hη hp hε a
  have hxO := hcell hx
  have hf' := (abs_le.mp (hf x hxO)).1
  have hg' := (abs_le.mp (hg x hxO)).1
  have hl := hlower x hxO
  simp only [rescale, hxa] at hf' hg'
  nlinarith

/-- The lower median scaling converts the normalized estimate into a bound
of order `ε⁻¹` for the unscaled weighted sum. -/
theorem weighted_vertex_lower_div_epsilon {μ : Measure ℂ} {η : ℝ → ℂ}
    {ε : ℝ} (hη : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (a : ℤ) (mε t L e₁ e₂ C : ℝ) (u v : ℤ → ℝ) (f g : ℂ → ℝ) (O : Set ℂ)
    (ht : 0 ≤ t) (hC : 0 < C) (hscale : C⁻¹ * ε⁻¹ ≤ mε)
    (hmargin : 0 ≤ L - e₁ - t * e₂) (hcell : cell ε η a ⊆ O)
    (hf : ∀ x ∈ O, |rescale mε ε η u x - f x| ≤ e₁)
    (hg : ∀ x ∈ O, |rescale mε ε η v x - g x| ≤ e₂)
    (hlower : ∀ x ∈ O, L ≤ f x + t * g x) :
    (L - e₁ - t * e₂) / C / ε ≤ u a + t * v a := by
  have hm : 0 < mε :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hC) (inv_pos.mpr hε)) hscale
  have hnormalized := weighted_vertex_lower_of_uniform_bounds hη hp hε a mε t L e₁ e₂
    u v f g O ht hcell hf hg hlower
  have hunscaled : (L - e₁ - t * e₂) * mε ≤ u a + t * v a := by
    apply (le_div_iff₀ hm).mp
    simpa [div_eq_mul_inv, mul_comm] using hnormalized
  have hscaled := mul_le_mul_of_nonneg_left hscale hmargin
  have : (L - e₁ - t * e₂) / C / ε ≤ (L - e₁ - t * e₂) * mε := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact this.trans hunscaled

/-- If the marked point is not visited before time zero, its least
containing cell is the cell indexed by zero. -/
theorem vertexOf_zero_of_no_earlier_visit {η : ℝ → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hzero : η 0 = 0)
    (hprev : ∀ s : ℝ, s < 0 → η s ≠ 0) : vertexOf ε η 0 = 0 := by
  have hleast : IsLeast {k : ℤ | (0 : ℂ) ∈ cell ε η k} 0 := by
    constructor
    · exact ⟨0, ⟨by simp; linarith, by simp⟩, hzero⟩
    · intro b hb
      by_contra hn
      have hbneg : b < 0 := lt_of_not_ge hn
      obtain ⟨s, hs, hs0⟩ := hb
      have hbneg' : (b : ℝ) < 0 := by exact_mod_cast hbneg
      have hsneg : s < 0 := lt_of_le_of_lt hs.2 (mul_neg_of_pos_of_neg hε hbneg')
      exact hprev s hsneg hs0
  exact hleast.csInf_eq

end MatedCRT
