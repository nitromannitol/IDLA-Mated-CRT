import MatedCRT.Defs.Setting

/-!
# Intersections of events of polynomially high probability

If `E_r` and `F_r` hold with polynomially high probability as `r → 0` and, almost surely, `E_r ∩ F_r ⊆ G_r` for all
`r ∈ (0, r₁)`, then `G_r` holds with polynomially high probability (`polyHighProb_of_inter_ae`).
-/

namespace MatedCRT.Sec7

open MeasureTheory Set HarmonicBalls

theorem polyHighProb_of_inter_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E F G : ℝ → Set Ω}
    (hE : PolyHighProb P E) (hF : PolyHighProb P F) {q : Ω → Prop} (hq : ∀ᵐ ω ∂P, q ω) {r₁ : ℝ}
    (hr₁ : 0 < r₁) (h : ∀ r : ℝ, 0 < r → r < r₁ → ∀ ω, ω ∈ E r → ω ∈ F r → q ω → ω ∈ G r) :
    PolyHighProb P G := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  obtain ⟨p', hp', C', r₀', hr₀', hb'⟩ := hF
  refine ⟨min p p', lt_min hp hp', |C| + |C'|, min (min r₀ r₀') (min r₁ 1),
    lt_min (lt_min hr₀ hr₀') (lt_min hr₁ one_pos), fun r hr hrr => ?_⟩
  have hr0 : r < r₀ := hrr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hr0' : r < r₀' := hrr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr1 : r < r₁ := hrr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr1' : r ≤ 1 := (hrr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hq0 : P {ω | ¬ q ω} = 0 := ae_iff.1 hq
  have hpow : ∀ a : ℝ, min p p' ≤ a → ∀ K : ℝ, K * r ^ a ≤ |K| * r ^ min p p' := fun a ha K =>
    (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hr.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1' ha) (abs_nonneg K))
  calc P (G r)ᶜ ≤ P ((E r)ᶜ ∪ (F r)ᶜ ∪ {ω | ¬ q ω}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hc
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hc
        exact hω (h r hr hr1 ω hc.1.1 hc.1.2 hc.2)
    _ ≤ P (E r)ᶜ + P (F r)ᶜ + P {ω | ¬ q ω} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (C * r ^ p) + ENNReal.ofReal (C' * r ^ p') + 0 := by
        rw [hq0]
        exact add_le_add (add_le_add (hb r hr hr0) (hb' r hr hr0')) le_rfl
    _ ≤ ENNReal.ofReal (|C| * r ^ min p p') + ENNReal.ofReal (|C'| * r ^ min p p') := by
        rw [add_zero]
        exact add_le_add (ENNReal.ofReal_le_ofReal (hpow p (min_le_left _ _) C))
          (ENNReal.ofReal_le_ofReal (hpow p' (min_le_right _ _) C'))
    _ = ENNReal.ofReal ((|C| + |C'|) * r ^ min p p') := by
        rw [add_mul, ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hr.le _))
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hr.le _))]

end MatedCRT.Sec7
