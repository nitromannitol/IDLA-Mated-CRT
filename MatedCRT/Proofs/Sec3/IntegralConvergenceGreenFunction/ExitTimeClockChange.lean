import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.RatClockInverse

/-!
# Lemma 3.4 (item 3): exit times of time-changed paths

For a continuous, strictly increasing, unbounded clock `C` with `C 0 = 0`, the clock inverse `clockInverse C` (the
right-continuous inverse `inf {s | u < C s}`) satisfies the threshold rules `clockInverse C u ≤ σ ↔ u ≤ C σ` and
`clockInverse C u < σ ← u < C σ`. For a path `b` and an open set `B`, the first exit time of the time-changed path
`t ↦ b (clockInverse C (c * t))` is the image under the inverse time change of the first exit time of `b`
(`pathExitTime_comp`). These give the indicator of the truncated path integrals (Lemma 3.4, Truncation.lean:26).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- **Threshold of the clock inverse.** For a continuous, strictly increasing, unbounded clock `C`, `clockInverse C u ≤ σ`
if and only if `u ≤ C σ`. -/
lemma clockInverse_le_iff {C : ℝ≥0 → ℝ} (hC : Continuous C) (hmono : StrictMono C)
    (hunb : ∀ M : ℝ, ∃ s : ℝ≥0, M < C s) (u σ : ℝ≥0) :
    clockInverse C u ≤ σ ↔ (u : ℝ) ≤ C σ := by
  have hne : {s : ℝ≥0 | (u : ℝ) < C s}.Nonempty := by
    obtain ⟨s, hs⟩ := hunb u
    exact ⟨s, hs⟩
  constructor
  · intro h
    unfold clockInverse at h
    by_contra hlt0
    have hlt : C σ < u := not_le.1 hlt0
    have hopen : IsOpen {x : ℝ≥0 | C x < u} := isOpen_lt hC continuous_const
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen σ hlt
    have hδ' : (0 : ℝ≥0) < δ.toNNReal := Real.toNNReal_pos.2 hδ
    have hlt2 : sInf {s : ℝ≥0 | (u : ℝ) < C s} < σ + δ.toNNReal :=
      lt_of_le_of_lt h (lt_add_of_pos_right _ hδ')
    obtain ⟨s, hs, hs2⟩ := exists_lt_of_csInf_lt hne hlt2
    have hs' : (u : ℝ) < C s := hs
    have hσs : σ ≤ s := by
      by_contra hs3
      have hs3' : s < σ := not_le.1 hs3
      have h1 : C s ≤ C σ := hmono.monotone hs3'.le
      linarith
    have hmem : s ∈ Metric.ball σ δ := by
      rw [Metric.mem_ball, NNReal.dist_eq, abs_sub_lt_iff]
      have h4 := NNReal.coe_lt_coe.2 hs2
      rw [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at h4
      have h5 : (σ : ℝ) ≤ (s : ℝ) := NNReal.coe_le_coe.2 hσs
      constructor <;> linarith
    have h6 : C s < u := hball hmem
    linarith
  · intro h
    unfold clockInverse
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hlt : (u : ℝ) < C (σ + ε) := lt_of_le_of_lt h (hmono (lt_add_of_pos_right σ hε))
    exact csInf_le (OrderBot.bddBelow _) hlt

/-- **Strict threshold of the clock inverse.** If `u < C σ` then `clockInverse C u < σ`. -/
lemma clockInverse_lt_of_lt_clock {C : ℝ≥0 → ℝ} (hC : Continuous C) (h0 : C 0 = 0) (u σ : ℝ≥0)
    (h : (u : ℝ) < C σ) : clockInverse C u < σ := by
  have hσ : 0 < σ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ σ) with h' | h'
    · subst h'
      rw [h0] at h
      have : (0 : ℝ) ≤ (u : ℝ) := u.2
      linarith
    · exact h'
  have hev : ∀ᶠ x in 𝓝[<] σ, (u : ℝ) < C x :=
    nhdsWithin_le_nhds (Filter.Tendsto.eventually_const_lt h (hC.tendsto σ))
  have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ⟩
  obtain ⟨s, hs1, hs2⟩ := (hev.and self_mem_nhdsWithin).exists
  unfold clockInverse
  exact lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hs1) hs2

/-- **Inverse of the clock at its values.** `clockInverse C` inverts `C` on `ℝ≥0`. -/
lemma clockInverse_clock_eq {C : ℝ≥0 → ℝ} (hC : Continuous C) (hmono : StrictMono C)
    (hunb : ∀ M : ℝ, ∃ s : ℝ≥0, M < C s) (u s : ℝ≥0) (hu : (u : ℝ) = C s) :
    clockInverse C u = s := by
  apply le_antisymm
  · exact (clockInverse_le_iff hC hmono hunb u s).2 hu.le
  · by_contra hlt0
    have hlt : clockInverse C u < s := not_le.1 hlt0
    have h1 : (u : ℝ) ≤ C (clockInverse C u) := (clockInverse_le_iff hC hmono hunb u _).1 le_rfl
    have h2 : C (clockInverse C u) < C s := hmono hlt
    linarith

/-- The time-changed clock inverse `s ↦ clockInverse C (c * s)` is strictly increasing. -/
lemma strictMono_clockInverse_comp {C : ℝ≥0 → ℝ} (hC : Continuous C) (hmono : StrictMono C) (h0 : C 0 = 0)
    (hunb : ∀ M : ℝ, ∃ s : ℝ≥0, M < C s) {c : ℝ≥0} (hc : 0 < c) :
    StrictMono fun s : ℝ≥0 => clockInverse C (c * s) := by
  intro s s' hss'
  have hlt : c * s < c * s' := mul_lt_mul_of_pos_left hss' hc
  have h1 : ((c * s' : ℝ≥0) : ℝ) ≤ C (clockInverse C (c * s')) :=
    (clockInverse_le_iff hC hmono hunb _ _).1 le_rfl
  exact clockInverse_lt_of_lt_clock hC h0 _ _ (lt_of_lt_of_le (NNReal.coe_lt_coe.2 hlt) h1)

/-- The first exit time of a path from an open set is attained: if it is finite, the path lies outside the set at
that time. -/
lemma pathExitTime_attained {B : Set ℂ} (hB : IsOpen B) (b : ContinuousPath ℂ) {σ : ℝ≥0}
    (hσ : pathExitTime B b = (σ : ℝ≥0∞)) : b σ ∉ B := by
  have hcl : IsClosed {t : ℝ≥0 | b t ∉ B} := hB.isClosed_compl.preimage b.continuous
  have hne : {t : ℝ≥0 | b t ∉ B}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have htop : pathExitTime B b = ⊤ := by
      unfold pathExitTime
      rw [sInf_eq_top]
      rintro x ⟨t, rfl, ht⟩
      have hmem : t ∈ ({t : ℝ≥0 | b t ∉ B} : Set ℝ≥0) := ht
      rw [hne] at hmem
      exact hmem.elim
    rw [htop] at hσ
    exact ENNReal.coe_ne_top hσ.symm
  have hval : pathExitTime B b = ((sInf {t : ℝ≥0 | b t ∉ B} : ℝ≥0) : ℝ≥0∞) := by
    unfold pathExitTime
    apply le_antisymm
    · apply sInf_le
      exact ⟨sInf {t : ℝ≥0 | b t ∉ B}, rfl, hcl.csInf_mem hne (OrderBot.bddBelow _)⟩
    · refine le_sInf ?_
      rintro x ⟨t, rfl, ht⟩
      exact ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) ht)
  rw [hval] at hσ
  have hσeq : sInf {t : ℝ≥0 | b t ∉ B} = σ := ENNReal.coe_injective hσ
  rw [← hσeq]
  exact hcl.csInf_mem hne (OrderBot.bddBelow _)

/-- **Exit time of a time-changed path.** If `ψ` is strictly increasing and `φ` is its inverse, the first exit time of
`t ↦ b (ψ t)` from an open set is `φ` of the first exit time of `b` (and `⊤` if `b` never exits). -/
lemma pathExitTime_comp {B : Set ℂ} (hB : IsOpen B) (b : ContinuousPath ℂ) {ψ φ : ℝ≥0 → ℝ≥0}
    (hψ : StrictMono ψ) (hφ : ∀ s, ψ (φ s) = s) :
    pathExitTime B (fun t => b (ψ t)) =
      if pathExitTime B b = ⊤ then ⊤ else ((φ (pathExitTime B b).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  split_ifs with hσ
  · unfold pathExitTime
    rw [sInf_eq_top]
    rintro x ⟨t, rfl, ht⟩
    have h1 : pathExitTime B b ≤ ((ψ t : ℝ≥0) : ℝ≥0∞) := sInf_le ⟨ψ t, rfl, ht⟩
    rw [hσ] at h1
    exact absurd h1 (by simp)
  · set σ := (pathExitTime B b).toNNReal with hσdef
    have hσ' : pathExitTime B b = (σ : ℝ≥0∞) := (ENNReal.coe_toNNReal hσ).symm
    have hat : b σ ∉ B := pathExitTime_attained hB b hσ'
    apply le_antisymm
    · apply sInf_le
      exact ⟨φ σ, rfl, by simp only [hφ σ]; exact hat⟩
    · refine le_sInf ?_
      rintro x ⟨t, rfl, ht⟩
      have hle : φ σ ≤ t := by
        by_contra hlt0
        have hlt : t < φ σ := not_le.1 hlt0
        have h1 : ψ t < σ := by
          have := hψ hlt
          rw [hφ σ] at this
          exact this
        have h2 : pathExitTime B b ≤ ((ψ t : ℝ≥0) : ℝ≥0∞) := sInf_le ⟨ψ t, rfl, ht⟩
        rw [hσ'] at h2
        exact absurd (ENNReal.coe_le_coe.1 h2) (not_le.2 h1)
      exact ENNReal.coe_le_coe.2 hle

/-- **Truncation indicator of a time-changed path.** For `0 < t` the time `t` is at most the first exit time of
`t ↦ b (clockInverse C (c * t))` if and only if the path has exited (`pathExitTime B b ≠ ⊤`) and `clockInverse C (c * t)`
is at most the first exit time `σ` of `b`. -/
lemma le_toReal_exitTime_comp {B : Set ℂ} (hB : IsOpen B) (b : ContinuousPath ℂ) {C : ℝ≥0 → ℝ}
    (hC : Continuous C) (hmono : StrictMono C) (h0 : C 0 = 0) (hunb : ∀ M : ℝ, ∃ s : ℝ≥0, M < C s)
    {c : ℝ≥0} (hc : 0 < c) {t : ℝ≥0} (ht : 0 < t) :
    (t : ℝ) ≤ (pathExitTime B (fun s => b (clockInverse C (c * s)))).toReal ↔
      (pathExitTime B b ≠ ⊤ ∧ clockInverse C (c * t) ≤ (pathExitTime B b).toNNReal) := by
  have hψ : StrictMono (fun s : ℝ≥0 => clockInverse C (c * s)) :=
    strictMono_clockInverse_comp hC hmono h0 hunb hc
  have hCnn : ∀ s : ℝ≥0, (0 : ℝ) ≤ C s := fun s => by
    have h1 : C 0 ≤ C s := hmono.monotone (zero_le : (0 : ℝ≥0) ≤ s)
    rw [h0] at h1
    exact h1
  have hφ : ∀ s : ℝ≥0, clockInverse C (c * ((C s).toNNReal / c)) = s := by
    intro s
    rw [mul_div_cancel₀ _ hc.ne']
    exact clockInverse_clock_eq hC hmono hunb _ s (Real.coe_toNNReal _ (hCnn s))
  have hE := pathExitTime_comp (ψ := fun s : ℝ≥0 => clockInverse C (c * s))
    (φ := fun s : ℝ≥0 => (C s).toNNReal / c) hB b hψ hφ
  rw [hE]
  split_ifs with hσ
  · have hpos : (0 : ℝ) < t := NNReal.coe_pos.2 ht
    rw [ENNReal.toReal_top]
    constructor
    · intro h
      linarith
    · intro h
      exact absurd hσ h.1
  · have h1 := hψ.le_iff_le (a := t) (b := (C (pathExitTime B b).toNNReal).toNNReal / c)
    simp only [hφ] at h1
    rw [ENNReal.coe_toReal, NNReal.coe_le_coe]
    constructor
    · intro h
      exact ⟨hσ, h1.symm.mp h⟩
    · intro h
      exact h1.symm.mpr h.2

end MatedCRT
