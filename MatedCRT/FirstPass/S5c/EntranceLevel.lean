import MatedCRT.FirstPass.S5c.EntranceAtoms

/-!
# FIRST PASS, 5.1 stopped clause: measurability of the entrance-time level sets (Gap 2 insertion, `hentr`)

Operator ruling 21:25 UTC: `hentr` is NEW (Gap 2 of CHATGPT-G-hT-G-stopped.md), to be proved, never frozen. Pathwise, for a
monotone family `Λ` of open sets and a rational closed disk `C`, the entrance time `τ_C = inf {s > 0 : C ⊆ Λ_s}` equals a
positive time `t` iff no rational `q ∈ (0, t)` has `C ⊆ Λ_q` and every rational `s > t` has `C ⊆ Λ_s`. Hence the level set
`{τ_C = t}` is a countable intersection of containment events at rational times, and it is measurable as soon as those
containment events are (the decoder input of Gap 2: rational containment tests measurable under the environment law;
AE/null-measurable versions acceptable per the ruling). Deterministic set theory plus countable intersections.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- **Pathwise characterisation of the entrance level**: for a monotone family and `t > 0`, `τ_C = t` iff no rational earlier
time contains `C` and every rational later time contains `C`. -/
theorem entranceTime_eq_iff {Λ : ℝ → Set ℂ} {C : Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : MonotoneOn Λ (Ioi 0)) :
    entranceTime Λ C = t ↔
      ((∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ (q : ℝ)) ∧
        (∀ s : ℚ, t < (s : ℝ) → C ⊆ Λ (s : ℝ))) := by
  constructor
  · intro h
    unfold entranceTime at h
    have hne : {s : ℝ | 0 < s ∧ C ⊆ Λ s}.Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      rw [hem, Real.sInf_empty] at h
      exact ht.ne h
    have hbdd : BddBelow {s : ℝ | 0 < s ∧ C ⊆ Λ s} := ⟨0, fun s hs => hs.1.le⟩
    constructor
    · intro q hq0 hqt hCq
      have hmem : (q : ℝ) ∈ {s : ℝ | 0 < s ∧ C ⊆ Λ s} := ⟨hq0, hCq⟩
      have hle := csInf_le hbdd hmem
      rw [h] at hle
      linarith
    · intro s hs
      obtain ⟨x, hx, hxs⟩ := exists_lt_of_csInf_lt hne (show sInf {s : ℝ | 0 < s ∧ C ⊆ Λ s} < (s : ℝ) by
        rw [h]; exact hs)
      exact fun y hy => hmono (mem_Ioi.2 hx.1) (mem_Ioi.2 (lt_trans hx.1 hxs)) hxs.le (hx.2 hy)
  · rintro ⟨h1, h2⟩
    unfold entranceTime
    obtain ⟨q0, hq0⟩ := exists_rat_gt t
    have hq0pos : (0 : ℝ) < (q0 : ℝ) := lt_trans ht hq0
    have hne : {s : ℝ | 0 < s ∧ C ⊆ Λ s}.Nonempty := ⟨(q0 : ℝ), hq0pos, h2 q0 hq0⟩
    have hbdd : BddBelow {s : ℝ | 0 < s ∧ C ⊆ Λ s} := ⟨0, fun s hs => hs.1.le⟩
    apply le_antisymm
    · by_contra hgt0
      have hgt := not_le.1 hgt0
      obtain ⟨s, hts, hslt⟩ := exists_rat_btwn hgt
      have hspos : (0 : ℝ) < (s : ℝ) := lt_trans ht hts
      have hmemS : (s : ℝ) ∈ {s : ℝ | 0 < s ∧ C ⊆ Λ s} := ⟨hspos, h2 s hts⟩
      have hle := csInf_le hbdd hmemS
      linarith
    · by_contra hlt0
      have hlt := not_le.1 hlt0
      obtain ⟨x, hx, hxt⟩ := exists_lt_of_csInf_lt hne hlt
      obtain ⟨q, hxq, hqt⟩ := exists_rat_btwn hxt
      exact h1 q (lt_trans hx.1 hxq) hqt
        (fun y hy => hmono (mem_Ioi.2 hx.1) (mem_Ioi.2 (lt_trans hx.1 hxq)) hxq.le (hx.2 hy))

/-- **Measurability of the entrance level sets** (`hentr`, Gap 2 insertion): if the containment events `{C ⊆ Λ_q}` at
rational times are measurable, then `{ω | τ_C(Λ ω) = t}` is measurable for each `t > 0`. -/
theorem measurableSet_entranceLevel {Ω : Type*} [MeasurableSpace Ω] {Λ : Ω → ℝ → Set ℂ} {C : Set ℂ} {t : ℝ}
    (ht : 0 < t) (hmono : ∀ ω, MonotoneOn (Λ ω) (Ioi 0))
    (hC : ∀ q : ℚ, MeasurableSet {ω | C ⊆ Λ ω (q : ℝ)}) :
    MeasurableSet {ω | entranceTime (Λ ω) C = t} := by
  have hset : {ω | entranceTime (Λ ω) C = t} =
      (⋂ q : ℚ, {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ ω (q : ℝ)}) ∩
        (⋂ s : ℚ, {ω | t < (s : ℝ) → C ⊆ Λ ω (s : ℝ)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact entranceTime_eq_iff ht (hmono ω)
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun q => ?_) (MeasurableSet.iInter fun s => ?_)
  · by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) < t
    · have e : {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ ω (q : ℝ)} = {ω | C ⊆ Λ ω (q : ℝ)}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, h.1, h.2, true_implies]
      rw [e]
      exact (hC q).compl
    · have e : {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ ω (q : ℝ)} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h1 h2
        exact absurd ⟨h1, h2⟩ h
      rw [e]
      exact MeasurableSet.univ
  · by_cases h : t < (s : ℝ)
    · have e : {ω | t < (s : ℝ) → C ⊆ Λ ω (s : ℝ)} = {ω | C ⊆ Λ ω (s : ℝ)} := by
        ext ω
        simp only [mem_ofPred_eq, h, true_implies]
      rw [e]
      exact hC s
    · have e : {ω | t < (s : ℝ) → C ⊆ Λ ω (s : ℝ)} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h'
        exact absurd h' h
      rw [e]
      exact MeasurableSet.univ

/-- Countably many positive atoms of the entrance-time laws, for positive times only (the level sets are measurable for
`t > 0`, and the events for `t ≤ 0` are empty). -/
theorem countable_positive_entrance_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → ℝ} (hτ : ∀ t : ℝ, 0 < t → MeasurableSet {ω | τ ω = t}) :
    {t : ℝ | 0 < P {ω | 0 < t ∧ τ ω = t}}.Countable := by
  have hmeas : ∀ t : ℝ, MeasurableSet {ω | 0 < t ∧ τ ω = t} := fun t => by
    by_cases ht : 0 < t
    · have e : {ω | 0 < t ∧ τ ω = t} = {ω | τ ω = t} := by
        ext ω
        simp only [mem_ofPred_eq, ht, true_and]
      rw [e]
      exact hτ t ht
    · have e : {ω | 0 < t ∧ τ ω = t} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => ht h.1
      rw [e]
      exact MeasurableSet.empty
  have hdisj : Pairwise (fun t t' : ℝ => Disjoint {ω | 0 < t ∧ τ ω = t} {ω | 0 < t' ∧ τ ω = t'}) := by
    intro t t' htt'
    refine Set.disjoint_left.2 ?_
    intro ω h1 h2
    exact htt' (h1.2.symm.trans h2.2)
  exact Measure.countable_meas_pos_of_disjoint_iUnion hmeas hdisj

/-- **Fixed-deterministic-time null event from rational containment** (Gap 1 repair with `hentr` PROVED from the rational
containment events, Gap 2): the new-mass event at a fixed time `t > 0` is null, given that the containment events
`{C ⊆ Λ_q}` at rational disks `C` and rational times `q` are measurable and the scaling `hscale` (Draft Lemma 2.6 transport). -/
theorem newMass_null_of_rational_containment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Λ : Ω → ℝ → Set ℂ}
    (hmono : ∀ ω, MonotoneOn (Λ ω) (Ioi 0)) (hopen : ∀ ω, ∀ s : ℝ, 0 < s → IsOpen (Λ ω s))
    (hC : ∀ (c : ℚ × ℚ) (r q : ℚ), MeasurableSet {ω | ratDisk c r ⊆ Λ ω (q : ℝ)})
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P {ω | NewMassAt (Λ ω) (b * t)} = P {ω | NewMassAt (Λ ω) t})
    (t : ℝ) (ht : 0 < t) : P {ω | NewMassAt (Λ ω) t} = 0 := by
  set E' : ℝ → Set Ω := fun s => {ω | 0 < s ∧ NewMassAt (Λ ω) s} with hE'
  have hscale' : ∀ b s : ℝ, 0 < b → 0 < s → P (E' (b * s)) = P (E' s) := by
    intro b s hb hs
    have e1 : E' (b * s) = {ω | NewMassAt (Λ ω) (b * s)} := by
      ext ω
      exact ⟨fun h => h.2, fun h => ⟨mul_pos hb hs, h⟩⟩
    have e2 : E' s = {ω | NewMassAt (Λ ω) s} := by
      ext ω
      exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
    rw [e1, e2, hscale b s hb hs]
  have hcount : {s : ℝ | 0 < P (E' s)}.Countable := by
    have hsub : {s : ℝ | 0 < P (E' s)} ⊆
        ⋃ i : (ℚ × ℚ) × ℚ, {s : ℝ | 0 < P {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s}} := by
      intro s hs
      by_contra hno
      have hnull : ∀ i : (ℚ × ℚ) × ℚ, P {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s} = 0 := by
        intro i
        by_contra hi
        exact hno (mem_iUnion.2 ⟨i, pos_iff_ne_zero.2 hi⟩)
      have hcovs : E' s ⊆ ⋃ i : (ℚ × ℚ) × ℚ, {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s} := by
        rintro ω ⟨hs0, hNA⟩
        obtain ⟨c, r, hτ⟩ := exists_entrance_eq_of_newMass hs0 (hmono ω) (hopen ω) hNA
        exact mem_iUnion.2 ⟨(c, r), hs0, hτ⟩
      have hle : P (E' s) ≤
          P (⋃ i : (ℚ × ℚ) × ℚ, {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s}) :=
        measure_mono hcovs
      have h0 : P (⋃ i : (ℚ × ℚ) × ℚ, {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s}) = 0 :=
        measure_iUnion_null hnull
      have hs' : 0 < P (E' s) := hs
      exact (not_le.2 hs') (hle.trans_eq h0)
    exact Set.Countable.mono hsub (Set.countable_iUnion fun i =>
      countable_positive_entrance_pos P (fun t' ht' =>
        measurableSet_entranceLevel ht' hmono (fun q => hC i.1 i.2 q)))
  have heq : E' t = {ω | NewMassAt (Λ ω) t} := by
    ext ω
    exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
  rw [← heq]
  exact null_of_scale_invariant P E' hscale' hcount t ht

end MatedCRT.S5c
