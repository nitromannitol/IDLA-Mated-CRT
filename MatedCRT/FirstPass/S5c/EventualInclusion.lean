import MatedCRT.FirstPass.S5c.InclusionCode

/-!
# FIRST PASS, Lemma 5.3 (three-inputs §2.4): inclusion events along an eventually-large radius

For a family of open sets `S n ω` (the clusters `cluster (μ ω) n 0 t` at radius `n : ℕ`) whose interior closures
eventually equal the target set `Λ ω` (Theorem 2.3(c) at radius `n`, for `n` larger than a bound of `Λ ω`), the
event `{ω | C ⊆ Λ ω}` is null measurable for a compact `C`, although the openness of `S n ω` is only known
eventually in `n` (never almost surely at a fixed radius). The proof expresses the event through the countable
`D`-test form (`inclBall_iff_dense`, `inclCompact_iff_cover`) at each radius, which is null measurable from the point
events alone, and then takes `⋃ N ⋂ n ≥ N`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- The countable `D`-test form of `ball c r ⊆ interior (closure (S ω))`: a countable Boolean combination of the
point events `{ω | d ∈ S ω}`, `d ∈ D` (no openness needed to state it). -/
theorem nullMeasurableSet_ballTest {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Set ℂ} (hDc : D.Countable) {S : Ω → Set ℂ}
    (hpt : ∀ d ∈ D, NullMeasurableSet {ω | d ∈ S ω} P) (c : ℂ) (r : ℝ) :
    NullMeasurableSet {ω | ∀ q ∈ D ∩ ball c r, ∀ n : ℕ,
      ∃ p ∈ D ∩ S ω, dist p q < 1 / ((n : ℝ) + 1)} P := by
  have hDc' : Countable D := hDc.to_subtype
  have : Countable (D ∩ ball c r : Set ℂ) := (hDc.mono inter_subset_left).to_subtype
  have hset : {ω | ∀ q ∈ D ∩ ball c r, ∀ n : ℕ,
      ∃ p ∈ D ∩ S ω, dist p q < 1 / ((n : ℝ) + 1)} =
      ⋂ q : ↥(D ∩ ball c r), ⋂ n : ℕ, ⋃ p : D,
        ({ω | dist (p : ℂ) (q : ℂ) < 1 / ((n : ℝ) + 1)} ∩ {ω | (p : ℂ) ∈ S ω}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff] at *
    constructor
    · intro h q n
      obtain ⟨p, ⟨hpD, hpS⟩, hd⟩ := h q.1 q.2 n
      exact ⟨⟨p, hpD⟩, hd, hpS⟩
    · intro h q hq n
      obtain ⟨p, hd, hpS⟩ := h ⟨q, hq⟩ n
      exact ⟨p.1, ⟨p.2, hpS⟩, hd⟩
  rw [hset]
  refine NullMeasurableSet.iInter fun q => NullMeasurableSet.iInter fun n =>
    NullMeasurableSet.iUnion fun p => ?_
  exact (MeasurableSet.const _).nullMeasurableSet.inter (hpt p p.2)

/-- Eventual-radius compact inclusion: if `S n ω` is open and `Λ ω = interior (closure (S n ω))` for all `n` large
(depending on `ω`), then `{ω | C ⊆ Λ ω}` is null measurable for compact `C`. -/
theorem nullMeasurableSet_inclCompact_eventually {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Set ℂ} (hDc : D.Countable) (hD : Dense D) {S : ℕ → Ω → Set ℂ} {Λ : Ω → Set ℂ}
    (hpt : ∀ n : ℕ, ∀ d ∈ D, NullMeasurableSet {ω | d ∈ S n ω} P)
    (heq : ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsOpen (S n ω) ∧ Λ ω = interior (closure (S n ω)))
    {C : Set ℂ} (hC : IsCompact C) :
    NullMeasurableSet {ω | C ⊆ Λ ω} P := by
  classical
  have hDc' : Countable D := hDc.to_subtype
  -- the D-test event of the cover by codeBalls at radius n
  set G : ℕ → Set Ω := fun n => {ω | ∃ F : Finset (D × ℕ), (C ⊆ ⋃ i ∈ F, codeBall D i) ∧
    ∀ i ∈ F, ∀ q ∈ D ∩ codeBall D i, ∀ k : ℕ, ∃ p ∈ D ∩ S n ω, dist p q < 1 / ((k : ℝ) + 1)} with hGdef
  have hGmeas : ∀ n, NullMeasurableSet (G n) P := by
    intro n
    have hunion : G n = ⋃ F : Finset (D × ℕ), {ω | (C ⊆ ⋃ i ∈ F, codeBall D i) ∧
        ∀ i ∈ F, ∀ q ∈ D ∩ codeBall D i, ∀ k : ℕ, ∃ p ∈ D ∩ S n ω, dist p q < 1 / ((k : ℝ) + 1)} := by
      ext ω
      simp only [hGdef, mem_ofPred_eq, mem_iUnion]
    rw [hunion]
    refine NullMeasurableSet.iUnion fun F => ?_
    rw [Set.ofPred_and]
    refine (MeasurableSet.const _).nullMeasurableSet.inter ?_
    have hF : {ω | ∀ i ∈ F, ∀ q ∈ D ∩ codeBall D i, ∀ k : ℕ, ∃ p ∈ D ∩ S n ω, dist p q < 1 / ((k : ℝ) + 1)} =
        ⋂ i : F, {ω | ∀ q ∈ D ∩ codeBall D i.1, ∀ k : ℕ, ∃ p ∈ D ∩ S n ω, dist p q < 1 / ((k : ℝ) + 1)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h i => h i.1 i.2, fun h i hi => h ⟨i, hi⟩⟩
    rw [hF]
    exact NullMeasurableSet.iInter fun i => nullMeasurableSet_ballTest hDc (hpt n) _ _
  -- pointwise: on open S n ω, the D-test event is the inclusion event
  have key : ∀ n : ℕ, ∀ ω : Ω, IsOpen (S n ω) → (ω ∈ G n ↔ C ⊆ interior (closure (S n ω))) := by
    intro n ω hopen
    rw [inclCompact_iff_cover hD hC]
    simp only [hGdef, mem_ofPred_eq]
    constructor
    · rintro ⟨F, hcov, hF⟩
      exact ⟨F, hcov, fun i hi => (inclBall_iff_dense hD hopen _ _).2 (hF i hi)⟩
    · rintro ⟨F, hcov, hF⟩
      exact ⟨F, hcov, fun i hi => (inclBall_iff_dense hD hopen _ _).1 (hF i hi)⟩
  -- the eventual-radius union-intersection
  set H : Set Ω := ⋃ N : ℕ, ⋂ n : ℕ, {ω | N ≤ n → ω ∈ G n} with hHdef
  have hHmeas : NullMeasurableSet H P := by
    refine NullMeasurableSet.iUnion fun N => NullMeasurableSet.iInter fun n => ?_
    by_cases hNn : N ≤ n
    · have : {ω | N ≤ n → ω ∈ G n} = G n := by
        ext ω
        simp [hNn]
      rw [this]
      exact hGmeas n
    · have : {ω | N ≤ n → ω ∈ G n} = univ := by
        ext ω
        simp [hNn]
      rw [this]
      exact MeasurableSet.univ.nullMeasurableSet
  have hae : {ω | C ⊆ Λ ω} =ᵐ[P] H := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [heq] with ω hω
    obtain ⟨N, hN⟩ := hω
    constructor
    · intro hC'
      refine mem_iUnion.2 ⟨N, mem_iInter.2 fun n => ?_⟩
      intro hNn
      show ω ∈ G n
      rw [key n ω (hN n hNn).1, ← (hN n hNn).2]
      exact hC'
    · intro hω'
      obtain ⟨M, hM⟩ := mem_iUnion.1 hω'
      have hGn : ω ∈ G (max M N) := mem_iInter.1 hM (max M N) (le_max_left _ _)
      have hNm : N ≤ max M N := le_max_right _ _
      show C ⊆ Λ ω
      rw [(hN (max M N) hNm).2]
      exact (key (max M N) ω (hN (max M N) hNm).1).1 hGn
  exact hHmeas.congr hae.symm

end MatedCRT.S5c
