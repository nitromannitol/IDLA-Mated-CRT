import MatedCRT.FirstPass.S5c.BorelModification

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), measure layer, step M2): threshold sets as Borel preimages

Generic, no frozen input. Let `Y : Ω → X` be `m`-measurable (the moment vector of the field-measurable version of the
LQG measure) and `v : Ω → ℝ` a random least supersolution value. Suppose that almost surely, for every real `c`,
`c < v ω` iff `c < q` and `Y ω ∉ S q` for some rational `q`, where `S q ⊆ X` is the analytic set of supersolution moments
(B1bThreshold, `nullMeasurableSet_lt_leastSupersolution_rat`). Then each threshold set `{c < v}` is almost surely equal to
the preimage `Y⁻¹ T` of a Borel set `T ⊆ X`.

The sets `S q` enter only through `exists_borel_null_modification` (M1): `Y⁻¹ (S q)` and `Y⁻¹ (B q)` agree off an
`m`-measurable `P`-null set; countably many such sets are taken, so the union is still `m`-measurable and null.
-/

namespace MatedCRT.S5c

open MeasureTheory Set

theorem threshold_borel_ae {Ω X : Type*} [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω} [MeasurableSpace X]
    (hm : m ≤ mΩ) {P : @Measure Ω mΩ} [IsProbabilityMeasure P] {Y : Ω → X} (hY : Measurable[m] Y)
    {S : ℚ → Set X} (hS : ∀ q : ℚ, ∀ Q : Measure X, IsFiniteMeasure Q → NullMeasurableSet (S q) Q)
    {v : Ω → ℝ} (hid : ∀ᵐ ω ∂P, ∀ c : ℝ, c < v ω ↔ ∃ q : ℚ, c < (q : ℝ) ∧ Y ω ∉ S q) (c : ℝ) :
    ∃ T : Set X, MeasurableSet T ∧ ∀ᵐ ω ∂P, (c < v ω ↔ Y ω ∈ T) := by
  choose B hB N hNm hNP hgood using fun q : ℚ =>
    @exists_borel_null_modification Ω X mΩ m _ hm P _ Y hY (S q) (hS q)
  have hNall : MeasurableSet[m] (⋃ q : ℚ, N q) := MeasurableSet.iUnion fun q => hNm q
  have hPall : P (⋃ q : ℚ, N q) = 0 := measure_iUnion_null fun q => hNP q
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋃ q : ℚ, N q := by
    refine ae_iff.2 ?_
    convert hPall using 2
    ext ω
    simp
  refine ⟨⋃ q : ℚ, ⋃ (_ : c < (q : ℝ)), (B q)ᶜ,
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => (hB q).compl, ?_⟩
  filter_upwards [hid, hae] with ω hω hnot
  rw [hω c]
  constructor
  · rintro ⟨q, hq, hYS⟩
    refine mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq, ?_⟩⟩
    intro hYB
    apply hYS
    exact (hgood q ω (fun h => hnot (mem_iUnion.2 ⟨q, h⟩))).2 hYB
  · intro hmem
    obtain ⟨q, hq⟩ := mem_iUnion.1 hmem
    obtain ⟨hcq, hnB⟩ := mem_iUnion.1 hq
    refine ⟨q, hcq, fun hYS => hnB ?_⟩
    exact (hgood q ω (fun h => hnot (mem_iUnion.2 ⟨q, h⟩))).1 hYS

end MatedCRT.S5c
