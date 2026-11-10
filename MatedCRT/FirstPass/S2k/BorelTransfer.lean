import MatedCRT.FirstPass.Frozen.S2k
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # FIRST PASS S2k: Borel full-law transfer (section 3.1 of the closure cycle note)

Written argument: `notes/fp-gaps/CHATGPT-closure-inside-cycle.md`, section 3.1, equations (4)–(5): from a Borel
full-probability set `E` of a reference probability space and a measurable map `F` into a separable metric space, there
is a Borel set `H` of the target with full law such that every point of `H` is the image of a point of `E`.

The only external input is the frozen Lusin theorem `FrozenLusinCompactContinuity` (Kechris 17.11–17.12). -/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRT.FirstPass.S2k

variable {X Y : Type} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Compact approximation of a Borel full set `E` on which the Borel map `F` is continuous: for every `ε > 0` there is a
compact `K ⊆ E` with `F|K` continuous and `P Kᶜ < ε` (the compact inner approximation of section 3.1). -/
theorem exists_compact_sub_continuousOn (hL : FrozenLusinCompactContinuity)
    (P : Measure X) [IsProbabilityMeasure P] {E : Set X} (hE : MeasurableSet E) (hfull : P Eᶜ = 0)
    (F : X → Y) (hF : Measurable F) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K ⊆ E, IsCompact K ∧ ContinuousOn F K ∧ P Kᶜ < ε := by
  obtain ⟨K1, hK1c, hK1P, hK1F⟩ := hL X Y P F hF (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K2, hK2E, hK2c, hK2P⟩ :=
    hE.exists_isCompact_sdiff_lt (measure_ne_top P E) (ENNReal.half_pos hε.ne').ne'
  refine ⟨K2 ∩ K1, inter_subset_left.trans hK2E, hK2c.inter_right hK1c.isClosed,
    hK1F.mono inter_subset_right, ?_⟩
  have hsub : (K2 ∩ K1)ᶜ ⊆ Eᶜ ∪ (E \ K2) ∪ K1ᶜ := by
    intro x hx
    by_cases hxE : x ∈ E <;> by_cases hx2 : x ∈ K2 <;> by_cases hx1 : x ∈ K1 <;> simp_all
  calc P (K2 ∩ K1)ᶜ ≤ P (Eᶜ ∪ (E \ K2) ∪ K1ᶜ) := measure_mono hsub
    _ ≤ P (Eᶜ ∪ (E \ K2)) + P K1ᶜ := measure_union_le _ _
    _ ≤ (P Eᶜ + P (E \ K2)) + P K1ᶜ := add_le_add (measure_union_le _ _) le_rfl
    _ = P (E \ K2) + P K1ᶜ := by rw [hfull, zero_add]
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hK2P hK1P
    _ = ε := ENNReal.add_halves ε

/-- **Borel full-law transfer (section 3.1, equations (4)–(5)).** Let `P` be a probability measure on a complete
separable metric space `X`, `E ⊆ X` a Borel set with `P Eᶜ = 0`, and `F : X → Y` a Borel map into a separable metric
space `Y`. Then there is a Borel set `H ⊆ Y` such that every point of `H` is `F x` for some `x ∈ E`, and `P (F⁻¹' H) = 1`. -/
theorem exists_borel_image_fullLaw (hL : FrozenLusinCompactContinuity)
    (P : Measure X) [IsProbabilityMeasure P] {E : Set X} (hE : MeasurableSet E) (hfull : P Eᶜ = 0)
    (F : X → Y) (hF : Measurable F) :
    ∃ H : Set Y, MeasurableSet H ∧ (∀ y ∈ H, ∃ x ∈ E, F x = y) ∧ P (F ⁻¹' H) = 1 := by
  choose K hKE hKc hKF hKP using fun n : ℕ =>
    exists_compact_sub_continuousOn hL P hE hfull F hF
      (ε := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _))
  set H : Set Y := ⋃ n, F '' K n with hH
  have hHm : MeasurableSet H :=
    MeasurableSet.iUnion fun n => ((hKc n).image_of_continuousOn (hKF n)).isClosed.measurableSet
  refine ⟨H, hHm, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.1 hy
    exact ⟨x, hKE n hx, rfl⟩
  · have hFH : MeasurableSet (F ⁻¹' H) := hF hHm
    have hsub : ∀ n, (F ⁻¹' H)ᶜ ⊆ (K n)ᶜ := by
      intro n x hx hKx
      exact hx (mem_preimage.2 (mem_iUnion.2 ⟨n, mem_image_of_mem F hKx⟩))
    have hT : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hD : P (F ⁻¹' H)ᶜ = 0 := by
      refine nonpos_iff_eq_zero.1 (ge_of_tendsto hT (Filter.Eventually.of_forall fun n => ?_))
      exact (measure_mono (hsub n)).trans (hKP n).le
    exact (prob_compl_eq_zero_iff hFH).1 hD

end MatedCRT.FirstPass.S2k
