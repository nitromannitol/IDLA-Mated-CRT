import Mathlib

/-!
# Continuous mapping theorem for maps continuous almost everywhere under the limit

If probability measures `μs i` converge weakly to `μ` along a countably generated filter and a
measurable map `f` is continuous at `μ`-almost every point, then the push-forwards `f_* (μs i)` converge
weakly to `f_* μ` (Billingsley, *Convergence of Probability Measures*, Theorem 2.7).  Mathlib has the
statement for continuous `f` only (`ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`).

* `tendsto_map_of_ae_continuousAt`: the theorem, by the open-set form of the portmanteau theorem;
* `ae_le_zero_of_tendsto_of_continuousAt`: if `F` is continuous at every point of a set of full
  `μ`-measure, and for every `κ > 0` the weak-limit approximants charge every open subset of
  `{F > κ}` with mass tending to `0`, then `F ≤ 0` holds `μ`-almost everywhere.  Nothing is assumed to be
  measurable about `F`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MatedCRT.AeContinuousMapping

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [HasOuterApproxClosed X] [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]

/-- **Continuous mapping theorem** (measurable `f`, continuous `μ`-almost everywhere). -/
theorem tendsto_map_of_ae_continuousAt {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X} (h : Tendsto μs L (𝓝 μ))
    {f : X → Y} (hf : Measurable f) (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x) :
    Tendsto (fun i => (μs i).map f) L (𝓝 (μ.map f)) := by
  refine tendsto_of_forall_isOpen_le_liminf' fun G hG => ?_
  have hmeas : MeasurableSet (f ⁻¹' G) := hf hG.measurableSet
  have hsub : f ⁻¹' G ⊆ interior (f ⁻¹' G) ∪ {x | ¬ ContinuousAt f x} := by
    intro x hx
    by_cases hcx : ContinuousAt f x
    · exact Or.inl (mem_interior_iff_mem_nhds.2 (hcx.preimage_mem_nhds (hG.mem_nhds hx)))
    · exact Or.inr hcx
  have h1 : (μ : Measure X) (f ⁻¹' G) ≤ (μ : Measure X) (interior (f ⁻¹' G)) := by
    calc (μ : Measure X) (f ⁻¹' G)
        ≤ (μ : Measure X) (interior (f ⁻¹' G) ∪ {x | ¬ ContinuousAt f x}) := measure_mono hsub
      _ ≤ (μ : Measure X) (interior (f ⁻¹' G)) + (μ : Measure X) {x | ¬ ContinuousAt f x} :=
          measure_union_le _ _
      _ = (μ : Measure X) (interior (f ⁻¹' G)) := by rw [ae_iff.1 hc, add_zero]
  have h2 := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h
    (isOpen_interior : IsOpen (interior (f ⁻¹' G)))
  have h3 : L.liminf (fun i => (μs i : Measure X) (interior (f ⁻¹' G))) ≤
      L.liminf (fun i => (μs i : Measure X) (f ⁻¹' G)) :=
    liminf_le_liminf (Eventually.of_forall fun i => measure_mono interior_subset)
  have hA : ∀ ν : ProbabilityMeasure X,
      ((ν.map f : ProbabilityMeasure Y) : Measure Y) G = (ν : Measure X) (f ⁻¹' G) :=
    fun ν => ν.map_apply' hf.aemeasurable hG.measurableSet
  simp only [hA]
  exact h1.trans (h2.trans h3)

/-- A function continuous on a set of full measure vanishes almost everywhere when the
approximating measures charge the open subsets of every `{F > κ}` less and less. -/
theorem ae_le_zero_of_tendsto_of_continuousAt {μs : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (h : Tendsto μs atTop (𝓝 μ)) {F : X → ℝ}
    (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt F x)
    (hF : ∀ κ : ℝ, 0 < κ → ∀ O : Set X, IsOpen O → (∀ x ∈ O, κ < F x) →
      Tendsto (fun n => (μs n : Measure X) O) atTop (𝓝 0)) :
    ∀ᵐ x ∂(μ : Measure X), F x ≤ 0 := by
  have hk : ∀ k : ℕ, (μ : Measure X) {x | 1 / ((k : ℝ) + 1) < F x} = 0 := by
    intro k
    have hκ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    set κ : ℝ := 1 / ((k : ℝ) + 1) with hκdef
    set O : Set X := interior {x | κ / 2 < F x} with hO
    have hsub : {x | κ < F x} ⊆ O ∪ {x | ¬ ContinuousAt F x} := by
      intro x hx
      by_cases hcx : ContinuousAt F x
      · refine Or.inl (mem_interior_iff_mem_nhds.2 ?_)
        exact hcx.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by have hx' : κ < F x := hx; show κ / 2 < F x; linarith))
      · exact Or.inr hcx
    have hO0 : (μ : Measure X) O = 0 := by
      have h2 := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h (isOpen_interior : IsOpen O)
      have hlim := hF (κ / 2) (by positivity) O isOpen_interior
        (fun x hx => by
          have hx' := interior_subset (s := {y : X | κ / 2 < F y}) hx
          exact hx')
      rw [hlim.liminf_eq] at h2
      exact le_antisymm h2 bot_le
    refine measure_mono_null hsub (measure_union_null hO0 (ae_iff.1 hc))
  have h0 : (μ : Measure X) {x | 0 < F x} = 0 := by
    have : {x | 0 < F x} = ⋃ k : ℕ, {x | 1 / ((k : ℝ) + 1) < F x} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx
        exact ⟨k, hk⟩
      · rintro ⟨k, hk⟩
        exact lt_trans (by positivity) hk
    rw [this]
    exact measure_iUnion_null hk
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
  simpa using hx

end MatedCRT.AeContinuousMapping
