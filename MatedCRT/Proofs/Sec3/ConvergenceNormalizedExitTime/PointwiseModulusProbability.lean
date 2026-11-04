import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BoundaryProbability
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ContinuousModulusProbability

/-! Probability control of the modulus from pointwise measurability. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- An almost surely continuous random function with almost everywhere
measurable evaluations has a probabilistic modulus on a compact set. -/
theorem pointwiseMeasurable_modulus_small_in_probability
    {Ω α : Type} [MeasurableSpace Ω] [PseudoMetricSpace α] [SecondCountableTopology α]
    (P : Measure Ω) [IsFiniteMeasure P] (K : Set α) (hK : IsCompact K)
    (F : Ω → α → ℝ) (hF : ∀ x ∈ K, AEMeasurable (fun ω => F ω x) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (F ω) K)
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ω x - F ω y|} ≤ e := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  let : Countable D := hDc.to_subtype
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let A : ℕ → Set Ω := fun n => {ω | ∃ x y : D,
    dist x.1.1 y.1.1 < R n ∧ t < |F ω x - F ω y|}
  have hAmeas : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    have hA : A n = ⋃ x : D, ⋃ y : D, if dist x.1.1 y.1.1 < R n then
        {ω | t < |F ω x - F ω y|} else ∅ := by
      ext ω
      simp only [A, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨x, y, hxy, hfx⟩
        exact ⟨x, y, by simpa [hxy] using hfx⟩
      · rintro ⟨x, y, hxy⟩
        by_cases h : dist x.1.1 y.1.1 < R n
        · exact ⟨x, y, h, by simpa [h] using hxy⟩
        · simp [h] at hxy
    rw [hA]
    apply NullMeasurableSet.iUnion
    intro x
    apply NullMeasurableSet.iUnion
    intro y
    split_ifs
    · exact nullMeasurableSet_lt aemeasurable_const
        (((hF x x.1.property).sub (hF y y.1.property)).abs)
    · exact MeasurableSet.empty.nullMeasurableSet
  have hRlim : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    apply tendsto_measure_zero_of_ae_eventually_not_mem P A hAmeas
    filter_upwards [hcont] with ω hc
    have hu := hK.uniformContinuousOn_of_continuous hc
    obtain ⟨δ, hδ, huδ⟩ := Metric.uniformContinuousOn_iff.mp hu t ht
    have hsmall := hRlim.eventually (Iio_mem_nhds hδ)
    filter_upwards [hsmall] with n hn
    rintro ⟨x, y, hxy, hbad⟩
    have hb := huδ x x.1.property y y.1.property (hxy.trans hn)
    exact (not_lt_of_ge (by simpa [Real.dist_eq] using hb.le)) hbad
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim e he).exists
  refine ⟨R n, by dsimp [R]; positivity, ?_⟩
  calc
    P {ω | ∃ x ∈ K, ∃ y ∈ K, dist x y < R n ∧ t < |F ω x - F ω y|} ≤ P (A n) := by
      apply measure_mono_ae
      filter_upwards [hcont] with ω hc
      rintro ⟨x, hx, y, hy, hxy, hbad⟩
      have hc' : Continuous (fun x : K => F ω x) :=
        continuousOn_iff_continuous_domRestrict.mp hc
      let U : Set (K × K) := {p | dist p.1.1 p.2.1 < R n ∧
        t < |F ω p.1 - F ω p.2|}
      have hU : IsOpen U :=
        (isOpen_lt ((continuous_subtype_val.comp continuous_fst).dist
          (continuous_subtype_val.comp continuous_snd)) continuous_const).inter
        (isOpen_lt continuous_const ((hc'.comp continuous_fst).sub
          (hc'.comp continuous_snd)).abs)
      have hp : (⟨x, hx⟩, ⟨y, hy⟩) ∈ U := ⟨hxy, hbad⟩
      obtain ⟨p, hpD, hpU⟩ := (hDd.prod hDd).exists_mem_open hU ⟨_, hp⟩
      exact ⟨⟨p.1, hpD.1⟩, ⟨p.2, hpD.2⟩, hpU.1, hpU.2⟩
    _ ≤ e := hn

end MatedCRT
