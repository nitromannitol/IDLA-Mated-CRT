import LatticeProb.Prob.FiniteMeasureStandardBorel
import LatticeProb.Prob.ProbabilityMeasureBorel

/-!
# Probability measures concentrated on a `G_δ` set; Borel structure along an embedding

Two general facts about the space `ProbabilityMeasure X` of Borel probability measures with the
topology of convergence in distribution.

* `MatedCRT.isGδ_setOf_measure_eq_one`: for a metric space `H` and a `G_δ` set `S ⊆ H`, the
  probability measures concentrated on `S`, that is `{ν | ν S = 1}`, form a `G_δ` subset of
  `ProbabilityMeasure H`. Writing `S = ⋂ₙ Uₙ` with `Uₙ` open, `ν S = 1` holds iff `ν Uₙᶜ < 1 / k`
  for all `n` and `k`, and each of these conditions is open since evaluation at a closed set is
  upper semicontinuous (Portmanteau theorem).
* `MatedCRT.borelSpace_probabilityMeasure_of_isEmbedding`: if `T : ProbabilityMeasure X →
  ProbabilityMeasure H` is a topological embedding into the probability measures on a compact
  metric space `H` which is measurable for the evaluation `σ`-algebras, then the evaluation
  `σ`-algebra of `ProbabilityMeasure X` is its Borel `σ`-algebra. The Borel `σ`-algebra of
  `ProbabilityMeasure X` is the pull-back by `T` of the Borel (= evaluation) `σ`-algebra of
  `ProbabilityMeasure H`, hence is contained in the evaluation `σ`-algebra; the reverse inclusion
  holds for every pseudo-metrizable `X` (Portmanteau theorem).
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace MatedCRT

/-- A null set is a set of measure `< 1 / n` for every `n`. -/
theorem measure_eq_zero_iff_forall_lt_inv_nat {H : Type*} [MeasurableSpace H]
    (μ : Measure H) (A : Set H) : μ A = 0 ↔ ∀ n : ℕ, μ A < (n : ℝ≥0∞)⁻¹ := by
  refine ⟨fun h n => h ▸ ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n), fun h => ?_⟩
  by_contra h0
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h0
  exact lt_asymm hn (h n)

/-- The probability measures concentrated on a `G_δ` subset `S` of a metric space form a `G_δ`
subset of the space of probability measures with the topology of convergence in distribution. -/
theorem isGδ_setOf_measure_eq_one {H : Type*} [MetricSpace H] [MeasurableSpace H]
    [BorelSpace H] {S : Set H} (hS : IsGδ S) :
    IsGδ {ν : ProbabilityMeasure H | (ν : Measure H) S = 1} := by
  obtain ⟨T, hTo, hTc, rfl⟩ := hS
  have hmeas : ∀ t ∈ T, MeasurableSet t := fun t ht => (hTo t ht).measurableSet
  have key : {ν : ProbabilityMeasure H | (ν : Measure H) (⋂₀ T) = 1} =
      ⋂ t : T, ⋂ n : ℕ, (fun ν : ProbabilityMeasure H => (ν : Measure H) (t : Set H)ᶜ) ⁻¹'
        Iio (n : ℝ≥0∞)⁻¹ := by
    ext ν
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iio]
    rw [← prob_compl_eq_zero_iff (MeasurableSet.sInter hTc hmeas), compl_sInter, sUnion_image,
      measure_biUnion_null_iff hTc]
    simp only [measure_eq_zero_iff_forall_lt_inv_nat, Subtype.forall]
  rw [key]
  have := hTc.to_subtype
  refine IsGδ.iInter fun t => IsGδ.iInter fun n => IsOpen.isGδ ?_
  exact (LatticeProb.probabilityMeasure_usc_of_isClosed
    (hTo t t.2).isClosed_compl).isOpen_preimage _

/-- Let `X` be pseudo-metrizable and `T : ProbabilityMeasure X → ProbabilityMeasure H` a
topological embedding into the probability measures on a compact metric space `H`, measurable for
the evaluation `σ`-algebras. Then the evaluation `σ`-algebra of `ProbabilityMeasure X` is its
Borel `σ`-algebra. -/
theorem borelSpace_probabilityMeasure_of_isEmbedding {X H : Type*} [TopologicalSpace X]
    [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace H] [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
    {T : ProbabilityMeasure X → ProbabilityMeasure H} (hT : Topology.IsEmbedding T)
    (hTm : Measurable T) : BorelSpace (ProbabilityMeasure X) := by
  refine ⟨le_antisymm LatticeProb.giry_le_borel_probabilityMeasure ?_⟩
  refine MeasurableSpace.generateFrom_le fun s hs => ?_
  obtain ⟨t, ht, rfl⟩ := (hT.toIsInducing.isOpen_iff (s := s)).1 hs
  exact hTm ht.measurableSet

end MatedCRT
