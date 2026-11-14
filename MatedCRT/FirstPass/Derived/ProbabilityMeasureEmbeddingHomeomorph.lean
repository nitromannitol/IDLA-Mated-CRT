import LatticeProb.Prob.FiniteMeasureStandardBorel

/-!
# Probability measures on a Polish space embedded in a compact metric space

Let `i : X → H` be a topological embedding of a Polish space `X` into a compact metric space `H`.
By the Lusin–Souslin theorem the range of `i` is a Borel set and `i` is a measurable embedding.

The push-forward `μ ↦ i_* μ` is a homeomorphism, for the topologies of convergence in
distribution, from the probability measures on `X` onto the probability measures on `H` giving
full mass to the range of `i`; its inverse is the pull-back `ν ↦ i^* ν`. Continuity of the inverse
is the portmanteau theorem: every open `V ⊆ X` is `i⁻¹ W` for an open `W ⊆ H`, and
`(i^* ν)(i⁻¹ W) = ν(W)`. The push-forward is measurable for the evaluation σ-algebras, since
`(i_* μ)(A) = μ(i⁻¹ A)`.

No nonemptiness assumption is needed: the inverse is the pull-back measure, not the push-forward
along a measurable left inverse of `i`.
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT

section FullMass

/-- A probability measure giving full mass to a measurable set `S` is concentrated on `S`. -/
theorem ae_mem_of_measure_eq_one {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {S : Set Ω} (hS : MeasurableSet S) (h : ν S = 1) :
    ∀ᵐ x ∂ν, x ∈ S := by
  exact mem_ae_iff.2 ((prob_compl_eq_zero_iff hS).2 h)

/-- A probability measure giving full mass to a measurable set `S` charges `A ∩ S` as it
charges `A`. -/
theorem measure_inter_of_measure_eq_one {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {S : Set Ω} (hS : MeasurableSet S) (h : ν S = 1) (A : Set Ω) :
    ν (A ∩ S) = ν A := by
  rw [← Measure.restrict_apply' hS,
    Measure.restrict_eq_self_of_ae_mem (ae_mem_of_measure_eq_one hS h)]

end FullMass

variable {X H : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace H] [CompactSpace H] [MeasurableSpace H] [BorelSpace H] {i : X → H}

omit [CompactSpace H] in
/-- **Lusin–Souslin.** A topological embedding of a Polish space into a metric space is a
measurable embedding. -/
theorem measurableEmbedding_of_isEmbedding (hi : IsEmbedding i) : MeasurableEmbedding i :=
  hi.continuous.measurableEmbedding hi.injective

omit [CompactSpace H] in
/-- The range of a topological embedding of a Polish space into a metric space is a Borel set. -/
theorem measurableSet_range_of_isEmbedding (hi : IsEmbedding i) : MeasurableSet (Set.range i) :=
  (measurableEmbedding_of_isEmbedding hi).measurableSet_range

/-- The push-forward `i_* μ` of a probability measure on `X`, as a probability measure on `H`
giving full mass to the range of `i`. -/
noncomputable def pushforwardRange (hi : IsEmbedding i) (μ : ProbabilityMeasure X) :
    {ν : ProbabilityMeasure H // (ν : Measure H) (Set.range i) = 1} :=
  ⟨⟨(μ : Measure X).map i,
    (Measure.isProbabilityMeasure_map_iff hi.continuous.measurable.aemeasurable).mpr inferInstance⟩,
    by
      show ((μ : Measure X).map i) (Set.range i) = 1
      rw [Measure.map_apply hi.continuous.measurable (measurableSet_range_of_isEmbedding hi),
        Set.preimage_range, measure_univ]⟩

omit [CompactSpace H] in
theorem coe_pushforwardRange (hi : IsEmbedding i) (μ : ProbabilityMeasure X) :
    ((pushforwardRange hi μ : ProbabilityMeasure H) : Measure H) = (μ : Measure X).map i :=
  rfl

/-- The pull-back `i^* ν` of a probability measure on `H` giving full mass to the range of `i`. -/
noncomputable def comapRange (hi : IsEmbedding i)
    (ν : {ν : ProbabilityMeasure H // (ν : Measure H) (Set.range i) = 1}) :
    ProbabilityMeasure X :=
  ⟨((ν : ProbabilityMeasure H) : Measure H).comap i, ⟨by
    rw [(measurableEmbedding_of_isEmbedding hi).comap_apply, Set.image_univ]
    exact ν.2⟩⟩

omit [CompactSpace H] in
theorem coe_comapRange (hi : IsEmbedding i)
    (ν : {ν : ProbabilityMeasure H // (ν : Measure H) (Set.range i) = 1}) :
    ((comapRange hi ν : ProbabilityMeasure X) : Measure X) =
      ((ν : ProbabilityMeasure H) : Measure H).comap i :=
  rfl

omit [CompactSpace H] in
/-- The pull-back `i^* ν` charges `i⁻¹ W` as `ν` charges `W`. -/
theorem comapRange_apply_preimage (hi : IsEmbedding i)
    (ν : {ν : ProbabilityMeasure H // (ν : Measure H) (Set.range i) = 1}) (W : Set H) :
    ((comapRange hi ν : ProbabilityMeasure X) : Measure X) (i ⁻¹' W) =
      ((ν : ProbabilityMeasure H) : Measure H) W := by
  rw [coe_comapRange, (measurableEmbedding_of_isEmbedding hi).comap_apply,
    Set.image_preimage_eq_inter_range]
  exact measure_inter_of_measure_eq_one (measurableSet_range_of_isEmbedding hi) ν.2 W

/-- **Probability measures on an embedded Polish space.** For a topological embedding
`i : X → H` of a Polish space into a compact metric space, the push-forward `μ ↦ i_* μ` is a
homeomorphism, for the topologies of convergence in distribution, from the probability measures
on `X` onto the probability measures on `H` giving full mass to the range of `i`. -/
noncomputable def probabilityMeasureRangeHomeomorph (hi : IsEmbedding i) :
    ProbabilityMeasure X ≃ₜ {ν : ProbabilityMeasure H // (ν : Measure H) (Set.range i) = 1} where
  toFun := pushforwardRange hi
  invFun := comapRange hi
  left_inv μ := by
    apply Subtype.ext
    show ((comapRange hi (pushforwardRange hi μ) : ProbabilityMeasure X) : Measure X) =
      (μ : Measure X)
    rw [coe_comapRange, coe_pushforwardRange]
    exact (measurableEmbedding_of_isEmbedding hi).comap_map _
  right_inv ν := by
    apply Subtype.ext
    apply Subtype.ext
    show ((pushforwardRange hi (comapRange hi ν) : ProbabilityMeasure H) : Measure H) =
      ((ν : ProbabilityMeasure H) : Measure H)
    rw [coe_pushforwardRange, coe_comapRange, (measurableEmbedding_of_isEmbedding hi).map_comap]
    exact Measure.restrict_eq_self_of_ae_mem
      (ae_mem_of_measure_eq_one (measurableSet_range_of_isEmbedding hi) ν.2)
  continuous_toFun := by
    show Continuous (pushforwardRange hi)
    have hm : Measurable i := hi.continuous.measurable
    have hfun : Subtype.val ∘ pushforwardRange hi = fun μ : ProbabilityMeasure X => μ.map i := by
      funext μ
      apply Subtype.ext
      show ((pushforwardRange hi μ : ProbabilityMeasure H) : Measure H) =
        ((μ.map i : ProbabilityMeasure H) : Measure H)
      rw [coe_pushforwardRange, ProbabilityMeasure.toMeasure_map]
    refine continuous_induced_rng.2 ?_
    rw [hfun]
    exact ProbabilityMeasure.continuous_map hi.continuous
  continuous_invFun := by
    show Continuous (comapRange hi)
    refine continuous_iff_seqContinuous.mpr fun νs ν hν => ?_
    have hopen : ∀ V : Set X, IsOpen V →
        ((comapRange hi ν : ProbabilityMeasure X) : Measure X) V ≤
          atTop.liminf (fun n => ((comapRange hi (νs n) : ProbabilityMeasure X) : Measure X) V) := by
      intro V hV
      obtain ⟨W, hW, rfl⟩ := hi.toIsInducing.isOpen_iff.mp hV
      simp only [comapRange_apply_preimage]
      exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
        ((continuous_subtype_val.tendsto ν).comp hν) hW
    exact tendsto_of_forall_isOpen_le_liminf_nat' hopen

theorem coe_probabilityMeasureRangeHomeomorph_apply (hi : IsEmbedding i) (μ : ProbabilityMeasure X) :
    ((probabilityMeasureRangeHomeomorph hi μ : ProbabilityMeasure H) : Measure H) =
      (μ : Measure X).map i :=
  coe_pushforwardRange hi μ

theorem coe_probabilityMeasureRangeHomeomorph_symm_apply (hi : IsEmbedding i)
    (ν : {ν : ProbabilityMeasure H // (ν : Measure H) (Set.range i) = 1}) :
    (((probabilityMeasureRangeHomeomorph hi).symm ν : ProbabilityMeasure X) : Measure X) =
      ((ν : ProbabilityMeasure H) : Measure H).comap i :=
  rfl

/-- The push-forward charges every set `A ⊆ H` as `μ` charges `i⁻¹ A`. -/
theorem probabilityMeasureRangeHomeomorph_apply_apply (hi : IsEmbedding i)
    (μ : ProbabilityMeasure X) (A : Set H) :
    ((probabilityMeasureRangeHomeomorph hi μ : ProbabilityMeasure H) : Measure H) A =
      (μ : Measure X) (i ⁻¹' A) := by
  rw [coe_probabilityMeasureRangeHomeomorph_apply,
    (measurableEmbedding_of_isEmbedding hi).map_apply]

/-- The push-forward along `i` is measurable for the evaluation σ-algebras on probability
measures, since `(i_* μ)(A) = μ(i⁻¹ A)`. -/
theorem measurable_probabilityMeasureRangeHomeomorph (hi : IsEmbedding i) :
    Measurable (fun μ : ProbabilityMeasure X =>
      (probabilityMeasureRangeHomeomorph hi μ : ProbabilityMeasure H)) := by
  have hmeas : Measurable fun μ : ProbabilityMeasure X => (μ : Measure X).map i := by
    refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
    simp only [Measure.map_apply hi.continuous.measurable hB]
    exact (Measure.measurable_coe (hi.continuous.measurable hB)).comp measurable_subtype_coe
  have h2 : Measurable fun μ : ProbabilityMeasure X =>
      ((probabilityMeasureRangeHomeomorph hi μ : ProbabilityMeasure H) : Measure H) := by
    simp only [coe_probabilityMeasureRangeHomeomorph_apply]
    exact hmeas
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact h2 ht

end MatedCRT
