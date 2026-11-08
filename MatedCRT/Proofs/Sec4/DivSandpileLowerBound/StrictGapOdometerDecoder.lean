import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapCompactZero
import HarmonicBalls.Proofs.Sec5.LocalRestrictedShiftedCluster
import HarmonicBalls.Proofs.Sec5.RestrictedContainmentTest

/-! Measurable shifted-odometer and noncoincidence decoders. -/

namespace MatedCRT

open Set MeasureTheory Metric TopologicalSpace _root_.HarmonicBalls

/-- A single measurable decoder represents the shifted odometer away from the
pole and the noncoincidence set for every measure with continuous Green
potential and a nonempty shifted supersolution class. -/
theorem exists_measurable_shiftedOdometer_and_nonCoincidence
    {R t : ℝ} {z : ℂ} (hR : 0 < R) :
    ∃ (F : Measure ℂ → ℂ → ℝ) (C : Measure ℂ → Set ℂ),
      (∀ x, Measurable (fun ν => F ν x)) ∧ Measurable C ∧
      ∀ ν : Measure ℂ, ContinuousOn (greenPotentialBall ν R) (closedBall 0 R) →
        (shiftedSupersolutions ν R z t).Nonempty →
        (∀ x ∈ ball (0 : ℂ) R, x ≠ z → F ν x = shiftedOdometer ν R z t x) ∧
        C ν = nonCoincidenceSet ν R z t := by
  classical
  obtain ⟨Q, hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder hR
  let G : ℂ → C(closedBall (0 : ℂ) R, ℝ) → ℝ := fun x =>
    if hx : x ∈ ball (0 : ℂ) R ∧ x ≠ z then
      Classical.choose (exists_continuous_shiftedOdometer_decoder_of_nonempty (t := t) hR
        (ball_subset_closedBall hx.1) hx.2)
    else fun _ => 0
  have hG (x : ℂ) : Continuous (G x) := by
    dsimp only [G]
    split_ifs with hx
    · exact (Classical.choose_spec
        (exists_continuous_shiftedOdometer_decoder_of_nonempty (t := t) hR
          (ball_subset_closedBall hx.1) hx.2)).1
    · exact continuous_const
  let F : Measure ℂ → ℂ → ℝ := fun ν x => G x (Q ν)
  let C : Measure ℂ → Set ℂ := fun ν =>
    {x | x ∈ ball (0 : ℂ) R ∧ (x = z ∨ 0 < F ν x)}
  have hFm : ∀ x, Measurable (fun ν => F ν x) := fun x => (hG x).measurable.comp hQ
  have hCm : Measurable C := by
    apply Measurable.of_eval
    intro x
    exact measurable_const.and (measurable_const.or (measurable_const.lt (hFm x)))
  refine ⟨F, C, hFm, hCm, ?_⟩
  intro ν hcont hclass
  have hFeq : ∀ x ∈ ball (0 : ℂ) R, x ≠ z → F ν x = shiftedOdometer ν R z t x := by
    intro x hx hxz
    have hgood := (Classical.choose_spec
      (exists_continuous_shiftedOdometer_decoder_of_nonempty (t := t) hR
        (ball_subset_closedBall hx) hxz)).2 ν hcont hclass (Q ν) (hQeq ν hcont)
    have hp : x ∈ ball (0 : ℂ) R ∧ x ≠ z := ⟨hx, hxz⟩
    simpa only [F, G, dite_eq_left hp] using hgood.symm
  refine ⟨hFeq, ?_⟩
  ext x
  rw [mem_nonCoincidenceSet_iff]
  change (x ∈ ball (0 : ℂ) R ∧ (x = z ∨ 0 < F ν x)) ↔ _
  by_cases hx : x ∈ ball (0 : ℂ) R
  · by_cases hxz : x = z
    · simp [hxz]
    · simp [hx, hxz, hFeq x hx hxz]
  · simp [hx]

/-- Compact containment of an open decoded set has a measurable
representative on samples whose closure is compact. -/
theorem exists_measurable_open_compact_containment
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → Set ℂ) (hC : Measurable C)
    (U : Set ℂ) (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    ∃ E : Set Ω, MeasurableSet E ∧ ∀ ω,
      IsOpen (C ω) → IsCompact (closure (C ω)) →
      (ω ∈ E ↔ closure (C ω) ⊆ U) := by
  let E : Set Ω := {ω | ∃ n : ℕ, ∀ m : ℕ,
    denseSeq ℂ m ∈ C ω → 1 / ((n : ℝ) + 1) ≤ infDist (denseSeq ℂ m) Uᶜ}
  have hE : MeasurableSet E := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro n
    apply Measurable.forall
    intro m
    exact ((measurable_pi_apply (denseSeq ℂ m)).comp hC).imp measurable_const
  refine ⟨E, hE, ?_⟩
  intro ω ho hk
  have heq : denseSequenceClosure (C ω) = closure (C ω) :=
    (closure_eq_closure_inter_denseSeq ho).symm
  have h := denseSequenceClosure_subset_open_iff hU hUc (heq ▸ hk)
  rw [heq] at h
  exact h.symm

/-- Compact confinement and the failure of open-set regularity have a joint
measurable representative when zeros are decoded continuously off a set
already contained in the open cluster. -/
theorem exists_measurable_confined_regularity_defect
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → Set ℂ) (hC : Measurable C)
    (f : Ω → ℂ → ℝ) (hf : ∀ x, Measurable (fun ω => f ω x))
    (D U : Set ℂ) (hD : IsOpen D) (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    ∃ E : Set Ω, MeasurableSet E ∧ ∀ ω,
      IsOpen (C ω) → IsCompact (closure (C ω)) →
      (∀ (p : ℕ × ℕ), closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ D →
        ContinuousOn (f ω) (closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1))) ∧
        ∀ x ∈ closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1)), 0 ≤ f ω x) →
      (∀ x ∈ D, x ∉ C ω ↔ f ω x = 0) →
      (∀ x ∈ U, x ∉ D → x ∈ C ω) →
      (ω ∈ E ↔ closure (C ω) ⊆ U ∧ interior (closure (C ω)) ≠ C ω) := by
  obtain ⟨K, hK, hKgood⟩ := exists_measurable_open_compact_containment C hC U hU hUc
  obtain ⟨Z, hZ, hZgood⟩ := exists_measurable_regularization_zero_test_of_open C hC f hf D hD
  refine ⟨K ∩ Z, hK.inter hZ, ?_⟩
  intro ω ho hk hreg hzero hcover
  have heqK := hKgood ω ho hk
  have heqZ := hZgood ω ho hreg hzero
  constructor
  · rintro ⟨hmemK, hmemZ⟩
    obtain ⟨x, _, hx, hxnot⟩ := heqZ.mp hmemZ
    refine ⟨heqK.mp hmemK, ?_⟩
    intro heq
    exact hxnot (heq ▸ hx)
  · rintro ⟨hcompact, hne⟩
    refine ⟨heqK.mpr hcompact, heqZ.mpr ?_⟩
    have hnsub : ¬ interior (closure (C ω)) ⊆ C ω := by
      intro hsub
      exact hne (Set.Subset.antisymm hsub ho.subset_interior_closure)
    obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnsub
    have hxU : x ∈ U := hcompact (interior_subset hx)
    have hxD : x ∈ D := by
      by_contra hn
      exact hxnot (hcover x hxU hn)
    exact ⟨x, hxD, hx, hxnot⟩

/-- The confined regularization defect of a shifted noncoincidence set has
a measurable representative on measures with the stated regularity. -/
theorem exists_measurable_nonCoincidence_regularity_defect
    {R t : ℝ} {z : ℂ} (hR : 0 < R) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      ContinuousOn (greenPotentialBall ν R) (closedBall 0 R) →
      (shiftedSupersolutions ν R z t).Nonempty →
      IsOpen (nonCoincidenceSet ν R z t) →
      ContinuousOn (shiftedOdometer ν R z t) (ball (0 : ℂ) R \ {z}) →
      (ν ∈ E ↔ closure (nonCoincidenceSet ν R z t) ⊆ ball 0 R ∧
        interior (closure (nonCoincidenceSet ν R z t)) ≠ nonCoincidenceSet ν R z t) := by
  obtain ⟨F, C, hF, hC, hgood⟩ := exists_measurable_shiftedOdometer_and_nonCoincidence (t := t) (z := z) hR
  let D : Set ℂ := ball (0 : ℂ) R \ {z}
  have hD : IsOpen D := isOpen_ball.inter isClosed_singleton.isOpen_compl
  have hUc : (ball (0 : ℂ) R)ᶜ.Nonempty := by
    refine ⟨(R : ℂ), ?_⟩
    simp only [mem_compl_iff, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR, lt_self_iff_false, not_false_eq_true]
  obtain ⟨E, hE, hEgood⟩ := exists_measurable_confined_regularity_defect
    C hC F hF D (ball 0 R) hD isOpen_ball hUc
  refine ⟨E, hE, ?_⟩
  intro ν hpot hclass hopen hcont
  have hcompact : IsCompact (closure (nonCoincidenceSet ν R z t)) := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    exact ball_subset_closedBall (mem_nonCoincidenceSet_iff.mp hx).1
  obtain ⟨hFeq, hCeq⟩ := hgood ν hpot hclass
  have hreg : ∀ (p : ℕ × ℕ),
      closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ D →
      ContinuousOn (F ν) (closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1))) ∧
      ∀ x ∈ closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1)), 0 ≤ F ν x := by
    intro p hsub
    constructor
    · apply (hcont.mono hsub).congr
      intro x hx
      have hxD := hsub hx
      have hxz : x ≠ z := by simpa only [D, mem_sdiff, mem_singleton_iff] using hxD.2
      exact hFeq x hxD.1 hxz
    · intro x hx
      have hxD := hsub hx
      have hxz : x ≠ z := by simpa only [D, mem_sdiff, mem_singleton_iff] using hxD.2
      rw [hFeq x hxD.1 hxz]
      exact shiftedOdometer_nonneg hclass (ball_subset_closedBall hxD.1) hxz
  have hzero : ∀ x ∈ D, x ∉ C ν ↔ F ν x = 0 := by
    intro x hx
    have hxz : x ≠ z := by simpa only [D, mem_sdiff, mem_singleton_iff] using hx.2
    have hn : 0 ≤ F ν x := by
      rw [hFeq x hx.1 hxz]
      exact shiftedOdometer_nonneg hclass (ball_subset_closedBall hx.1) hxz
    rw [hCeq, mem_nonCoincidenceSet_iff]
    simp only [hx.1, hxz, false_or, true_and, not_lt]
    rw [hFeq x hx.1 hxz] at hn ⊢
    exact ⟨fun h => le_antisymm h hn, fun h => h.le⟩
  have hcover : ∀ x ∈ ball (0 : ℂ) R, x ∉ D → x ∈ C ν := by
    intro x hx hn
    have hxz : x = z := by
      by_contra hne
      exact hn ⟨hx, by simpa only [mem_singleton_iff] using hne⟩
    rw [hCeq, mem_nonCoincidenceSet_iff]
    exact ⟨hx, Or.inl hxz⟩
  have hresult := hEgood ν (hCeq ▸ hopen) (hCeq ▸ hcompact) hreg hzero hcover
  simpa only [hCeq] using hresult

end MatedCRT
