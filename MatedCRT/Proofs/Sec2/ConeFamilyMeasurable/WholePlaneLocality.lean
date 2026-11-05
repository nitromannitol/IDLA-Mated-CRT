import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.FixedDisk
import HarmonicBalls.Draft.Section1

/-! # Fixed-time measurability from harmonic-ball locality -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Point membership in the interior of a random closed set is null measurable
when point membership in the closed set is null measurable. -/
theorem nullMeasurableSet_mem_interior_of_closed
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → Set ℂ)
    (hclosed : ∀ ω, IsClosed (F ω))
    (hmem : ∀ x : ℂ, NullMeasurableSet {ω | x ∈ F ω} P) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ interior (F ω)} P := by
  classical
  obtain ⟨C, hC, hdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable C := hC.to_subtype
  let B := TopologicalSpace.countableBasis ℂ
  have : Countable B := (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  have hb : ∀ b : B, NullMeasurableSet
      {ω | x ∈ (b : Set ℂ) ∧ ∀ y : C, (y : ℂ) ∈ (b : Set ℂ) → (y : ℂ) ∈ F ω} P := by
    intro b
    by_cases hx : x ∈ (b : Set ℂ)
    · have hy : ∀ y : C, NullMeasurableSet
          {ω | (y : ℂ) ∈ (b : Set ℂ) → (y : ℂ) ∈ F ω} P := by
        intro y
        by_cases hy : (y : ℂ) ∈ (b : Set ℂ)
        · simpa [hy] using hmem y
        · simp [hy]
      have h := NullMeasurableSet.iInter hy
      convert h using 1
      ext ω
      simp [hx]
    · simp [hx]
  have h := NullMeasurableSet.iUnion hb
  convert h using 1
  ext ω
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · intro hx
    obtain ⟨b, hb, hxb, hsub⟩ :=
      (TopologicalSpace.isBasis_countableBasis ℂ).exists_subset_of_mem_open hx isOpen_interior
    exact ⟨⟨b, hb⟩, hxb, fun y hy => interior_subset (hsub hy)⟩
  · rintro ⟨b, hxb, hy⟩
    have hopen : IsOpen (b : Set ℂ) :=
      (TopologicalSpace.isBasis_countableBasis ℂ).isOpen b.property
    have hsub : (b : Set ℂ) ⊆ F ω := by
      apply (hdense.open_subset_closure_inter hopen).trans
      apply closure_minimal _ (hclosed ω)
      rintro y ⟨hyb, hyC⟩
      exact hy ⟨y, hyC⟩ hyb
    exact interior_maximal hsub hopen hxb

/-- HB22 Proposition 1.3 implies fixed-time point membership is null measurable
for every almost surely valid whole-plane harmonic-ball family. -/
theorem nullMeasurableSet_mem_wholePlaneHarmonicBall
    (hloc : HarmonicBallLocalSetStmt.{0}) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (z : ℂ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) z)
    {t : ℝ} (ht : 0 < t) (x : ℂ) : NullMeasurableSet {ω | x ∈ Λ ω t} P := by
  have hclosed : ∀ y : ℂ, NullMeasurableSet {ω | y ∈ closure (Λ ω t)} P := by
    intro y
    obtain ⟨E, hE, hEq⟩ := hloc γ α hγ hγ2 hα Ω P hC hcirc μ hh hμ z Λ hΛ t ht.le
      ({y}ᶜ) isClosed_singleton.isOpen_compl
    have hEm : MeasurableSet E := hh.fieldSigmaAlgebra_le α _ _ hE
    have hnull : NullMeasurableSet {ω | closure (Λ ω t) ⊆ ({y} : Set ℂ)ᶜ} P := by
      apply hEm.nullMeasurableSet.congr
      simpa [ht.ne'] using hEq.symm
    convert hnull.compl using 1
    ext ω
    simp [Set.subset_compl_iff_disjoint_left]
  have hi := nullMeasurableSet_mem_interior_of_closed P (fun ω => closure (Λ ω t))
    (fun _ => isClosed_closure) hclosed x
  apply hi.congr
  filter_upwards [hΛ] with ω hω
  exact propext (by rw [hω.2.isRegularOpen t ht])

/-- Any countable collection of positive-time point evaluations admits one
simultaneous measurable version. -/
theorem aemeasurable_wholePlaneHarmonicBall_countable
    (hloc : HarmonicBallLocalSetStmt.{0}) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (z : ℂ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) z)
    {ι : Type} [Countable ι] (t : ι → ℝ) (ht : ∀ i, 0 < t i) (x : ι → ℂ) :
    AEMeasurable (fun ω i => x i ∈ Λ ω (t i)) P := by
  apply aemeasurable_pi_iff.mpr
  intro i
  have hm := nullMeasurableSet_mem_wholePlaneHarmonicBall hloc hγ hγ2 hα hh hμ z Λ hΛ (ht i) (x i)
  obtain ⟨E, -, hE, hEq⟩ := hm.exists_measurable_subset_ae_eq
  refine ⟨fun ω => ω ∈ E, measurableSet_setOfPred.mp hE, ?_⟩
  filter_upwards [hEq] with ω hω
  exact hω.symm

end MatedCRT
