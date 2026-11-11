import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.WholePlaneLocality
import HarmonicBalls.Proofs.Sec5.LocalFirstContactRepresentative

/-! # Simultaneous measurability of whole-plane harmonic-ball families -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace

/-- HB22 locality gives a single measurable version of the whole positive-time
family, including all spatial points simultaneously. -/
theorem aemeasurable_wholePlaneHarmonicBall_family
    (hloc : HarmonicBallLocalSetStmt.{0}) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (z : ℂ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) z) :
    AEMeasurable (fun ω (p : Ioi (0 : ℝ) × ℂ) => p.2 ∈ Λ ω p.1) P := by
  classical
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let V : Ω → Q × ℕ → Prop := fun ω p => denseSeq ℂ p.2 ∈ Λ ω p.1
  have hV : AEMeasurable V P :=
    aemeasurable_wholePlaneHarmonicBall_countable hloc hγ hγ2 hα hh hμ z Λ hΛ
      (fun p : Q × ℕ => p.1) (fun p => p.1.property) (fun p => denseSeq ℂ p.2)
  let V' := hV.mk V
  have hV' : Measurable V' := hV.measurable_mk
  let S : Ω → Q → Set ℂ := fun ω q => {x | ∃ n : ℕ, x = denseSeq ℂ n ∧ V' ω (q, n)}
  have hS : Measurable S := by
    apply Measurable.of_eval
    intro q
    apply Measurable.of_eval
    intro x
    change Measurable (fun ω => ∃ n : ℕ, x = denseSeq ℂ n ∧ V' ω (q, n))
    exact Measurable.exists fun n => measurable_const.and ((measurable_pi_apply (q, n)).comp hV')
  let R : Ω → Q → Set ℂ := fun ω q => denseSequenceRegularization (S ω q)
  have hR : Measurable R := measurable_denseSequenceRegularization_family.comp hS
  let A : Ω → Ioi (0 : ℝ) → Set ℂ := fun ω t => ⋃ q : {q : Q // (q : ℝ) < t}, R ω q
  have hA : Measurable A := by
    apply Measurable.of_eval
    intro t
    apply Measurable.of_eval
    intro x
    have hm : Measurable (fun ω => ∃ q : {q : Q // (q : ℝ) < t}, x ∈ R ω q) :=
      Measurable.exists fun q => (measurable_pi_apply x).comp ((measurable_pi_apply q.1).comp hR)
    convert hm using 1
    funext ω
    apply propext
    change x ∈ (⋃ q : {q : Q // (q : ℝ) < t}, R ω q) ↔ _
    exact mem_iUnion
  let F : Ω → Ioi (0 : ℝ) → Set ℂ := fun ω t => denseSequenceRegularization (A ω t)
  have hF : Measurable F := measurable_denseSequenceRegularization_family.comp hA
  have hF' : Measurable (fun ω (p : Ioi (0 : ℝ) × ℂ) => p.2 ∈ F ω p.1) := by
    apply Measurable.of_eval
    intro p
    exact (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp hF)
  refine hF'.aemeasurable.congr ?_
  filter_upwards [hΛ, hV.ae_eq_mk] with ω hω hVω
  have hRq : ∀ q : Q, R ω q = Λ ω q := by
    intro q
    have hS' : S ω q = Λ ω q ∩ range (denseSeq ℂ) := by
      ext x
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_range]
      constructor
      · rintro ⟨n, rfl, hn⟩
        exact ⟨(iff_of_eq (congrFun hVω (q, n))).mpr hn, ⟨n, rfl⟩⟩
      · rintro ⟨hx, n, rfl⟩
        exact ⟨n, rfl, (iff_of_eq (congrFun hVω (q, n))).mp hx⟩
    have hopen := (hω.2.isRegularOpen q q.property).isOpen
    have hc : denseSequenceClosure (S ω q) = closure (Λ ω q) := by
      rw [denseSequenceClosure, hS']
      simpa only [inter_assoc, inter_self] using (closure_eq_closure_inter_denseSeq hopen).symm
    dsimp only [R, denseSequenceRegularization]
    rw [hc, show denseSequenceClosure (closure (Λ ω q))ᶜ = closure (closure (Λ ω q))ᶜ from
      (closure_eq_closure_inter_denseSeq isClosed_closure.isOpen_compl).symm]
    rw [← interior_eq_compl_closure_compl, hω.2.isRegularOpen q q.property]
  funext p
  apply propext
  have hAo : IsOpen (A ω p.1) := by
    apply isOpen_iUnion
    intro q
    rw [hRq q]
    exact (hω.2.isRegularOpen q q.1.property).isOpen
  have hcl : closure (Λ ω p.1) = closure (A ω p.1) := by
    rw [closure_eq_closure_iUnion_earlier_rat_of_hausdorffContinuousOn p.1.property
      (fun s hs t ht hst => hω.2.monotoneOn hs ht hst) hω.2.hausdorffContinuousOn]
    congr 1
    ext x
    simp only [A, mem_iUnion]
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨⟨⟨q, q.property.1⟩, q.property.2⟩, by simpa only [hRq] using hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨⟨q.1, q.1.property, q.property⟩, by simpa only [hRq] using hq⟩
  change (p.2 ∈ F ω p.1) ↔ p.2 ∈ Λ ω p.1
  dsimp only [F]
  rw [denseSequenceRegularization_eq hAo, ← hcl, hω.2.isRegularOpen p.1 p.1.property]

end MatedCRT
