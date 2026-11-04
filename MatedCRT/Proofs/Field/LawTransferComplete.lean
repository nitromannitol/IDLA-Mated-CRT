import MatedCRT.Proofs.Field.LawTransferEvents
import MatedCRT.Proofs.Field.LawTransferCovariance
import MatedCRT.Proofs.Field.LawTransferPairings
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-! # Lemma 6.6 from Leonardo Bonanno's annulus estimate

We transfer annulus events between the GFF interfaces by equality of the joint laws of
mean-zero pairings, then apply Bonanno's proof of Gwynne–Miller, Lemma 3.1. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric HarmonicBalls

/-- Transfer the annulus events to Leonardo Bonanno's normalized distribution-valued GFF. -/
theorem annulusGFFLawTransfer : AnnulusGFFLawTransferStep := by
  intro Ω _ P hC hcirc hP hwp s₁ s₂ r E hs₁ hs₁₂ hs₂ hrpos hlocal
  let : IsProbabilityMeasure P := hP
  obtain ⟨Ω', mΩ', P', hP', h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  let U : ℕ → Set ℂ := fun k =>
    (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k) : Set ℂ)
  have hU : ∀ k, U k = annulus 0 (s₁ * r k) (s₂ * r k) := by
    intro k
    ext z
    simp [U, HarmonicBalls.annulus, LQGMetric.Blueprint.annulus, Metric.mem_ball,
      Metric.mem_closedBall, dist_eq_norm, not_le, and_comm]
  let I : ℕ → Type := fun k => {φ : LQGMetric.TestC0 // tsupport (φ.1 : ℂ → ℝ) ⊆ U k}
  let X : Ω → ∀ k, I k → ℝ := fun ω k φ => hC ω φ.1.1
  let Y : Ω' → ∀ k, I k → ℝ := fun ω k φ => h ω φ.1.1
  have hXm : Measurable X := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun φ => ?_
    exact hwp.measurable_pairing _ (Field.isTestFunction_of_TestC φ.1.1)
  have hYm : Measurable Y := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun φ => ?_
    exact (LQGMetric.GFFInv.measurable_pair φ.1.1).comp hh.1.measurable
  let R : (LQGMetric.TestC0 → ℝ) → ∀ k, I k → ℝ := fun f k φ => f φ.1
  have hRm : Measurable R := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun φ => ?_
    exact measurable_pi_apply φ.1
  have hpair := Field.map_pairings_eq P P' hC hcirc h hwp hh.1
  have hbaseX : Measurable (fun ω (φ : LQGMetric.TestC0) => hC ω φ.1) := by
    exact measurable_pi_iff.mpr fun φ => hwp.measurable_pairing _ (Field.isTestFunction_of_TestC φ.1)
  have hbaseY : Measurable (fun ω (φ : LQGMetric.TestC0) => h ω φ.1) := by
    exact measurable_pi_iff.mpr fun φ => (LQGMetric.GFFInv.measurable_pair φ.1).comp hh.1.measurable
  have hlaw : P.map X = P'.map Y := by
    have heq := congrArg (fun μ : Measure (LQGMetric.TestC0 → ℝ) => μ.map R) hpair
    rw [Measure.map_map hRm hbaseX, Measure.map_map hRm hbaseY] at heq
    exact heq
  have hE : ∀ k, ∃ E' : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun ω => X ω k) inferInstance] E' ∧ E k =ᵐ[P] E' := by
    intro k
    obtain ⟨E', hEm, hEa⟩ := hlocal k
    refine ⟨E', ?_, hEa⟩
    rw [← hU k, Field.modConstSigma_eq_localPairings] at hEm
    exact hEm
  obtain ⟨F, hF, hsingle, hnone⟩ :=
    transfer_local_events_of_joint_law P P' X Y hXm hYm hlaw E hE
  refine ⟨Ω', mΩ', P', h, F, hP', hh, ?_, hsingle, hnone⟩
  intro k
  have hle : MeasurableSpace.comap (fun ω => Y ω k) inferInstance ≤
      LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
        (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k)) := by
    exact Field.localPairings_le_shifted_fieldSigma h
      (fun ω => -LQGMetric.circleAvg (h ω) (r k) 0) _
  exact hle _ (hF k)

/-- Lemma 6.6, obtained from Bonanno's annulus estimate and the law transfer. -/
theorem annulusIterate : AnnulusIterateStmt :=
  annulusIterate_of_leo annulusGFFLawTransfer

end MatedCRT

