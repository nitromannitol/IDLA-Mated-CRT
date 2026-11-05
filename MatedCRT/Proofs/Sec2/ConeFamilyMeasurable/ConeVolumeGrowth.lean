import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ClusterDecoder
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit

/-! # Stopped cone families and volume growth -/

namespace MatedCRT

open MeasureTheory Filter Metric Set HarmonicBalls

/-- The volume-growth estimate gives the fixed-disk hypotheses for the
obstacle decoder for an arbitrary cone field. -/
theorem IsConeField.ae_volumeGrowth_inside_unit
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    {R : ℝ} (hR : R < 1) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧ ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus := by
  let A : ℝ := (2 - γ) ^ 2 / 2
  let B : ℝ := (2 + γ) ^ 2 / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound := h27 γ hγ hγ2 (A / 2) (B + 1) (by positivity)
    (by dsimp [A] at *; linarith) (by dsimp [B]; linarith)
    Ω P hC hcirc μ hcone
  have hpoly : PolyHighProb P (ballMassBoundEvent μ R (A / 2) (B + 1)) := by
    refine hbound.mono_of_small (sub_pos.2 hR) ?_
    intro δ hδ hδR ω hω z hz
    exact hω z (ball_subset_ball (by linarith) hz)
  filter_upwards [hcone.2.2, ae_volumeGrowth_of_poly_ballMass (a := A / 4) (b := B + 2)
    (by positivity) (by linarith) (by positivity) (by linarith) hpoly] with ω hμ hV
  exact ⟨hμ.isLocallyFiniteMeasure, _, _, hV⟩

/-- A measurable cone measure and stopping time determine the stopped
family when the volume-growth estimate holds. -/
theorem aemeasurable_coneFamilyProcess_of_volumeGrowth
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (hμ : AEMeasurable μ P) {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hT : AEMeasurable T P)
    (hf : ∀ᵐ ω ∂P, IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) :
    AEMeasurable (fun ω => familyProcess (Λ ω) (T ω)) P :=
  aemeasurable_familyProcess_of_positiveTime_cluster hT
    (aemeasurable_regularizedClusterFamily_of_volumeGrowth (by norm_num) hμ
      (hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num))) hf

end MatedCRT
