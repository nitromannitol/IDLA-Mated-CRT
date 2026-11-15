import HarmonicBalls.Proofs.GFF.CoordinateModification
import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.LQG.LGDExponentZeroOne

/-! # Coordinates of a normalized whole-plane Gaussian free field -/

set_option autoImplicit false

open MeasureTheory Filter

namespace MatedCRT

/-- A normalized distribution-valued whole-plane GFF admits the joint pairing
and circle-average representation on the same probability space. At all dyadic
radii simultaneously, its circle averages agree spatially almost everywhere. -/
theorem exists_normalizedGFF_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P) :
    ∃ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc ∧
      (∀ ω (φ : LQGMetric.TestC), hC ω φ = X ω φ) ∧
      (∀ r, 0 < r → ∀ z, (fun ω => hcirc ω r z) =ᵐ[P]
        fun ω => LQGMetric.circleAvg (X ω) r z) ∧
      ∀ᵐ ω ∂P, ∀ k : ℕ, hcirc ω (LatticeProb.LQG.dyadicScale k) =ᵐ[volume]
        fun z => LQGMetric.circleAvg (X ω) (QuantumZipper.radius k) z := by
  obtain ⟨hC, hcirc, hg, hp, hc⟩ := HarmonicBalls.normalizedGFF_exists_projectGFF hX
  have hg' := (HarmonicBalls.LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hg
  have hs := LatticeProb.LQG.ae_ae_eq_circleAvg_of_isWholePlaneGFF hX.1.measurable hg' hc
  refine ⟨hC, hcirc, hg', hp, ?_, ?_⟩
  · intro r hr z
    filter_upwards [hc r hr z, hX.2] with ω hω hnorm
    simpa only [LQGMetric.CircleAvg.cInc, hnorm, sub_zero] using hω
  · filter_upwards [hs, hX.2] with ω hω hnorm k
    filter_upwards [hω k] with z hz
    simpa only [hnorm, sub_zero] using hz

end MatedCRT
