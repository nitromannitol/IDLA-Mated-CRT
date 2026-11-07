import MatedCRT.Proposed.BerestyckiGwynne
import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ConeVolumeGrowth
import HarmonicBalls.Proofs.Sec6.GreenPotentialBound

/-! # The cited cone ball-mass estimate implies Lemma 2.7 -/

namespace MatedCRT

open HarmonicBalls MeasureTheory Set Metric
open scoped ENNReal

/-- The exponents in Lemma 2.7 follow from the symmetric slack in
Berestycki--Gwynne's ball-mass estimate. -/
theorem volumeGrowthStmt_of_berestyckiGwynne
    (hBG : BerestyckiGwynneConeBallMassStmt) : VolumeGrowthStmt := by
  intro γ hγ hγ2 βp βm hβp hβpUpper hβm Ω _ P hC hcirc μ hcone
  let ζ := min 1 (min ((2 - γ) ^ 2 / 2 - βp) (βm - (2 + γ) ^ 2 / 2)) / 2
  have hζpos : 0 < ζ := by dsimp [ζ]; positivity
  have hζone : ζ < 1 := by
    dsimp [ζ]
    have := min_le_left (1 : ℝ) (min ((2 - γ) ^ 2 / 2 - βp) (βm - (2 + γ) ^ 2 / 2))
    linarith
  have hζp : ζ ≤ (2 - γ) ^ 2 / 2 - βp := by
    dsimp [ζ]
    have h : min 1 (min ((2 - γ) ^ 2 / 2 - βp) (βm - (2 + γ) ^ 2 / 2)) ≤
        (2 - γ) ^ 2 / 2 - βp := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hζm : ζ ≤ βm - (2 + γ) ^ 2 / 2 := by
    dsimp [ζ]
    have h : min 1 (min ((2 - γ) ^ 2 / 2 - βp) (βm - (2 + γ) ^ 2 / 2)) ≤
        βm - (2 + γ) ^ 2 / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨p, hp, C, δ₀, hδ₀, hprob⟩ := hBG Ω P γ hC hcirc μ hγ hγ2 hcone ζ hζpos hζone
  refine ⟨p, hp, C, min δ₀ 1, lt_min hδ₀ one_pos, ?_⟩
  intro δ hδ hδsmall
  have hδ₀' : δ < δ₀ := lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδone : δ ≤ 1 := (lt_of_lt_of_le hδsmall (min_le_right _ _)).le
  refine (measure_mono ?_).trans (hprob δ hδ hδ₀')
  intro ω hbad hgood
  apply hbad
  intro z hz
  obtain ⟨hlower, hupper⟩ := hgood z hz
  constructor
  · exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδone (by linarith))).trans hlower
  · exact hupper.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδone (by linarith)))

/-- The almost sure uniform upper mass bound used to control the logarithmic
singularity of the cone clock, for any exponent strictly below the sharp
threshold. The dyadic Borel--Cantelli and interpolation argument is supplied
by `ae_volumeGrowth_of_poly_ballMass`. -/
theorem IsConeField.ae_uniform_cone_ball_mass
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (hBG : BerestyckiGwynneConeBallMassStmt)
    {R b : ℝ} (hR : R < 1) (hb : 0 < b) (hbSharp : b < (2 - γ) ^ 2 / 2) :
    ∀ᵐ ω ∂P, ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ ω (ball z r) ≤ ENNReal.ofReal (r ^ b) := by
  let A : ℝ := (2 - γ) ^ 2 / 2
  let B : ℝ := (2 + γ) ^ 2 / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound := volumeGrowthStmt_of_berestyckiGwynne hBG γ hγ hγ2
    ((b + A) / 2) (B + 1) (by dsimp [A] at *; linarith)
    (by dsimp [A] at *; linarith) (by dsimp [B]; linarith)
    Ω P hC hcirc μ hcone
  have hpoly : PolyHighProb P (ballMassBoundEvent μ R ((b + A) / 2) (B + 1)) := by
    refine hbound.mono_of_small (sub_pos.2 hR) ?_
    intro δ hδ hδR ω hω z hz
    exact hω z (ball_subset_ball (by linarith) hz)
  filter_upwards [ae_volumeGrowth_of_poly_ballMass (a := b) (b := B + 2)
    hb (by dsimp [A] at *; linarith) (by linarith) (by linarith) hpoly] with ω hvol
  obtain ⟨_, _, r₀, hr₀, hmass⟩ := hvol
  exact ⟨r₀, hr₀, fun r hr hr₀ z hz => (hmass r hr hr₀ z hz).2⟩

/-- Cone ball-mass estimates give a uniformly bounded Green potential on
each open subdomain of a buffered disk. This includes a pole at the origin. -/
theorem IsConeField.ae_greenPotential_bddAbove
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (hBG : BerestyckiGwynneConeBallMassStmt)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) {D : Set ℂ}
    (hD : IsOpen D) (hDR : D ⊆ ball (0 : ℂ) R) :
    ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ y, greenPotential D (μ ω) y ≤ M := by
  filter_upwards [hcone.ae_volumeGrowth_inside_unit hγ hγ2
    (volumeGrowthStmt_of_berestyckiGwynne hBG) hR1] with ω hω
  have : IsLocallyFiniteMeasure (μ ω) := hω.1
  obtain ⟨βminus, βplus, hvol⟩ := hω.2
  exact Section6.greenPotential_bddAbove_of_volumeGrowth hR hD hDR hvol

end MatedCRT
