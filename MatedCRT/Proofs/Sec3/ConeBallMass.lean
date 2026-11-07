import MatedCRT.Proposed.BerestyckiGwynne
import MatedCRT.Draft.Section2

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

end MatedCRT
