import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-! # Stability of volume growth under comparable ball masses -/

namespace MatedCRT

open MeasureTheory Metric HarmonicBalls

/-- Uniform comparison of small ball masses preserves the volume-growth
condition after allowing positive slack in the exponents. -/
theorem volumeGrowth_of_ballMass_comparison
    {μ ν : Measure ℂ} {R βm βp c C : ℝ}
    (hV : VolumeGrowth μ R βm βp) (hc : 0 < c) (hC : 0 ≤ C)
    (hcomp : ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ → ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal c * μ (ball z r) ≤ ν (ball z r) ∧
        ν (ball z r) ≤ ENNReal.ofReal C * μ (ball z r)) :
    VolumeGrowth ν R (βm + 1) (βp / 2) := by
  obtain ⟨hβm, hβp, r₀, hr₀, hmass⟩ := hV
  obtain ⟨r₁, hr₁, hcomp⟩ := hcomp
  obtain ⟨r₂, hr₂, hsmall⟩ := exists_pos_of_eventually_nhdsGT
    ((eventually_rpow_le_mul hc (a := βm) (b := βm + 1) (by linarith)).and
      (eventually_mul_rpow_le C (a := βp) (b := βp / 2) (by linarith)))
  refine ⟨by linarith, by linarith, min r₀ (min r₁ r₂), by positivity, ?_⟩
  intro r hr hrr z hz
  have hr₀' : r < r₀ := lt_of_lt_of_le hrr (min_le_left _ _)
  have hr₁' : r < r₁ := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_left _ _))
  have hr₂' : r < r₂ := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hlo, hhi⟩ := hmass r hr hr₀' z hz
  obtain ⟨hlo', hhi'⟩ := hcomp r hr hr₁' z hz
  obtain ⟨hpowlo, hpowhi⟩ := hsmall r hr hr₂'
  constructor
  · calc
      ENNReal.ofReal (r ^ (βm + 1)) ≤ ENNReal.ofReal (c * r ^ βm) := ENNReal.ofReal_le_ofReal hpowlo
      _ = ENNReal.ofReal c * ENNReal.ofReal (r ^ βm) := ENNReal.ofReal_mul hc.le
      _ ≤ ENNReal.ofReal c * μ (ball z r) := by gcongr
      _ ≤ ν (ball z r) := hlo'
  · calc
      ν (ball z r) ≤ ENNReal.ofReal C * μ (ball z r) := hhi'
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (r ^ βp) := by gcongr
      _ = ENNReal.ofReal (C * r ^ βp) := (ENNReal.ofReal_mul hC).symm
      _ ≤ ENNReal.ofReal (r ^ (βp / 2)) := ENNReal.ofReal_le_ofReal hpowhi

/-- Volume growth also transfers when ball radii and centres are changed by
fixed factors. This is the deterministic estimate needed for coordinate
rescaling of a measure. -/
theorem volumeGrowth_of_scaled_ballMass_comparison
    {μ ν : Measure ℂ} {R R' βm βp c C k : ℝ} {f : ℂ → ℂ}
    (hV : VolumeGrowth μ R' βm βp) (hc : 0 < c) (hC : 0 ≤ C) (hk : 0 < k)
    (hf : ∀ z ∈ ball (0 : ℂ) R, f z ∈ ball (0 : ℂ) R')
    (hcomp : ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ → ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal c * μ (ball (f z) (k * r)) ≤ ν (ball z r) ∧
        ν (ball z r) ≤ ENNReal.ofReal C * μ (ball (f z) (k * r))) :
    VolumeGrowth ν R (βm + 1) (βp / 2) := by
  obtain ⟨hβm, hβp, r₀, hr₀, hmass⟩ := hV
  obtain ⟨r₁, hr₁, hcomp⟩ := hcomp
  have hck : 0 < c * k ^ βm := mul_pos hc (Real.rpow_pos_of_pos hk _)
  obtain ⟨r₂, hr₂, hsmall⟩ := exists_pos_of_eventually_nhdsGT
    ((eventually_rpow_le_mul hck (a := βm) (b := βm + 1) (by linarith)).and
      (eventually_mul_rpow_le (C * k ^ βp) (a := βp) (b := βp / 2) (by linarith)))
  refine ⟨by linarith, by linarith, min (r₀ / k) (min r₁ r₂), by positivity, ?_⟩
  intro r hr hrr z hz
  have hrr₀ : k * r < r₀ := by
    have := lt_of_lt_of_le hrr (min_le_left (r₀ / k) (min r₁ r₂))
    simpa [mul_comm] using (lt_div_iff₀ hk).mp this
  have hr₁' : r < r₁ := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_left _ _))
  have hr₂' : r < r₂ := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hlo, hhi⟩ := hmass (k * r) (mul_pos hk hr) hrr₀ (f z) (hf z hz)
  obtain ⟨hlo', hhi'⟩ := hcomp r hr hr₁' z hz
  obtain ⟨hpowlo, hpowhi⟩ := hsmall r hr hr₂'
  have hloeq : c * (k * r) ^ βm = (c * k ^ βm) * r ^ βm := by
    rw [Real.mul_rpow hk.le hr.le]; ring
  have hhieq : C * (k * r) ^ βp = (C * k ^ βp) * r ^ βp := by
    rw [Real.mul_rpow hk.le hr.le]; ring
  constructor
  · calc
      ENNReal.ofReal (r ^ (βm + 1)) ≤ ENNReal.ofReal ((c * k ^ βm) * r ^ βm) :=
        ENNReal.ofReal_le_ofReal hpowlo
      _ = ENNReal.ofReal c * ENNReal.ofReal ((k * r) ^ βm) := by
        rw [← ENNReal.ofReal_mul hc.le, hloeq]
      _ ≤ ENNReal.ofReal c * μ (ball (f z) (k * r)) := by gcongr
      _ ≤ ν (ball z r) := hlo'
  · calc
      ν (ball z r) ≤ ENNReal.ofReal C * μ (ball (f z) (k * r)) := hhi'
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((k * r) ^ βp) := by gcongr
      _ = ENNReal.ofReal ((C * k ^ βp) * r ^ βp) := by
        rw [← ENNReal.ofReal_mul hC, hhieq]
      _ ≤ ENNReal.ofReal (r ^ (βp / 2)) := ENNReal.ofReal_le_ofReal hpowhi

end MatedCRT
