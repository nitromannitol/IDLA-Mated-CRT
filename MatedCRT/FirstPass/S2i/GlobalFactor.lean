import MatedCRT.FirstPass.S2i.CanonicalFactor
import MatedCRT.FirstPass.S2g.ScaleGluing
import MatedCRT.FirstPass.S2g.ScaleInvariance

/-! # The global family factor (FirstPass S2i, z2): `ConeGlobalFamilyFactorStep`

Deterministic part: the extension `extCircle` of a carrier point, the scaled circle profiles `scaleProc γ n p`
(`circleProcess` of the rescaled profile at the cone scale radius `scaleRad γ n p` and scale `b n = n + 1`), and their
identities with the cone scaling (`scaleProc_circleProcess`). Route: notes/fp-gaps/CHATGPT-q1-open-steps.md Section 9,
with the gluing `globalFamilyProcess_eq_of_scales` (FirstPass/S2g/ScaleGluing.lean). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- The extension of a circle average process to all radii, by `0` at nonpositive radii. -/
noncomputable def extCircle (p : Ioi (0 : ℝ) × ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then p (⟨r, h⟩, z) else 0

theorem circleProcess_extCircle (p : Ioi (0 : ℝ) × ℂ → ℝ) : circleProcess (extCircle p) = p := by
  funext q
  obtain ⟨⟨r, hr⟩, z⟩ := q
  have hr' : 0 < r := hr
  simp [circleProcess, extCircle, hr']

theorem coneScaleRadius_extCircle_circleProcess (γ : ℝ) (c : ℝ → ℂ → ℝ) (b : ℝ) :
    coneScaleRadius γ (extCircle (circleProcess c)) b = coneScaleRadius γ c b := by
  unfold coneScaleRadius
  congr 1
  ext r
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, by simpa [extCircle, circleProcess, hr] using h⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, by simpa [extCircle, circleProcess, hr] using h⟩

theorem circleProcess_rescaledCircle_extCircle (γ : ℝ) (c : ℝ → ℂ → ℝ) {R b : ℝ} (hR : 0 < R) :
    circleProcess (rescaledCircle γ (extCircle (circleProcess c)) R b) =
      circleProcess (rescaledCircle γ c R b) := by
  funext q
  obtain ⟨⟨r, hr⟩, z⟩ := q
  have hRr : 0 < R * r := mul_pos hR hr
  simp [circleProcess, rescaledCircle, extCircle, hRr]

/-- The scale radius `R_{b_n}` of a carrier point, at the scale `b n = n + 1` (the sequence of Section 9, G1). -/
noncomputable def scaleRad (γ : ℝ) (n : ℕ) (p : Ioi (0 : ℝ) × ℂ → ℝ) : ℝ :=
  coneScaleRadius γ (extCircle p) ((n : ℝ) + 1)

/-- The circle process of the rescaled profile at scale `b n`, for the carrier point `p`. -/
noncomputable def scaleProc (γ : ℝ) (n : ℕ) (p : Ioi (0 : ℝ) × ℂ → ℝ) : Ioi (0 : ℝ) × ℂ → ℝ :=
  circleProcess (rescaledCircle γ (extCircle p) (scaleRad γ n p) ((n : ℝ) + 1))

/-- On a circle average process of a continuous profile with positive scale radius, `scaleProc` is the circle process
of the cone rescaling `rescaledCircle γ c (R_b) b` (`coneScaleRadius γ c b`). -/
theorem scaleProc_circleProcess (γ : ℝ) (n : ℕ) (c : ℝ → ℂ → ℝ)
    (hR : 0 < coneScaleRadius γ c ((n : ℝ) + 1)) :
    scaleProc γ n (circleProcess c) =
      circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
  unfold scaleProc scaleRad
  rw [coneScaleRadius_extCircle_circleProcess]
  exact circleProcess_rescaledCircle_extCircle γ c hR

end MatedCRT
