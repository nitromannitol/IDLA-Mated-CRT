import MatedCRT.FirstPass.S2i.CanonicalFactor
import MatedCRT.FirstPass.S2g.ScaleGluing
import MatedCRT.FirstPass.S2g.ScaleInvariance
import MatedCRT.FirstPass.S2i.ContinuousDecoder
import MatedCRT.Proofs.Measurability.ConeRescaledCircle

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


/-- The decoded log-profile along the real line at zero angle: `r ↦ c_x(r, 0) + Q log r` for the grid decoder `c_x`. -/
noncomputable def profAlong (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (x : ℕ → ℝ) (r : ℝ) : ℝ :=
  extCircle (fun q => profileDec hD x q) r 0 + lqgQ γ * Real.log r

theorem measurable_profAlong_rat (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (q : ℚ) (hq : 0 < (q : ℝ)) :
    Measurable fun x : ℕ → ℝ => profAlong γ hD x (q : ℝ) := by
  have hfun : (fun x : ℕ → ℝ => profAlong γ hD x (q : ℝ)) =
      fun x : ℕ → ℝ => profileDec hD x (⟨(q : ℝ), hq⟩, (0 : ℂ)) + lqgQ γ * Real.log q := by
    funext x
    simp only [profAlong, extCircle, hq, dite_true]
  have hm : Measurable fun x : ℕ → ℝ => ((x, (⟨(q : ℝ), hq⟩, (0 : ℂ))) : (ℕ → ℝ) × CirclePt) :=
    measurable_id.prodMk measurable_const
  rw [hfun]
  exact ((measurable_profileDec hD).comp hm).add measurable_const

/-- On a Borel set of codes of continuous profiles, the set where the scale radius exceeds `s` is Borel
(Mathlib-free level-set characterization, `lt_sSup_level_iff`). -/
theorem measurableSet_inter_radius_gt (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (b s : ℝ)
    (S : Set (ℕ → ℝ)) (hS : MeasurableSet S)
    (hcont : ∀ x ∈ S, ContinuousOn (profAlong γ hD x) (Ioi 0)) :
    MeasurableSet (S ∩ {x : ℕ → ℝ | s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b}) := by
  have hF : ∀ q : ℚ, 0 < (q : ℝ) → Measurable fun x : ℕ → ℝ => profAlong γ hD x (q : ℝ) :=
    fun q hq => measurable_profAlong_rat γ hD q hq
  have h1 := measurableSet_levelBoundedTest hF (γ⁻¹ * Real.log b)
  have h2 := measurableSet_existsLevelAbove hF (γ⁻¹ * Real.log b) s
  have h3 := measurableSet_existsLevelAbove hF (γ⁻¹ * Real.log b) 0
  have hP : MeasurableSet {x : ℕ → ℝ | (levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
      existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) s) ∨
      (s < 0 ∧ ¬(levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
        existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) 0))} := by
    exact (h1.inter h2).union ((MeasurableSet.const _).inter (h1.inter h3).compl)
  have heq : S ∩ {x : ℕ → ℝ | s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b} =
      S ∩ {x : ℕ → ℝ | (levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
      existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) s) ∨
      (s < 0 ∧ ¬(levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
        existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) 0))} := by
    ext x
    constructor
    · rintro ⟨hxS, hx⟩
      refine ⟨hxS, ?_⟩
      have hx' : s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b := hx
      have hr : coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b =
          sSup {r : ℝ | 0 < r ∧ profAlong γ hD x r = γ⁻¹ * Real.log b} := by
        unfold coneScaleRadius profAlong
        rfl
      rw [hr] at hx'
      exact (lt_sSup_level_iff (hcont x hxS) s).1 hx'
    · rintro ⟨hxS, hx⟩
      refine ⟨hxS, ?_⟩
      have hr : coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b =
          sSup {r : ℝ | 0 < r ∧ profAlong γ hD x r = γ⁻¹ * Real.log b} := by
        unfold coneScaleRadius profAlong
        rfl
      show s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b
      have hr : coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b =
          sSup {r : ℝ | 0 < r ∧ profAlong γ hD x r = γ⁻¹ * Real.log b} := by
        unfold coneScaleRadius profAlong
        rfl
      rw [hr]
      exact (lt_sSup_level_iff (hcont x hxS) s).2 hx
  rw [heq]
  exact hS.inter hP

end MatedCRT
