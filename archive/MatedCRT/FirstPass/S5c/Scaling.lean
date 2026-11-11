import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Proofs.Sec5.LaplacianScaling

/-!
# FIRST PASS, Lemma 5.3: mass scaling of the least supersolution (G-5-3 note, Section 1)

For `0 < s ≤ u`, multiplying an admissible supersolution at mass `u` by `s / u` gives one at mass `s`
(its Laplacian is at most `(s/u) μ ≤ μ` and its obstacle is scaled correctly). Taking infima gives
`v_{B_r;z}(s) ≤ (s/u) v_{B_r;z}(u)` pointwise, hence `v_s / s ≤ v_u / u`: the continuum input of the
monotonicity of `R_n = -w_{s_n} / s_n` (G-5-3 Section 1, eq. (3)). Harmonic-balls potential theory only
(Armitage-Gardiner, Armstrong-Kuusi-Mourrat least supersolutions); no paper input.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open _root_.HarmonicBalls

/-- A Laplacian bound is preserved when the reference measure is enlarged. -/
lemma laplacianLE_mono_measure {w : ℂ → ℝ} {μ₁ μ₂ : Measure ℂ} {U : Set ℂ}
    (h : LaplacianLE w μ₁ U) (hle : μ₁ ≤ μ₂) : LaplacianLE w μ₂ U :=
  ⟨h.1, fun φ hφ hφ0 hi =>
    (h.2 φ hφ hφ0 (hi.mono_measure hle)).trans
      (integral_mono_measure hle (Filter.Eventually.of_forall fun x => hφ0 x) hi)⟩

/-- Scaling a supersolution by `c ∈ (0, 1]` keeps the Laplacian bound, the reference measure being `c μ ≤ μ`. -/
lemma laplacianLE_const_mul_of_le_one {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ} (h : LaplacianLE w μ U)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : LaplacianLE (fun x => c * w x) μ U := by
  refine laplacianLE_mono_measure (h.const_mul hc) ?_
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 hc1)

/-- **Mass scaling** (G-5-3 Section 1): for `0 < s ≤ u`, `v_{B_r;z}(s)(x) ≤ (s/u) v_{B_r;z}(u)(x)` at every
`x` of the closed disk, provided the values at `x` of the supersolutions are bounded below (the pole case is
Lemma 3.1 of the harmonic-balls paper, a hypothesis here). -/
theorem leastSupersolution_le_scaled {μ : Measure ℂ} {r : ℝ} {z : ℂ} {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u)
    (x : ℂ) (hb : ∀ t : ℝ, 0 ≤ t → BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z t)) :
    leastSupersolution μ r z s x ≤ (s / u) * leastSupersolution μ r z u x := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hc0 : 0 < s / u := div_pos hs hu
  have hc1 : s / u ≤ 1 := (div_le_one hu).2 hsu
  -- admissible supersolutions at mass `u`, scaled by `s / u`, are admissible at mass `s`
  have hmem : ∀ w ∈ supersolutions μ r z u, (fun y => (s / u) * w y) ∈ supersolutions μ r z s := by
    rintro w ⟨hc, hL, hob⟩
    refine ⟨continuousOn_const.mul hc, laplacianLE_const_mul_of_le_one hL hc0 hc1, ?_⟩
    intro y hy hyz
    have h1 := hob y hy hyz
    have h2 : (s / u) * (-u * greenFunction (ball 0 r) z y) ≤ (s / u) * w y :=
      mul_le_mul_of_nonneg_left h1 hc0.le
    have h3 : (s / u) * (-u * greenFunction (ball 0 r) z y) = -s * greenFunction (ball 0 r) z y := by
      field_simp
    linarith
  -- infimum at mass `s` lies below each scaled admissible value at mass `u`
  have hlow : ∀ w ∈ supersolutions μ r z u, leastSupersolution μ r z s x ≤ (s / u) * w x := by
    intro w hw
    have hS := hb s hs.le
    exact csInf_le hS ⟨fun y => (s / u) * w y, hmem w hw, rfl⟩
  -- infimum at mass `u` dominates `(u/s)` times the infimum at mass `s`
  have hne : ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z u).Nonempty :=
    ⟨(fun w : ℂ → ℝ => w x) 0, Set.mem_image_of_mem _ (zero_mem_supersolutions μ r z hu.le)⟩
  have hge : (u / s) * leastSupersolution μ r z s x ≤ leastSupersolution μ r z u x := by
    show (u / s) * leastSupersolution μ r z s x ≤ sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z u)
    refine le_csInf hne ?_
    rintro _ ⟨w, hw, rfl⟩
    show (u / s) * leastSupersolution μ r z s x ≤ w x
    have h1 := hlow w hw
    have h2 : (u / s) * leastSupersolution μ r z s x ≤ (u / s) * ((s / u) * w x) :=
      mul_le_mul_of_nonneg_left h1 (div_pos hu hs).le
    have h3 : (u / s) * ((s / u) * w x) = w x := by field_simp
    linarith
  have h4 : leastSupersolution μ r z s x = (s / u) * ((u / s) * leastSupersolution μ r z s x) := by
    field_simp
  rw [h4]
  exact mul_le_mul_of_nonneg_left hge hc0.le

end MatedCRT.S5c
