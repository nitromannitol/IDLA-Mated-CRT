import MatedCRT.FirstPass.S4S6c.ShellConstOrder68
import MatedCRT.Defs.Setting

/-!
# The doubling constant `Dbl = max 1 C_good` of the one-test bound

The side condition `hdbl` of `shellOneTest_of_direct` (ShellHoneInst68.lean) bounds the mass of the enlarged test ball by
the mass of the test ball: `μ(B_{3 c₀ R}(x)) ≤ Dbl · μ(B_{c₀ R}(x))`. With `Dbl := max 1 C_good` it follows from the
good-annulus event (`IsGoodAnnulusEvent`, Defs/Setting.lean:333) by a deterministic argument:

* `B_{3 c₀ R}(x) ⊆ 𝔸_{R,2R}(z)` and `x ∈ 𝔸_{R,2R}(z)` (the geometric hypotheses, for the exit vertex `x` of the shell
  test ball around `z` with radius `R`);
* on `B_{3 c₀ R}(x)` the kernel satisfies `1 ≤ log(R/|u - x|) + 1` (since `|u - x| < R`), so
  `μ(B_{3c₀R}(x)) ≤ ∫_{𝔸} (log(R/|u-x|)+1) dμ(u)`;
* the good-annulus event bounds this supremum over `v ∈ 𝔸` by `C_good · inf_{w ∈ 𝔸} μ(B_{c₀R}(w))`, and `x ∈ 𝔸`.

The geometric inclusions are not derived here: they are named hypotheses of the lemma (the exit-vertex geometry is the
input `hx1`-type claim of `shellOneTest_of_direct`, still named). Terminology: good annuli (Armstrong-Kuusi-Mourrat),
Euclidean annuli (Armitage-Gardiner).
-/

open MeasureTheory Set Metric

namespace MatedCRT
namespace Lemma68ShellDbl

/-- **The doubling bound of the test balls from the good annulus.** If `x` lies in the annulus `𝔸_{R,2R}(z)` and the
enlarged ball `B_{3c₀R}(x)` lies in it too (with `3 c₀ ≤ 1`), then the good-annulus event `IsGoodAnnulusEvent μ c₀ C R z`
gives `μ(B_{3c₀R}(x)) ≤ C · μ(B_{c₀R}(x))`. -/
theorem measure_three_le_of_good_annulus {μ : Measure ℂ} {c0 C R : ℝ} {z x : ℂ} (_hc0 : 0 < c0) (hc3 : 3 * c0 ≤ 1)
    (hR : 0 < R) (hgood : MatedCRT.IsGoodAnnulusEvent μ c0 C R z)
    (hx : x ∈ HarmonicBalls.annulus z R (2 * R))
    (hsub : ball x (3 * c0 * R) ⊆ HarmonicBalls.annulus z R (2 * R)) :
    μ (ball x (3 * c0 * R)) ≤ ENNReal.ofReal C * μ (ball x (c0 * R)) := by
  -- pointwise: the kernel dominates `1` on the enlarged ball
  have hker : ∀ u ∈ ball x (3 * c0 * R),
      (1 : ENNReal) ≤ ENNReal.ofReal (Real.log (R / ‖u - x‖) + 1) := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    rcases eq_or_ne ‖u - x‖ 0 with h0 | h0
    · rw [h0, div_zero, Real.log_zero, zero_add, ENNReal.ofReal_one]
    · have hpos : 0 < ‖u - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hle : ‖u - x‖ ≤ R := by nlinarith
      have h1 : 1 ≤ R / ‖u - x‖ := (one_le_div hpos).2 hle
      have hlog : 0 ≤ Real.log (R / ‖u - x‖) := Real.log_nonneg h1
      rw [ENNReal.one_le_ofReal]
      linarith
  have h1 : μ (ball x (3 * c0 * R)) ≤
      ∫⁻ u in ball x (3 * c0 * R), ENNReal.ofReal (Real.log (R / ‖u - x‖) + 1) ∂μ := by
    have := setLIntegral_mono' (μ := μ) measurableSet_ball hker
    simpa [setLIntegral_const] using this
  have h2 : ∫⁻ u in ball x (3 * c0 * R), ENNReal.ofReal (Real.log (R / ‖u - x‖) + 1) ∂μ ≤
      ∫⁻ u in HarmonicBalls.annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - x‖) + 1) ∂μ :=
    lintegral_mono_set hsub
  have h3 : ∫⁻ u in HarmonicBalls.annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - x‖) + 1) ∂μ ≤
      ⨆ v ∈ HarmonicBalls.annulus z R (2 * R),
        ∫⁻ u in HarmonicBalls.annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ :=
    le_iSup₂ (f := fun v _ => ∫⁻ u in HarmonicBalls.annulus z R (2 * R),
      ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ) x hx
  have h4 : (⨆ v ∈ HarmonicBalls.annulus z R (2 * R),
        ∫⁻ u in HarmonicBalls.annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ) ≤
      ENNReal.ofReal C * ⨅ w ∈ HarmonicBalls.annulus z R (2 * R), μ (ball w (c0 * R)) := hgood
  have h5 : ENNReal.ofReal C * ⨅ w ∈ HarmonicBalls.annulus z R (2 * R), μ (ball w (c0 * R)) ≤
      ENNReal.ofReal C * μ (ball x (c0 * R)) :=
    by gcongr; exact iInf₂_le x hx
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- **The doubling constant.** With `Dbl := max 1 C_good` (`shellDbl68`, ShellConstOrder68.lean), the test balls satisfy
`μ(B_{3c₀R}(x)) ≤ Dbl · μ(B_{c₀R}(x))` under the geometric hypotheses of `measure_three_le_of_good_annulus`. -/
theorem measure_three_le_shellDbl68 {μ : Measure ℂ} {c0 C R : ℝ} {z x : ℂ} (hc0 : 0 < c0) (hc3 : 3 * c0 ≤ 1)
    (hR : 0 < R) (hgood : MatedCRT.IsGoodAnnulusEvent μ c0 C R z)
    (hx : x ∈ HarmonicBalls.annulus z R (2 * R))
    (hsub : ball x (3 * c0 * R) ⊆ HarmonicBalls.annulus z R (2 * R)) :
    μ (ball x (3 * c0 * R)) ≤ ENNReal.ofReal (MatedCRT.Lemma68ConstOrder.shellDbl68 C) * μ (ball x (c0 * R)) := by
  refine (measure_three_le_of_good_annulus hc0 hc3 hR hgood hx hsub).trans ?_
  have hD : ENNReal.ofReal C ≤ ENNReal.ofReal (MatedCRT.Lemma68ConstOrder.shellDbl68 C) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  gcongr

end Lemma68ShellDbl
end MatedCRT

#print axioms MatedCRT.Lemma68ShellDbl.measure_three_le_of_good_annulus
#print axioms MatedCRT.Lemma68ShellDbl.measure_three_le_shellDbl68
