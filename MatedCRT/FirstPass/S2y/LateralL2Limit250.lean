import MatedCRT.FirstPass.S2y.LateralHc250

/-!
# L² convergence of the whole-plane pairings along an approximating sequence

If test functions `ψ n` tend to a test function `φ` pointwise, are uniformly bounded and vanish off a fixed ball, then
`E[(h(ψ n) - h(φ))²] → 0` (dominated convergence for the whole-plane kernel `wholePlaneCov`, `LateralL2250`).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT.LQGMeasure

lemma measurable_wholePlaneCov_pair : Measurable (fun p : ℂ × ℂ => wholePlaneCov p.1 p.2) := by
  unfold wholePlaneCov
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `E[(h(ψ n) - h(φ))²] → 0` along a uniformly bounded sequence of test functions tending pointwise to `φ`. -/
theorem tendsto_integral_sq_pairing_sub [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {ψ : ℕ → ℂ → ℝ} {φ : ℂ → ℝ} {R M : ℝ}
    (hψ : ∀ n, IsTestFunction univ (ψ n)) (hφ : IsTestFunction univ φ)
    (hψR : ∀ n x, x ∉ closedBall (0 : ℂ) R → ψ n x = 0) (hφR : ∀ x, x ∉ closedBall (0 : ℂ) R → φ x = 0)
    (hψM : ∀ n x, |ψ n x| ≤ M) (hφM : ∀ x, |φ x| ≤ M)
    (hlim : ∀ x, Tendsto (fun n => ψ n x) atTop (𝓝 (φ x))) :
    Tendsto (fun n => ∫ ω, (hC ω (ψ n) - hC ω φ) ^ 2 ∂P) atTop (𝓝 0) := by
  have key := tendsto_double_integral_zero_of_pointwise (K := fun p : ℂ × ℂ => wholePlaneCov p.1 p.2)
    (R := R) (M := 2 * M) measurable_wholePlaneCov_pair (integrableOn_wholePlaneCov_square R)
    (g := fun n x => ψ n x - φ x)
    (fun n => ((hψ n).1.continuous.measurable).sub (hφ.1.continuous.measurable))
    (fun n x => by
      have h1 := hψM n x
      have h2 := hφM x
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
    (fun n x hx => by simp [hψR n x hx, hφR x hx])
    (fun x => by
      have := (hlim x).sub_const (φ x)
      simpa using this)
  refine key.congr (fun n => ?_)
  rw [integral_sq_pairing_sub h (hψ n) hφ]

end MatedCRT.LQGMeasure
