import MatedCRT.FirstPass.Derived.BLPathFunctionalDUnif
import LatticeProb.Prob.LevyProkhorovModulus

/-!
# Integrals of a bounded Lipschitz path functional against nearby laws of paths

A bounded Lipschitz path functional `F` for the local uniform series distance (the test functionals of the
random-walk-to-Liouville-Brownian-motion theorem, Berestycki–Gwynne (2020), Thm. 1.2) has a modulus of continuity
for the integral metric `dUnif` (`exists_dUnif_lt_abs_sub_le_of_isBoundedLipschitzPathFunctional`).  Combined with
the Lévy–Prokhorov bound for bounded continuous functions with a modulus of continuity, this gives:

* `abs_integral_sub_integral_le_of_pathLevyProkhorovEDist_lt`: for every `η > 0` there is `a > 0` such that two
  laws of continuous paths at Lévy–Prokhorov distance `< a` (for `dUnif`) have `F`-integrals within `η`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Integrals of a bounded Lipschitz path functional at small Lévy–Prokhorov distance.**  For every `η > 0`
there is `a > 0` such that `pathLevyProkhorovEDist μ ν < a` implies `|∫ F dμ - ∫ F dν| ≤ η`, for all laws
`μ, ν` of continuous paths `[0, ∞) → ℂ`. -/
theorem abs_integral_sub_integral_le_of_pathLevyProkhorovEDist_lt
    {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F) {η : ℝ} (hη : 0 < η) :
    ∃ a : ℝ, 0 < a ∧ ∀ μ ν : ProbabilityMeasure (ContinuousPath ℂ),
      pathLevyProkhorovEDist μ ν < ENNReal.ofReal a →
        |∫ x, F x ∂(μ : Measure (ContinuousPath ℂ)) - ∫ x, F x ∂(ν : Measure (ContinuousPath ℂ))| ≤ η := by
  obtain ⟨a1, ha1, hmod⟩ :=
    exists_dUnif_lt_abs_sub_le_of_isBoundedLipschitzPathFunctional hF (half_pos hη)
  have hε : 0 < min a1 (η / 4) := lt_min ha1 (by positivity)
  refine ⟨min a1 (η / 4), hε, fun μ ν hμν => ?_⟩
  have key := abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_modulus
    (Ω := ContinuousPath ℂ) (μ : Measure (ContinuousPath ℂ)) (ν : Measure (ContinuousPath ℂ))
    (ε := min a1 (η / 4)) (c := η / 2) hε (half_pos hη).le hμν (blPathFunctionalBCF hF)
    (fun x y hxy => hmod x y (lt_of_lt_of_le hxy (min_le_left _ _)))
  refine key.trans ?_
  have h1 := norm_blPathFunctionalBCF_le hF
  have h2 : min a1 (η / 4) ≤ η / 4 := min_le_right _ _
  have h3 : 2 * ‖blPathFunctionalBCF hF‖ * min a1 (η / 4) ≤ 2 * 1 * (η / 4) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 zero_le_two) h2 hε.le (by norm_num)
  linarith

end MatedCRT.FirstPass.Derived
