import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedApproximation

/-! # Estimates for radial retraction onto a disk -/

namespace MatedCRT

open Metric Set
open scoped NNReal

/-- The scalar coefficient of radial retraction is Lipschitz, with constant
the reciprocal of the disk radius. -/
theorem abs_ballRetraction_coefficient_sub_le {r : ℝ} (hr : 0 < r) (z x y : ℂ) :
    |r / max r (dist x z) - r / max r (dist y z)| ≤ dist x y / r := by
  set a := max r (dist x z) with ha
  set b := max r (dist y z) with hb
  have har : r ≤ a := le_max_left _ _
  have hbr : r ≤ b := le_max_left _ _
  have hap : 0 < a := lt_of_lt_of_le hr har
  have hbp : 0 < b := lt_of_lt_of_le hr hbr
  have hd : |a - b| ≤ dist x y := by
    calc
      |a - b| = |max (dist x z) r - max (dist y z) r| := by rw [ha, hb, max_comm r, max_comm r]
      _ ≤ |dist x z - dist y z| := abs_max_sub_max_le_abs _ _ _
      _ ≤ dist x y := by simpa only [Real.dist_eq] using dist_dist_dist_le_left x y z
  have heq : r / a - r / b = r * (b - a) / (a * b) := by
    field_simp
  rw [heq, abs_div, abs_mul, abs_of_pos hr, abs_sub_comm,
    abs_of_pos (mul_pos hap hbp)]
  apply (div_le_iff₀ (mul_pos hap hbp)).2
  have hden : r * r ≤ a * b := mul_le_mul har hbr hr.le hap.le
  have hn := mul_le_mul_of_nonneg_left hd hr.le
  have ht := mul_le_mul_of_nonneg_left hden (div_nonneg (dist_nonneg (x := x) (y := y)) hr.le)
  have hcancel : dist x y / r * (r * r) = r * dist x y := by field_simp
  rw [hcancel] at ht
  linarith

/-- Radial retraction is Lipschitz on each bounded disk around its center. -/
theorem dist_ballRetraction_le {r R : ℝ} (hr : 0 < r) (z x y : ℂ)
    (hy : dist y z ≤ R) :
    dist (ballRetraction z r x) (ballRetraction z r y) ≤
      (1 + R / r) * dist x y := by
  set a := r / max r (dist x z) with ha
  set b := r / max r (dist y z) with hb
  have ha0 : 0 ≤ a := div_nonneg hr.le (le_of_lt (hr.trans_le (le_max_left _ _)))
  have ha1 : a ≤ 1 := (div_le_one (hr.trans_le (le_max_left _ _))).2 (le_max_left _ _)
  have hR : 0 ≤ R := dist_nonneg.trans hy
  have hc : |a - b| ≤ dist x y / r := abs_ballRetraction_coefficient_sub_le hr z x y
  have hid : ballRetraction z r x - ballRetraction z r y =
      (a : ℂ) * (x - y) + ((a - b : ℝ) : ℂ) * (y - z) := by
    simp only [ballRetraction, ← ha, ← hb, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, hid]
  calc
    ‖(a : ℂ) * (x - y) + ((a - b : ℝ) : ℂ) * (y - z)‖ ≤
        ‖(a : ℂ) * (x - y)‖ + ‖((a - b : ℝ) : ℂ) * (y - z)‖ := norm_add_le _ _
    _ = a * dist x y + |a - b| * dist y z := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg ha0, ← dist_eq_norm, ← dist_eq_norm]
    _ ≤ dist x y + (dist x y / r) * R := by
      gcongr
      exact mul_le_of_le_one_left dist_nonneg ha1
    _ = (1 + R / r) * dist x y := by ring

/-- Hölder data on the closed disk remain Hölder after radial retraction on
every larger closed disk. -/
theorem holder_ballRetraction {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (z : ℂ)
    {ψ : ℂ → ℝ} (hψ : IsHolderContinuousOn ψ (closedBall z r)) :
    IsHolderContinuousOn (fun x => ψ (ballRetraction z r x)) (closedBall z R) := by
  obtain ⟨C, χ, hχ, hχ1, hhol⟩ := hψ
  let K : ℝ≥0 := ⟨1 + R / r, by positivity⟩
  have hret : LipschitzOnWith K (ballRetraction z r) (closedBall z R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact dist_ballRetraction_le hr z x y (mem_closedBall.mp hy)
  refine ⟨C * K ^ (χ : ℝ), χ, hχ, hχ1, ?_⟩
  simpa only [mul_one, Function.comp_def] using
    hhol.comp hret.holderOnWith (fun x hx => ballRetraction_mem z hr x)

/-- The exit-cell comparison holds for data Hölder on the closed disk. -/
theorem correctedProjectedExit_of_holder_data (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    {ψ : ℂ → ℝ} (hψ : IsHolderContinuousOn ψ (closedBall z r))
    (hy : y ∈ ball z r) :
    TendstoInProbability S.P
      (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y -
        interpolatedExitExpectation S r z y ψ ε ω) (fun _ => 0) :=
  correctedProjectedExit_of_holder_retraction 𝒮 h211 hmeps hexc hX h28
    hγ hγ2 hρ hρ1 S hS hr hball
    ⟨1, by norm_num, holder_ballRetraction hr (by linarith) z hψ⟩ hy

end MatedCRT
