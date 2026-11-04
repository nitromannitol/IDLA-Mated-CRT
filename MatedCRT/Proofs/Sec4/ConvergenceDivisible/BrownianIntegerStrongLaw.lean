import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RadialLawTransfer
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import MarkovProcess.Examples.BrownianMotion

/-! # Brownian motion at integer times -/

namespace MatedCRT

open Filter MeasureTheory ProbabilityTheory MarkovProcess Topology
open scoped NNReal

/-- The canonical Brownian motion is sublinear along the nonnegative integers. -/
theorem brownian_integer_strong_law :
    ∀ᵐ w ∂brownianMotion 0, Tendsto
      (fun n : ℕ => w (n : ℝ≥0) / (n : ℝ)) atTop (𝓝 0) := by
  let X : ℕ → ContinuousPath ℝ → ℝ := fun n w => w ((n + 1 : ℕ) : ℝ≥0) - w (n : ℝ≥0)
  have hXlaw : ∀ n, HasLaw (X n) (gaussianReal 0 1) (brownianMotion 0) := by
    intro n
    refine ⟨((ContinuousPath.measurable_coordinateProcess _).sub
      (ContinuousPath.measurable_coordinateProcess _)).aemeasurable, ?_⟩
    simpa [X] using brownianMotion_map_increment 0 (n : ℝ≥0) ((n + 1 : ℕ) : ℝ≥0) (by simp)
  have hindep : Pairwise (fun i j => X i ⟂ᵢ[brownianMotion 0] X j) := by
    have hi : ProbabilityTheory.HasIndepIncrements
        (fun (t : ℝ≥0) (w : ContinuousPath ℝ) => w t) (brownianMotion 0) := by
      simpa [ProbabilityTheory.HasIndepIncrements, MarkovProcess.HasIndepIncrements] using
        hasIndepIncrements_brownianMotion 0
    have hi' := hi.nat (t := fun n : ℕ => (n : ℝ≥0)) Nat.mono_cast
    intro i j hij
    exact hi'.indepFun hij
  have hint : Integrable (X 0) (brownianMotion 0) :=
    (hXlaw 0).integrable (memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1))
  have hmean : (brownianMotion 0)[X 0] = 0 := by
    rw [(hXlaw 0).integral_eq, integral_id_gaussianReal]
  have hslln := strong_law_ae_real X hint hindep (fun n => (hXlaw n).identDistrib (hXlaw 0))
  have hzero : ∀ᵐ w ∂brownianMotion 0, w 0 = 0 := by
    have h := (isBrownianReal_brownianMotion 0).hasLaw_eval 0
    simp only [sub_zero, gaussianReal_zero_var] at h
    exact h.ae_eq_of_dirac
  filter_upwards [hslln, hzero] with w hw hz
  rw [hmean] at hw
  convert hw using 1
  ext n
  congr 1
  simpa [X, hz] using (Finset.sum_range_sub (fun n : ℕ => w (n : ℝ≥0)) n).symm

/-- The centered circle-average radial process is sublinear at integer
logarithmic times. -/
theorem IsQuantumCone.ae_radial_integer_sublinear
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (hcirc ω (Real.exp (-(n : ℝ))) 0 - γ * n) / n) atTop (𝓝 0) :=
  hcone.ae_radial_integer_sublinear_of_brownian brownian_integer_strong_law

end MatedCRT
