import MatedCRT.Proofs.Sec4.GreenRecursion
import MatedCRT.Proofs.WalkPotential.Markov

/-!
# `GreenKernelLaplacianStep` and `NormExitTimeLaplacianStep`

This module was first written by worker c1.

The first-step recursion of the expected truncated visit counts `E N c = E_c[visits to b before min(τ_A, N)]`,
from the Markov property at time `1` (`srwLaw_eq_srwFirstStepLaw`, `lintegral_srwStep`,
MatedCRT/Proofs/WalkPotential/Markov.lean), gives `Δ G_A(·, b) = -δ_b` on `A` (eq:discrete-green-laplacian, line 797;
`laplacian_toReal_of_recursion`), hence eq:discrete-normalized-green-laplacian (line 804) and
eq:discrete-normalized-exit-laplacian (line 790) (Lawler-Limic, Proposition 6.2.3).
-/

namespace MatedCRT

open MeasureTheory Set Classical
open scoped ENNReal

variable {m : ℤ → ℤ → ℕ} {A : Set ℤ}

/-- Integration against the first-step decomposition of the walk. -/
theorem lintegral_srwLaw_firstStep (m : ℤ → ℤ → ℕ) (a : ℤ) {f : (ℕ → ℤ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂srwLaw m a = ∫⁻ b, ∫⁻ y, f (pathCons a y) ∂srwLaw m b ∂srwStep m a := by
  rw [srwLaw_eq_srwFirstStepLaw m a, srwFirstStepLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    hf.aemeasurable]
  refine lintegral_congr fun b => ?_
  rw [lintegral_map hf (measurable_pathCons a)]

/-- First-step recursion of the expected truncated visit counts. -/
theorem lintegral_visitsTrunc_succ (hlf : IsLocallyFiniteMult m) (hcons : ∀ a, m a (a + 1) ≠ 0) {a : ℤ}
    (ha : a ∈ A) (b : ℤ) (N : ℕ) :
    ∫⁻ x, visitsTrunc A b (N + 1) x ∂srwLaw m a = (if a = b then 1 else 0) +
      ∑ c ∈ nbrs hlf a, ENNReal.ofReal ((m a c : ℝ) / mdeg m a) * ∫⁻ x, visitsTrunc A b N x ∂srwLaw m c := by
  have hdeg : mdeg m a ≠ 0 := (mdeg_pos_of_ne_zero hlf (hcons a)).ne'
  have hdegpos : (0 : ℝ) < mdeg m a := Nat.cast_pos.2 (mdeg_pos_of_ne_zero hlf (hcons a))
  rw [lintegral_srwLaw_firstStep m a (measurable_visitsTrunc A b (N + 1))]
  have hpath : ∀ y, visitsTrunc A b (N + 1) (pathCons a y) = (if a = b then 1 else 0) + visitsTrunc A b N y :=
    fun y => by
      rw [visitsTrunc_succ (x := pathCons a y) ha]
      rfl
  have h1 : ∀ c, ∫⁻ y, visitsTrunc A b (N + 1) (pathCons a y) ∂srwLaw m c =
      (if a = b then 1 else 0) + ∫⁻ y, visitsTrunc A b N y ∂srwLaw m c := by
    intro c
    simp_rw [hpath]
    rw [lintegral_add_left measurable_const _, lintegral_const, measure_univ, mul_one]
  simp_rw [h1]
  rw [lintegral_add_left measurable_const _, lintegral_const, measure_univ, mul_one, lintegral_srwStep hlf hdeg,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.ofReal_div_of_pos hdegpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]
  ring

/-- **eq:discrete-green-laplacian** (line 797): `Δ G_A(·, b) = -δ_b` on a finite `A`. -/
theorem greenFn_laplacian_fst (hlf : IsLocallyFiniteMult m) (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite)
    (b : ℤ) : ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0) := by
  refine laplacian_toReal_of_recursion hcons hlf hA (E := fun N c => ∫⁻ x, visitsTrunc A b N x ∂srwLaw m c)
    (fun c N M h => lintegral_mono fun x => visitsTrunc_mono b x h) (fun c => by simp [visitsTrunc_zero])
    (fun N c hc => ?_) (fun N a ha => lintegral_visitsTrunc_succ hlf hcons ha b N)
    (G := fun c => ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m c) fun c => ?_
  · calc ∫⁻ x, visitsTrunc A b N x ∂srwLaw m c = ∫⁻ _, 0 ∂srwLaw m c := by
          refine lintegral_congr_ae ?_
          filter_upwards [srwLaw_ae_start m c] with x hx
          exact visitsTrunc_of_not_mem (by rw [hx]; exact hc) b N
      _ = 0 := lintegral_zero
  · simp_rw [visitsBeforeExit_eq_iSup]
    exact lintegral_iSup (fun N => measurable_visitsTrunc A b N) fun N M h x => visitsTrunc_mono b x h

/-- **eq:discrete-normalized-green-laplacian** (line 804; Lawler-Limic, Proposition 6.2.3). -/
theorem greenKernelLaplacianStep : GreenKernelLaplacianStep :=
  fun _ _ hsymm hlf hcons hA =>
    greenKernel_laplacian_of_firstStep hsymm hlf hcons hA fun b => greenFn_laplacian_fst hlf hcons hA b

/-- **eq:discrete-normalized-exit-laplacian** (line 790; Lawler-Limic, Proposition 6.2.3). -/
theorem normExitTimeLaplacianStep : NormExitTimeLaplacianStep :=
  fun _ _ _ hlf hcons hA => normExitTime_laplacian_of_firstStep hlf hA fun b => greenFn_laplacian_fst hlf hcons hA b

end MatedCRT
