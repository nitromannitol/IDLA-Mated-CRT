import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.LinearAlgebra.Pi

/-!
# The law of a centred Gaussian process is determined by its covariance

Two real-valued Gaussian processes indexed by the same set `T`, both centred and with the same covariances, have the
same finite-dimensional distributions (`map_restrict_eq_of_covariance`), hence the same law on the product σ-algebra of
`T → ℝ` (`map_eq_of_covariance`, by uniqueness of projective limits). A linear functional of a finite-dimensional
marginal is a finite linear combination `∑ cᵢ Xᵢ`; its mean is `0` and its variance is `∑ cᵢ cⱼ Cov(Xᵢ, Xⱼ)`, and the
characteristic function of a Gaussian law is `exp(i m - σ²/2)`.

Used for the translation invariance of the whole-plane GFF modulo additive constant
(`MatedCRT/Proofs/Field/Translation.lean`).
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory

variable {T Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- A continuous linear functional on `ℝ^I` is `x ↦ ∑ᵢ xᵢ cᵢ`. -/
lemma strongDual_pi_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ))
    (x : ι → ℝ) : L x = ∑ i, x i * L (fun j => if i = j then 1 else 0) := by
  have h := L.toLinearMap.pi_apply_eq_sum_univ x
  simpa [smul_eq_mul] using h

/-- The variance of a finite linear combination of square-integrable random variables. -/
lemma variance_sum_mul_eq {ι : Type*} [Fintype ι] {Q : Measure Ω} [IsProbabilityMeasure Q] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 Q) (c : ι → ℝ) :
    variance (fun ω => ∑ i, c i * X i ω) Q = ∑ i, ∑ j, c i * c j * covariance (X i) (X j) Q := by
  have hm : ∀ i, MemLp (fun ω => c i * X i ω) 2 Q := fun i => (hX i).const_mul (c i)
  have hae : AEMeasurable (fun ω => ∑ i, c i * X i ω) Q :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hm i).aestronglyMeasurable.aemeasurable
  rw [← covariance_self hae, covariance_fun_sum_fun_sum hm hm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- **Centred Gaussian processes with the same covariance have the same finite-dimensional laws.** -/
theorem map_restrict_eq_of_covariance {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P')
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P' = 0)
    (hcov : ∀ s t, covariance (X s) (X t) P = covariance (Y s) (Y t) P') (I : Finset T) :
    P.map (fun ω => I.restrict fun t => X t ω) = P'.map (fun ω => I.restrict fun t => Y t ω) := by
  classical
  have hXI := hX.hasGaussianLaw I
  have hYI := hY.hasGaussianLaw I
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hX.hasGaussianLaw_eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P' := fun t => (hY.hasGaussianLaw_eval t).memLp_two
  apply Measure.ext_of_charFunDual
  funext L
  rw [hXI.charFunDual_map_eq L, hYI.charFunDual_map_eq L]
  set c : I → ℝ := fun i => L (fun j => if i = j then 1 else 0) with hc
  have hLX : (⇑L ∘ fun ω => I.restrict fun t => X t ω) = fun ω => ∑ i : I, c i * X i ω := by
    funext ω
    rw [Function.comp_apply, strongDual_pi_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hLY : (⇑L ∘ fun ω => I.restrict fun t => Y t ω) = fun ω => ∑ i : I, c i * Y i ω := by
    funext ω
    rw [Function.comp_apply, strongDual_pi_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hmeanX : ∫ ω, (∑ i : I, c i * X i ω) ∂P = 0 := by
    rw [integral_finsetSum _ fun (i : I) _ => ((hXm i).integrable one_le_two).const_mul (c i)]
    simp [integral_const_mul, hX0]
  have hmeanY : ∫ ω, (∑ i : I, c i * Y i ω) ∂P' = 0 := by
    rw [integral_finsetSum _ fun (i : I) _ => ((hYm i).integrable one_le_two).const_mul (c i)]
    simp [integral_const_mul, hY0]
  have hvX : variance (fun ω => ∑ i : I, c i * X i ω) P =
      ∑ i : I, ∑ j : I, c i * c j * covariance (X i) (X j) P :=
    variance_sum_mul_eq (X := fun (i : I) => X i) (fun i => hXm i) c
  have hvY : variance (fun ω => ∑ i : I, c i * Y i ω) P' =
      ∑ i : I, ∑ j : I, c i * c j * covariance (Y i) (Y j) P' :=
    variance_sum_mul_eq (X := fun (i : I) => Y i) (fun i => hYm i) c
  rw [hLX, hLY, hmeanX, hmeanY, hvX, hvY]
  simp only [hcov]

/-- **Centred Gaussian processes with the same covariance have the same law** on the product σ-algebra. -/
theorem map_eq_of_covariance {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P')
    (hXmeas : ∀ t, Measurable (X t)) (hYmeas : ∀ t, Measurable (Y t))
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P' = 0)
    (hcov : ∀ s t, covariance (X s) (X t) P = covariance (Y s) (Y t) P') :
    P.map (fun ω t => X t ω) = P'.map (fun ω t => Y t ω) := by
  have hXm' : Measurable fun ω t => X t ω := Measurable.of_eval hXmeas
  have hYm' : Measurable fun ω t => Y t ω := Measurable.of_eval hYmeas
  have h1 := isProjectiveLimit_map (X := X) (P := P) hXm'.aemeasurable
  have h2 := isProjectiveLimit_map (X := Y) (P := P') hYm'.aemeasurable
  refine h1.unique fun I => ?_
  exact (h2 I).trans (map_restrict_eq_of_covariance hX hY hX0 hY0 hcov I).symm

end MatedCRT.Field
