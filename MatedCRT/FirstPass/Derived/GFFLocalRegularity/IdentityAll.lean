import MatedCRT.FirstPass.Derived.GFFLocalRegularity.NewtonGradient
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelDist

/-!
# From one test function at a time to all test functions

For a continuous field `Y = (Y₀, Y₁)` on `ℂ`, the distribution `−∑ᵢ ∂_{eᵢ} Yᵢ` on an open set `U`
(`negDivDist`, built from Mathlib's `Distribution.ofFun` and `Distribution.lineDerivCLM`) pairs with a
test function `φ` as `∑ᵢ ∫ Yᵢ ∂_{eᵢ} φ`. A distribution on `U` is determined by its pairings with a fixed
countable family of test functions (`LQGMetric.injective_distOn_pairings`, from the separability of the
spaces `𝓓_K`). Hence, if a random distribution `h` satisfies `h φ = ∑ᵢ ∫ Yᵢ ∂_{eᵢ} φ` almost surely for each
fixed `φ`, the identity holds almost surely for every `φ` simultaneously (`ae_forall_eq_sum_integral`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Distributions

namespace MatedCRT.GFFLocalRegularity

variable {U : TopologicalSpace.Opens ℂ}

/-- The distribution `−∑ᵢ ∂_{eᵢ} Yᵢ` on `U` of a field `Y = (Y₀, Y₁)`. -/
def negDivDist (U : TopologicalSpace.Opens ℂ) (Y : Fin 2 → ℂ → ℝ) : LQGMetric.DistOn U :=
  -∑ i : Fin 2, Distribution.lineDerivCLM (basis i) (Distribution.ofFun U (Y i) volume ⊤)

/-- For a continuous field, `−∑ᵢ ∂_{eᵢ} Yᵢ` pairs with `φ` as `∑ᵢ ∫ Yᵢ ∂_{eᵢ} φ`. -/
theorem negDivDist_apply {Y : Fin 2 → ℂ → ℝ} (hY : ∀ i, Continuous (Y i)) (φ : LQGMetric.TestOn U) :
    negDivDist U Y φ = ∑ i : Fin 2, ∫ x, Y i x * fderiv ℝ φ x (basis i) := by
  simp only [negDivDist, neg_apply, FunLike.coe_sum,
    Finset.sum_apply, Finset.sum_neg_distrib, neg_neg, Distribution.lineDerivCLM_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Distribution.ofFun_apply ((hY i).locallyIntegrable.locallyIntegrableOn _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp),
    ((φ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv, smul_eq_mul, mul_comm]

/-- **The identity for all test functions at once.** If, for each test function `φ`, almost surely
`h φ = ∑ᵢ ∫ Yᵢ ∂_{eᵢ} φ` for a field `Y` continuous in the space variable, then almost surely the identity
holds for every `φ`. -/
theorem ae_forall_eq_sum_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn U} {Y : Fin 2 → ℂ → Ω → ℝ} (hY : ∀ i ω, Continuous fun x => Y i x ω)
    (hfix : ∀ φ : LQGMetric.TestOn U,
      ∀ᵐ ω ∂P, h ω φ = ∑ i : Fin 2, ∫ x, Y i x ω * fderiv ℝ φ x (basis i)) :
    ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestOn U,
      h ω φ = ∑ i : Fin 2, ∫ x, Y i x ω * fderiv ℝ φ x (basis i) := by
  have hgen : ∀ᵐ ω ∂P, ∀ j : ℕ × ℕ, h ω (LQGMetric.distGen U j) =
      ∑ i : Fin 2, ∫ x, Y i x ω * fderiv ℝ (LQGMetric.distGen U j) x (basis i) :=
    ae_all_iff.2 fun j => hfix _
  filter_upwards [hgen] with ω hω
  have heq : h ω = negDivDist U (fun i x => Y i x ω) :=
    LQGMetric.injective_distOn_pairings U (funext fun j => by
      dsimp only
      rw [hω j, negDivDist_apply (fun i => hY i ω)])
  intro φ
  rw [heq, negDivDist_apply (fun i => hY i ω)]

end MatedCRT.GFFLocalRegularity
