import MatedCRT.FirstPass.Derived.MarkovStepInstance

/-!
# Kernel representation of the scale-`n` integrals on the product of annealed laws

On the independent product `annealedWalks hS ε k₀` of the annealed laws `S.P ⊗ₘ walkKernel hS (ε n) (k₀ n)`,
the `n`-th coordinate has the annealed law of the `n`-th scale (`annealedWalks_map_eval`). By Fubini's theorem for
the composition-product, an integral of a function of the `n`-th coordinate is the `S.P`-average of the integral
against the quenched walk law:

* `integral_annealedWalks_eval`: `∫ F (p n) d(annealedWalks) = ∫ ∫ F (ω, x) d(walkKernel ω) dS.P(ω)` for every
  `F` integrable for the annealed law of the `n`-th scale.
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess LatticeProb
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

section Annealed

variable {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}

/-- **Integrals of the `n`-th coordinate of the product of annealed laws.**  For `F` integrable for the annealed
law `S.P ⊗ₘ walkKernel hS (ε n) (k₀ n)` of the `n`-th scale, the integral of `F` at the `n`-th coordinate of
`annealedWalks hS ε k₀` is the `S.P`-average of the integral of `F (ω, ·)` against the quenched walk law. -/
theorem integral_annealedWalks_eval (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ)
    (k₀ : ℕ → ℤ) (n : ℕ) {F : Ω × (ℕ → ℤ) → ℝ}
    (hF : Integrable F (S.P ⊗ₘ walkKernel hS (ε n) (k₀ n))) :
    ∫ p, F (p n) ∂annealedWalks hS ε k₀ =
      ∫ ω, ∫ x, F (ω, x) ∂(walkKernel hS (ε n) (k₀ n) ω) ∂S.P := by
  have hπ : Measurable fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n := measurable_pi_apply n
  have hmap := annealedWalks_map_eval hS ε k₀ n
  have hFm : AEStronglyMeasurable F
      ((annealedWalks hS ε k₀).map fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n) := by
    rw [hmap]
    exact hF.aestronglyMeasurable
  calc ∫ p, F (p n) ∂annealedWalks hS ε k₀
      = ∫ x, F x ∂((annealedWalks hS ε k₀).map fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n) :=
        (integral_map hπ.aemeasurable hFm).symm
    _ = ∫ x, F x ∂(S.P ⊗ₘ walkKernel hS (ε n) (k₀ n)) := by rw [hmap]
    _ = ∫ ω, ∫ x, F (ω, x) ∂(walkKernel hS (ε n) (k₀ n) ω) ∂S.P := Measure.integral_compProd hF

end Annealed

end MatedCRT
