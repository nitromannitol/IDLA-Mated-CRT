import MatedCRT.FirstPass.Derived.MarkovStepInstance

/-!
# The annealed integral at one scale as an integral of quenched path laws (BG20 Lemma 7.4)

On the product space `annealedWalks` of the scales, the expectation of a bounded continuous functional of
the environment datum `Dₙ` and the `n`-th interpolated walk equals the expectation, over the environment,
of the integral against the quenched path law started at `kₙ`:
`E[g (Dₙ, Xₙ)] = ∫ ∫ g (Dₙ ω, x) d(walkPathLaw ω)(x) dP(ω)`.
This is the kernel representation used to pass to the limit with
`LatticeProb.tendsto_integral_integral_of_tendstoInMeasure_levyProkhorovDist`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Kernel representation of the annealed integral at the `n`-th scale.**  For a bounded continuous
`g` on the product of the datum space and the path space, the annealed expectation of
`g (Dₙ, Xₙ)` over `annealedWalks` is the environment average of the integral of `g (Dₙ ω, ·)` against the
quenched path law of the walk started at `kₙ`. -/
theorem integral_annealedWalks_eq_integral_walkPathLaw
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    {S₀ : Type*} [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [MeasurableSpace S₀]
    [BorelSpace S₀]
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) (k₀ : ℕ → ℤ)
    {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ} (hm : ∀ n, 0 < m n)
    {d : ℕ → Ω → S₀} (hd : ∀ n, Measurable (d n)) (g : (S₀ × C(ℝ≥0, ℂ)) →ᵇ ℝ) (n : ℕ) :
    ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2) ∂annealedWalks hS ε k₀ =
      ∫ ω, ∫ x, g (d n ω, x)
        ∂(walkPathLaw S (v n) (hm n).le (ε n) (k₀ n) ω : Measure C(ℝ≥0, ℂ)) ∂S.P := by
  have hev : Measurable fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n := measurable_pi_apply n
  have hF : Measurable fun q : Ω × (ℕ → ℤ) =>
      g (d n q.1, interpPathCM (v n q.1) (hm n).le q.2) :=
    g.continuous.measurable.comp (((hd n).comp measurable_fst).prodMk
      ((measurable_interpPathCM_uncurry (hm n).le).comp
        (((hv n).comp measurable_fst).prodMk measurable_snd)))
  have h1 : ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2)
      ∂annealedWalks hS ε k₀ = ∫ q, g (d n q.1, interpPathCM (v n q.1) (hm n).le q.2)
        ∂(S.P ⊗ₘ walkKernel hS (ε n) (k₀ n)) := by
    rw [← annealedWalks_map_eval hS ε k₀ n]
    exact (integral_map hev.aemeasurable hF.aestronglyMeasurable).symm
  rw [h1, Measure.integral_compProd]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hfm : Measurable fun y : C(ℝ≥0, ℂ) => g (d n ω, y) :=
      g.continuous.measurable.comp (measurable_const.prodMk measurable_id)
    exact integral_walkStartKernel hS (v n) (hm n).le (ε n) ω (k₀ n) hfm
  · exact Integrable.of_bound hF.aestronglyMeasurable ‖g‖
      (Filter.Eventually.of_forall fun q => by simpa using g.norm_coe_le_norm _)

end MatedCRT
