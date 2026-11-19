import MatedCRT.FirstPass.Derived.AnnealedWalksStartLawIntegral
import MatedCRT.FirstPass.Derived.MarkovTimeChange

/-!
# The Markov step of the embedded walks, for the family `K = id` of path laws

`ae_markovAt_of_walk_markov_step_at` is stated for a pseudo-metric carrier `S₀` of the data and a continuous map
`K : S₀ → PathLawFamily`.  The carrier of random continuous families of path laws,
`PathLawFamily = C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))`, is pseudo-metrizable, second countable and Borel,
but carries no `PseudoMetricSpace` instance.  This file records the instance of the Markov step with
`S₀ = PathLawFamily` and `K = id`, choosing a compatible pseudo-metric inside the proof, so that its statement
mentions no metric: if the pair `(D_n, X_n)` of the datum and the embedded walk converges in law to
`νD ⊗ₘ (s ↦ s z₀)`, and the quenched walk law at the discrete time `j_n / m_n` is close in Lévy–Prokhorov
distance to the datum evaluated at the position of the walk, then `s` has the Markov property at `(z₀, t)` for
`νD`-almost every `s`.

* `ae_markovAt_pathLawFamily_of_walk_markov_step_at`: the statement above.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb Preorder
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The Markov step with the family of path laws as the datum** (BG20 Lemma 7.4, Markov part).  For data
`d n ω ∈ PathLawFamily` such that `(d n (p n).1, X_n)` converges in law to `νD ⊗ₘ (s ↦ s z₀)` under the annealed
laws of the embedded walks, and such that the quenched walk law at the step `j n` stays close in Lévy–Prokhorov
distance, in probability, to `d n (p n).1` evaluated at the position of the interpolated walk at time
`j n / m n → t`, the family `s` has the Markov property at `(z₀, t)` for `νD`-almost every `s`. -/
theorem ae_markovAt_pathLawFamily_of_walk_markov_step_at
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n))
    {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ} (hm : ∀ n, 0 < m n) (j : ℕ → ℕ)
    {d : ℕ → Ω → PathLawFamily} (hd : ∀ n, Measurable (d n))
    {ν : Measure (PathLawFamily × C(ℝ≥0, ℂ))} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (PathLawFamily × C(ℝ≥0, ℂ)) →ᵇ ℝ,
      Filter.Tendsto (fun n => ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2)
          ∂annealedWalksAt hS ε hk) Filter.atTop (nhds (∫ q, g q ∂ν)))
    {t T : ℝ≥0}
    (hs : Filter.Tendsto (fun n => ((j n / m n : ℝ).toNNReal)) Filter.atTop (nhds t))
    (hsT : ∀ n, ((j n / m n : ℝ).toNNReal) ≤ T)
    (hclose : TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : (_ : ℕ) → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (v n) (hm n).le (ε n) (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1 :
          Measure C(ℝ≥0, ℂ))
        (d n (p n).1 (interpPathCM (v n (p n).1) (hm n).le (p n).2 ((j n / m n : ℝ).toNNReal)) :
          Measure C(ℝ≥0, ℂ))) Filter.atTop 0)
    {νD : Measure PathLawFamily} [IsProbabilityMeasure νD] {κ₀ : Kernel PathLawFamily C(ℝ≥0, ℂ)} {z₀ : ℂ}
    (hν : ν = νD ⊗ₘ κ₀) (hκ₀ : ∀ s : PathLawFamily, κ₀ s = (s z₀ : Measure C(ℝ≥0, ℂ))) :
    ∀ᵐ s ∂νD, MarkovAt (⇑(s : PathLawFamily)) z₀ t := by
  let : PseudoMetricSpace PathLawFamily := TopologicalSpace.pseudoMetrizableSpacePseudoMetric PathLawFamily
  let : MeasurableSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ))) := borel _
  have : BorelSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ))) := ⟨rfl⟩
  exact ae_markovAt_of_walk_markov_step_at hS ε hk hv hm j hd hlaw hs hsT (K := id) continuous_id
    hclose hν hκ₀

end MatedCRT.FirstPass.Derived
