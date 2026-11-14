import MatedCRT.FirstPass.Derived.MarkovTimeChange
import LatticeProb.Prob.MarkovPathKernelDense

/-!
# The Markov property of a random continuous family of path laws, simultaneously in `(z, s)`

The Markov half of Berestycki–Gwynne (2020), Lemma 7.4, is obtained at a fixed pair `(z, s)` and almost every
environment `d` from the Markov step of the random walk and the convergence of the quenched path laws
(`ae_markovAt_of_walk_markov_step`).  Definition 7.1 asks for the Markov property at every `z` and `s`.  Since
`z ↦ P_z` is continuous, the Markov property at the pairs of a countable dense subset of `ℂ × ℝ≥0` propagates to
all pairs (`LatticeProb.markovAt_of_dense`), and a countable intersection of almost sure events is almost sure.

* `ae_isMarkovianPathFamily_of_ae_markovAt`: if for every `(z, s)` the Markov property at `(z, s)` holds for
  almost every `d`, then for almost every `d` the continuous family `K d` is Markovian (Definition 7.1);
* `ae_isMarkovTCBM_of_defines`: with the almost sure time-changed Brownian motion property (Definition 7.2,
  first half), the family is almost surely a Markovian time-changed Brownian motion.
-/

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- **Markov property for every `(z, s)` simultaneously, almost surely** (Berestycki–Gwynne, Lemma 7.4, quantifier
step): a random continuous family of path laws `K d` that, for every fixed `(z, s)`, has the Markov property at
`(z, s)` for almost every `d`, is almost surely Markovian in the sense of Definition 7.1. -/
theorem ae_isMarkovianPathFamily_of_ae_markovAt {S₀ : Type*} [MeasurableSpace S₀] {νD : Measure S₀}
    (K : S₀ → PathLawFamily) (h : ∀ (z : ℂ) (s : ℝ≥0), ∀ᵐ d ∂νD, LatticeProb.MarkovAt (⇑(K d)) z s) :
    ∀ᵐ d ∂νD, IsMarkovianPathFamily (K d) := by
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense (ℂ × ℝ≥0)
  have hQ : ∀ᵐ d ∂νD, ∀ q ∈ Q, LatticeProb.MarkovAt (⇑(K d)) q.1 q.2 :=
    (ae_ball_iff hQc).2 fun q _ => h q.1 q.2
  filter_upwards [hQ] with d hd
  exact fun z s => LatticeProb.markovAt_of_dense (K d).continuous hQd hd z s

/-- **Lemma 7.4 assembly**: a random continuous family of path laws that is almost surely a time-changed
Brownian motion (Definition 7.2, first half) and has the Markov property at every fixed `(z, s)` for almost every
environment is almost surely a Markovian time-changed Brownian motion. -/
theorem ae_isMarkovTCBM_of_defines {S₀ : Type*} [MeasurableSpace S₀] {νD : Measure S₀}
    (K : S₀ → PathLawFamily) (hdef : ∀ᵐ d ∂νD, DefinesTimeChangedBM (K d))
    (h : ∀ (z : ℂ) (s : ℝ≥0), ∀ᵐ d ∂νD, LatticeProb.MarkovAt (⇑(K d)) z s) :
    ∀ᵐ d ∂νD, IsMarkovTCBM (K d) := by
  filter_upwards [hdef, ae_isMarkovianPathFamily_of_ae_markovAt K h] with d h1 h2
  exact ⟨h1, h2⟩

end MatedCRT
