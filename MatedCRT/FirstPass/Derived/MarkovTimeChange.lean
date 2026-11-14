import MatedCRT.External.RevuzTimeChange
import LatticeProb.Prob.MarkovPathKernelDense

/-!
# Markovian time-changed planar Brownian motions: Definitions 7.1-7.3 of Berestycki-Gwynne

The three definitions that open Section 7 of Berestycki-Gwynne, *Random walks on mated-CRT maps and
Liouville Brownian motion* (arXiv 2003.10320), for a family `P : ℂ → Prob(C([0,∞), ℂ))` of path laws that is
continuous in the weak topology (the topology on such families of Section 6 is the topology of locally uniform
convergence of the laws in the Lévy-Prokhorov metric, which on a separable space is continuity into
`ProbabilityMeasure`):

* `IsMarkovianPathFamily` (Definition 7.1): the conditional law of `X_{s+·}` given `X|[0,s]` under `P_z` is
  `P_{X_s}`, in the test function form of `LatticeProb.MarkovAt` for every `z` and `s`.
* `DefinesTimeChangedBM` (Definition 7.2): for every `z`, under `P_z` the path is `u ↦ B_{τ_u}` for a standard
  planar Brownian motion `B` started at `z` and a continuous, strictly increasing process `τ` with `τ_0 = 0`
  (on some probability space carrying both). `IsMarkovTCBM` adds the Markov property.
* `IsInvariantFor`, `IsReversibleFor` (Definition 7.3): invariance `∫ P_z[X_t ∈ A] dμ(z) = μ(A)` and
  reversibility `∫_B P_z[X_t ∈ A] dμ(z) = ∫_A P_w[X_t ∈ B] dμ(w)` for Borel sets `A, B` and every `t`.

Reversibility implies invariance (take `B = ℂ`): `IsReversibleFor.isInvariantFor`.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

/-- Families of path laws `z ↦ P_z` on `C([0,∞), ℂ)`, continuous in `z` for the weak topology. -/
abbrev PathLawFamily : Type := C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))

/-- **Definition 7.1 (Markovian).** For every `z` and `s ≥ 0` the conditional law of `X_{s+·}` given
`X|[0,s]` is `P_{X_s}` under `P_z`. -/
def IsMarkovianPathFamily (P : PathLawFamily) : Prop :=
  ∀ (z : ℂ) (s : ℝ≥0), LatticeProb.MarkovAt (⇑P) z s

/-- **Definition 7.2 (time-changed Brownian motion).** For every `z` there are a probability space carrying a
standard planar Brownian motion `B` started at `z` (law `planarLaw z`) and a continuous, strictly increasing
process `τ` with `τ_0 = 0`, with `X_u = B_{τ_u}` for all `u` almost surely, and `P_z` is the law of `X`. -/
def DefinesTimeChangedBM (P : PathLawFamily) : Prop :=
  ∀ z : ℂ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (B X : Ω → ContinuousPath ℂ) (τ : Ω → ℝ≥0 → ℝ≥0),
    AEMeasurable B Q ∧ AEMeasurable X Q ∧ Q.map B = planarLaw z ∧
    (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧ ∀ u, X ω u = B ω (τ ω u)) ∧
    (P z : Measure (ContinuousPath ℂ)) = Q.map X

/-- **Definition 7.2 (Markovian time-changed Brownian motion).** -/
def IsMarkovTCBM (P : PathLawFamily) : Prop :=
  DefinesTimeChangedBM P ∧ IsMarkovianPathFamily P

/-- **Definition 7.3 (invariant measure).** `∫ P_z[X_t ∈ A] dμ(z) = μ(A)` for every Borel `A ⊆ ℂ` and `t ≥ 0`. -/
def IsInvariantFor (P : PathLawFamily) (μ : Measure ℂ) : Prop :=
  ∀ (t : ℝ≥0) (A : Set ℂ), MeasurableSet A →
    ∫⁻ z, (P z : Measure (ContinuousPath ℂ)) {x | x t ∈ A} ∂μ = μ A

/-- **Definition 7.3 (reversible measure).** `∫_B P_z[X_t ∈ A] dμ(z) = ∫_A P_w[X_t ∈ B] dμ(w)` for all Borel
`A, B ⊆ ℂ` and `t ≥ 0`. -/
def IsReversibleFor (P : PathLawFamily) (μ : Measure ℂ) : Prop :=
  ∀ (t : ℝ≥0) (A B : Set ℂ), MeasurableSet A → MeasurableSet B →
    ∫⁻ z in B, (P z : Measure (ContinuousPath ℂ)) {x | x t ∈ A} ∂μ =
      ∫⁻ w in A, (P w : Measure (ContinuousPath ℂ)) {x | x t ∈ B} ∂μ

/-- A reversible measure is invariant (take `B = ℂ` in Definition 7.3). -/
theorem IsReversibleFor.isInvariantFor {P : PathLawFamily} {μ : Measure ℂ} (h : IsReversibleFor P μ) :
    IsInvariantFor P μ := by
  intro t A hA
  have h1 := h t A Set.univ hA MeasurableSet.univ
  simp only [Measure.restrict_univ] at h1
  rw [h1]
  simp [Measure.restrict_apply]

end MatedCRT
