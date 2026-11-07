import MatedCRT.Defs.LogCorrelatedField
import MatedCRT.Defs.RandomMeasureConvergence

/-!
# Convergence of Gaussian multiplicative chaos

Staged literature input for independent source audit; this is a proposition,
not an axiom or a proof of the published theorem.
-/

namespace MatedCRT

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Berestycki, *An elementary approach to Gaussian multiplicative chaos*,
arXiv:1506.09113v2, Theorem 1.1, p. 3, with assumptions (1.2)--(1.5),
pp. 2--3. The domain is bounded and open; the continuous part of the
covariance extends continuously to its closure. The finite reference
measure has dimension at least `d` in the energy sense, the regularizers
satisfy (1.4), and `0 < γ < √(2d)`. The limit is common to all regularizers;
for every Borel set its mass converges in probability and in `L¹`, and the
measures converge weakly in probability on the domain. -/
def BerestyckiGMCConvergenceStmt : Prop :=
  ∀ (k : ℕ) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (D : Set (EuclideanSpace ℝ (Fin k)))
    (g : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) → ℝ)
    (h : SignedMeasure (EuclideanSpace ℝ (Fin k)) → Ω → ℝ)
    (σ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure σ]
    (d γ : ℝ),
    IsOpen D → IsPreconnected D → D.Nonempty → Bornology.IsBounded D →
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      g p.1 p.2) (closure D ×ˢ closure D) →
    IsLogCorrelatedField P D g h → σ (closure D)ᶜ = 0 →
    0 ≤ d → d ≤ k → HasFiniteDimensionalEnergy σ d →
    0 < γ → γ < Real.sqrt (2 * d) →
    ∃ μ : Ω → Measure D,
      ∀ (θ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure θ],
        IsGMCRegularizer k θ →
        ∃ H : ℝ → Ω → EuclideanSpace ℝ (Fin k) → ℝ,
          IsLogFieldRegularizationVersion P k D h θ H ∧
          TendstoWeaklyInProbability P
            (fun ε ω => gmcApprox P (σ.comap Subtype.val) γ
              (fun (ω' : Ω) (x : D) => H ε ω' x.1) ω) μ ∧
          ∀ S : Set D, MeasurableSet S →
            Integrable (fun ω => (μ ω).real S) P ∧
            (∀ᶠ ε in 𝓝[>] (0 : ℝ), Integrable
              (fun ω => (gmcApprox P (σ.comap Subtype.val) γ
                (fun (ω' : Ω) (x : D) => H ε ω' x.1) ω).real S) P) ∧
            (∀ δ : ℝ, 0 < δ → Tendsto
              (fun ε => P {ω | δ < |(gmcApprox P (σ.comap Subtype.val) γ
                (fun (ω' : Ω) (x : D) => H ε ω' x.1) ω).real S - (μ ω).real S|})
              (𝓝[>] 0) (𝓝 0)) ∧
            Tendsto (fun ε => ∫ ω, |(gmcApprox P (σ.comap Subtype.val) γ
              (fun (ω' : Ω) (x : D) => H ε ω' x.1) ω).real S - (μ ω).real S| ∂P)
              (𝓝[>] 0) (𝓝 0)

end MatedCRT
