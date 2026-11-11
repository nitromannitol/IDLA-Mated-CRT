import Mathlib
import MarkovProcess.Path.Basic
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightedClock

/-!
# The base clock and its quenched occupation identity (Appendix B, step S1)

Source: `paper/appendix-occupation-C16.tex`, Lemma lem:occ-base (lines 140-151, eq:occ-base) and its
proof (lines 152-240). The base clock `A` is the limit of the circle-average clocks `A_ε`
(eq:occ-var, line 140 onwards); it is continuous and strictly increasing before `σ`.

What is formalized here:
* `BaseOccupationIdentity`: the conclusion of lem:occ-base, as a Prop (quenched, for every bounded
  Borel test function `q`, on one event of full field probability);
* `weightedClock_quenchedMean_of_base`: the identity of lem:occ-base implies the quenched mean of the
  weighted clock (paper eq:occ-weightedmean, S4 of `WeightedClock.lean`).

What is NOT formalized (the proof of lem:occ-base, lines 152-240, is not in Lean):
* the GMC convergence of the clocks (Berestycki 2017, Theorem 1.1, p. 3, hypotheses (1.2)-(1.5);
  Berestycki 2015, Theorem 1.2, p. 949, with proof p. 959 and Remark 3.5, p. 959): literature input
  (i) and (ii) of tex:113-124; not a Prop in `MatedCRT/External`;
* the Dirichlet-clock to clock transfer with multiplier `e^{γH}` (tex:199-201): no written argument;
* the ordinary Brownian occupation identity `E_y ∫_0^τ f(B) dt = 2 ∫_D G_D f` (step S0, Potential.lean).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

/-- The conclusion of Lemma lem:occ-base (paper tex:140-151, eq:occ-base): for the base clock `dA ω b`
of the path `b` in environment `ω`, `E_y[∫_0^σ q(B_s) dA(s) | g] = 2 ∫_D G_D(y,x) q(x) ν(dx)`,
simultaneously for every bounded Borel `q` (quenched form: the conditional expectation given the
environment is the Brownian integral for `P`-almost every `ω`). `G` is the Green function of `D` with
pole `y`; `ν ω = μ_g`. The factor `2` is the one of the ordinary Brownian occupation kernel `2 G_D`
(paper tex:48-52). -/
def BaseOccupationIdentity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (PB : Measure (ContinuousPath ℂ)) (D : Set ℂ) (G : ℂ → ℝ) (ν : Ω → Measure ℂ)
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
    ∫⁻ b, ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b) ∂PB =
      ∫⁻ x in D, ENNReal.ofReal (2 * G x) * q x ∂(ν ω)

/-- The identity of lem:occ-base yields the quenched mean of the weighted clock (paper
eq:occ-weightedmean, tex:277-281). The measurability input `hmeas` and the weight identity `hweight`
(eq:occ-weight, S2) are the hypotheses of `weightedClock_quenchedMean`. -/
theorem weightedClock_quenchedMean_of_base
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (PB : Measure (ContinuousPath ℂ))
    (γ : ℝ) (D : Set ℂ) (hDm : MeasurableSet D) (hD : D ⊆ ball 0 1)
    (G : ℂ → ℝ) (hGm : Measurable G)
    (μ ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0)
    (hbase : BaseOccupationIdentity P PB D G ν dA σ)
    (hmeas : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂P, ∀ S : Set ℂ, MeasurableSet S → S ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, g x ∂(μ ω) = ∫⁻ x in S, g x * gammaWeight γ x ∂(ν ω)) :
    ∀ᵐ ω ∂P, ∫⁻ b, weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) ∂PB =
      ∫⁻ x in D, ENNReal.ofReal (2 * G x) ∂(μ ω) :=
  weightedClock_quenchedMean P PB γ D hDm hD G hGm μ ν dA σ hbase hmeas hweight

end MatedCRT.KilledOccupation
