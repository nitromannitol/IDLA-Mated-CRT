import MatedCRT.Draft.Section6
import MatedCRT.Steps.Sec6.ExitTimeScaleInvariance

/-!
# Lemma 6.8 (lemma:constant-order-lower-bound-div, line 2455; proof lines 2493-2621), route (b) of E-A10

`ConstantOrderLowerBoundDivLogStmt` is Lemma 6.8 in the form of ESCALATIONS "E-A10 resolution (c4)", verdict (b):
the constant `s₂` of the printed statement is replaced by `s₂ / (1 + |log r|)²`. Everything else is the Draft
statement `ConstantOrderLowerBoundDivStmt` verbatim (in particular the reading E-A9 of "exits through `A`").

The proof (`constantOrderLowerBoundDiv_of_steps`, MatedCRT/Proofs/Sec6/ConstantOrderLowerBoundDiv/OfSteps.lean)
follows lines 2493-2621 with the scale fix of E-A10 for line 2506 (`δ` dyadic with `√δ ∈ (r/(8√2), r/8]`, the shell
`(Θ̄ + B_{r/2+√δ}) \ (Θ̄ + B_{r/2})` in place of `(Θ̄ + B_{4√δ}) \ (Θ̄ + B_{3√δ})`), and Step 4 of route (b)
(`ExitTimeLogLossStep`, a consequence of Lemma 2.18). Two facts which the printed proof uses without proof are
isolated here:
* `GoodScaleEventMeasurableStep`: the events of Lemmas 6.4 and 2.7 at a fixed scale `δ` are `σ(h)`-measurable up to
  an inner approximation. Line 2505 ("by the Borel-Cantelli lemma, a.s. there exists a random `𝛅' > 0`") needs it for
  the `σ(h)`-measurability of `𝛅'`, which the statement asserts for `𝛅`.
* `SrwVisitSecondMomentStep`: the second moment method of line 2545 for the number `V` of visits to a set before the
  exit time, with `V ≤ τ` (line 2616). A general fact about simple random walk on a multigraph.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Lemma 6.8, route (b) of E-A10** (lemma:constant-order-lower-bound-div, line 2455). The Draft statement
`ConstantOrderLowerBoundDivStmt` with the bound `1 - s₂` replaced by `1 - s₂ / (1 + |log r|)²`: the second moment
bound of Step 4 (line 2612) loses the factor `(1 + log (1/𝐫_z))²` against the scale-invariant good-annulus event of
correction [C5], and `𝐫_z ≥ δ ≥ r²/128`. -/
def ConstantOrderLowerBoundDivLogStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm → ∃ ω₀ : ℝ, 0 < ω₀ ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ A ⊆ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ Θ,
        (∀ z : ℂ, ((A ∩ cellVertices ε (S.η ω) (ball z r)).ncard : ℝ) < s₁ * r ^ (2 * βm) / ε) →
        ∀ a ∈ cellVertices ε (S.η ω) (frontier (thickening (r / 2) (fillCells ε (S.η ω) Θ))),
          srwLaw (S.mult ε ω) a {x | ∀ n : ℕ,
            (n : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ Θ) x →
            x n ∈ A} ≤ ENNReal.ofReal (1 - s₂ / (1 + |Real.log r|) ^ 2)}

/-- The event of Lemma 6.4 at the scale `δ`, for the measure `μ = μ_h`: every `z ∈ (B_{ρ - 3√δ} \ B_{10√δ}) ∩
(δ/100) ℤ²` has a radius `𝐫_z ∈ [δ, √δ] ∩ {7^{-n}}` for which `E_{𝐫_z}(z; C)` occurs. -/
def GoodAnnulusCover (μ : Measure ℂ) (ρ c₀ C δ : ℝ) : Prop :=
  ∀ z : ℂ, z ∈ ball 0 (ρ - 3 * Real.sqrt δ) \ ball 0 (10 * Real.sqrt δ) →
    (∃ m n : ℤ, z = ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)) →
    ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulusEvent μ c₀ C r z

/-- The event of Lemma 2.7 at the scale `δ`, for the measure `μ = μ_h`:
`δ^{β⁻} ≤ μ(B_δ(z)) ≤ δ^{β⁺}` for all `z ∈ B_{1-δ}`. -/
def VolumeGrowthAt (μ : Measure ℂ) (βp βm δ : ℝ) : Prop :=
  ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ βm) ≤ μ (ball z δ) ∧ μ (ball z δ) ≤ ENNReal.ofReal (δ ^ βp)

/-- The event `E` contains a `σ(h)`-measurable event `F` with `P[Fᶜ] ≤ P[Eᶜ]` (the probability of the complement is
the outer measure). This holds if `E` is measurable for the completion of `σ(h)`. -/
def IsFieldInnerMeasurable {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (E : Set Ω) : Prop :=
  ∃ F : Set Ω, MeasurableSet[S.fieldSigma] F ∧ F ⊆ E ∧ S.P Fᶜ ≤ S.P Eᶜ

/-- **Step (measurability of the good-scale events, line 2505).** The events of Lemma 6.4 (`GoodAnnulusCover`) and of
Lemma 2.7 (`VolumeGrowthAt`) at a fixed scale `δ` are `σ(h)`-measurable up to an inner approximation. Both are
determined by `μ_h`, which is a measurable function of `h` (eq:measure-lim, line 470); the events involve suprema and
infima over the points of annuli and balls, so their measurability is for the completed `σ`-algebra (measurable
projection). Used for the Borel-Cantelli step of line 2505, which yields the `σ(h)`-measurable `𝛅`. -/
def GoodScaleEventMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ ρ c₀ C βp βm δ : ℝ,
    IsFieldInnerMeasurable S {ω | GoodAnnulusCover (S.μ ω) ρ c₀ C δ} ∧
    IsFieldInnerMeasurable S {ω | VolumeGrowthAt (S.μ ω) βp βm δ}

/-- **Step (second moment method for the visits before the exit time, lines 2543-2546 and 2616).** For simple random
walk on any multigraph `m` on `ℤ`, started at `b`, the number `V = #{n < τ_W : X_n ∈ E}` of visits to `E` before the
exit time from `W` satisfies `E[V]² ≤ E[V²] P[V ≥ 1] ≤ E[τ_W²] P[V ≥ 1]`, where `E[V] = ∑_{b' ∈ E} G_W(b, b')` is
written through the expected visit counts (`visitsBeforeExit`). -/
def SrwVisitSecondMomentStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (W E : Set ℤ) (b : ℤ),
    (∑' b' : E, ∫⁻ x, visitsBeforeExit W b' x ∂srwLaw m b) ^ 2 ≤
      exitTimeMoment m W b 2 * srwLaw m b {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime W x ∧ x n ∈ E}

end MatedCRT
