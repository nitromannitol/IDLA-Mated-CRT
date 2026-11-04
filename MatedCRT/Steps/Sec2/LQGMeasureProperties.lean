import MatedCRT.Draft.Section2

/-!
# Fact 2.2 split into its parts (properties of the LQG area measure of the quantum cone)

Fact 2.2 (fact:lqg-measure, lines 474-489; `LQGMeasurePropertiesStmt`) lists four properties of the LQG area measure
`μ_h` of the quantum cone. Here `μ_h` is, by definition (`HarmonicBalls.IsLQGMeasure`), a.s. the vague limit along
the dyadic scales `ε = 2⁻ᵏ` of the circle average approximations `ε^{γ²/2} e^{γ h_ε(z)} dz` (eq:measure-lim, line 468).
The statement is split into one Prop per part:
* I. `LQGMeasureRadonPart`: a.s. `μ_h` is locally finite (immediate from the definition) and non-atomic
  (`LQGMeasureNonAtomicPart`, cited);
* II. `LQGMeasureLocalityPart`: `μ_h(U)` is a.s. a `σ(h|_U)`-measurable random variable; it follows from the
  definition once circle averages are known to be local functionals of the field (`ConeCircleAverageLocalityStep`);
* III. `LQGMeasureWeylScalingPart`: a.s. `e^{γ f} · μ_h = μ_{h + f}` for every continuous `f`;
* IV. `LQGMeasureConformalCovariancePart`: a.s. coordinate change for every complex affine map. Its non-elementary
  content is the dilation case `LQGMeasureDilationCovariancePart`: the dyadic limit defining `μ_h` does not see
  the scales `s 2⁻ᵏ` for `s ∉ 2^ℤ`.

`lqgMeasureProperties_of_parts` assembles Fact 2.2 from the four parts.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Fact 2.2 I, non-atomic half** (line 477). A.s. the LQG measure of the quantum cone has no atoms:
`μ_h({x}) = 0` for every `x ∈ ℂ` simultaneously. This is not a consequence of the vague dyadic limit definition alone;
it is the non-atomicity of Gaussian multiplicative chaos (DS11, from the moment bounds for `μ_h(B_r(z))`; for a fixed
point `x`, the first moment bound is Leonardo Bonanno's `MatedCRTHarmonic.GMCFacts.ae_measure_singleton_eq_zero`,
for the whole-plane field). Cited. -/
def LQGMeasureNonAtomicPart : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, NullSingletonClass (μ ω)

/-- **Fact 2.2 I** (Radon measure, line 477). A.s. `μ_h` is a non-atomic locally finite Borel measure. -/
def LQGMeasureRadonPart : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧ NullSingletonClass (μ ω)

/-- **Fact 2.2 II** (Locality, lines 478-480). For every deterministic open `U`, `μ_h(U)` is a.s. equal to a
`σ(h|_U)`-measurable random variable (`σ(h|_U) = fieldSigmaAlgebra 0 hC U`). -/
def LQGMeasureLocalityPart : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ U : Set ℂ, IsOpen U → ∃ X : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra 0 hC U] X ∧
    (fun ω => μ ω U) =ᵐ[P] X

/-- **Circle averages are local functionals of the field** (the field ingredient of Fact 2.2 II). For the cone field,
an open `U` and a circle `∂B_ε(x)` whose closed disk lies in `U`, the circle average `h_ε(x)` is a.s. equal to a
`σ(h|_U)`-measurable random variable. It is the pairing of `h` with the uniform measure `ν_{ε,x}` on `∂B_ε(x)`,
supported in `U`, hence the `L²` limit of the pairings with the test functions `ν_{ε,x} * ψ_δ` supported in `U`
(mollifier `ψ_δ`, `δ → 0`): DS11 Section 3.1 for `h^ℂ`, and for the cone field through Definition 2.1 (the lateral
part has the law of that of `h^ℂ`, jointly in pairings and circle averages; the radial part enters both continuously).
The analogue for differences of circle averages modulo additive constant is `CircleAverageModConstStep`. -/
def ConeCircleAverageLocalityStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
  ∀ U : Set ℂ, IsOpen U → ∀ (ε : ℝ) (x : ℂ), 0 < ε → closedBall x ε ⊆ U →
    ∃ D : Ω → ℝ, Measurable[fieldSigmaAlgebra 0 hC U] D ∧ (fun ω => hcirc ω ε x) =ᵐ[P] D

/-- **Fact 2.2 III** (Weyl scaling, line 481). A.s., for every continuous `f : ℂ → ℝ`, the measure `e^{γ f} dμ_h` is the
LQG measure of `h + f` (the vague dyadic limit of the circle average approximations of `h + f`). -/
def LQGMeasureWeylScalingPart : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
    IsLQGLimit γ (addCircleAverage (hcirc ω) f)
      ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))

/-- **Fact 2.2 IV** (Conformal covariance, lines 483-487), for the complex affine maps `φ(z) = a z + w` (E-A6). A.s.,
for every `a ≠ 0` and `w`, the measure `A ↦ μ_h(φ(A))` is the LQG measure of `h ∘ φ + Q log |φ'|`. -/
def LQGMeasureConformalCovariancePart : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, ∀ a w : ℂ, a ≠ 0 →
    IsLQGLimit γ (fun r z => hcirc ω (‖a‖ * r) (a * z + w) + lqgQ γ * Real.log ‖a‖)
      ((μ ω).map fun x => a⁻¹ * (x - w))

/-- **Fact 2.2 IV for dilations** (lines 483-487 with `φ(z) = s z`, `s > 0`). A.s., for every `s > 0`, the measure
`A ↦ μ_h(s A)` is the LQG measure of `h(s ·) + Q log s`. Equivalently (by the change of variables `x = s z`), a.s. the
circle average approximations of `h` converge vaguely to `μ_h` along every rescaled dyadic sequence `s 2⁻ᵏ`, and not
only along `2⁻ᵏ`. Cited: DS11 Proposition 2.1 (a fixed map), SW16 (all maps simultaneously). -/
def LQGMeasureDilationCovariancePart : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
    IsLQGLimit γ (fun r z => hcirc ω (s * r) ((s : ℂ) * z) + lqgQ γ * Real.log s)
      ((μ ω).map fun x => (s : ℂ)⁻¹ * x)

/-- **Fact 2.2 IV for the non-dyadic dilations** `φ(z) = s z`, `1 < s < 2`. The dilations by powers of `2` only shift
the dyadic sequence of scales `2⁻ᵏ` defining `μ_h`, so `LQGMeasureDilationCovariancePart` reduces to this case. A.s.,
for every `s ∈ (1, 2)`, the circle average approximations of `h` converge vaguely to `μ_h` along `s 2⁻ᵏ`, in the form of
Fact 2.2 IV for `φ(z) = s z`. Cited: DS11 Proposition 2.1 (a fixed map), SW16 (all maps simultaneously). -/
def LQGMeasureNonDyadicDilationPart : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, ∀ s : ℝ, 1 < s → s < 2 →
    IsLQGLimit γ (fun r z => hcirc ω (s * r) ((s : ℂ) * z) + lqgQ γ * Real.log s)
      ((μ ω).map fun x => (s : ℂ)⁻¹ * x)

/-- **Fact 2.2 from its parts.** -/
theorem lqgMeasureProperties_of_parts (hI : LQGMeasureRadonPart) (hII : LQGMeasureLocalityPart)
    (hIII : LQGMeasureWeylScalingPart) (hIV : LQGMeasureConformalCovariancePart) :
    LQGMeasurePropertiesStmt := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hμ
  exact ⟨hI γ hγ hγ2 Ω P hC hcirc μ hμ, hII γ hγ hγ2 Ω P hC hcirc μ hμ, hIII γ hγ hγ2 Ω P hC hcirc μ hμ,
    hIV γ hγ hγ2 Ω P hC hcirc μ hμ⟩

end MatedCRT
