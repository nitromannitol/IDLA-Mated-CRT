import MatedCRT.FirstPass.Derived.GMS21Lemma33Cone

/-!
# The laws of the area measures of the two quantum cones on a bounded annulus: the three steps

`ConeAnnulusAreaLawEquivalence γ` (`GMS21Lemma33Cone.lean`) asserts that the laws of the outer data
`(e, μ_β|{δ < |z| < M})` of the `γ`-quantum cone (`β = γ`) and of the `0`-quantum cone (`β = 0`) are mutually
absolutely continuous, jointly with an independent curve `e`. Both cone fields are
`coneField X (coneRadial γ β B B')`: the lateral part of a whole-plane GFF plus the radial function
`z ↦ A_{-log |z|}` of the radial process `A` (`coneRadial`). On `{δ < |z| < M}` only the values `A_t` for
`-log M < t < -log δ` enter:

* for `t ≥ 0` (inside the unit circle) `A_t = B_t + β t`, the path `coneInnerPath β T B` on `[0, T]`;
* for `t < 0` (outside the unit circle) `A_{-s} = c(ℓ + s) - Q s` with `c(u) = B'_u + (Q - β) u` and `ℓ` the last
  zero of `c`, so that `A` on `[-S, 0)` is read off the path `coneOuterWindow (Q - β) S B'`.

The proof has three steps, each a statement of this file, combined in `ConeAnnulusAreaLawEquivalence.lean`:

* `ConeAnnulusLocality γ δ M` (locality of the LQG area measure): the outer data is almost surely a fixed
  measurable function of the curve, the lateral part of the field, the inner path and the outer window;
* `ConeInnerPathLaw` (Cameron–Martin): the laws of `coneInnerPath α₁ T B` and `coneInnerPath α₂ T B₀` are
  absolutely continuous for Brownian motions `B, B₀`;
* `ConeOuterWindowLaw` (Williams' path decomposition and Cameron–Martin): the laws of the outer windows of two
  Brownian motions with positive drifts `v₁, v₂` are absolutely continuous;

with the uniqueness of the law of the lateral part of a whole-plane GFF (`LateralPartLaw`).

Source: the answer to MQ-sbl-18, section "The field laws on a bounded annulus"; Gwynne–Miller–Sheffield
(arXiv:1705.11161), §2.3.1; Duplantier–Miller–Sheffield (arXiv:1409.7055), Definition 4.10; Miller–Sheffield,
Imaginary geometry I (arXiv:1201.1496), Proposition 3.4.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-- The radial process of a cone inside the unit circle up to time `T`: `t ↦ b_t + α min(t, T)`. On `[0, T]` it is
`coneRadial γ α b b'`. -/
def coneInnerPath (α T : ℝ) (b : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => b t + α * min (t : ℝ) T

/-- The radial process of a cone outside the unit circle up to `log`-radius `S`: `s ↦ c(ℓ + min(s, S))` with
`c(u) = b'_u + v u` and `ℓ` the last zero of `c`. For `0 < s ≤ S`, `coneRadial γ α b b' (-s)` is this value minus
`Q s`, with `v = Q - α`. -/
noncomputable def coneOuterWindow (v S : ℝ) (b' : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  fun s => (fun c : ℝ → ℝ => c (lastZeroR c + min (s : ℝ) S)) (fun u => b' u.toNNReal + v * u)

/-- **Brownian paths are almost everywhere measurable.** For a Brownian motion `B`, the path map `ω ↦ (t ↦ B_t(ω))`
into `ℝ≥0 → ℝ` (product σ-algebra) is almost everywhere measurable. -/
def BrownianPathAEMeasurable : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ),
    IsBrownianReal B P → AEMeasurable (fun ω t => B t ω) P

/-- **Step 1, locality of the area measure on the annulus.** For `0 < δ < M` there are times `T, S ≥ 0` and a
measurable map `G` such that for every `α < Q`, every whole-plane GFF `X` and Brownian motions `B, B'` with the
independence structure of the cone data, and every random curve `e`, almost surely the outer data of the cone
`coneField X (coneRadial γ α B B')` on `{δ < |z| < M}` is `G` of the curve, the lateral part of `X`, the inner path
`coneInnerPath α T B` and the outer window `coneOuterWindow (Q - α) S B'`. -/
def ConeAnnulusLocality (γ δ M : ℝ) : Prop :=
  ∃ (T S : ℝ) (G : C(ℝ, ℂ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → C(ℝ, ℂ) × Measure ℂ), 0 ≤ T ∧ 0 ≤ S ∧
    Measurable G ∧
    ∀ (α : ℝ), α < lqgQ γ → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → Field) (B B' : ℝ≥0 → Ω → ℝ) (e : Ω → C(ℝ, ℂ)),
      LQGMetric.IsWholePlaneGFF X P → IsBrownianReal B P → IsBrownianReal B' P →
      (IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
        IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) →
      ∀ᵐ ω ∂P, annulusOuterData (e ω) (quantumConeArea γ α X B B' ω) δ M =
        G (e ω, lateralPart (X ω), coneInnerPath α T (fun t => B t ω),
          coneOuterWindow (lqgQ γ - α) S (fun t => B' t ω))

/-- **Step 2, the inner radial paths (Cameron–Martin).** For Brownian motions `B, B₀`, drifts `α₁, α₂` and `T ≥ 0`, the path
`coneInnerPath α₁ T B` is almost everywhere measurable and its law is absolutely continuous with respect to the law
of `coneInnerPath α₂ T B₀`. -/
def ConeInnerPathLaw : Prop :=
  ∀ (α₁ α₂ T : ℝ), 0 ≤ T → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B B₀ : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → IsBrownianReal B₀ P →
    AEMeasurable (fun ω => coneInnerPath α₁ T (fun t => B t ω)) P ∧
      P.map (fun ω => coneInnerPath α₁ T (fun t => B t ω)) ≪
        P.map (fun ω => coneInnerPath α₂ T (fun t => B₀ t ω))

/-- **Step 3, the outer radial windows (Williams' path decomposition and Cameron–Martin).** For Brownian motions
`B', B₀'`, positive drifts `v₁, v₂` and `S ≥ 0`, the window `coneOuterWindow v₁ S B'` is almost everywhere measurable and its
law is absolutely continuous with respect to the law of `coneOuterWindow v₂ S B₀'`. -/
def ConeOuterWindowLaw : Prop :=
  ∀ (v₁ v₂ S : ℝ), 0 < v₁ → 0 < v₂ → 0 ≤ S → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B' B₀' : ℝ≥0 → Ω → ℝ), IsBrownianReal B' P → IsBrownianReal B₀' P →
    AEMeasurable (fun ω => coneOuterWindow v₁ S (fun t => B' t ω)) P ∧
      P.map (fun ω => coneOuterWindow v₁ S (fun t => B' t ω)) ≪
        P.map (fun ω => coneOuterWindow v₂ S (fun t => B₀' t ω))

/-- **Step 3, a measurable version of the outer window.** For `v > 0` and `S ≥ 0` there is a measurable map `Φ` on paths such
that for every Brownian motion `B'` almost surely `coneOuterWindow v S B' = Φ B'`. -/
def ConeOuterWindowMeasurable : Prop :=
  ∀ (v S : ℝ), 0 < v → 0 ≤ S → ∃ Φ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ), Measurable Φ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B' : ℝ≥0 → Ω → ℝ),
      IsBrownianReal B' P → ∀ᵐ ω ∂P, coneOuterWindow v S (fun t => B' t ω) = Φ (fun t => B' t ω)

/-- **The law of the lateral part of a whole-plane GFF.** The lateral part `h - h_{|·|}(0)` does not see the additive
constant: it agrees almost surely with a measurable map `Λ` of the field, and the law of `Λ X` is the same for any
two whole-plane GFFs. -/
def LateralPartLaw : Prop :=
  ∃ Λ : Field → Field, Measurable Λ ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Field),
      LQGMetric.IsWholePlaneGFF X P → ∀ᵐ ω ∂P, lateralPart (X ω) = Λ (X ω)) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X X₀ : Ω → Field),
      LQGMetric.IsWholePlaneGFF X P → LQGMetric.IsWholePlaneGFF X₀ P →
      P.map (fun ω => Λ (X ω)) = P.map (fun ω => Λ (X₀ ω))

end MatedCRT
