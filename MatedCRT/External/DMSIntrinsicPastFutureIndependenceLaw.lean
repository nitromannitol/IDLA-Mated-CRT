import MatedCRT.External.DMSIntrinsicPastFutureIndependence
import MatedCRT.FirstPass.SLERef.Code

/-!
# Literature input: the past and future intrinsic curve-decorated wedges, for the law of the DMS curve

`DMSIntrinsicPastFutureIndependenceLaw ν`: Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of
trees*, arXiv:1409.7055v4, Theorem 1.9 (pp. 26-27; (1.9); lines 1301-1349 of the text), with the two halves taken as
intrinsic curve-decorated wedges (Gwynne–Miller, arXiv:1701.05174, Definition 2.1, (2.6) and §2.3.3, p. 18), as in
`DMSIntrinsicPastFutureIndependence`, on every mating-of-trees coupling whose Lebesgue-area curve `ηL` has the law of
the space-filling SLE of the construction of DMS: the law of the rational-time code `slePathCode (ηL ·)` is
`ν (16 / γ²)`.

Theorem 1.9 starts from the whole-plane space-filling SLE_{κ'} from `∞` to `∞` of the imaginary-geometry construction
(Miller–Sheffield, *Imaginary geometry IV*, Theorem 1.16; DMS footnote 4), sampled independently of the quantum cone.
The coupling predicate `MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling` asserts that `ηL` is a measurable function
`Φ` of the imaginary-geometry field with the clauses of its field `igMap`; the extra hypothesis
`P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)` pins the law of `ηL` to the law `ν (16 / γ²)` of that curve,
rooted at `0` and parametrized by Lebesgue area. The family `ν` is the normalized law of whole-plane space-filling SLE
(`HasNormalizedSLELaw`, `SLEReferenceExistsInput`); a consumer pairs this input with `HasNormalizedSLELaw 𝒮 ν` for the
same `ν`, which identifies the law of the Lebesgue-area curve of every valid environment for the model `𝒮`. The cone
area and root then determine the area-parametrized curve `η`, and the independence of the cone and the curve is a
clause of the coupling.

Cited input; to be replaced when proved in the mating-of-trees lane. PENDING TRUTH CHECK.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- **Literature input (Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*,
arXiv:1409.7055v4, Theorem 1.9, pp. 26-27 of the text; the stationarity is (1.9), the
independence of the two quantum wedges is the last sentence; the two wedges as intrinsic curve-decorated
surfaces: Gwynne–Miller, arXiv:1701.05174, Definition 2.1, (2.6) and §2.3.3, p. 18), for the law `ν (16 / γ²)` of
the Lebesgue-area parametrized whole-plane space-filling SLE_{16/γ²} from `∞` to `∞` rooted at `0`.** PENDING TRUTH
CHECK. Cited input; to be replaced when proved in the mating-of-trees lane.

For `γ ∈ (0, 2)`, on every probability space carrying a mating-of-trees coupling (the `γ`-quantum cone
`h = coneField X (coneRadial γ γ B B')` and the independent whole-plane space-filling SLE_{16/γ²} `η` from `∞` to `∞`,
parametrized by `γ`-LQG area with `η(0) = 0`) whose Lebesgue-area curve `ηL` has the rational-time code law
`ν (16 / γ²)`, and for measurable versions `H` of the field and `η'` of the curve:
* (1.9) for each `t`, the curve-decorated quantum surfaces of `(h, η')` and of `(h(· + η'(t)), η'(· + t) - η'(t))`
  have the same law: they give the same probability to every set of `curveDecoratedSurfaceSigma γ univ`;
* the past and future intrinsic curve-decorated wedges, over the times `(-∞, 0]` and `[0, ∞)`, are independent: the
  `σ`-algebras `intrinsicCurveDecoratedSurfaceSigma γ (Iic 0)` and `intrinsicCurveDecoratedSurfaceSigma γ (Ici 0)`,
  pulled back by `(H, η')`, are independent under `P`. -/
def DMSIntrinsicPastFutureIndependenceLaw (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRTHarmonic.MatedCRT.Path2),
    MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
    P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H →
      (∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ = H ω φ) →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂P, η' ω = η ω) →
      (∀ t : ℝ, ∀ A : Set (LQGMetric.DistC × C(ℝ, ℂ)), MeasurableSet[curveDecoratedSurfaceSigma γ univ] A →
        P ((fun ω => (H ω, η' ω)) ⁻¹' A) = P ((fun ω => lqgAreaTimeRecentre t (H ω, η' ω)) ⁻¹' A)) ∧
      Indep (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Iic 0)))
        (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Ici 0))) P

end MatedCRT
