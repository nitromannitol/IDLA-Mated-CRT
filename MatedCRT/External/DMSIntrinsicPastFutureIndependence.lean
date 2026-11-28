import MatedCRT.External.DMSPastFutureIndependence

/-!
# Literature input: stationarity and independence of the past and future intrinsic curve-decorated wedges

`DMSIntrinsicPastFutureIndependence`: Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*,
arXiv:1409.7055v4, Theorem 1.9 (pp. 26-27; (1.9); lines 1301-1349 of the text). Let `(ℂ, h, 0, ∞)` be a `γ`-quantum
cone and `η'` a whole-plane space-filling SLE_{κ'}, `κ' = 16/γ²`, from `∞` to `∞`, sampled independently of the cone
and reparametrized by `γ`-LQG area with `η'(0) = 0`. Then the joint law of `(h, η')` as a path-decorated quantum
surface is invariant under shifting by `t` units of LQG area time and recentring, (1.9), and the past and future
`η'((-∞, 0])` and `η'([0, ∞))`, as path-decorated quantum surfaces, are independent quantum wedges.

Each half enters as its *intrinsic* curve-decorated wedge (Gwynne–Miller, arXiv:1701.05174, Definition 2.1, (2.6) and
§2.3.3, p. 18): in the thin regime `κ' ∈ (4, 8)` the ordered chain of beads (the connected components of the interior
of the half-range), each with the field on its interior up to the LQG coordinate change, and the area-parametrized
curve on each bead, lifted to the bead; in the thick regime `κ' ≥ 8` the interior of the half-range is a single
simply connected domain and the data are its chart. Two pairs (field, curve) have the same intrinsic curve-decorated
surface over a set of times `T` when a conformal bijection of the interiors of the two ranges `η(T)` carries the
field of one to the field of the other by the LQG coordinate change and the curve at every time of `T` at which it is
in the interior of its range to the curve at the same time (`IsIntrinsicCurveDecoratedReembedding`). No condition is
put on the boundary of the range, so distinct prime ends of a bead may have the same planar image; on the beads the
lifted curve, its entry and exit marks and the order of the beads are determined by the visits to the interior,
which are dense in each traversal interval.

The setup is the mating-of-trees coupling `MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling` of Lattice-Probability,
as in `DMSPastFutureIndependence`: the cone is `coneField X (coneRadial γ γ B B')` (the circle average embedding, DMS
Definition 4.10) and `η` is the whole-plane space-filling SLE_{16/γ²} of the imaginary-geometry field reparametrized by
its `γ`-LQG area. The stationarity is stated, as there, for the `σ`-algebra `curveDecoratedSurfaceSigma γ univ` of the
curve-decorated quantum surface over all times.

Cited input; to be replaced when proved in the mating-of-trees lane. PENDING TRUTH CHECK.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- **Intrinsic re-embedding of a curve-decorated quantum surface** (Duplantier–Miller–Sheffield, Section 1.2 and the
beaded quantum surfaces of pp. 11-12 of the text, a homeomorphism of the chain of beads conformal on each
bead; Gwynne–Miller, arXiv:1701.05174, Definition 2.1, (2.6)). For a set of times
`T`, `f` maps the intrinsic curve-decorated surface of `(h₂, η₂)` over `T` onto the one of `(h₁, η₁)`: with
`K₁ = η₁(T)` and `K₂ = η₂(T)`, `f` is conformal and injective on the interior of `K₂` and maps it onto the interior of
`K₁` (so it maps each connected component of the interior of `K₂`, a bead in the thin regime, conformally onto one of
`K₁`); `f ∘ η₂ = η₁` at the times of `T` at which `η₂` is in the interior of `K₂`, and these are the times of `T` at
which `η₁` is in the interior of `K₁`; and `h₂ = h₁ ∘ f + Q log |f'|` on the interior of `K₂`, as pairings:
`⟨h₂, φ⟩ = ⟨h₁, ψ⟩ + Q ∫ log |f'| φ` for every test function `φ` supported in the interior of `K₂`, where
`ψ(f(x)) |f'(x)|² = φ(x)` on the interior of `K₂` and `ψ = 0` off its image. -/
def IsIntrinsicCurveDecoratedReembedding (γ : ℝ) (T : Set ℝ) (h₁ : LQGMetric.DistC) (η₁ : C(ℝ, ℂ))
    (h₂ : LQGMetric.DistC) (η₂ : C(ℝ, ℂ)) (f : ℂ → ℂ) : Prop :=
  (∀ t ∈ T, η₂ t ∈ interior (η₂ '' T) → f (η₂ t) = η₁ t) ∧
    (∀ t ∈ T, η₁ t ∈ interior (η₁ '' T) → η₂ t ∈ interior (η₂ '' T)) ∧
    InjOn f (interior (η₂ '' T)) ∧ DifferentiableOn ℂ f (interior (η₂ '' T)) ∧
    f '' interior (η₂ '' T) = interior (η₁ '' T) ∧
    ∀ φ ψ : LQGMetric.TestC, tsupport (φ : ℂ → ℝ) ⊆ interior (η₂ '' T) →
      (∀ x ∈ interior (η₂ '' T), ψ (f x) * ‖deriv f x‖ ^ 2 = φ x) →
      (∀ y, y ∉ f '' interior (η₂ '' T) → ψ y = 0) →
      h₂ φ = h₁ ψ + MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ x, Real.log ‖deriv f x‖ * φ x

/-- Two pairs (field, curve) with the same intrinsic curve-decorated surface over the times `T`: the second is an
intrinsic re-embedding of the first. -/
def IsSameIntrinsicCurveDecoratedSurface (γ : ℝ) (T : Set ℝ) (p₁ p₂ : LQGMetric.DistC × C(ℝ, ℂ)) : Prop :=
  ∃ f : ℂ → ℂ, IsIntrinsicCurveDecoratedReembedding γ T p₁.1 p₁.2 p₂.1 p₂.2 f

/-- **The `σ`-algebra of the intrinsic curve-decorated surface over the times `T`**: the measurable sets of pairs
(field, curve) which contain, together with a pair, every pair with the same intrinsic curve-decorated surface over
`T`. -/
@[instance_reducible]
def intrinsicCurveDecoratedSurfaceSigma (γ : ℝ) (T : Set ℝ) : MeasurableSpace (LQGMetric.DistC × C(ℝ, ℂ)) where
  MeasurableSet' A := MeasurableSet A ∧ ∀ p₁ p₂, IsSameIntrinsicCurveDecoratedSurface γ T p₁ p₂ → (p₁ ∈ A ↔ p₂ ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun p₁ p₂ h => not_congr (hA.2 p₁ p₂ h)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun p₁ p₂ h => by
    simp only [mem_iUnion]
    exact exists_congr fun i => (hf i).2 p₁ p₂ h⟩

/-- **Literature input (Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*,
arXiv:1409.7055v4, Theorem 1.9, pp. 26-27 of the text; the stationarity is (1.9), the
independence of the two quantum wedges is the last sentence; the two wedges as intrinsic curve-decorated
surfaces: Gwynne–Miller, arXiv:1701.05174, Definition 2.1, (2.6) and §2.3.3, p. 18).** PENDING TRUTH CHECK. Cited
input; to be replaced when proved in the mating-of-trees lane.

For `γ ∈ (0, 2)`, on every probability space carrying a mating-of-trees coupling (the `γ`-quantum cone
`h = coneField X (coneRadial γ γ B B')` and the independent whole-plane space-filling SLE_{16/γ²} `η` from `∞` to `∞`,
parametrized by `γ`-LQG area with `η(0) = 0`), and for measurable versions `H` of the field and `η'` of the curve:
* (1.9) for each `t`, the curve-decorated quantum surfaces of `(h, η')` and of `(h(· + η'(t)), η'(· + t) - η'(t))`
  have the same law: they give the same probability to every set of `curveDecoratedSurfaceSigma γ univ`;
* the past and future intrinsic curve-decorated wedges, over the times `(-∞, 0]` and `[0, ∞)`, are independent: the
  `σ`-algebras `intrinsicCurveDecoratedSurfaceSigma γ (Iic 0)` and `intrinsicCurveDecoratedSurfaceSigma γ (Ici 0)`,
  pulled back by `(H, η')`, are independent under `P`. -/
def DMSIntrinsicPastFutureIndependence : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRTHarmonic.MatedCRT.Path2),
    MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
    ∀ H : Ω → LQGMetric.DistC, Measurable H →
      (∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ = H ω φ) →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂P, η' ω = η ω) →
      (∀ t : ℝ, ∀ A : Set (LQGMetric.DistC × C(ℝ, ℂ)), MeasurableSet[curveDecoratedSurfaceSigma γ univ] A →
        P ((fun ω => (H ω, η' ω)) ⁻¹' A) = P ((fun ω => lqgAreaTimeRecentre t (H ω, η' ω)) ⁻¹' A)) ∧
      Indep (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Iic 0)))
        (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Ici 0))) P

end MatedCRT
