import MatedCRT.Defs.Setting

/-!
# Literature input: stationarity and independence of the past and future of space-filling SLE on the γ-quantum cone

`DMSPastFutureIndependence`: Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*,
arXiv:1409.7055v4, Theorem 1.9 (pp. 26-27; lines 1301-1349 of the text). Let `(ℂ, h, 0, ∞)` be a `γ`-quantum cone
and `η'` a whole-plane space-filling SLE_{κ'}, `κ' = 16/γ²`, from `∞` to `∞`, sampled independently of the cone and
reparametrized by `γ`-LQG area with `η'(0) = 0`. Then the joint law of `(h, η')` as a path-decorated quantum surface is
invariant under shifting by `t` units of LQG area time and recentring, (1.9):
`(h, η') =d (h(· + η'(t)), η'(· + t) - η'(t))`; and the quantum surfaces parametrized by `η'([0, ∞])` and
`η'([-∞, 0])` are independent.

The setup is the mating-of-trees coupling `MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling` of Lattice-Probability:
the cone is `coneField X (coneRadial γ γ B B')` (the circle average embedding, DMS Definition 4.10) and `η` is the
whole-plane space-filling SLE_{16/γ²} of the imaginary-geometry field reparametrized by its `γ`-LQG area. The past and
future surfaces enter with their curve decoration (`curveDecoratedSurfaceSigma`), the form in which
Berestycki–Gwynne (2020), arXiv:2003.10320, (7.35), use the theorem. The identification of the two surfaces as
quantum wedges of weight `2 - γ²/2` and the covariance (1.8) of the boundary-length process are not part of this
statement.

Cited input; to be replaced when proved in the mating-of-trees lane. PENDING TRUTH CHECK.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- **Re-embedding of a curve-decorated quantum surface** (Duplantier–Miller–Sheffield, Section 1.2;
Berestycki–Gwynne (2020), (2.1)). For a set of times `T`, `f` maps the curve-decorated quantum surface
`(η₂(T), h₂, η₂|_T)` onto `(η₁(T), h₁, η₁|_T)`: `f ∘ η₂ = η₁` on `T`; `f` is injective and continuous on `K₂ = η₂(T)`,
conformal on the interior of `K₂` and maps it onto the interior of `K₁ = η₁(T)`; and `h₂ = h₁ ∘ f + Q log |f'|` on
the interior of `K₂`, as pairings: `⟨h₂, φ⟩ = ⟨h₁, ψ⟩ + Q ∫ log |f'| φ` for every test function `φ` supported in
the interior of `K₂`, where `ψ(f(x)) |f'(x)|² = φ(x)` on the interior of `K₂` and `ψ = 0` off its image. -/
def IsCurveDecoratedReembedding (γ : ℝ) (T : Set ℝ) (h₁ : LQGMetric.DistC) (η₁ : C(ℝ, ℂ))
    (h₂ : LQGMetric.DistC) (η₂ : C(ℝ, ℂ)) (f : ℂ → ℂ) : Prop :=
  (∀ t ∈ T, f (η₂ t) = η₁ t) ∧ InjOn f (η₂ '' T) ∧ ContinuousOn f (η₂ '' T) ∧
    DifferentiableOn ℂ f (interior (η₂ '' T)) ∧ f '' interior (η₂ '' T) = interior (η₁ '' T) ∧
    ∀ φ ψ : LQGMetric.TestC, tsupport (φ : ℂ → ℝ) ⊆ interior (η₂ '' T) →
      (∀ x ∈ interior (η₂ '' T), ψ (f x) * ‖deriv f x‖ ^ 2 = φ x) →
      (∀ y, y ∉ f '' interior (η₂ '' T) → ψ y = 0) →
      h₂ φ = h₁ ψ + MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ x, Real.log ‖deriv f x‖ * φ x

/-- Two pairs (field, curve) with the same curve-decorated quantum surface over the times `T`: the second is a
re-embedding of the first. -/
def IsSameCurveDecoratedSurface (γ : ℝ) (T : Set ℝ) (p₁ p₂ : LQGMetric.DistC × C(ℝ, ℂ)) : Prop :=
  ∃ f : ℂ → ℂ, IsCurveDecoratedReembedding γ T p₁.1 p₁.2 p₂.1 p₂.2 f

/-- **The `σ`-algebra of the curve-decorated quantum surface over the times `T`**: the measurable sets of pairs
(field, curve) which contain, together with a pair, every pair with the same curve-decorated quantum surface over
`T`. -/
@[instance_reducible]
def curveDecoratedSurfaceSigma (γ : ℝ) (T : Set ℝ) : MeasurableSpace (LQGMetric.DistC × C(ℝ, ℂ)) where
  MeasurableSet' A := MeasurableSet A ∧ ∀ p₁ p₂, IsSameCurveDecoratedSurface γ T p₁ p₂ → (p₁ ∈ A ↔ p₂ ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun p₁ p₂ h => not_congr (hA.2 p₁ p₂ h)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun p₁ p₂ h => by
    simp only [mem_iUnion]
    exact exists_congr fun i => (hf i).2 p₁ p₂ h⟩

/-- **Shifting by `t` units of LQG area time and recentring** (Duplantier–Miller–Sheffield, (1.9)):
`(h, η') ↦ (h(· + η'(t)), η'(· + t) - η'(t))`. -/
noncomputable def lqgAreaTimeRecentre (t : ℝ) (p : LQGMetric.DistC × C(ℝ, ℂ)) : LQGMetric.DistC × C(ℝ, ℂ) :=
  (LQGMetric.affineComp 1 (p.2 t) p.1, ⟨fun u => p.2 (u + t) - p.2 t, by fun_prop⟩)

/-- **Literature input (Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*,
arXiv:1409.7055v4, Theorem 1.9, pp. 26-27, lines 1301-1349 of the text; the stationarity is (1.9), line 1347, the
independence is the last sentence, line 1349).** PENDING TRUTH CHECK. Cited input; to be replaced when proved in the
mating-of-trees lane.

For `γ ∈ (0, 2)`, on every probability space carrying a mating-of-trees coupling (the `γ`-quantum cone
`h = coneField X (coneRadial γ γ B B')` and the independent whole-plane space-filling SLE_{16/γ²} `η` from `∞` to `∞`,
parametrized by `γ`-LQG area with `η(0) = 0`), and for measurable versions `H` of the field and `η'` of the curve:
* (1.9) for each `t`, the curve-decorated quantum surfaces of `(h, η')` and of `(h(· + η'(t)), η'(· + t) - η'(t))`
  have the same law: they give the same probability to every set of `curveDecoratedSurfaceSigma γ univ`;
* the past and future curve-decorated quantum surfaces `(η'((-∞, 0]), h, η'|_{(-∞, 0]})` and
  `(η'([0, ∞)), h, η'|_{[0, ∞)})` are independent: the `σ`-algebras `curveDecoratedSurfaceSigma γ (Iic 0)` and
  `curveDecoratedSurfaceSigma γ (Ici 0)`, pulled back by `(H, η')`, are independent under `P`. -/
def DMSPastFutureIndependence : Prop :=
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
      Indep (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (curveDecoratedSurfaceSigma γ (Iic 0)))
        (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (curveDecoratedSurfaceSigma γ (Ici 0))) P

end MatedCRT
