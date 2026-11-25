import MatedCRT.FirstPass.Derived.WindowChartBG
import MatedCRT.FirstPass.Derived.ProbabilityMeasurePolish
import LatticeProb.Prob.CoupledIndependentLimit
import LatticeProb.Prob.IndepPi

/-!
# Independence of the windows (Berestycki–Gwynne (2020), Lemma 7.21) from the independence of the past and future
curve-decorated quantum surfaces (Duplantier–Miller–Sheffield, Theorem 1.9)

Berestycki–Gwynne (2020), arXiv:2003.10320, prove Lemma 7.21 (lines 3761-3838 of the text) as follows. Fix a time
`s ∈ (b, a')` between the two windows. By Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of
trees*, Theorem 1.9, the past and future curve-decorated quantum surfaces (7.35) at `s` are independent. The chart
field of each window is determined by the quantum surface containing it (line 3775). The discrete analogues
`P^{D,ε}_0` of the window chart laws are determined by the same surfaces (lines 3783-3804), so the triples at level
`ε` are independent, and their distance to the chart laws of the walk at level `ε` tends to zero in probability
(lines 3812-3831). The chart laws of the walk converge jointly with the chart fields (7.36) (lines 3831-3838), and
independence passes to the limit in law.

This file formalizes that argument for the inverse charts `windowChartBG` of `WindowChartBG.lean`.

## Main definitions

* `IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f`: `f` maps the curve-decorated quantum surface `(η₂(T), h₂, η₂|_T)` onto
  `(η₁(T), h₁, η₁|_T)` with the coordinate change `h₂ = h₁ ∘ f + Q log |f'|`.
* `curveSurfaceSigma γ T`: the `σ`-algebra of the curve-decorated quantum surface over the times `T` (measurable sets of
  pairs (field, curve) invariant under re-embedding).
* `DMS21PastFutureIndependence`: Duplantier–Miller–Sheffield, Theorem 1.9 (independence of the past and future
  curve-decorated quantum surfaces), as a named hypothesis.
* `BG20WindowFieldSurfaceInput`, `BG20DiscreteWindowLawInput`, `BG20WindowJointConvergenceInput`: the three steps of
  the printed proof of Lemma 7.21 stated as named hypotheses, with their source lines.
* `finCoords A B`: the finite-dimensional coordinates of a pair (field, probability law).

## Main statements

* `indepFun_prod_of_forall_finset`: two pairs (field, probability law) are independent once all their
  finite-dimensional coordinates are.
* `bg20ChartIndependenceInputBG_of_dms21`: `BG20ChartIndependenceInputBG` from the four hypotheses above.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-! ### Curve-decorated quantum surfaces -/

/-- **Re-embedding of a curve-decorated quantum surface.** For a set of times `T` (the past `(-∞, s]` or the future
`[s, ∞)` of the curve), `f` maps the curve-decorated quantum surface `(η₂(T), h₂, η₂|_T)` onto
`(η₁(T), h₁, η₁|_T)` (Duplantier–Miller–Sheffield, Section 1.2; Berestycki–Gwynne (2020), (2.1)): `f ∘ η₂ = η₁` on
`T`; `f` is injective and continuous on `K₂ = η₂(T)`, conformal on the interior of `K₂` and maps it onto the interior
of `K₁ = η₁(T)`; and `h₂ = h₁ ∘ f + Q log |f'|` on the interior of `K₂`, as pairings:
`⟨h₂, φ⟩ = ⟨h₁, ψ⟩ + Q ∫ log |f'| φ` for every test function `φ` supported in the interior of `K₂`, where
`ψ = (φ ∘ f⁻¹) |(f⁻¹)'|²`, that is `ψ(f(x)) |f'(x)|² = φ(x)` on the interior of `K₂` and `ψ = 0` off its image. -/
def IsSurfaceReembedding (γ : ℝ) (T : Set ℝ) (h₁ : LQGMetric.DistC) (η₁ : C(ℝ, ℂ)) (h₂ : LQGMetric.DistC)
    (η₂ : C(ℝ, ℂ)) (f : ℂ → ℂ) : Prop :=
  (∀ t ∈ T, f (η₂ t) = η₁ t) ∧ InjOn f (η₂ '' T) ∧ ContinuousOn f (η₂ '' T) ∧
    DifferentiableOn ℂ f (interior (η₂ '' T)) ∧ f '' interior (η₂ '' T) = interior (η₁ '' T) ∧
    ∀ φ ψ : LQGMetric.TestC, tsupport (φ : ℂ → ℝ) ⊆ interior (η₂ '' T) →
      (∀ x ∈ interior (η₂ '' T), ψ (f x) * ‖deriv f x‖ ^ 2 = φ x) →
      (∀ y, y ∉ f '' interior (η₂ '' T) → ψ y = 0) →
      h₂ φ = h₁ ψ + MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ x, Real.log ‖deriv f x‖ * φ x

/-- Two pairs (field, curve) with the same curve-decorated quantum surface over the times `T`: the second is a
re-embedding of the first. -/
def SameCurveSurface (γ : ℝ) (T : Set ℝ) (p₁ p₂ : LQGMetric.DistC × C(ℝ, ℂ)) : Prop :=
  ∃ f : ℂ → ℂ, IsSurfaceReembedding γ T p₁.1 p₁.2 p₂.1 p₂.2 f

/-- **The `σ`-algebra of the curve-decorated quantum surface over the times `T`**: the measurable sets of pairs
(field, curve) which contain, together with a pair, every pair with the same curve-decorated quantum surface over
`T`. A function of the pair measurable for it is a function of the quantum surface. -/
@[instance_reducible]
def curveSurfaceSigma (γ : ℝ) (T : Set ℝ) : MeasurableSpace (LQGMetric.DistC × C(ℝ, ℂ)) where
  MeasurableSet' A := MeasurableSet A ∧ ∀ p₁ p₂, SameCurveSurface γ T p₁ p₂ → (p₁ ∈ A ↔ p₂ ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun p₁ p₂ h => not_congr (hA.2 p₁ p₂ h)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun p₁ p₂ h => by
    simp only [mem_iUnion]
    exact exists_congr fun i => (hf i).2 p₁ p₂ h⟩

theorem curveSurfaceSigma_le (γ : ℝ) (T : Set ℝ) :
    curveSurfaceSigma γ T ≤ (inferInstance : MeasurableSpace (LQGMetric.DistC × C(ℝ, ℂ))) :=
  fun _ hA => hA.1

/-- **Literature input (Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*,
arXiv:1409.7055, Theorem 1.9, last sentence (1409.7055.txt line 1349), with the stationarity (1.9); used in
Berestycki–Gwynne (2020), proof of Lemma 7.21, (7.35), 2003.10320.txt lines 3768-3774).** PENDING TRUTH CHECK.

For the `γ`-quantum cone `h` and an independent whole-plane space-filling SLE_{16/γ²} `η` from `∞` to `∞`
parametrized by `γ`-LQG area with `η(0) = 0` (a valid environment), and every time `s`, the past and future
curve-decorated quantum surfaces `(η((-∞, s]), h|_{η((-∞, s])}, η|_{(-∞, s]})` and
`(η([s, ∞)), h|_{η([s, ∞))}, η|_{[s, ∞)})` are independent: the `σ`-algebras `curveSurfaceSigma γ (Iic s)` and
`curveSurfaceSigma γ (Ici s)`, pulled back by measurable versions `H` of the field and `η'` of the curve, are
independent under `P`. Theorem 1.9 states this at `s = 0` (the two surfaces are independent quantum wedges); the
invariance (1.9) of `(h, η)` under shifting by `s` units of LQG area time and recentring gives every `s`. -/
def DMS21PastFutureIndependence (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ s : ℝ, Indep (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (curveSurfaceSigma γ (Iic s)))
      (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (curveSurfaceSigma γ (Ici s))) S.P

/-! ### The window data as functions of the field and the curve -/

/-- The chart field `h ∘ φ + Q log |φ'|` of the window `(a, u, b)` of the curve `p.2`, for the field `p.1` and the
inverse chart `windowChartBG a u b p.2`. -/
noncomputable def windowFieldBG (γ a u b : ℝ) (p : LQGMetric.DistC × C(ℝ, ℂ)) : 𝓓(unitDiscOpens, ℝ) → ℝ :=
  chartFieldPairing γ p.1 (windowDomain p.2 a u b) (p.2 u) (windowChartBG a u b p.2)

theorem windowChartField_eq_windowFieldBG (γ a u b : ℝ) (q : JointSample) :
    windowChartField γ a u b (windowChartBG a u b q.1.2) q =
      windowFieldBG γ a u b (LQGMetric.pairJInv ⊤ q.1.1.1, q.1.2) :=
  rfl

/-- The chart law of the window `(a, u, b)` of the curve `η` for the family of path laws `K` and the inverse chart
`windowChartBG a u b η`: the image of the law from `η(u)` under "stop at the exit from the window and apply the
chart". -/
noncomputable def windowLawBG (a u b : ℝ) (η : C(ℝ, ℂ)) (K : PathLawFamily) : Measure (ContinuousPath ℂ) :=
  chartLaw K (η u) (windowDomain η a u b) (windowChartBG a u b η)

theorem windowChartLaw_eq_windowLawBG (a u b : ℝ) (q : JointSample) :
    windowChartLaw a u b (windowChartBG a u b q.1.2) q = windowLawBG a u b q.1.2 q.2 :=
  rfl

theorem isProbabilityMeasure_windowLawBG (a u b : ℝ) (η : C(ℝ, ℂ)) (K : PathLawFamily) :
    IsProbabilityMeasure (windowLawBG a u b η K) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_chartStopPath _ (isOpen_windowDomain η a u b) _).aemeasurable).2 inferInstance

/-- The chart law of the window as a probability measure. -/
noncomputable def windowPLawBG (a u b : ℝ) (η : C(ℝ, ℂ)) (K : PathLawFamily) :
    ProbabilityMeasure (ContinuousPath ℂ) :=
  ⟨windowLawBG a u b η K, isProbabilityMeasure_windowLawBG a u b η K⟩

theorem measurable_windowPLawBG (a u b : ℝ) :
    Measurable fun q : JointSample => windowPLawBG a u b q.1.2 q.2 :=
  (measurable_windowChartLaw_windowChartBG a u b).subtype_mk

/-! ### Finite-dimensional coordinates -/

section Coordinates

variable {I E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- The coordinates of a pair (field, probability law): the values `x_i`, `i ∈ A`, and the integrals `∫ g dν`,
`g ∈ B`. -/
noncomputable def finCoords (A : Finset I) (B : Finset (E →ᵇ ℝ)) (p : (I → ℝ) × ProbabilityMeasure E) :
    (A → ℝ) × (B → ℝ) :=
  (fun i => p.1 i, fun g => ∫ x, g.1 x ∂(p.2 : Measure E))

variable [BorelSpace E]

theorem measurable_finCoords (A : Finset I) (B : Finset (E →ᵇ ℝ)) :
    Measurable (finCoords (I := I) (E := E) A B) :=
  Measurable.prodMk (Measurable.of_eval fun i : A => (measurable_pi_apply (i : I)).comp measurable_fst)
    (Measurable.of_eval fun g : B =>
      (LatticeProb.measurable_integral_probabilityMeasure_of_boundedContinuous g.1).comp measurable_snd)

/-- On a second countable space of probability measures with its Borel `σ`-algebra, the `σ`-algebra is generated by
the integrals of the bounded continuous functions. -/
theorem probabilityMeasure_measurableSpace_le_iSup [SecondCountableTopology (ProbabilityMeasure E)]
    [BorelSpace (ProbabilityMeasure E)] :
    (inferInstance : MeasurableSpace (ProbabilityMeasure E)) ≤
      ⨆ g : E →ᵇ ℝ, MeasurableSpace.comap
        (fun ν : ProbabilityMeasure E => ∫ x, g x ∂(ν : Measure E)) (inferInstance : MeasurableSpace ℝ) := by
  refine (BorelSpace.measurable_eq (α := ProbabilityMeasure E)).le.trans ?_
  refine MeasurableSpace.generateFrom_le fun O hO => ?_
  have hB := TopologicalSpace.isTopologicalBasis_of_subbasis
    (LatticeProb.topology_eq_generateFrom_weakSubbasis (E := E))
  obtain ⟨s, hsB, hsc, rfl⟩ := hB.exists_countable_biUnion_of_isOpen hO
  refine MeasurableSet.biUnion hsc fun a ha => ?_
  obtain ⟨g, ⟨hgfin, hgsub⟩, rfl⟩ := hsB ha
  refine MeasurableSet.sInter hgfin.countable fun t ht => ?_
  obtain ⟨f, V, hV, rfl⟩ := hgsub ht
  exact le_iSup (fun g : E →ᵇ ℝ => MeasurableSpace.comap
    (fun ν : ProbabilityMeasure E => ∫ x, g x ∂(ν : Measure E)) (inferInstance : MeasurableSpace ℝ)) f _
    ⟨V, hV.measurableSet, rfl⟩

/-- A map into the probability measures is measurable once all its integrals of bounded continuous functions are. -/
theorem measurable_probabilityMeasure_of_integral [SecondCountableTopology (ProbabilityMeasure E)]
    [BorelSpace (ProbabilityMeasure E)] {α : Type*} {mα : MeasurableSpace α} {Z : α → ProbabilityMeasure E}
    (h : ∀ g : E →ᵇ ℝ, Measurable fun a => ∫ x, g x ∂(Z a : Measure E)) : Measurable Z := by
  refine Measurable.mono ?_ le_rfl (probabilityMeasure_measurableSpace_le_iSup (E := E))
  refine measurable_iff_comap_le.2 ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun g => ?_
  rw [MeasurableSpace.comap_comp]
  exact (h g).comap_le

/-- `comap (Ψ ∘ Z) ≤ comap Z m` for `Ψ` measurable for `m`. -/
theorem comap_comp_le_comap_of_measurable {α β γ : Type*} [mγ : MeasurableSpace γ] {m : MeasurableSpace β}
    {Ψ : β → γ} (hΨ : Measurable[m] Ψ) (Z : α → β) :
    MeasurableSpace.comap (fun a => Ψ (Z a)) mγ ≤ MeasurableSpace.comap Z m := by
  rw [show (fun a => Ψ (Z a)) = Ψ ∘ Z from rfl, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hΨ.comap_le

/-- **Independence from the finite-dimensional coordinates.** Two random pairs (field, probability law) are
independent once, for all finite sets of indices and of bounded continuous functions, their coordinates are. -/
theorem indepFun_prod_of_forall_finset {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    [IsProbabilityMeasure μ] [SecondCountableTopology (ProbabilityMeasure E)]
    [BorelSpace (ProbabilityMeasure E)] {Xf Yf : Ω' → I → ℝ} {Xp Yp : Ω' → ProbabilityMeasure E}
    (hXf : Measurable Xf) (hYf : Measurable Yf) (hXp : Measurable Xp) (hYp : Measurable Yp)
    (h : ∀ (A A' : Finset I) (B B' : Finset (E →ᵇ ℝ)),
      IndepFun (fun q => finCoords A B (Xf q, Xp q)) (fun q => finCoords A' B' (Yf q, Yp q)) μ) :
    IndepFun (fun q => (Xf q, (Xp q : Measure E))) (fun q => (Yf q, (Yp q : Measure E))) μ := by
  classical
  have hcoe : Measurable fun ν : ProbabilityMeasure E => (ν : Measure E) := measurable_subtype_coe
  suffices hsuff : IndepFun (fun q => (Xf q, Xp q)) (fun q => (Yf q, Yp q)) μ by
    exact hsuff.comp (measurable_fst.prodMk (hcoe.comp measurable_snd))
      (measurable_fst.prodMk (hcoe.comp measurable_snd))
  -- the `σ`-algebras of the coordinates, a directed family
  let mX : Finset I × Finset (E →ᵇ ℝ) → MeasurableSpace Ω' := fun AB =>
    MeasurableSpace.comap (fun q => finCoords AB.1 AB.2 (Xf q, Xp q)) inferInstance
  let mY : Finset I × Finset (E →ᵇ ℝ) → MeasurableSpace Ω' := fun AB =>
    MeasurableSpace.comap (fun q => finCoords AB.1 AB.2 (Yf q, Yp q)) inferInstance
  have hmono : ∀ (Zf : Ω' → I → ℝ) (Zp : Ω' → ProbabilityMeasure E),
      Monotone fun AB : Finset I × Finset (E →ᵇ ℝ) =>
        MeasurableSpace.comap (fun q => finCoords AB.1 AB.2 (Zf q, Zp q)) inferInstance := by
    rintro Zf Zp ⟨A₁, B₁⟩ ⟨A₂, B₂⟩ ⟨hA, hB⟩
    have hr : Measurable fun p : (A₂ → ℝ) × (B₂ → ℝ) =>
        ((fun i : A₁ => p.1 ⟨i.1, hA i.2⟩, fun g : B₁ => p.2 ⟨g.1, hB g.2⟩) : (A₁ → ℝ) × (B₁ → ℝ)) :=
      Measurable.prodMk (Measurable.of_eval fun i : A₁ => (measurable_pi_apply _).comp measurable_fst)
        (Measurable.of_eval fun g : B₁ => (measurable_pi_apply _).comp measurable_snd)
    exact comap_comp_le_comap_of_measurable hr (fun q => finCoords A₂ B₂ (Zf q, Zp q))
  -- the pairs are measurable for the supremum of the coordinate `σ`-algebras
  have hsup : ∀ (Zf : Ω' → I → ℝ) (Zp : Ω' → ProbabilityMeasure E),
      MeasurableSpace.comap (fun q => (Zf q, Zp q)) inferInstance ≤
        ⨆ AB : Finset I × Finset (E →ᵇ ℝ),
          MeasurableSpace.comap (fun q => finCoords AB.1 AB.2 (Zf q, Zp q)) inferInstance := by
    intro Zf Zp
    let M : MeasurableSpace Ω' := ⨆ AB : Finset I × Finset (E →ᵇ ℝ),
      MeasurableSpace.comap (fun q => finCoords AB.1 AB.2 (Zf q, Zp q)) inferInstance
    have hle : ∀ AB : Finset I × Finset (E →ᵇ ℝ),
        MeasurableSpace.comap (fun q => finCoords AB.1 AB.2 (Zf q, Zp q)) inferInstance ≤ M :=
      fun AB => le_iSup (fun AB : Finset I × Finset (E →ᵇ ℝ) =>
        MeasurableSpace.comap (fun q => finCoords AB.1 AB.2 (Zf q, Zp q)) inferInstance) AB
    have hf : Measurable[M] Zf := by
      refine Measurable.of_eval fun i => ?_
      have h1 : Measurable[MeasurableSpace.comap (fun q => finCoords {i} ∅ (Zf q, Zp q)) inferInstance]
          (fun q => finCoords {i} ∅ (Zf q, Zp q)) := comap_measurable _
      exact (((measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset I))).comp
        measurable_fst).comp h1).mono (hle ({i}, ∅)) le_rfl
    have hp : Measurable[M] Zp := by
      refine measurable_probabilityMeasure_of_integral fun g => ?_
      have h1 : Measurable[MeasurableSpace.comap (fun q => finCoords ∅ {g} (Zf q, Zp q)) inferInstance]
          (fun q => finCoords ∅ {g} (Zf q, Zp q)) := comap_measurable _
      exact (((measurable_pi_apply (⟨g, Finset.mem_singleton_self g⟩ : ({g} : Finset (E →ᵇ ℝ)))).comp
        measurable_snd).comp h1).mono (hle (∅, {g})) le_rfl
    exact (hf.prodMk hp).comap_le
  have hXm : ∀ AB : Finset I × Finset (E →ᵇ ℝ), mX AB ≤ ‹MeasurableSpace Ω'› := fun AB =>
    ((measurable_finCoords AB.1 AB.2).comp (hXf.prodMk hXp)).comap_le
  have hYm : ∀ AB : Finset I × Finset (E →ᵇ ℝ), mY AB ≤ ‹MeasurableSpace Ω'› := fun AB =>
    ((measurable_finCoords AB.1 AB.2).comp (hYf.prodMk hYp)).comap_le
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right ?_ (hsup Yf Yp)) (hsup Xf Xp)
  refine indep_iSup_of_directed_le (fun AB => ?_) hXm (iSup_le hYm) (hmono Xf Xp).directed_le
  refine (indep_iSup_of_directed_le (fun AB' => ?_) hYm (hXm AB) (hmono Yf Yp).directed_le).symm
  exact ((IndepFun_iff_Indep _ _ _).1 (h AB.1 AB'.1 AB.2 AB'.2)).symm

end Coordinates

/-! ### Closeness in probability -/

section Closeness

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem tendsto_measure_le_edist_of_ae_eq {α : Type*} [PseudoEMetricSpace α] {x u : ℕ → Ω → α}
    (h : ∀ n, ∀ᵐ ω ∂μ, x n ω = u n ω) :
    ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => μ {ω | δ ≤ edist (x n ω) (u n ω)}) atTop (𝓝 0) := by
  intro δ hδ
  have h0 : ∀ n, μ {ω | δ ≤ edist (x n ω) (u n ω)} = 0 := fun n => by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (h n))
    show ¬x n ω = u n ω
    intro he
    have hω' : δ ≤ edist (x n ω) (u n ω) := hω
    rw [he, edist_self] at hω'
    exact (not_le.2 hδ) hω'
  simp only [h0]
  exact tendsto_const_nhds

theorem tendsto_measure_le_edist_of_abs_sub {x u : ℕ → Ω → ℝ}
    (h : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => μ {ω | δ ≤ |x n ω - u n ω|}) atTop (𝓝 0)) :
    ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => μ {ω | δ ≤ edist (x n ω) (u n ω)}) atTop (𝓝 0) := by
  intro δ hδ
  have hmin : 0 < min δ 1 := lt_min hδ one_pos
  have hδ' : 0 < (min δ 1).toReal :=
    ENNReal.toReal_pos hmin.ne' ((min_le_right δ 1).trans_lt ENNReal.one_lt_top).ne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h _ hδ') (fun _ => zero_le)
    fun n => measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq] at hω ⊢
  rw [edist_dist, Real.dist_eq] at hω
  exact ENNReal.toReal_le_of_le_ofReal (abs_nonneg _) ((min_le_left _ _).trans hω)

theorem tendsto_measure_le_edist_prod {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {x u : ℕ → Ω → α} {y v : ℕ → Ω → β}
    (hx : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => μ {ω | δ ≤ edist (x n ω) (u n ω)}) atTop (𝓝 0))
    (hy : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => μ {ω | δ ≤ edist (y n ω) (v n ω)}) atTop (𝓝 0)) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => μ {ω | δ ≤ edist (x n ω, y n ω) (u n ω, v n ω)}) atTop (𝓝 0) := by
  intro δ hδ
  have hsub : ∀ n, {ω | δ ≤ edist (x n ω, y n ω) (u n ω, v n ω)} ⊆
      {ω | δ ≤ edist (x n ω) (u n ω)} ∪ {ω | δ ≤ edist (y n ω) (v n ω)} := by
    intro n ω hω
    simp only [mem_ofPred_eq, Prod.edist_eq, le_max_iff] at hω
    exact hω
  have hsum := (hx δ hδ).add (hy δ hδ)
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (measure_mono (hsub n)).trans (measure_union_le _ _)

theorem tendsto_measure_le_edist_pi {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, PseudoEMetricSpace (β i)] {x u : ℕ → Ω → ∀ i, β i}
    (h : ∀ i, ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => μ {ω | δ ≤ edist (x n ω i) (u n ω i)}) atTop (𝓝 0)) :
    ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => μ {ω | δ ≤ edist (x n ω) (u n ω)}) atTop (𝓝 0) := by
  intro δ hδ
  have hsub : ∀ n, {ω | δ ≤ edist (x n ω) (u n ω)} ⊆ ⋃ i, {ω | δ ≤ edist (x n ω i) (u n ω i)} := by
    intro n ω hω
    simp only [mem_ofPred_eq, edist_pi_def] at hω
    obtain ⟨i, -, hi⟩ := (Finset.le_sup_iff (by simpa using hδ)).1 hω
    exact mem_iUnion.2 ⟨i, hi⟩
  have hsum : Tendsto (fun n => ∑ i, μ {ω | δ ≤ edist (x n ω i) (u n ω i)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ => h i δ hδ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (measure_mono (hsub n)).trans (measure_iUnion_fintype_le μ _)

end Closeness

/-! ### The steps of the printed proof of Lemma 7.21 -/

/-- **Step of Berestycki–Gwynne (2020), proof of Lemma 7.21 (2003.10320.txt lines 3775-3776): "By definition,
`(h^D, η^D)` (resp. `(h̃^D, η̃^D)`) is determined by the first (resp. second) quantum surface in (7.35)", for the chart
field.** PENDING TRUTH CHECK.

In a valid environment with measurable versions `H` of the field and `η'` of the curve, for a window `(a, u, b)` and
a time `s > b` (resp. `s < a`), the chart field of the window for the inverse chart `windowChartBG` of the normalization
of Section 7.3 is almost surely a function of the past (resp. future) curve-decorated quantum surface at `s`: it agrees
almost surely with `F (H, η')` for a function `F` measurable for `curveSurfaceSigma γ (Iic s)` (resp.
`curveSurfaceSigma γ (Ici s)`). -/
def BG20WindowFieldSurfaceInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ a u b s : ℝ, a < u → u < b →
      (b < s → ∃ F : LQGMetric.DistC × C(ℝ, ℂ) → 𝓓(unitDiscOpens, ℝ) → ℝ,
        Measurable[curveSurfaceSigma γ (Iic s)] F ∧
          ∀ᵐ ω ∂S.P, windowFieldBG γ a u b (H ω, η' ω) = F (H ω, η' ω)) ∧
      (s < a → ∃ F : LQGMetric.DistC × C(ℝ, ℂ) → 𝓓(unitDiscOpens, ℝ) → ℝ,
        Measurable[curveSurfaceSigma γ (Ici s)] F ∧
          ∀ᵐ ω ∂S.P, windowFieldBG γ a u b (H ω, η' ω) = F (H ω, η' ω))

/-- **Step of Berestycki–Gwynne (2020), proof of Lemma 7.21 (2003.10320.txt lines 3783-3831): the discrete analogue
`P^{D,ε}_0` of the window chart law.** PENDING TRUTH CHECK.

In Berestycki–Gwynne, `P^{D,ε}_0` is the conditional law given `(h, η)` of the walk on the subgraph `T^ε` of the
mated-CRT map induced by the vertices in `[a', b'] ∩ εℤ`, started from `u_ε`, stopped on hitting `∂T^ε`, mapped by
`φ⁻¹ ∘ η` and interpolated; it is almost surely determined by the past (resp. future) curve-decorated quantum surface
(lines 3783-3804), and its Prokhorov distance to the law of the chart image of the walk at level `ε` tends to zero in
probability (lines 3812-3831). Here: for every sequence `ε_n → 0` there are probability laws `R_n` on path space,
functions of (field, curve) measurable for `curveSurfaceSigma γ (Iic s)` (resp. `curveSurfaceSigma γ (Ici s)`), such
that for every bounded continuous `g`, `∫ g dR_n - ∫ g d(chart law of the window for the interpolated walk law at
level ε_n)` tends to zero in probability. The chart law of the walk is stopped at the exit from the window `U`
(`windowLawBG`), where Berestycki–Gwynne stop it on hitting `η(εℤ \ [a', b'])`. -/
def BG20DiscreteWindowLawInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ a u b s : ℝ, a < u → u < b →
      (b < s → ∃ R : ℕ → LQGMetric.DistC × C(ℝ, ℂ) → ProbabilityMeasure (ContinuousPath ℂ),
        (∀ n, Measurable[curveSurfaceSigma γ (Iic s)] (R n)) ∧
          ∀ g : ContinuousPath ℂ →ᵇ ℝ, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => S.P {ω | δ ≤
            |∫ x, g x ∂(R n (H ω, η' ω) : Measure (ContinuousPath ℂ)) -
              ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|}) atTop (𝓝 0)) ∧
      (s < a → ∃ R : ℕ → LQGMetric.DistC × C(ℝ, ℂ) → ProbabilityMeasure (ContinuousPath ℂ),
        (∀ n, Measurable[curveSurfaceSigma γ (Ici s)] (R n)) ∧
          ∀ g : ContinuousPath ℂ →ᵇ ℝ, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => S.P {ω | δ ≤
            |∫ x, g x ∂(R n (H ω, η' ω) : Measure (ContinuousPath ℂ)) -
              ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|}) atTop (𝓝 0))

/-- **Step of Berestycki–Gwynne (2020), proof of Lemma 7.21 (2003.10320.txt lines 3831-3838), no written argument:
"it is easily seen from the convergence `(h, η, P^ε) → (h, η, P)` in law that (7.36) holds if we replace
`P^{D,ε}_0` by the `P^ε_{η(u_ε)}`-law of `φ⁻¹(X̂^ε)`".** PENDING TRUTH CHECK.

In the setting of `BG20ChartIndependenceInputBG` (a weak limit `ν''` of the joint laws of the field coordinates, the
coordinate `E`, the curve and the interpolated walk laws at levels `ε_n`, almost surely a linear time change of the
Liouville Brownian law field), for windows `a < u < b < a' < u' < b'`: the finite-dimensional coordinates (pairings
with finitely many test functions on the unit disc, integrals of finitely many bounded continuous functions on path
space) of the two pairs (chart field, chart law of the window for the interpolated walk law at level `ε_n`) converge
jointly in law to those of the two pairs (chart field, window chart law) under `ν''`. -/
def BG20WindowJointConvergenceInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν'' : Measure JointSample, IsProbabilityMeasure ν'' →
    (∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 (∫ q, f q ∂ν''))) →
    (∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
    ∀ a u b a' u' b' : ℝ, a < u → u < b → b < a' → a' < u' → u' < b' →
    ∀ (A A' : Finset 𝓓(unitDiscOpens, ℝ)) (B B' : Finset (ContinuousPath ℂ →ᵇ ℝ))
      (Φ : ((A → ℝ) × (B → ℝ)) × ((A' → ℝ) × (B' → ℝ)) →ᵇ ℝ),
      Tendsto (fun n => ∫ ω, Φ
          (finCoords A B (windowFieldBG γ a u b (H ω, η' ω),
              windowPLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)),
            finCoords A' B' (windowFieldBG γ a' u' b' (H ω, η' ω),
              windowPLawBG a' u' b' (η' ω) (interpWalkLaw S η' (ε n) ω))) ∂S.P)
        atTop (𝓝 (∫ q, Φ
          (finCoords A B (windowChartField γ a u b (windowChartBG a u b q.1.2) q, windowPLawBG a u b q.1.2 q.2),
            finCoords A' B' (windowChartField γ a' u' b' (windowChartBG a' u' b' q.1.2) q,
              windowPLawBG a' u' b' q.1.2 q.2)) ∂ν''))

/-! ### Lemma 7.21 -/

/-- **Berestycki–Gwynne (2020), Lemma 7.21, for the inverse charts `windowChartBG` (`BG20ChartIndependenceInputBG`),
following the printed proof (2003.10320.txt lines 3768-3838).** Take `s = (b + a')/2` between the windows. By
`DMS21PastFutureIndependence` the past and future curve-decorated quantum surfaces at `s` are independent; by
`BG20WindowFieldSurfaceInput` and `BG20DiscreteWindowLawInput` the chart fields and the discrete analogues of the window
chart laws are functions of these surfaces, so at each level the coordinates of the two windows built from them are
independent; they are close in probability to the coordinates built from the chart laws of the walk
(`BG20DiscreteWindowLawInput`), whose joint laws converge to those of the joint limit (`BG20WindowJointConvergenceInput`);
the independence passes to the limit (`LatticeProb.indepFun_of_tendsto_law_of_coupled`) for each finite set of
coordinates, hence for the pairs (`indepFun_prod_of_forall_finset`). -/
theorem bg20ChartIndependenceInputBG_of_dms21 {𝒮 : SpaceFillingSLEModel}
    (hDMS : DMS21PastFutureIndependence 𝒮) (hF : BG20WindowFieldSurfaceInput 𝒮)
    (hL : BG20DiscreteWindowLawInput 𝒮) (hJ : BG20WindowJointConvergenceInput 𝒮) :
    BG20ChartIndependenceInputBG 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  classical
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hν : IsProbabilityMeasure ν'' := hν''
  have hbs : b < (b + a') / 2 := by linarith
  have hsa : (b + a') / 2 < a' := by linarith
  obtain ⟨F₁, hF₁m, hF₁⟩ := (hF γ hγ hγ2 Ω S hS η' hη' hae H hH hrep a u b ((b + a') / 2) hau hub).1 hbs
  obtain ⟨F₂, hF₂m, hF₂⟩ :=
    (hF γ hγ hγ2 Ω S hS η' hη' hae H hH hrep a' u' b' ((b + a') / 2) ha'u' hu'b').2 hsa
  obtain ⟨R₁, hR₁m, hR₁⟩ :=
    (hL γ hγ hγ2 Ω S hS η' hη' hae H hH hrep ε hε0 hε a u b ((b + a') / 2) hau hub).1 hbs
  obtain ⟨R₂, hR₂m, hR₂⟩ :=
    (hL γ hγ hγ2 Ω S hS η' hη' hae H hH hrep ε hε0 hε a' u' b' ((b + a') / 2) ha'u' hu'b').2 hsa
  have hind := hDMS γ hγ hγ2 Ω S hS H hH hrep η' hη' hae ((b + a') / 2)
  have hZ : Measurable fun ω => (H ω, η' ω) := hH.prodMk hη'
  have hsample : ∀ n, AEMeasurable
      (fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω)) S.P := fun n =>
    (((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη').aemeasurable.prodMk
      (aemeasurable_interpWalkLaw hS hη' hae (hε0 n))
  have hWf₁ := measurable_windowChartField_windowChartBG γ a u b
  have hWf₂ := measurable_windowChartField_windowChartBG γ a' u' b'
  have hWp₁ := measurable_windowPLawBG a u b
  have hWp₂ := measurable_windowPLawBG a' u' b'
  have hfin : ∀ (A A' : Finset 𝓓(unitDiscOpens, ℝ)) (B B' : Finset (ContinuousPath ℂ →ᵇ ℝ)),
      IndepFun (fun q : JointSample =>
          finCoords A B (windowChartField γ a u b (windowChartBG a u b q.1.2) q, windowPLawBG a u b q.1.2 q.2))
        (fun q : JointSample => finCoords A' B'
          (windowChartField γ a' u' b' (windowChartBG a' u' b' q.1.2) q, windowPLawBG a' u' b' q.1.2 q.2)) ν'' := by
    intro A A' B B'
    -- the limit coordinates
    let X : JointSample → (A → ℝ) × (B → ℝ) := fun q =>
      finCoords A B (windowChartField γ a u b (windowChartBG a u b q.1.2) q, windowPLawBG a u b q.1.2 q.2)
    let Y : JointSample → (A' → ℝ) × (B' → ℝ) := fun q =>
      finCoords A' B' (windowChartField γ a' u' b' (windowChartBG a' u' b' q.1.2) q, windowPLawBG a' u' b' q.1.2 q.2)
    have hXm : Measurable X := (measurable_finCoords A B).comp (hWf₁.prodMk hWp₁)
    have hYm : Measurable Y := (measurable_finCoords A' B').comp (hWf₂.prodMk hWp₂)
    -- the coordinates of the walk at level `ε n`
    let Un : ℕ → Ω → (A → ℝ) × (B → ℝ) := fun n ω =>
      finCoords A B (windowFieldBG γ a u b (H ω, η' ω), windowPLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω))
    let Vn : ℕ → Ω → (A' → ℝ) × (B' → ℝ) := fun n ω =>
      finCoords A' B' (windowFieldBG γ a' u' b' (H ω, η' ω),
        windowPLawBG a' u' b' (η' ω) (interpWalkLaw S η' (ε n) ω))
    have hUn : ∀ n, AEMeasurable (Un n) S.P := fun n => by
      refine (hXm.comp_aemeasurable (hsample n)).congr (ae_of_all _ fun ω => ?_)
      show finCoords A B (windowFieldBG γ a u b (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω)), η' ω), _) = _
      rw [LQGMetric.pairJInv_pairJ]
    have hVn : ∀ n, AEMeasurable (Vn n) S.P := fun n => by
      refine (hYm.comp_aemeasurable (hsample n)).congr (ae_of_all _ fun ω => ?_)
      show finCoords A' B' (windowFieldBG γ a' u' b' (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω)), η' ω), _) = _
      rw [LQGMetric.pairJInv_pairJ]
    -- the coordinates built from the past and future surfaces
    let Xn : ℕ → Ω → (A → ℝ) × (B → ℝ) := fun n ω => finCoords A B (F₁ (H ω, η' ω), R₁ n (H ω, η' ω))
    let Yn : ℕ → Ω → (A' → ℝ) × (B' → ℝ) := fun n ω => finCoords A' B' (F₂ (H ω, η' ω), R₂ n (H ω, η' ω))
    have hΨ₁ : ∀ n, Measurable[curveSurfaceSigma γ (Iic ((b + a') / 2))]
        (fun p => finCoords A B (F₁ p, R₁ n p)) := fun n =>
      (measurable_finCoords A B).comp (hF₁m.prodMk (hR₁m n))
    have hΨ₂ : ∀ n, Measurable[curveSurfaceSigma γ (Ici ((b + a') / 2))]
        (fun p => finCoords A' B' (F₂ p, R₂ n p)) := fun n =>
      (measurable_finCoords A' B').comp (hF₂m.prodMk (hR₂m n))
    have hXn : ∀ n, Measurable (Xn n) := fun n =>
      ((hΨ₁ n).mono (curveSurfaceSigma_le γ _) le_rfl).comp hZ
    have hYn : ∀ n, Measurable (Yn n) := fun n =>
      ((hΨ₂ n).mono (curveSurfaceSigma_le γ _) le_rfl).comp hZ
    have hindn : ∀ n, IndepFun (Xn n) (Yn n) S.P := fun n => by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left
        (indep_of_indep_of_le_right hind (comap_comp_le_comap_of_measurable (hΨ₂ n) _))
        (comap_comp_le_comap_of_measurable (hΨ₁ n) _)
    -- the joint laws
    let ρ : ℕ → ProbabilityMeasure (((A → ℝ) × (B → ℝ)) × ((A' → ℝ) × (B' → ℝ))) := fun n =>
      ⟨S.P.map fun ω => (Un n ω, Vn n ω),
        (Measure.isProbabilityMeasure_map_iff ((hUn n).prodMk (hVn n))).2 hP⟩
    let ρ₀ : ProbabilityMeasure (((A → ℝ) × (B → ℝ)) × ((A' → ℝ) × (B' → ℝ))) :=
      ⟨ν''.map fun q => (X q, Y q), (Measure.isProbabilityMeasure_map_iff (hXm.prodMk hYm).aemeasurable).2 hν⟩
    have hρ : Tendsto ρ atTop (𝓝 ρ₀) := by
      refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun Φ => ?_
      have h1 : ∀ n, ∫ z, Φ z ∂(ρ n : Measure (((A → ℝ) × (B → ℝ)) × ((A' → ℝ) × (B' → ℝ)))) =
          ∫ ω, Φ (Un n ω, Vn n ω) ∂S.P := fun n =>
        integral_map ((hUn n).prodMk (hVn n)) Φ.continuous.aestronglyMeasurable
      have h2 : ∫ z, Φ z ∂(ρ₀ : Measure (((A → ℝ) × (B → ℝ)) × ((A' → ℝ) × (B' → ℝ)))) =
          ∫ q, Φ (X q, Y q) ∂ν'' :=
        integral_map (hXm.prodMk hYm).aemeasurable Φ.continuous.aestronglyMeasurable
      rw [h2]
      exact (hJ γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
        hau hub hba' ha'u' hu'b' A A' B B' Φ).congr fun n => (h1 n).symm
    -- closeness in probability
    have hclose₁ : ∀ δ : ℝ≥0∞, 0 < δ →
        Tendsto (fun n => S.P {ω | δ ≤ edist (Xn n ω) (Un n ω)}) atTop (𝓝 0) := by
      refine tendsto_measure_le_edist_prod (x := fun n ω => (Xn n ω).1) (u := fun n ω => (Un n ω).1)
        (y := fun n ω => (Xn n ω).2) (v := fun n ω => (Un n ω).2) ?_ ?_
      · refine tendsto_measure_le_edist_of_ae_eq fun n => ?_
        filter_upwards [hF₁] with ω hω
        exact funext fun i => (congrFun hω i).symm
      · refine tendsto_measure_le_edist_pi fun g => ?_
        exact tendsto_measure_le_edist_of_abs_sub (hR₁ g.1)
    have hclose₂ : ∀ δ : ℝ≥0∞, 0 < δ →
        Tendsto (fun n => S.P {ω | δ ≤ edist (Yn n ω) (Vn n ω)}) atTop (𝓝 0) := by
      refine tendsto_measure_le_edist_prod (x := fun n ω => (Yn n ω).1) (u := fun n ω => (Vn n ω).1)
        (y := fun n ω => (Yn n ω).2) (v := fun n ω => (Vn n ω).2) ?_ ?_
      · refine tendsto_measure_le_edist_of_ae_eq fun n => ?_
        filter_upwards [hF₂] with ω hω
        exact funext fun i => (congrFun hω i).symm
      · refine tendsto_measure_le_edist_pi fun g => ?_
        exact tendsto_measure_le_edist_of_abs_sub (hR₂ g.1)
    exact LatticeProb.indepFun_of_tendsto_law_of_coupled (fun n => (hXn n).aemeasurable)
      (fun n => (hYn n).aemeasurable) hUn hVn hXm.aemeasurable hYm.aemeasurable hindn
      (ρ := ρ) (ρ₀ := ρ₀) (fun _ => rfl) rfl hρ (tendsto_measure_le_edist_prod hclose₁ hclose₂)
  exact indepFun_prod_of_forall_finset hWf₁ hWf₂ hWp₁ hWp₂ hfin

end MatedCRT
