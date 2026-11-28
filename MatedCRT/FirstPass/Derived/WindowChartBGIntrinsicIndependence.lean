import MatedCRT.External.DMSIntrinsicPastFutureIndependence
import MatedCRT.FirstPass.Derived.DMSPastFutureIndependenceOfExternal

/-!
# Independence of the windows (Berestycki–Gwynne (2020), Lemma 7.21) from the independence of the past and future
intrinsic curve-decorated wedges (Duplantier–Miller–Sheffield, Theorem 1.9)

Berestycki–Gwynne (2020), arXiv:2003.10320, prove Lemma 7.21 (lines 3761-3838 of the text) from the independence of
the past and future curve-decorated quantum surfaces (7.35) at a time `s` between the two windows. This
file runs the argument of `bg20ChartIndependenceInputBG_of_dms21` with the two halves taken as intrinsic
curve-decorated wedges (`intrinsicCurveDecoratedSurfaceSigma`, the cited input `DMSIntrinsicPastFutureIndependence`):
the chart field of each window and the discrete analogue `P^{D,ε}_0` of its chart law are functions of the intrinsic
wedge containing the window (the named steps `BG20WindowFieldIntrinsicInput` and
`BG20DiscreteWindowLawIntrinsicInput`).

The independence at every time `s` comes from the one at time `0` as in `dms21PastFutureIndependence_of_external`: a
re-embedding over all times restricts to a re-embedding over any set of times `T`, which is an intrinsic re-embedding
over `T` (`IsCurveDecoratedReembedding.intrinsic`), so the intrinsic `σ`-algebras of the past and of the future are
contained in the `σ`-algebra over all times, on which the stationarity (1.9) identifies the laws of `(h, η')` and
`(h, η'(· + s))`; time shifts carry intrinsic re-embeddings over `T` to intrinsic re-embeddings over `T - s`.

## Main statements

* `dms21IntrinsicPastFutureIndependence_of_external`: `DMS21IntrinsicPastFutureIndependence 𝒮` (every time `s`) from
  `DMSIntrinsicPastFutureIndependence`.
* `bg20ChartIndependenceInputBG_of_dmsIntrinsic`: `BG20ChartIndependenceInputBG` from
  `DMSIntrinsicPastFutureIndependence`, the two named steps above and `BG20WindowJointConvergenceInput`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

namespace DMSIntrinsicPastFuture

open DMSPastFuture

/-- A re-embedding of curve-decorated quantum surfaces over the times `T` is an intrinsic one: a time of `T` at which
`η₁` is in the interior of `η₁(T) = f(η₂(T))` is one at which `η₂` is in the interior of `η₂(T)`, by injectivity of
`f` on `η₂(T)`. -/
theorem _root_.MatedCRT.IsCurveDecoratedReembedding.intrinsic {γ : ℝ} {T : Set ℝ} {h₁ h₂ : LQGMetric.DistC}
    {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ} (hf : IsCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) :
    IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  refine ⟨fun t ht _ => h1 t ht, fun t ht hint => ?_, h2.mono interior_subset, h4, h5, h6⟩
  rw [← h1 t ht, ← h5] at hint
  obtain ⟨x, hx, hfx⟩ := hint
  have hxt : x = η₂ t := h2 (interior_subset hx) (mem_image_of_mem η₂ ht) hfx
  rw [hxt] at hx
  exact hx

/-- The `σ`-algebra of the intrinsic curve-decorated surface over `T` is contained in the one of the curve-decorated
quantum surface over all times. -/
theorem intrinsicCurveDecoratedSurfaceSigma_le_univ (γ : ℝ) (T : Set ℝ) :
    intrinsicCurveDecoratedSurfaceSigma γ T ≤ curveDecoratedSurfaceSigma γ univ :=
  fun _ hA => ⟨hA.1, fun p₁ p₂ hp => by
    obtain ⟨f, hf⟩ := hp
    exact hA.2 p₁ p₂ ⟨f, (isCurveDecoratedReembedding_restrict hf T).intrinsic⟩⟩

theorem intrinsicCurveDecoratedSurfaceSigma_le (γ : ℝ) (T : Set ℝ) :
    intrinsicCurveDecoratedSurfaceSigma γ T ≤ (inferInstance : MeasurableSpace (LQGMetric.DistC × C(ℝ, ℂ))) :=
  fun _ hA => hA.1

/-- An intrinsic re-embedding over the times `T` is one, for the time-shifted curves, over the times `T' = T - c`. -/
theorem isIntrinsicCurveDecoratedReembedding_timeShift {γ : ℝ} {T T' : Set ℝ} {c : ℝ}
    (hT : ∀ u, u ∈ T' ↔ u + c ∈ T) {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ}
    (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) :
    IsIntrinsicCurveDecoratedReembedding γ T' h₁ (timeShiftCurve c η₁) h₂ (timeShiftCurve c η₂) f := by
  have himg : ∀ η : C(ℝ, ℂ), timeShiftCurve c η '' T' = η '' T := by
    intro η
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u + c, (hT u).1 hu, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t - c, (hT (t - c)).2 (by rwa [sub_add_cancel]), ?_⟩
      simp only [timeShiftCurve, ContinuousMap.coe_mk, sub_add_cancel]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  rw [IsIntrinsicCurveDecoratedReembedding, himg, himg]
  exact ⟨fun u hu hint => h1 (u + c) ((hT u).1 hu) hint, fun u hu hint => h2 (u + c) ((hT u).1 hu) hint,
    h3, h4, h5, h6⟩

/-- The intrinsic past (resp. future) of `(h, η)` after the time `s` generates no more than the intrinsic past
(resp. future) of `(h, η(· + s))` after the time `0`. -/
theorem comap_le_comap_curveTimeShift_intrinsic (γ : ℝ) {T T' : Set ℝ} {c : ℝ} (hT : ∀ u, u ∈ T' ↔ u + -c ∈ T)
    {Ω : Type*} (p : Ω → LQGMetric.DistC × C(ℝ, ℂ)) :
    MeasurableSpace.comap p (intrinsicCurveDecoratedSurfaceSigma γ T') ≤
      MeasurableSpace.comap (fun ω => curveTimeShift c (p ω)) (intrinsicCurveDecoratedSurfaceSigma γ T) := by
  rintro _ ⟨A, hA, rfl⟩
  refine ⟨curveTimeShift (-c) ⁻¹' A, ⟨measurable_curveTimeShift (-c) hA.1, fun p₁ p₂ hp => ?_⟩, ?_⟩
  · obtain ⟨f, hf⟩ := hp
    exact hA.2 (curveTimeShift (-c) p₁) (curveTimeShift (-c) p₂)
      ⟨f, isIntrinsicCurveDecoratedReembedding_timeShift hT hf⟩
  · ext ω
    simp only [mem_preimage, curveTimeShift_neg_curveTimeShift]

end DMSIntrinsicPastFuture

/-- **Independence of the past and future intrinsic curve-decorated wedges at every time** (Duplantier–Miller–Sheffield,
arXiv:1409.7055v4, Theorem 1.9 with the stationarity (1.9); the two halves as intrinsic curve-decorated wedges,
Gwynne–Miller, arXiv:1701.05174, Definition 2.1 and §2.3.3; used in Berestycki–Gwynne (2020), (7.35)). In a valid environment with measurable versions `H` of the field and `η'` of the curve, for
every time `s`, the `σ`-algebras `intrinsicCurveDecoratedSurfaceSigma γ (Iic s)` and
`intrinsicCurveDecoratedSurfaceSigma γ (Ici s)`, pulled back by `(H, η')`, are independent. -/
def DMS21IntrinsicPastFutureIndependence (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ s : ℝ, Indep (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Iic s)))
      (MeasurableSpace.comap (fun ω => (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Ici s))) S.P

open DMSPastFuture DMSIntrinsicPastFuture in
/-- `DMS21IntrinsicPastFutureIndependence 𝒮` from the cited input `DMSIntrinsicPastFutureIndependence`. A valid
environment carries a mating-of-trees coupling whose cone field and curve agree almost surely with its field and
curve. -/
theorem dms21IntrinsicPastFutureIndependence_of_external (hDMS : DMSIntrinsicPastFutureIndependence)
    (𝒮 : SpaceFillingSLEModel) : DMS21IntrinsicPastFutureIndependence 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS H hH hHae η' hη' hηae s
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηc, η₀, hcpl, hae⟩ := hS.matingOfTrees
  have hHc : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ = H ω φ := by
    filter_upwards [hHae, hae] with ω h1 h2 φ
    exact (h2.2 φ).symm.trans (h1 φ)
  have hηc : ∀ᵐ ω ∂S.P, η' ω = ηc ω := by
    filter_upwards [hηae, hae] with ω h1 h2
    exact DFunLike.coe_injective (h1.trans h2.1.symm)
  obtain ⟨hstat, hind⟩ :=
    hDMS γ hγ hγ2 Ω S.P X X₀ hIG₀ B B' B₀ B₀' U ηL ηc η₀ S.bm hcpl H hH hHc η' hη' hηc
  have hlaw : ∀ C, MeasurableSet[curveDecoratedSurfaceSigma γ univ] C →
      S.P ((fun ω => curveTimeShift s (H ω, η' ω)) ⁻¹' C) = S.P ((fun ω => (H ω, η' ω)) ⁻¹' C) := by
    intro C hC
    rw [hstat s C hC]
    congr 1
    ext ω
    exact hC.2 _ _ (isSameCurveDecoratedSurface_recentre γ univ s (H ω, η' ω))
  have hq : Indep
      (MeasurableSpace.comap (fun ω => curveTimeShift s (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Iic 0)))
      (MeasurableSpace.comap (fun ω => curveTimeShift s (H ω, η' ω)) (intrinsicCurveDecoratedSurfaceSigma γ (Ici 0)))
      S.P := by
    rw [Indep_iff]
    rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    have hAu := intrinsicCurveDecoratedSurfaceSigma_le_univ γ _ A hA
    have hBu := intrinsicCurveDecoratedSurfaceSigma_le_univ γ _ B hB
    rw [← preimage_inter, hlaw _ (hAu.inter hBu), hlaw _ hAu, hlaw _ hBu, preimage_inter]
    exact (Indep_iff _ _ _).1 hind _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have hpast := comap_le_comap_curveTimeShift_intrinsic γ (T := Iic 0) (T' := Iic s) (c := s)
    (fun u => by rw [mem_Iic, mem_Iic]; constructor <;> intro h <;> linarith) (fun ω => (H ω, η' ω))
  have hfut := comap_le_comap_curveTimeShift_intrinsic γ (T := Ici 0) (T' := Ici s) (c := s)
    (fun u => by rw [mem_Ici, mem_Ici]; constructor <;> intro h <;> linarith) (fun ω => (H ω, η' ω))
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hq hpast) hfut

/-! ### The window data as functions of the intrinsic wedges -/

/-- **Step of Berestycki–Gwynne (2020), proof of Lemma 7.21: "By definition,
`(h^D, η^D)` (resp. `(h̃^D, η̃^D)`) is determined by the first (resp. second) quantum surface in (7.35)", with the two
quantum surfaces of (7.35) taken as intrinsic curve-decorated wedges.** PENDING TRUTH CHECK.

In a valid environment with measurable versions `H` of the field and `η'` of the curve, for a window `(a, u, b)` and
a time `s > b` (resp. `s < a`), the chart field of the window for the inverse chart `windowChartBG` of the normalization
of Section 7.3 is almost surely a function of the past (resp. future) intrinsic curve-decorated wedge at `s`: it
agrees almost surely with `F (H, η')` for a function `F` measurable for `intrinsicCurveDecoratedSurfaceSigma γ (Iic s)`
(resp. `intrinsicCurveDecoratedSurfaceSigma γ (Ici s)`). -/
def BG20WindowFieldIntrinsicInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ a u b s : ℝ, a < u → u < b →
      (b < s → ∃ F : LQGMetric.DistC × C(ℝ, ℂ) → 𝓓(unitDiscOpens, ℝ) → ℝ,
        Measurable[intrinsicCurveDecoratedSurfaceSigma γ (Iic s)] F ∧
          ∀ᵐ ω ∂S.P, windowFieldBG γ a u b (H ω, η' ω) = F (H ω, η' ω)) ∧
      (s < a → ∃ F : LQGMetric.DistC × C(ℝ, ℂ) → 𝓓(unitDiscOpens, ℝ) → ℝ,
        Measurable[intrinsicCurveDecoratedSurfaceSigma γ (Ici s)] F ∧
          ∀ᵐ ω ∂S.P, windowFieldBG γ a u b (H ω, η' ω) = F (H ω, η' ω))

/-- **Step of Berestycki–Gwynne (2020), proof of Lemma 7.21: the discrete analogue
`P^{D,ε}_0` of the window chart law, a function of the intrinsic curve-decorated wedge containing the window.** PENDING
TRUTH CHECK.

`BG20DiscreteWindowLawInput` with the two quantum surfaces of (7.35) taken as intrinsic curve-decorated
wedges: for every sequence `ε_n → 0` there are probability laws `R_n` on path space, functions of (field, curve)
measurable for `intrinsicCurveDecoratedSurfaceSigma γ (Iic s)` (resp. `intrinsicCurveDecoratedSurfaceSigma γ (Ici s)`),
such that for every bounded continuous `g`, `∫ g dR_n - ∫ g d(chart law of the window for the interpolated walk law at
level ε_n)` tends to zero in probability. -/
def BG20DiscreteWindowLawIntrinsicInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ a u b s : ℝ, a < u → u < b →
      (b < s → ∃ R : ℕ → LQGMetric.DistC × C(ℝ, ℂ) → ProbabilityMeasure (ContinuousPath ℂ),
        (∀ n, Measurable[intrinsicCurveDecoratedSurfaceSigma γ (Iic s)] (R n)) ∧
          ∀ g : ContinuousPath ℂ →ᵇ ℝ, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => S.P {ω | δ ≤
            |∫ x, g x ∂(R n (H ω, η' ω) : Measure (ContinuousPath ℂ)) -
              ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|}) atTop (𝓝 0)) ∧
      (s < a → ∃ R : ℕ → LQGMetric.DistC × C(ℝ, ℂ) → ProbabilityMeasure (ContinuousPath ℂ),
        (∀ n, Measurable[intrinsicCurveDecoratedSurfaceSigma γ (Ici s)] (R n)) ∧
          ∀ g : ContinuousPath ℂ →ᵇ ℝ, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => S.P {ω | δ ≤
            |∫ x, g x ∂(R n (H ω, η' ω) : Measure (ContinuousPath ℂ)) -
              ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|}) atTop (𝓝 0))

/-! ### Lemma 7.21 -/

open DMSIntrinsicPastFuture in
/-- **Berestycki–Gwynne (2020), Lemma 7.21, for the inverse charts `windowChartBG` (`BG20ChartIndependenceInputBG`),
following the printed proof with the two halves of (7.35) as intrinsic
curve-decorated wedges.** Take `s = (b + a')/2` between the windows. By `DMSIntrinsicPastFutureIndependence` the past
and future intrinsic curve-decorated wedges at `s` are independent
(`dms21IntrinsicPastFutureIndependence_of_external`); by `BG20WindowFieldIntrinsicInput` and
`BG20DiscreteWindowLawIntrinsicInput` the chart fields and the discrete analogues of the window chart laws are
functions of these wedges, so at each level the coordinates of the two windows built from them are independent; they
are close in probability to the coordinates built from the chart laws of the walk, whose joint laws converge to those
of the joint limit (`BG20WindowJointConvergenceInput`); the independence passes to the limit
(`LatticeProb.indepFun_of_tendsto_law_of_coupled`) for each finite set of coordinates, hence for the pairs
(`indepFun_prod_of_forall_finset`). -/
theorem bg20ChartIndependenceInputBG_of_dmsIntrinsic {𝒮 : SpaceFillingSLEModel}
    (hDMS : DMSIntrinsicPastFutureIndependence) (hF : BG20WindowFieldIntrinsicInput 𝒮)
    (hL : BG20DiscreteWindowLawIntrinsicInput 𝒮) (hJ : BG20WindowJointConvergenceInput 𝒮) :
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
  have hind := dms21IntrinsicPastFutureIndependence_of_external hDMS 𝒮 γ hγ hγ2 Ω S hS H hH hrep η' hη' hae
    ((b + a') / 2)
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
    -- the coordinates built from the past and future intrinsic wedges
    let Xn : ℕ → Ω → (A → ℝ) × (B → ℝ) := fun n ω => finCoords A B (F₁ (H ω, η' ω), R₁ n (H ω, η' ω))
    let Yn : ℕ → Ω → (A' → ℝ) × (B' → ℝ) := fun n ω => finCoords A' B' (F₂ (H ω, η' ω), R₂ n (H ω, η' ω))
    have hΨ₁ : ∀ n, Measurable[intrinsicCurveDecoratedSurfaceSigma γ (Iic ((b + a') / 2))]
        (fun p => finCoords A B (F₁ p, R₁ n p)) := fun n =>
      (measurable_finCoords A B).comp (hF₁m.prodMk (hR₁m n))
    have hΨ₂ : ∀ n, Measurable[intrinsicCurveDecoratedSurfaceSigma γ (Ici ((b + a') / 2))]
        (fun p => finCoords A' B' (F₂ p, R₂ n p)) := fun n =>
      (measurable_finCoords A' B').comp (hF₂m.prodMk (hR₂m n))
    have hXn : ∀ n, Measurable (Xn n) := fun n =>
      ((hΨ₁ n).mono (intrinsicCurveDecoratedSurfaceSigma_le γ _) le_rfl).comp hZ
    have hYn : ∀ n, Measurable (Yn n) := fun n =>
      ((hΨ₂ n).mono (intrinsicCurveDecoratedSurfaceSigma_le γ _) le_rfl).comp hZ
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
