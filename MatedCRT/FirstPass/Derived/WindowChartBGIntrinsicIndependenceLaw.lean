import MatedCRT.External.DMSIntrinsicPastFutureIndependenceLaw
import MatedCRT.FirstPass.Derived.WindowChartBGIntrinsicIndependence
import MatedCRT.FirstPass.Derived.WindowChartBGJointConvergence

/-!
# Independence of the windows (Berestycki–Gwynne (2020), Lemma 7.21) from Duplantier–Miller–Sheffield, Theorem 1.9,
for the law of the DMS curve

The cited input `DMSIntrinsicPastFutureIndependenceLaw ν` is Duplantier–Miller–Sheffield, Theorem 1.9, with the two
halves as intrinsic curve-decorated wedges, on the mating-of-trees couplings whose Lebesgue-area curve has the law
`ν (16 / γ²)`. For a space-filling SLE model `𝒮` with normalized law `ν` (`HasNormalizedSLELaw 𝒮 ν`), the coupling of
every valid environment satisfies this law clause: its Lebesgue-area curve `ηL` is a measurable Lebesgue-area
representative of the curve of the environment (the clauses `spaceFilling` and `areaParam` of the coupling), so the law
of its rational-time code is `ν (16 / γ²)`.

## Main statements

* `MatedCRTEnv.IsValid.map_slePathCode_coupling_eq`: the law clause for the coupling of a valid environment.
* `dms21IntrinsicPastFutureIndependence_of_externalLaw`: `DMS21IntrinsicPastFutureIndependence 𝒮` from
  `DMSIntrinsicPastFutureIndependenceLaw ν` and `HasNormalizedSLELaw 𝒮 ν`.
* `bg20ChartIndependenceInputBG_of_dms21Intrinsic`: `BG20ChartIndependenceInputBG 𝒮` from
  `DMS21IntrinsicPastFutureIndependence 𝒮`, the two intrinsic window steps and `BG20WindowJointConvergenceInput`
  (the argument of `bg20ChartIndependenceInputBG_of_dmsIntrinsic`).
* `bg20ChartIndependenceInputBG_of_dmsIntrinsicLaw`: `BG20ChartIndependenceInputBG 𝒮` from
  `DMSIntrinsicPastFutureIndependenceLaw ν`, `HasNormalizedSLELaw 𝒮 ν`, the two intrinsic window steps and the
  exterior regularity of Jordan domains for planar Brownian motion (`JordanDomainExteriorRegularity`), which gives
  the joint convergence step (`bg20WindowJointConvergenceInput`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **The law clause for the coupling of a valid environment.** For a space-filling SLE model `𝒮` with normalized
law `ν`, the Lebesgue-area curve `ηL` of a mating-of-trees coupling of a valid environment whose area-parametrized
curve agrees almost surely with the curve of the environment has the rational-time code law `ν (16 / γ²)`. -/
theorem MatedCRTEnv.IsValid.map_slePathCode_coupling_eq {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hLaw : HasNormalizedSLELaw 𝒮 ν) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL ηc η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL ηc η₀ S.bm)
    (hae : ∀ᵐ ω ∂S.P, ⇑(ηc ω) = S.η ω) :
    S.P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2) := by
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hκ : 4 < 16 / γ ^ 2 := by
    rw [lt_div_iff₀ (pow_pos hγ 2)]
    linarith
  refine hLaw Ω _ S.P S.fieldSigma (16 / γ ^ 2) S.η ηL hP hκ hS.isSLE hcpl.measurable_curves.1 ?_
  filter_upwards [hcpl.spaceFilling, hcpl.areaParam, hae] with ω h1 h2 h3
  obtain ⟨hsurj, hprop, h0, hvol⟩ := h1
  obtain ⟨φ, hφ0, hφ⟩ := h2.1
  unfold IsLebesgueRepresentative
  exact ⟨h0, hsurj, hprop, hvol, φ, hφ0, fun t => (congrFun h3 t).symm.trans (hφ t)⟩

open DMSPastFuture DMSIntrinsicPastFuture in
/-- `DMS21IntrinsicPastFutureIndependence 𝒮` from the cited input `DMSIntrinsicPastFutureIndependenceLaw ν` for a
model `𝒮` with normalized law `ν`. A valid environment carries a mating-of-trees coupling whose cone field and curve
agree almost surely with its field and curve, and whose Lebesgue-area curve has the law `ν (16 / γ²)`
(`MatedCRTEnv.IsValid.map_slePathCode_coupling_eq`); the independence at every time `s` comes from the one at time
`0` and the stationarity (1.9), as in `dms21IntrinsicPastFutureIndependence_of_external`. -/
theorem dms21IntrinsicPastFutureIndependence_of_externalLaw {ν : ℝ → Measure SLEPathCode}
    (hDMS : DMSIntrinsicPastFutureIndependenceLaw ν) {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) :
    DMS21IntrinsicPastFutureIndependence 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS H hH hHae η' hη' hηae s
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηc, η₀, hcpl, hae⟩ := hS.matingOfTrees
  have hHc : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ = H ω φ := by
    filter_upwards [hHae, hae] with ω h1 h2 φ
    exact (h2.2 φ).symm.trans (h1 φ)
  have hηc : ∀ᵐ ω ∂S.P, η' ω = ηc ω := by
    filter_upwards [hηae, hae] with ω h1 h2
    exact DFunLike.coe_injective (h1.trans h2.1.symm)
  have hlawL := hS.map_slePathCode_coupling_eq hLaw hγ hγ2 hcpl (hae.mono fun _ h => h.1)
  obtain ⟨hstat, hind⟩ :=
    hDMS γ hγ hγ2 Ω S.P X X₀ hIG₀ B B' B₀ B₀' U ηL ηc η₀ S.bm hcpl hlawL H hH hHc η' hη' hηc
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

open DMSIntrinsicPastFuture in
/-- **Berestycki–Gwynne (2020), Lemma 7.21, for the inverse charts `windowChartBG` (`BG20ChartIndependenceInputBG`),
from the independence of the past and future intrinsic curve-decorated wedges at every time
(`DMS21IntrinsicPastFutureIndependence 𝒮`)**, following the printed proof as in
`bg20ChartIndependenceInputBG_of_dmsIntrinsic`: take `s = (b + a')/2` between the windows; by
`BG20WindowFieldIntrinsicInput` and `BG20DiscreteWindowLawIntrinsicInput` the chart fields and the discrete analogues
of the window chart laws are functions of the past and future intrinsic wedges at `s`, so at each level the
coordinates of the two windows built from them are independent; they are close in probability to the coordinates
built from the chart laws of the walk, whose joint laws converge to those of the joint limit
(`BG20WindowJointConvergenceInput`); the independence passes to the limit (`LatticeProb.indepFun_of_tendsto_law_of_coupled`)
for each finite set of coordinates, hence for the pairs (`indepFun_prod_of_forall_finset`). -/
theorem bg20ChartIndependenceInputBG_of_dms21Intrinsic {𝒮 : SpaceFillingSLEModel}
    (hDMS : DMS21IntrinsicPastFutureIndependence 𝒮) (hF : BG20WindowFieldIntrinsicInput 𝒮)
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

/-- **Berestycki–Gwynne (2020), Lemma 7.21, for the inverse charts `windowChartBG` (`BG20ChartIndependenceInputBG`),
from Duplantier–Miller–Sheffield, Theorem 1.9, for the law of the DMS curve.** The premises are the cited input
`DMSIntrinsicPastFutureIndependenceLaw ν`, the normalized law `ν` of the model (`HasNormalizedSLELaw 𝒮 ν`), the two
intrinsic window steps `BG20WindowFieldIntrinsicInput` and `BG20DiscreteWindowLawIntrinsicInput`, and the exterior
regularity of Jordan domains for planar Brownian motion (`JordanDomainExteriorRegularity`; Pommerenke, Section 2.1,
and the Beurling estimate, Lawler, Theorem 3.76), which gives the joint convergence step
(`bg20WindowJointConvergenceInput`). -/
theorem bg20ChartIndependenceInputBG_of_dmsIntrinsicLaw {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel} (hDMS : DMSIntrinsicPastFutureIndependenceLaw ν) (hLaw : HasNormalizedSLELaw 𝒮 ν)
    (hF : BG20WindowFieldIntrinsicInput 𝒮) (hL : BG20DiscreteWindowLawIntrinsicInput 𝒮)
    (hJ : JordanDomainExteriorRegularity) : BG20ChartIndependenceInputBG 𝒮 :=
  bg20ChartIndependenceInputBG_of_dms21Intrinsic (dms21IntrinsicPastFutureIndependence_of_externalLaw hDMS hLaw)
    hF hL (bg20WindowJointConvergenceInput hJ)

end MatedCRT
