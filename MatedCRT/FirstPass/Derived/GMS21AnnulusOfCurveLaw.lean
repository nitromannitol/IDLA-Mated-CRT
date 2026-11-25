import MatedCRT.FirstPass.Derived.GMS21LocalCurveStoppedPick
import MatedCRT.FirstPass.Derived.GMS21AnnulusUniformTransfer
import MatedCRT.FirstPass.Derived.BlockExitSkeletonLevyProkhorov
import MatedCRT.FirstPass.Derived.StopAtExitWalkBound
import MatedCRT.FirstPass.Derived.EuclideanCurveLawSupport
import MatedCRT.FirstPass.Derived.TargetLawRotation
import LatticeProb.Topology.IsotropicTranslatedBrownianCurveLaw

/-!
# From the Lévy–Prokhorov distance of curve laws to the comparison on an annulus

In the proof of Theorem 3.4, case 1, of Gwynne–Miller–Sheffield (arXiv:1705.11161), the uniform-start invariance
principle (arXiv:1807.07515, Theorem 3.10), which compares the laws of the walk and of Brownian motion modulo time
parametrization in the local metric (1.8) of arXiv:1807.07515, is read on the paths stopped at their exits from an
annulus `B_R(0) \ closedBall 0 α` avoiding the origin.

* `measure_le_image_project_thickening`: the one-sided bound of
  `measure_le_of_levyProkhorovEDist_curveLaw_lt` with a measurable neighbourhood in the local metric.
* `brownianCurveLaw_eq_planar`: Brownian motion with an isotropic covariance `c • 1`, `c > 0`, started from `z`, has
  the curve law modulo time parametrization of planar Brownian motion from `z`.
* `exists_levyProkhorovEDist_stoppedExitCurve_annulus_lt`: for all `0 < α < b < ρ < R` and `c > 0` there is `δ > 0`
  such that, for every start `z ∈ closedBall 0 ρ \ B_b(0)` and every random continuous path `W` exiting the annulus
  almost surely, a Lévy–Prokhorov distance less than `δ` between the curve law of `W` and that of planar Brownian
  motion from `z` gives a Lévy–Prokhorov distance less than `c` between the laws of the curve classes of the two
  paths stopped at their exits from the annulus.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open LatticeProb LatticeProb.UnboundedRayIntervalIntegrand LatticeProb.UnboundedRayLocalDistance
  LatticeProb.UnboundedRayCurveSpace LatticeProb.ReparamDistanceIsometry
open ReflectedGMS.StatementIngredients

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _
local instance : BorelSpace (UnboundedRayCurveSpace 2) := ⟨rfl⟩

/-- Planar Brownian motion read in Euclidean coordinates is a probability law. -/
theorem isProbabilityMeasure_map_complexToEuclideanPath (z : ℂ) :
    IsProbabilityMeasure ((planarBrownianMotion z).map complexToEuclideanPath) :=
  (Measure.isProbabilityMeasure_map_iff continuous_complexToEuclideanPath.measurable.aemeasurable).2
    inferInstance

attribute [local instance] isProbabilityMeasure_map_complexToEuclideanPath

/-- The curve law depends only on the law of the path. -/
theorem curveLaw_congr {μ μ' : Measure (Path 2)} {i : IsProbabilityMeasure μ} {i' : IsProbabilityMeasure μ'}
    (h : μ = μ') (hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    (hμ' : ∀ᵐ (f : Path 2) ∂μ', ¬ Bornology.IsBounded (Set.range f)) :
    @curveLaw 2 μ i hμ = @curveLaw 2 μ' i' hμ' := by
  subst h
  rfl

/-- **One-sided bound with a measurable neighbourhood.** If the curve law of `ν` restricted to the unbounded paths is
within `δ > 0` of the curve law of `μ` in the Lévy–Prokhorov distance, then for every set `S` of paths, `ν S` is at most
the `μ`-mass of the unbounded paths whose curve class lies in the open `δ`-neighbourhood of the curve classes of the
unbounded paths of `S`, plus `2 δ`. -/
theorem measure_le_image_project_thickening (ν μ : Measure (Path 2)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f)) {δ : ℝ}
    (hδ : 0 < δ) (h : levyProkhorovEDist (GMS310.unboundedCurveLaw ν) (curveLaw μ hμ) < ENNReal.ofReal δ)
    (S : Set (Path 2)) :
    ν S ≤ μ (Subtype.val '' (project ⁻¹' thickening δ
        (project '' (Subtype.val ⁻¹' S : Set (UnboundedRay 2))))) + 2 * ENNReal.ofReal δ := by
  set Unb : Set (Path 2) := {f | ¬ Bornology.IsBounded (Set.range f)} with hUnb
  have hUm : MeasurableSet Unb := measurableSet_continuousMap_unbounded_range 0
  have hemb : MeasurableEmbedding (Subtype.val : UnboundedRay 2 → Path 2) :=
    MeasurableEmbedding.subtype_coe hUm
  set X : Set (UnboundedRayCurveSpace 2) := project '' (Subtype.val ⁻¹' S) with hX
  have hB : MeasurableSet (closure X) := isClosed_closure.measurableSet
  have hT : MeasurableSet (thickening δ X) := isOpen_thickening.measurableSet
  have h1 : ν (S ∩ Unb) ≤ GMS310.unboundedCurveLaw ν (closure X) := by
    unfold GMS310.unboundedCurveLaw
    rw [Measure.map_apply continuous_project.measurable hB, hemb.comap_apply]
    refine measure_mono ?_
    rintro f ⟨hfS, hf⟩
    exact ⟨⟨f, hf⟩, subset_closure ⟨⟨f, hf⟩, hfS, rfl⟩, rfl⟩
  have h2 : curveLaw μ hμ (thickening δ X) = μ (Subtype.val '' (project ⁻¹' thickening δ X)) := by
    rw [curveLaw_apply μ hμ hT]
    have hρ : (supportedLaw μ Unb hμ).map Subtype.val = μ := map_supportedLaw μ Unb hμ
    calc supportedLaw μ Unb hμ (project ⁻¹' thickening δ X)
        = (supportedLaw μ Unb hμ).map Subtype.val (Subtype.val '' (project ⁻¹' thickening δ X)) := by
          refine Eq.trans ?_ ((MeasurableEmbedding.subtype_coe hUm).map_apply _ _).symm
          exact congrArg (fun A => supportedLaw μ Unb hμ A)
            (Set.preimage_image_eq _ Subtype.val_injective).symm
      _ = μ (Subtype.val '' (project ⁻¹' thickening δ X)) := by rw [hρ]
  have h3 : ν Unbᶜ ≤ ENNReal.ofReal δ := by
    have hr := right_measure_le_of_levyProkhorovEDist_lt h MeasurableSet.univ
    rw [measure_univ] at hr
    have hν : GMS310.unboundedCurveLaw ν (thickening (ENNReal.ofReal δ).toReal univ) ≤ ν Unb := by
      unfold GMS310.unboundedCurveLaw
      rw [Measure.map_apply continuous_project.measurable isOpen_thickening.measurableSet,
        hemb.comap_apply]
      refine measure_mono ?_
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    rw [prob_compl_eq_one_sub hUm, tsub_le_iff_left]
    exact hr.trans (add_le_add hν le_rfl)
  have hl := left_measure_le_of_levyProkhorovEDist_lt h hB
  rw [ENNReal.toReal_ofReal hδ.le, thickening_closure] at hl
  calc ν S ≤ ν (S ∩ Unb) + ν Unbᶜ := by
        refine (measure_mono fun f hf => ?_).trans (measure_union_le _ _)
        by_cases hfU : f ∈ Unb
        · exact Or.inl ⟨hf, hfU⟩
        · exact Or.inr hfU
    _ ≤ (μ (Subtype.val '' (project ⁻¹' thickening δ X)) + ENNReal.ofReal δ) + ENNReal.ofReal δ :=
        add_le_add (h1.trans (hl.trans (add_le_add h2.le le_rfl))) h3
    _ = μ (Subtype.val '' (project ⁻¹' thickening δ X)) + 2 * ENNReal.ofReal δ := by
        rw [add_assoc, two_mul]

/-- **Isotropic Brownian motion modulo time parametrization.** Brownian motion with covariance `c • 1`, `c > 0`,
started from (the Euclidean reading of) `z` has the curve law modulo time parametrization of planar Brownian motion
from `z`. -/
theorem brownianCurveLaw_eq_planar (target : AnisotropicBrownianTarget) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1) (z : ℂ) :
    (GMS310.brownianCurveLaw target (Complex.orthonormalBasisOneI.repr z) :
        Measure (UnboundedRayCurveSpace 2)) =
      curveLaw ((planarBrownianMotion z).map complexToEuclideanPath)
        (ae_unbounded_range_map_planarBrownianMotion z) := by
  have horth : ∀ O : Matrix (Fin 2) (Fin 2) ℝ, O.transpose * O = 1 →
      (target.standardLaw : Measure (Path 2)).map (linearImageBrownianPath O) = target.standardLaw :=
    fun O hO => TargetLawRotation.map_linearImageBrownianPath_of_transpose_mul_self target.isStandard hO
  obtain ⟨hμ, hν, hcurve⟩ :=
    curveLaw_translated_isotropicBrownian target hc hcov horth (Complex.orthonormalBasisOneI.repr z)
  have hcpe : (TargetLawTemplateEvent.complexPathToEuc : ContinuousPath ℂ → BouRabeeGwynne.BrownianPath 2) =
      complexToEuclideanPath := rfl
  have hstd : (target.standardLaw : Measure (Path 2)).map
      (translatePath (Complex.orthonormalBasisOneI.repr z)) =
        (planarBrownianMotion z).map complexToEuclideanPath := by
    rw [TargetLawTemplateEvent.eq_map_complexPathToEuc target.isStandard, hcpe,
      Measure.map_map (continuous_translatePath _).measurable continuous_complexToEuclideanPath.measurable,
      ← StopAtExitCmp.map_translatePath_planarBrownianMotion z,
      Measure.map_map continuous_complexToEuclideanPath.measurable
        (StopAtExitCmp.translatePath z).continuous.measurable]
    congr 1
    funext b
    refine ContinuousMap.ext fun t => ?_
    show Complex.orthonormalBasisOneI.repr z + Complex.orthonormalBasisOneI.repr (b t) =
      Complex.orthonormalBasisOneI.repr (b t + z)
    rw [map_add, add_comm]
  exact hcurve.trans (curveLaw_congr hstd _ _)

/-- **From the curve law to the comparison on an annulus** (proof of Theorem 3.4, case 1, of arXiv:1705.11161). Let
`0 < α < b < ρ < R` and `c > 0`. There is `δ > 0` such that for every start `z ∈ closedBall 0 ρ \ B_b(0)` and every
random continuous path `W` exiting the annulus `B_R(0) \ closedBall 0 α` almost surely, if the curve law of `W`
(restricted to the unbounded paths) is within `δ` of the curve law of planar Brownian motion from `z` in the
Lévy–Prokhorov distance, then the laws of the curve classes of the two paths stopped at their exits from the annulus
are within `c`. -/
theorem exists_levyProkhorovEDist_stoppedExitCurve_annulus_lt {Ω' : Type*} [MeasurableSpace Ω']
    {α b ρ R c : ℝ} (hα : 0 < α) (hαb : α < b) (hbρ : b < ρ) (hρR : ρ < R) (hc : 0 < c) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ \ ball 0 b, ∀ (ν : Measure Ω') [IsProbabilityMeasure ν]
      (W : Ω' → ContinuousPath ℂ), Measurable W →
      (∀ᵐ w ∂ν, pathExitTime (ball (0 : ℂ) R \ closedBall 0 α) ⇑(W w) ≠ ⊤) →
      levyProkhorovEDist (GMS310.unboundedCurveLaw (ν.map fun w => complexToEuclideanPath (W w)))
          (curveLaw ((planarBrownianMotion z).map complexToEuclideanPath)
            (ae_unbounded_range_map_planarBrownianMotion z)) < ENNReal.ofReal δ →
      levyProkhorovEDist
          (ν.map fun w => StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R \ closedBall 0 α) (W w))
          ((planarBrownianMotion z).map
            (StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R \ closedBall 0 α))) <
        ENNReal.ofReal c := by
  obtain ⟨δ₂, hδ₂, hR2⟩ := StopAtExitCmp.exists_forall_stopAtExit_le_of_forall_le_variable_annulus
    (Ω' := Ω') hα hαb hbρ hρR one_pos (half_pos hc) (half_pos hc)
  set s : ℝ := min δ₂ 1 with hs
  have hs0 : 0 < s := lt_min hδ₂ one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsδ : s ≤ δ₂ := min_le_left _ _
  set δ : ℝ := min (Real.exp (-(R + 2)) * s * ((R + 2) - (R + 1))) (s / 2) with hδdef
  have hδ : 0 < δ := lt_min (by have : (R + 2) - (R + 1) = 1 := by ring
                                rw [this]; positivity) (half_pos hs0)
  have hAo : IsOpen (ball (0 : ℂ) R \ closedBall 0 α) := isOpen_ball.sdiff isClosed_closedBall
  refine ⟨δ, hδ, fun z hz ν _ W hW hfin hLP => ?_⟩
  have hE : Measurable (complexToEuclideanPath : ContinuousPath ℂ → Path 2) :=
    continuous_complexToEuclideanPath.measurable
  have hΦ : Measurable fun w => complexToEuclideanPath (W w) := hE.comp hW
  have : IsProbabilityMeasure (ν.map fun w => complexToEuclideanPath (W w)) :=
    (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).2 inferInstance
  -- the one-sided bound at variable radii `r ∈ (R + 1, R + 2)`
  have hvar : ∀ S : Set (ℝ≥0 → ℂ), ν {w | ⇑(W w) ∈ S} ≤
      planarBrownianMotion z {b | ∃ g ∈ S, ∃ r : ℝ, R + 1 < r ∧
        cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) <
          ENNReal.ofReal δ₂} + ENNReal.ofReal δ₂ := by
    intro S
    set S₂ : Set (Path 2) := {f | ∃ w, ⇑(W w) ∈ S ∧ complexToEuclideanPath (W w) = f} with hS₂
    have hA := measure_le_image_project_thickening (ν.map fun w => complexToEuclideanPath (W w))
      ((planarBrownianMotion z).map complexToEuclideanPath) (ae_unbounded_range_map_planarBrownianMotion z)
      hδ hLP S₂
    have hM : MeasurableSet (Subtype.val '' (project ⁻¹' thickening δ
        (project '' (Subtype.val ⁻¹' S₂ : Set (UnboundedRay 2))))) :=
      (MeasurableEmbedding.subtype_coe (measurableSet_continuousMap_unbounded_range 0)).measurableSet_image'
        (continuous_project.measurable isOpen_thickening.measurableSet)
    calc ν {w | ⇑(W w) ∈ S} ≤ ν ((fun w => complexToEuclideanPath (W w)) ⁻¹' S₂) :=
          measure_mono fun w hw => ⟨w, hw, rfl⟩
      _ ≤ (ν.map fun w => complexToEuclideanPath (W w)) S₂ := Measure.le_map_apply hΦ.aemeasurable S₂
      _ ≤ _ := hA
      _ ≤ _ := by
        rw [Measure.map_apply hE hM]
        refine add_le_add (measure_mono ?_) ?_
        · rintro b ⟨y, hy, hyb⟩
          obtain ⟨x, ⟨y', hy'S, rfl⟩, hxy⟩ := (mem_thickening_iff_exists_edist_lt _ _).1 hy
          obtain ⟨w, hwS, hwy⟩ := hy'S
          rw [edist_project, UnboundedRayLocalDistance.localEDist_comm] at hxy
          have h₁ : ∀ t, y'.1 t = Complex.orthonormalBasisOneI.repr (W w t) := fun t => by
            rw [← hwy]
            rfl
          have h₂ : ∀ t, y.1 t = Complex.orthonormalBasisOneI.repr (b t) := fun t => by
            rw [hyb]
            rfl
          obtain ⟨r, hr, hlt⟩ := exists_cmpEDist_stopAtExit_lt_of_localEDist_lt y' y h₁ h₂
            (a := R + 1) (b := R + 2) (by linarith) hs0.le hs1
            (lt_of_lt_of_le hxy (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
          exact ⟨⇑(W w), hwS, r, hr.1, lt_of_lt_of_le hlt (ENNReal.ofReal_le_ofReal hsδ)⟩
        · rw [two_mul, ← ENNReal.ofReal_add hδ.le hδ.le]
          refine ENNReal.ofReal_le_ofReal ?_
          have : δ ≤ s / 2 := min_le_right _ _
          linarith
  have hstop := hR2 z hz ν (fun w => ⇑(W w)) (fun w => (W w).continuous) hvar
  have hF : AEMeasurable
      (fun w => StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R \ closedBall 0 α) (W w)) ν :=
    ((StopAtExitLevyProkhorov.measurable_stoppedExitCurve _ hAo).comp hW).aemeasurable
  have hfinB : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion z),
      pathExitTime (ball (0 : ℂ) R \ closedBall 0 α) ⇑b ≠ ⊤ :=
    StopAtExitWalkBound.ae_pathExitTime_planarBrownianMotion_ne_top
      ((isBounded_ball (x := (0 : ℂ)) (r := R)).subset sdiff_subset) z
  have hle := BlockExit.levyProkhorovEDist_stoppedExitCurve_le_of_allSet ν W
    (ball (0 : ℂ) R \ closedBall 0 α) hF hfin (ball (0 : ℂ) R \ closedBall 0 α) hAo z hfinB
    (κ := c / 2) (E := ENNReal.ofReal (c / 2)) hstop
  rw [max_self] at hle
  exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hc).2 (half_lt_self hc))

end MatedCRT.GMS310Transfer
