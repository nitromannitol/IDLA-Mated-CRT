import MatedCRT.FirstPass.Derived.StopAtExitCurveClass
import LatticeProb.Prob.LevyProkhorovAllSets

/-!
# From a Lévy–Prokhorov bound on stopped curves to a bound on all sets of stopped paths

The law of the curve class of a planar path stopped at its first exit time from `U`, under planar
Brownian motion from `z`, is the stopped Brownian law of the Euclidean reading of `U` from the
Euclidean reading of `z`. A Lévy–Prokhorov bound between the law of the stopped curve class of
a random continuous path and this law gives, for every set `S` of stopped paths, a bound on the
probability that the path stopped at its exit time from `V` lies in `S`, in terms of the
Brownian probability of the `cmpEDist`-neighborhood of `S`.
-/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitLevyProkhorov

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp MatedCRT.StopAtExitCurveClass

/-- The curve class of a planar path stopped at its first exit time from `U`, in Euclidean
coordinates (`0` when the path never exits). -/
noncomputable def stoppedExitCurve (U : Set ℂ) (b : ContinuousPath ℂ) : BouRabeeGwynne.CurveSpace 2 :=
  isometryEquiv 2
    (normalizedPrefixCurve (complexToEuclideanPath b) (pathExitTime U ⇑b).toNNReal)

theorem stoppedBrownianCurve_complexPathToEuc_eq (U : Set ℂ) (z : ℂ) (b : ContinuousPath ℂ) :
    BouRabeeGwynne.stoppedBrownianCurve (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr z) (complexPathToEuc b) =
      stoppedExitCurve U (translatePath z b) :=
  stoppedBrownianCurve_complexPathToEuc U z b

theorem measurable_stoppedExitCurve (U : Set ℂ) (hU : IsOpen U) :
    Measurable (stoppedExitCurve U) := by
  have hV : IsOpen (Complex.orthonormalBasisOneI.repr '' U) :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenMap U hU
  have h0 := (BouRabeeGwynne.measurable_stoppedBrownianCurve hV
    (Complex.orthonormalBasisOneI.repr 0)).comp measurable_complexPathToEuc
  convert h0 using 1
  funext b
  have h := stoppedBrownianCurve_complexPathToEuc_eq U 0 b
  have ht : translatePath 0 b = b := by
    refine ContinuousMap.ext fun s => ?_
    simp
  rw [ht] at h
  exact h.symm

/-- The stopped Brownian curve law from `z` is the image of planar Brownian motion from `z`
under `stoppedExitCurve U`. -/
theorem stoppedBrownianLaw_eq_map (U : Set ℂ) (hU : IsOpen U) (z : ℂ)
    (μ : Measure (BouRabeeGwynne.BrownianPath 2)) (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ) :
    BouRabeeGwynne.stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr z) μ =
      (planarBrownianMotion z).map (stoppedExitCurve U) := by
  have hV : IsOpen (Complex.orthonormalBasisOneI.repr '' U) :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenMap U hU
  have hG := measurable_stoppedExitCurve U hU
  rw [BouRabeeGwynne.stoppedBrownianLaw, eq_map_complexPathToEuc hμ,
    Measure.map_map (BouRabeeGwynne.measurable_stoppedBrownianCurve hV _)
      measurable_complexPathToEuc,
    ← map_translatePath_planarBrownianMotion z,
    Measure.map_map hG (translatePath z).measurable]
  congr 1
  funext b
  exact stoppedBrownianCurve_complexPathToEuc_eq U z b

/-- A Lévy–Prokhorov bound between the law of the stopped curve class of a random path (stopped at
its exit time from `V`) and the planar Brownian stopped curve law from `z` (exit from `U`, open)
bounds, for every set `S` of stopped paths, the probability of `S` by the Brownian probability of
the `cmpEDist`-neighborhood of `S`, up to an additive `δ`. Both exit times are finite almost
surely. -/
theorem allSet_stopAtExit_le_of_levyProkhorovEDist {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (W : Ω → ContinuousPath ℂ) (V : Set ℂ)
    (hF : AEMeasurable (fun w => stoppedExitCurve V (W w)) ν)
    (hfin : ∀ᵐ w ∂ν, pathExitTime V ⇑(W w) ≠ ⊤) (U : Set ℂ) (hU : IsOpen U) (z : ℂ)
    (hfinB : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion z), pathExitTime U ⇑b ≠ ⊤) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (h : levyProkhorovEDist (ν.map fun w => stoppedExitCurve V (W w))
      ((planarBrownianMotion z).map (stoppedExitCurve U)) < ENNReal.ofReal δ)
    (S : Set (ℝ≥0 → ℂ)) :
    ν {w | stopAtExit V ⇑(W w) ∈ S} ≤
      planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ f ∈ S, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal (δ + ε)} +
      ENNReal.ofReal δ := by
  set F : Ω → BouRabeeGwynne.CurveSpace 2 := fun w => stoppedExitCurve V (W w) with hFdef
  set A : Set (BouRabeeGwynne.CurveSpace 2) :=
    {x | ∃ w, pathExitTime V ⇑(W w) ≠ ⊤ ∧ stopAtExit V ⇑(W w) ∈ S ∧ F w = x} with hA
  have h1 : ν {w | stopAtExit V ⇑(W w) ∈ S} ≤ ν (F ⁻¹' A) := by
    refine measure_mono_ae ?_
    filter_upwards [hfin] with w hw hwS
    exact ⟨w, hw, hwS, rfl⟩
  have h2 : ν (F ⁻¹' A) ≤ (ν.map F) A := Measure.le_map_apply hF A
  have h3 := measure_le_thickening_of_levyProkhorovEDist_lt (ν.map F)
    ((planarBrownianMotion z).map (stoppedExitCurve U)) hδ hε h A
  have hG := measurable_stoppedExitCurve U hU
  rw [Measure.map_apply hG Metric.isOpen_thickening.measurableSet] at h3
  have h4 : planarBrownianMotion z (stoppedExitCurve U ⁻¹' Metric.thickening (δ + ε) A) ≤
      planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ f ∈ S, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal (δ + ε)} := by
    refine measure_mono_ae ?_
    filter_upwards [hfinB] with b hb hbT
    obtain ⟨x, ⟨w, hw, hwS, rfl⟩, hxd⟩ := Metric.mem_thickening_iff.1 hbT
    refine ⟨stopAtExit V ⇑(W w), hwS, ?_⟩
    rw [cmpEDist_stopAtExit_eq_edist_normalizedPrefixCurve U V b (W w) hb hw]
    change edist (stoppedExitCurve U b) (stoppedExitCurve V (W w)) < _
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hxd, by positivity⟩ |>.trans_le le_rfl
  calc ν {w | stopAtExit V ⇑(W w) ∈ S} ≤ (ν.map F) A := h1.trans h2
    _ ≤ _ := h3.trans (add_le_add h4 le_rfl)

end MatedCRT.StopAtExitLevyProkhorov
