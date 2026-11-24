import MatedCRT.FirstPass.Derived.StopAtExitNested
import MatedCRT.FirstPass.Derived.StopAtExitLevyProkhorov
import MatedCRT.FirstPass.Derived.ExitReparamSetup

/-!
# Stopping at the exit from a ball and from an annulus

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1 (the transfer from the `0`-quantum
cone to the `γ`-quantum cone), local absolute continuity compares the two cones only on domains at positive distance
from the origin. The walk is therefore compared with Brownian motion until its exit from the annulus
`B_ρ(0) \ closedBall 0 α`, and the choice of `α` makes the probability that Brownian motion from a point of
`D \ B_δ(0)` hits `B_α(0)` before leaving `D` small. A path that leaves `U \ K` through the outer boundary has the same
exit time from `U` and from `U \ K`, so its curve classes stopped at the two exits coincide.

## Main results

* `HitsBeforeExit U K f`: the path `f` leaves `U \ K` in finite time, at a point of `K`.
* `pathExitTime_eq_of_not_hitsBeforeExit`: for `U` open, `K` closed and `f` continuous, if `f` does not hit `K` before
  it leaves `U` in this sense, the exit times of `f` from `U` and from `U \ K` agree.
* `levyProkhorovEDist_map_le_add_of_eq_off`: if `F₁ = G₁` off `E₁` and `F₂ = G₂` off `E₂`, the Lévy–Prokhorov
  distance of the laws of `F₁` and `F₂` is at most that of the laws of `G₁` and `G₂` plus `P₁ E₁ + P₂ E₂`.
* `levyProkhorovEDist_stoppedExitCurve_le_diff`: the Lévy–Prokhorov distance between the laws of the curve classes
  of two random paths stopped at their exits from `U` is at most the distance for the exits from `U \ K` plus the
  probabilities that the paths hit `K` before they leave `U`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

section Exit

/-- A path `f` *hits `K` before it leaves `U`*, read at the exit from `U \ K`: it leaves `U \ K` in finite time, at a
point of `K`. -/
def HitsBeforeExit (U K : Set ℂ) (f : ℝ≥0 → ℂ) : Prop :=
  pathExitTime (U \ K) f ≠ ⊤ ∧ f (pathExitTime (U \ K) f).toNNReal ∈ K

/-- The exit time from `U \ K` is at most the exit time from `U`. -/
theorem pathExitTime_diff_le (U K : Set ℂ) (f : ℝ≥0 → ℂ) : pathExitTime (U \ K) f ≤ pathExitTime U f := by
  unfold pathExitTime
  exact sInf_le_sInf fun c ⟨t, hc, ht⟩ => ⟨t, hc, fun hu => ht hu.1⟩

/-- A continuous path is outside the open set `V` at its (finite) exit time from `V`. -/
theorem apply_toNNReal_pathExitTime_not_mem {V : Set ℂ} (hV : IsOpen V) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hfin : pathExitTime V f ≠ ⊤) : f (pathExitTime V f).toNNReal ∉ V := by
  by_cases h0 : f 0 ∈ V
  · have hfr := pathExitPosition_mem_frontier_of_continuous hV hf h0 (lt_top_iff_ne_top.2 hfin)
    rw [StopAtExitCmp.pathExitPosition_eq_of_ne_top hfin, hV.frontier_eq] at hfr
    exact hfr.2
  · have hle : pathExitTime V f ≤ ((0 : ℝ≥0) : ℝ≥0∞) := sInf_le ⟨0, rfl, h0⟩
    have h00 : pathExitTime V f = 0 := le_antisymm (by simpa using hle) bot_le
    rw [h00, ENNReal.toNNReal_zero]
    exact h0

/-- If a continuous path leaves `U \ K` (`U` open, `K` closed) in finite time at a point outside `K`, its exit times
from `U` and from `U \ K` agree. -/
theorem pathExitTime_eq_of_exitPoint_not_mem {U K : Set ℂ} (hU : IsOpen U) (hK : IsClosed K)
    {f : ℝ≥0 → ℂ} (hf : Continuous f) (hfin : pathExitTime (U \ K) f ≠ ⊤)
    (hout : f (pathExitTime (U \ K) f).toNNReal ∉ K) :
    pathExitTime U f = pathExitTime (U \ K) f := by
  have hnot := apply_toNNReal_pathExitTime_not_mem (hU.sdiff hK) hf hfin
  refine le_antisymm ?_ (pathExitTime_diff_le U K f)
  have hU' : f (pathExitTime (U \ K) f).toNNReal ∉ U := fun hu => hnot ⟨hu, hout⟩
  calc pathExitTime U f ≤ ((pathExitTime (U \ K) f).toNNReal : ℝ≥0∞) := sInf_le ⟨_, rfl, hU'⟩
    _ = pathExitTime (U \ K) f := ENNReal.coe_toNNReal hfin

/-- If a continuous path does not hit the closed set `K` before it leaves the open set `U`, its exit times from `U`
and from `U \ K` agree. -/
theorem pathExitTime_eq_of_not_hitsBeforeExit {U K : Set ℂ} (hU : IsOpen U) (hK : IsClosed K)
    {f : ℝ≥0 → ℂ} (hf : Continuous f) (h : ¬ HitsBeforeExit U K f) :
    pathExitTime U f = pathExitTime (U \ K) f := by
  by_cases hfin : pathExitTime (U \ K) f = ⊤
  · have h1 := pathExitTime_diff_le U K f
    rw [hfin, top_le_iff] at h1
    rw [h1, hfin]
  · exact pathExitTime_eq_of_exitPoint_not_mem hU hK hf hfin fun hk => h ⟨hfin, hk⟩

/-- If a continuous path does not hit `K` before it leaves `U`, its curve classes stopped at the exits from `U` and
from `U \ K` coincide. -/
theorem stoppedExitCurve_eq_of_not_hitsBeforeExit {U K : Set ℂ} (hU : IsOpen U) (hK : IsClosed K)
    {b : ContinuousPath ℂ} (h : ¬ HitsBeforeExit U K ⇑b) :
    stoppedExitCurve U b = stoppedExitCurve (U \ K) b := by
  have he := pathExitTime_eq_of_not_hitsBeforeExit hU hK b.continuous h
  simp only [stoppedExitCurve, he]

end Exit

section LevyProkhorov

variable {Ω₁ Ω₂ X : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- One side of `levyProkhorovEDist_map_le_add_of_eq_off`. -/
theorem map_apply_le_map_thickening_add_of_eq_off (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    {F₁ G₁ : Ω₁ → X} {F₂ G₂ : Ω₂ → X} (hF₁ : AEMeasurable F₁ P₁) (hG₁ : AEMeasurable G₁ P₁)
    (hF₂ : AEMeasurable F₂ P₂) (hG₂ : AEMeasurable G₂ P₂) (E₁ : Set Ω₁) (E₂ : Set Ω₂)
    (h₁ : ∀ ω, ω ∉ E₁ → F₁ ω = G₁ ω) (h₂ : ∀ ω, ω ∉ E₂ → F₂ ω = G₂ ω) {c : ℝ≥0∞}
    (hc : levyProkhorovEDist (P₁.map G₁) (P₂.map G₂) < c) {r : ℝ} (hr : c.toReal ≤ r)
    {B : Set X} (hB : MeasurableSet B) :
    P₁.map F₁ B ≤ P₂.map F₂ (thickening r B) + (c + (P₁ E₁ + P₂ E₂)) := by
  have hT : MeasurableSet (thickening r B) := isOpen_thickening.measurableSet
  have hTc : MeasurableSet (thickening c.toReal B) := isOpen_thickening.measurableSet
  have hsub₁ : F₁ ⁻¹' B ⊆ G₁ ⁻¹' B ∪ E₁ := by
    intro ω hω
    by_cases hE : ω ∈ E₁
    · exact Or.inr hE
    · left
      change G₁ ω ∈ B
      rw [← h₁ ω hE]
      exact hω
  have hsub₂ : G₂ ⁻¹' thickening r B ⊆ F₂ ⁻¹' thickening r B ∪ E₂ := by
    intro ω hω
    by_cases hE : ω ∈ E₂
    · exact Or.inr hE
    · left
      change F₂ ω ∈ thickening r B
      rw [h₂ ω hE]
      exact hω
  have hlp := left_measure_le_of_levyProkhorovEDist_lt hc hB
  rw [Measure.map_apply_of_aemeasurable hG₁ hB, Measure.map_apply_of_aemeasurable hG₂ hTc] at hlp
  calc P₁.map F₁ B = P₁ (F₁ ⁻¹' B) := Measure.map_apply_of_aemeasurable hF₁ hB
    _ ≤ P₁ (G₁ ⁻¹' B) + P₁ E₁ := (measure_mono hsub₁).trans (measure_union_le _ _)
    _ ≤ P₂ (G₂ ⁻¹' thickening c.toReal B) + c + P₁ E₁ := add_le_add hlp le_rfl
    _ ≤ P₂ (G₂ ⁻¹' thickening r B) + c + P₁ E₁ :=
        add_le_add (add_le_add (measure_mono (preimage_mono (thickening_mono hr B))) le_rfl) le_rfl
    _ ≤ P₂ (F₂ ⁻¹' thickening r B) + P₂ E₂ + c + P₁ E₁ :=
        add_le_add (add_le_add ((measure_mono hsub₂).trans (measure_union_le _ _)) le_rfl) le_rfl
    _ = P₂.map F₂ (thickening r B) + (c + (P₁ E₁ + P₂ E₂)) := by
        rw [Measure.map_apply_of_aemeasurable hF₂ hT]
        ring

/-- **Changing random elements off small events.** If `F₁ = G₁` off `E₁` and `F₂ = G₂` off `E₂`, then the
Lévy–Prokhorov distance between the laws of `F₁` and `F₂` is at most the distance between the laws of `G₁` and `G₂`
plus `P₁ E₁ + P₂ E₂`. -/
theorem levyProkhorovEDist_map_le_add_of_eq_off (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    {F₁ G₁ : Ω₁ → X} {F₂ G₂ : Ω₂ → X} (hF₁ : AEMeasurable F₁ P₁) (hG₁ : AEMeasurable G₁ P₁)
    (hF₂ : AEMeasurable F₂ P₂) (hG₂ : AEMeasurable G₂ P₂) (E₁ : Set Ω₁) (E₂ : Set Ω₂)
    (h₁ : ∀ ω, ω ∉ E₁ → F₁ ω = G₁ ω) (h₂ : ∀ ω, ω ∉ E₂ → F₂ ω = G₂ ω) :
    levyProkhorovEDist (P₁.map F₁) (P₂.map F₂) ≤
      levyProkhorovEDist (P₁.map G₁) (P₂.map G₂) + P₁ E₁ + P₂ E₂ := by
  refine levyProkhorovEDist_le_of_forall _ _ _ fun ε B hε hεtop hB => ?_
  rw [add_assoc] at hε
  have hpq : P₁ E₁ + P₂ E₂ ≤ ε := le_add_self.trans hε.le
  have hcancel : ε - (P₁ E₁ + P₂ E₂) + (P₁ E₁ + P₂ E₂) = ε := tsub_add_cancel_of_le hpq
  have hdc : levyProkhorovEDist (P₁.map G₁) (P₂.map G₂) < ε - (P₁ E₁ + P₂ E₂) := by
    by_contra h
    have h' := add_le_add (not_lt.1 h) (le_refl (P₁ E₁ + P₂ E₂))
    rw [hcancel] at h'
    exact absurd hε (not_lt.2 h')
  have hr : (ε - (P₁ E₁ + P₂ E₂)).toReal ≤ ε.toReal := ENNReal.toReal_mono hεtop.ne tsub_le_self
  constructor
  · have h := map_apply_le_map_thickening_add_of_eq_off P₁ P₂ hF₁ hG₁ hF₂ hG₂ E₁ E₂ h₁ h₂ hdc hr hB
    rwa [hcancel] at h
  · have hdc' : levyProkhorovEDist (P₂.map G₂) (P₁.map G₁) < ε - (P₁ E₁ + P₂ E₂) := by
      rwa [levyProkhorovEDist_comm]
    have h := map_apply_le_map_thickening_add_of_eq_off P₂ P₁ hF₂ hG₂ hF₁ hG₁ E₂ E₁ h₂ h₁ hdc' hr hB
    rwa [add_comm (P₂ E₂) (P₁ E₁), hcancel] at h

end LevyProkhorov

/-- **Stopping at the exit from `U` versus `U \ K`.** For `U` open and `K` closed, the Lévy–Prokhorov distance
between the laws of the curve classes of two random continuous paths stopped at their exits from `U` is at most the
distance for the exits from `U \ K` plus the probabilities that the paths hit `K` before they leave `U`. -/
theorem levyProkhorovEDist_stoppedExitCurve_le_diff {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) {W₁ : Ω₁ → ContinuousPath ℂ} {W₂ : Ω₂ → ContinuousPath ℂ}
    (hW₁ : AEMeasurable W₁ P₁) (hW₂ : AEMeasurable W₂ P₂) {U K : Set ℂ} (hU : IsOpen U) (hK : IsClosed K) :
    levyProkhorovEDist (P₁.map fun ω => stoppedExitCurve U (W₁ ω))
        (P₂.map fun ω => stoppedExitCurve U (W₂ ω)) ≤
      levyProkhorovEDist (P₁.map fun ω => stoppedExitCurve (U \ K) (W₁ ω))
          (P₂.map fun ω => stoppedExitCurve (U \ K) (W₂ ω)) +
        P₁ {ω | HitsBeforeExit U K ⇑(W₁ ω)} + P₂ {ω | HitsBeforeExit U K ⇑(W₂ ω)} := by
  have hV : IsOpen (U \ K) := hU.sdiff hK
  exact levyProkhorovEDist_map_le_add_of_eq_off P₁ P₂
    ((measurable_stoppedExitCurve U hU).comp_aemeasurable hW₁)
    ((measurable_stoppedExitCurve _ hV).comp_aemeasurable hW₁)
    ((measurable_stoppedExitCurve U hU).comp_aemeasurable hW₂)
    ((measurable_stoppedExitCurve _ hV).comp_aemeasurable hW₂) _ _
    (fun _ hω => stoppedExitCurve_eq_of_not_hitsBeforeExit hU hK hω)
    (fun _ hω => stoppedExitCurve_eq_of_not_hitsBeforeExit hU hK hω)

/-- The exit point of a stopped curve class, read in `ℂ`. -/
noncomputable def curveExitPoint (q : BouRabeeGwynne.CurveSpace 2) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm (BouRabeeGwynne.CurveSpace.endPoint q)

theorem continuous_curveExitPoint : Continuous curveExitPoint :=
  Complex.orthonormalBasisOneI.repr.symm.continuous.comp BouRabeeGwynne.CurveSpace.continuous_endPoint

theorem edist_curveExitPoint_le (q q' : BouRabeeGwynne.CurveSpace 2) :
    edist (curveExitPoint q) (curveExitPoint q') ≤ edist q q' := by
  rw [curveExitPoint, curveExitPoint, Complex.orthonormalBasisOneI.repr.symm.isometry.edist_eq]
  simpa using BouRabeeGwynne.CurveSpace.endPoint_lipschitz.edist_le_mul q q'

theorem curveExitPoint_stoppedExitCurve (V : Set ℂ) (b : ContinuousPath ℂ) :
    curveExitPoint (stoppedExitCurve V b) = b (pathExitTime V b).toNNReal := by
  rw [curveExitPoint, ExitReparamSetup.endPoint_stoppedExitCurve, LinearIsometryEquiv.symm_apply_apply]

/-- **Hitting the hole, from a Lévy–Prokhorov bound.** If the laws of the curve classes of two random continuous
paths stopped at their exits from `U \ K` are at Lévy–Prokhorov distance less than `c`, then the probability that the
first path hits the closed set `K` before it leaves `U` is at most `c` plus the probability that the second path leaves
`U \ K` at a point of the `c`-thickening of `K`. -/
theorem measure_hitsBeforeExit_le_of_levyProkhorovEDist_lt {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) {W₁ : Ω₁ → ContinuousPath ℂ}
    {W₂ : Ω₂ → ContinuousPath ℂ} (hW₁ : AEMeasurable W₁ P₁) (hW₂ : AEMeasurable W₂ P₂) {U K : Set ℂ}
    (hU : IsOpen U) (hK : IsClosed K) {c : ℝ≥0∞}
    (hc : levyProkhorovEDist (P₁.map fun ω => stoppedExitCurve (U \ K) (W₁ ω))
      (P₂.map fun ω => stoppedExitCurve (U \ K) (W₂ ω)) < c) :
    P₁ {ω | HitsBeforeExit U K ⇑(W₁ ω)} ≤
      P₂ {ω | W₂ ω (pathExitTime (U \ K) ⇑(W₂ ω)).toNNReal ∈ thickening c.toReal K} + c := by
  have hV : IsOpen (U \ K) := hU.sdiff hK
  have hA : MeasurableSet (curveExitPoint ⁻¹' K) := (hK.preimage continuous_curveExitPoint).measurableSet
  have hT : MeasurableSet (thickening c.toReal (curveExitPoint ⁻¹' K)) := isOpen_thickening.measurableSet
  have hF₁ : AEMeasurable (fun ω => stoppedExitCurve (U \ K) (W₁ ω)) P₁ :=
    (measurable_stoppedExitCurve _ hV).comp_aemeasurable hW₁
  have hF₂ : AEMeasurable (fun ω => stoppedExitCurve (U \ K) (W₂ ω)) P₂ :=
    (measurable_stoppedExitCurve _ hV).comp_aemeasurable hW₂
  have hlp := left_measure_le_of_levyProkhorovEDist_lt hc hA
  rw [Measure.map_apply_of_aemeasurable hF₁ hA, Measure.map_apply_of_aemeasurable hF₂ hT] at hlp
  have h1 : {ω | HitsBeforeExit U K ⇑(W₁ ω)} ⊆
      (fun ω => stoppedExitCurve (U \ K) (W₁ ω)) ⁻¹' (curveExitPoint ⁻¹' K) := by
    intro ω hω
    change curveExitPoint (stoppedExitCurve (U \ K) (W₁ ω)) ∈ K
    rw [curveExitPoint_stoppedExitCurve]
    exact hω.2
  have h2 : (fun ω => stoppedExitCurve (U \ K) (W₂ ω)) ⁻¹' thickening c.toReal (curveExitPoint ⁻¹' K) ⊆
      {ω | W₂ ω (pathExitTime (U \ K) ⇑(W₂ ω)).toNNReal ∈ thickening c.toReal K} := by
    intro ω hω
    obtain ⟨q, hqK, hq⟩ := (mem_thickening_iff_exists_edist_lt _ _).1 hω
    change W₂ ω (pathExitTime (U \ K) ⇑(W₂ ω)).toNNReal ∈ thickening c.toReal K
    rw [← curveExitPoint_stoppedExitCurve]
    exact (mem_thickening_iff_exists_edist_lt _ _).2
      ⟨curveExitPoint q, hqK, (edist_curveExitPoint_le _ _).trans_lt hq⟩
  exact (measure_mono h1).trans (hlp.trans (add_le_add (measure_mono h2) le_rfl))

end MatedCRT
