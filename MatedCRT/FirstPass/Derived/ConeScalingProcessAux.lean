import MatedCRT.FirstPass.Derived.ConeScalingCircles

/-!
# Ingredients for the law of the circle average process of the rescaled quantum cone

* `nonsingularSet`: the circles `(r, z)` with `r ≠ |z|` form a dense subset of the index space `(0, ∞) × ℂ` of the
  circle average process.
* `continuous_circleProcess_of_continuousOn`: a circle average family which is continuous on `(0, ∞) × ℂ` gives a
  continuous process on the index space; the same holds for the rescaled family (`continuousOn_rescaledCircle`).
* `aemeasurable_rescaled_coord`: the coordinates of the circle average process of the rescaled cone at nonsingular
  circles are almost measurable (they are almost surely a measurable function of the rescaled radial pair and the
  dilated lateral circle averages).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- The circles of the index space `(0, ∞) × ℂ` which do not pass through the origin. -/
def nonsingularSet : Set (Set.Ioi (0 : ℝ) × ℂ) := {p | (p.1 : ℝ) ≠ ‖p.2‖}

lemma dense_nonsingularSet : Dense nonsingularSet := by
  intro p
  by_cases hp : (p.1 : ℝ) ≠ ‖p.2‖
  · exact subset_closure hp
  · have hp' : (p.1 : ℝ) = ‖p.2‖ := not_not.1 hp
    have hr : (0 : ℝ) < ‖p.2‖ := hp' ▸ p.1.2
    let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
    have hc : Tendsto c atTop (𝓝 1) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa [c] using (tendsto_const_nhds (x := (1 : ℝ))).add this
    have hlim : Tendsto (fun n : ℕ => (p.1, ((c n : ℝ) : ℂ) * p.2)) atTop (𝓝 p) := by
      have h2 : Tendsto (fun n : ℕ => ((c n : ℝ) : ℂ) * p.2) atTop (𝓝 p.2) := by
        have := ((Complex.continuous_ofReal.tendsto 1).comp hc).mul_const p.2
        simpa using this
      exact (tendsto_const_nhds (x := p.1)).prodMk_nhds h2
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    show (p.1 : ℝ) ≠ ‖((c n : ℝ) : ℂ) * p.2‖
    have hcn : 1 < c n := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [c]
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hp']
    intro h
    nlinarith

lemma continuous_circleProcess_of_continuousOn {f : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Ioi 0 ×ˢ univ)) : Continuous (circleProcess f) := by
  have h1 : Continuous (fun p : Set.Ioi (0 : ℝ) × ℂ => ((p.1 : ℝ), p.2)) := by fun_prop
  exact hc.comp_continuous h1 (fun p => ⟨p.1.2, mem_univ _⟩)

lemma continuousOn_rescaledCircle {γ b R : ℝ} (hR : 0 < R) {hc : ℝ → ℂ → ℝ}
    (h : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × ℂ => rescaledCircle γ hc R b p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hmap : MapsTo (fun p : ℝ × ℂ => (R * p.1, (R : ℂ) * p.2)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
    fun p hp => ⟨mul_pos hR hp.1, mem_univ _⟩
  have hcomp : ContinuousOn (fun p : ℝ × ℂ => hc (R * p.1) ((R : ℂ) * p.2)) (Ioi 0 ×ˢ univ) :=
    h.comp (f := fun p : ℝ × ℂ => (R * p.1, (R : ℂ) * p.2)) (by fun_prop : Continuous _).continuousOn hmap
  unfold rescaledCircle
  exact (hcomp.add continuousOn_const).sub continuousOn_const

/-- The coordinates of the circle average process of the rescaled cone at nonsingular circles are almost
measurable. -/
lemma aemeasurable_rescaled_coord {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) (q : NonsingularCircle) :
    AEMeasurable (fun ω => circleProcess
      (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) q.1) P := by
  have hXm : Measurable fun ω => radialProcess (hcirc ω) :=
    Measurable.prodMk
      (Measurable.of_eval fun t => h.measurable_circle _ _ (Real.exp_pos _))
      (Measurable.of_eval fun s => h.measurable_circle _ _ (Real.exp_pos _))
  have hres := radialProcess_rescaled_ae hγ0 hγ2 h b
  have hae' : AEMeasurable (fun ω => (radialProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b),
      dilVec (fun _ : Fin 1 => q) (coneScaleRadius γ (hcirc ω) b)
        (projCircle (lateralProcess (hC ω) (hcirc ω))))) P := by
    have h1 : AEMeasurable (fun ω => (radialRescale γ b (radialProcess (hcirc ω)),
        dilVec (fun _ : Fin 1 => q) (coneScaleRadius γ (hcirc ω) b)
          (projCircle (lateralProcess (hC ω) (hcirc ω))))) P :=
      ((measurable_radialRescale γ b).comp hXm).aemeasurable.prodMk
        (aemeasurable_dilVec_cone hγ0 hγ2 h b (fun _ : Fin 1 => q))
    refine h1.congr ?_
    filter_upwards [hres] with ω hω
    rw [hω]
  have h1 := (measurable_circleVecOf (fun _ : Fin 1 => q)).comp_aemeasurable hae'
  have h2 := (measurable_pi_apply (0 : Fin 1)).comp_aemeasurable h1
  refine h2.congr ?_
  filter_upwards [circleVec_rescaled_ae hγ0 hγ2 h b (fun _ : Fin 1 => q)] with ω hω
  exact (congrFun hω 0).symm

end MatedCRT.FirstPass.Derived
