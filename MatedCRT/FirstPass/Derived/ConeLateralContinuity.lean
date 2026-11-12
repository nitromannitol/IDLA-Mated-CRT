import MatedCRT.FirstPass.Derived.ConeLateralDilation

/-!
# Continuity of the lateral circle averages on the nonsingular circles

For a circle average process `(r, z) ↦ h_r(z)` which is continuous on `(0, ∞) × ℂ`, the lateral circle average
`h_r(z) - (average over ∂B_r(z) of x ↦ h_{|x|}(0))` is a continuous function of `(r, z)` on the set of circles
which do not pass through the origin (`r ≠ |z|`): on a neighbourhood of such a circle the radial function may be
replaced by `x ↦ h_{max(|x|, ε)}(0)`, which is continuous on the whole plane, and the circle average of a continuous
function is jointly continuous in the centre and the radius.

## Main results
* `continuous_circleAverage_uncurry`: joint continuity of `(r, z) ↦ circleAverage f z r` for continuous `f`.
* `continuous_projCircle_lateralProcess`: the pathwise statement.
* `ae_continuous_lateralCircle_gff`, `ae_continuous_lateralCircle_cone`: almost surely, the lateral circle average
  process is continuous on the nonsingular circles.
-/

open MeasureTheory Filter Topology Set HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- Joint continuity in the centre and the radius of the circle average of a continuous function. -/
lemma continuous_circleAverage_uncurry {f : ℂ → ℝ} (hf : Continuous f) :
    Continuous fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1 := by
  have hg : Continuous (Function.uncurry fun (p : ℝ × ℂ) (θ : ℝ) => f (circleMap p.2 p.1 θ)) := by
    refine hf.comp ?_
    simp only [circleMap]
    fun_prop
  unfold Real.circleAverage
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := (volume : Measure ℝ)) hg 0 (2 * Real.pi)).const_smul ((2 * Real.pi)⁻¹ : ℝ)

/-- Pathwise continuity of the lateral circle averages on the nonsingular circles. -/
theorem continuous_projCircle_lateralProcess {hC : (ℂ → ℝ) → ℝ} {hcirc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Continuous (projCircle (lateralProcess hC hcirc)) := by
  have hrad : ContinuousOn (fun s => hcirc s 0) (Ioi 0) :=
    hcont.comp (f := fun s : ℝ => (s, (0 : ℂ))) (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  have key : projCircle (lateralProcess hC hcirc) = fun p : NonsingularCircle =>
      hcirc (p.1.1 : ℝ) p.1.2 - Real.circleAverage (fun x => hcirc ‖x‖ 0) p.1.2 (p.1.1 : ℝ) := rfl
  have hmap : Continuous fun p : NonsingularCircle => ((p.1.1 : ℝ), p.1.2) := by fun_prop
  rw [key, continuous_iff_continuousAt]
  intro p0
  have h1 : ContinuousAt (fun p : NonsingularCircle => hcirc (p.1.1 : ℝ) p.1.2) p0 := by
    have hq : ContinuousAt (fun q : ℝ × ℂ => hcirc q.1 q.2) ((p0.1.1 : ℝ), p0.1.2) :=
      hcont.continuousAt (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) ⟨p0.1.1.2, mem_univ _⟩)
    exact ContinuousAt.comp (g := fun q : ℝ × ℂ => hcirc q.1 q.2)
      (f := fun p : NonsingularCircle => ((p.1.1 : ℝ), p.1.2)) hq hmap.continuousAt
  have hd : 0 < |‖p0.1.2‖ - (p0.1.1 : ℝ)| := abs_pos.2 (sub_ne_zero.2 (Ne.symm p0.2))
  set ε : ℝ := |‖p0.1.2‖ - (p0.1.1 : ℝ)| / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hF : Continuous fun x : ℂ => hcirc (max ‖x‖ ε) 0 :=
    hrad.comp_continuous (by fun_prop) (fun x => lt_max_of_lt_right hε)
  have hG := (continuous_circleAverage_uncurry hF).comp hmap
  have hopen : IsOpen {p : NonsingularCircle | ε < |‖p.1.2‖ - (p.1.1 : ℝ)|} :=
    isOpen_lt continuous_const (by fun_prop)
  have hmem : p0 ∈ {p : NonsingularCircle | ε < |‖p.1.2‖ - (p.1.1 : ℝ)|} := by
    show ε < |‖p0.1.2‖ - (p0.1.1 : ℝ)|
    rw [hεdef]; linarith
  have hev : (fun p : NonsingularCircle => Real.circleAverage (fun x : ℂ => hcirc (max ‖x‖ ε) 0)
        p.1.2 (p.1.1 : ℝ)) =ᶠ[𝓝 p0]
      fun p : NonsingularCircle => Real.circleAverage (fun x => hcirc ‖x‖ 0) p.1.2 (p.1.1 : ℝ) := by
    filter_upwards [hopen.mem_nhds hmem] with p hp
    apply Real.circleAverage_congr_sphere
    intro x hx
    rw [abs_of_pos p.1.1.2, mem_sphere_iff_norm] at hx
    have h3 : |‖p.1.2‖ - (p.1.1 : ℝ)| ≤ ‖x‖ := by
      refine abs_le.2 ⟨?_, ?_⟩
      · have := norm_sub_le x p.1.2
        linarith
      · have := norm_le_norm_add_norm_sub' p.1.2 x
        rw [norm_sub_rev] at this
        linarith
    have h4 : ε < ‖x‖ := lt_of_lt_of_le hp h3
    simp only [max_eq_left h4.le]
  have h2 : ContinuousAt (fun p : NonsingularCircle =>
      Real.circleAverage (fun x => hcirc ‖x‖ 0) p.1.2 (p.1.1 : ℝ)) p0 :=
    hG.continuousAt.congr hev
  exact h1.sub h2

/-- Almost surely the lateral circle averages of a whole-plane GFF are continuous on the nonsingular circles. -/
theorem ae_continuous_lateralCircle_gff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, Continuous (projCircle (lateralProcess (hC ω) (hcirc ω))) := by
  filter_upwards [hG.ae_continuousOn_circle] with ω hω
  exact continuous_projCircle_lateralProcess hω

/-- Almost surely the lateral circle averages of a quantum cone are continuous on the nonsingular circles. -/
theorem ae_continuous_lateralCircle_cone {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Continuous (projCircle (lateralProcess (hC ω) (hcirc ω))) := by
  filter_upwards [h.ae_continuousOn_circle] with ω hω
  exact continuous_projCircle_lateralProcess hω

end MatedCRT.FirstPass.Derived
