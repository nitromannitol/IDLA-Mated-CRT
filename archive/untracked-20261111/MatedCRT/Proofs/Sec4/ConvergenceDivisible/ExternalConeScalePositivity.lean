import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeRadialOriginLimit
import MatedCRT.External.QuantumCone

/-! # Cone scale positivity from the quantum-cone field scaling law -/

namespace MatedCRT

open Filter Set MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Topology
open scoped ENNReal NNReal

/-- Each fixed inner radial circle average has an atomless distribution. -/
theorem IsQuantumCone.ae_circle_ne_at_exp_neg_one
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) (a : ℝ) :
    ∀ᵐ ω ∂P, hcirc ω (Real.exp (-1)) 0 ≠ a := by
  let E : Set (ℝ≥0 → ℝ) := {f | f 1 ≠ a - γ}
  have hE : MeasurableSet E := by
    change MeasurableSet ((fun f : ℝ≥0 → ℝ => f 1) ⁻¹' ({a - γ}ᶜ))
    exact (measurable_pi_apply (1 : ℝ≥0)) (measurableSet_singleton _).compl
  have hb : ∀ᵐ w ∂brownianMotion 0, (fun t : ℝ≥0 => w t) ∈ E := by
    have hlaw := brownianMotion_map_eval (1 : ℝ≥0) 0
    let : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    have heval : Measurable (fun w : ContinuousPath ℝ => w 1) :=
      ContinuousPath.measurable_coordinateProcess 1
    have hz : brownianMotion 0 {w | w 1 = a - γ} = 0 := by
      change brownianMotion 0 ((fun w : ContinuousPath ℝ => w 1) ⁻¹' {a - γ}) = 0
      rw [← Measure.map_apply heval (measurableSet_singleton _), hlaw]
      exact measure_singleton _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with w hw
    exact hw
  filter_upwards [hcone.ae_radial_centered_of_brownian hE hb] with ω hω
  change hcirc ω (Real.exp (-(1 : ℝ))) 0 - γ * (1 : ℝ≥0) ≠ a - γ at hω
  simpa using hω

/-- The inward radial circle average tends to infinity. -/
theorem IsQuantumCone.ae_circle_tendsto_atTop
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) (hγ : 0 < γ) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => hcirc ω (Real.exp (-t)) 0) atTop atTop := by
  filter_upwards [hcone.ae_radial_sublinear] with ω hsub
  have hneg : Tendsto (fun t : ℝ => -(hcirc ω (Real.exp (-t)) 0 - γ * t) / t)
      atTop (𝓝 0) := by
    simpa only [neg_div, neg_zero] using hsub.neg
  have h := (tendsto_neg_atBot_atTop.comp (tendsto_atBot_of_sublinear_drift hγ hneg))
  convert h using 1
  ext t
  simp only [Function.comp_apply]
  ring

/-- The field scaling law implies almost sure positivity of cone radii. -/
theorem IsQuantumCone.ae_coneScaleRadius_pos_of_field_scaling
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hscale : QuantumConeScalingInput) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b := by
  classical
  let U : Ω → (Ioi (0 : ℝ) × ℂ → ℝ) := fun ω => circleProcess (hcirc ω)
  let T : Ω → (Ioi (0 : ℝ) × ℂ → ℝ) := fun ω =>
    circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)
  have hU : Measurable U := by
    apply measurable_pi_iff.mpr
    intro p
    exact hcone.measurable_circle p.1 p.2 p.1.2
  have hlaw : P.map T = P.map U := hscale γ hγ hγ2 Ω P hC hcirc inferInstance hcone b hb
  let p : Ioi (0 : ℝ) × ℂ := (⟨Real.exp (-1), Real.exp_pos _⟩, 0)
  have hzero (a : ℝ) : P.map U {f | f p = a} = 0 := by
    have hset : MeasurableSet {f : Ioi (0 : ℝ) × ℂ → ℝ | f p = a} := by
      change MeasurableSet ((fun f : Ioi (0 : ℝ) × ℂ → ℝ => f p) ⁻¹' {a})
      exact (measurable_pi_apply p) (measurableSet_singleton a)
    rw [Measure.map_apply hU hset]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcone.ae_circle_ne_at_exp_neg_one a] with ω hω
    exact hω
  have hT : AEMeasurable T P := by
    by_contra hn
    have hP : P ≠ 0 := by
      intro h
      have hu := congrArg (fun μ : Measure Ω => μ univ) h
      simp at hu
    have hdirac := Measure.map_of_not_aemeasurable_of_ne_zero hn hP
    let q : Ioi (0 : ℝ) × ℂ → ℝ := Classical.ofNonempty
    have heq : Measure.dirac q = P.map U := by simpa [q] using hdirac.symm.trans hlaw
    have he := congrArg (fun μ : Measure (Ioi (0 : ℝ) × ℂ → ℝ) => μ {f | f p = q p}) heq
    have hz := hzero (q p)
    simp [hz] at he
  let idx (n : ℕ) : Ioi (0 : ℝ) × ℂ := (⟨Real.exp (-(n : ℝ)), Real.exp_pos _⟩, 0)
  let E : Set (Ioi (0 : ℝ) × ℂ → ℝ) := {f | ∃ n : ℕ, f (idx n) ≠ f (idx 0)}
  have hE : MeasurableSet E := by
    have h := MeasurableSet.iUnion fun n : ℕ =>
      ((measurable_pi_apply (idx n)).measurableSet_eq (measurable_pi_apply (idx 0))).compl
    simpa [E] using h
  have hUE : ∀ᵐ ω ∂P, U ω ∈ E := by
    filter_upwards [hcone.ae_circle_tendsto_atTop hγ] with ω hω
    have hseq := hω.comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn⟩ := (hseq.eventually_gt_atTop (hcirc ω 1 0)).exists
    refine ⟨n, ?_⟩
    simpa [U, E, idx, circleProcess] using ne_of_gt hn
  have hTE : ∀ᵐ ω ∂P, T ω ∈ E := by
    apply (ae_map_iff hT hE).1
    rw [hlaw]
    exact (ae_map_iff hU.aemeasurable hE).2 hUE
  filter_upwards [hTE] with ω hω
  have hnonneg : 0 ≤ coneScaleRadius γ (hcirc ω) b := by
    apply Real.sSup_nonneg
    intro r hr
    exact hr.1.le
  have hne : coneScaleRadius γ (hcirc ω) b ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := hω
    apply hn
    simp [T, idx, circleProcess, rescaledCircle, hz]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end MatedCRT
