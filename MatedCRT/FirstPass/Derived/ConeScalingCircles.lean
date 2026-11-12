import MatedCRT.FirstPass.Derived.ConeScalingAssembly
import MatedCRT.FirstPass.Derived.RadialReadoutTwoSided

/-!
# Circle averages of the rescaled quantum cone at finitely many circles

For a `γ`-quantum cone with a.s. continuous circle averages, the circle average of the rescaled field
`h(R_b ·) + Q log R_b - γ⁻¹ log b` at a circle `q = (r, z)` avoiding the origin is the lateral circle average of `h`
at the dilated circle `R_b q` plus the radial read-out of the radial process of the rescaled field
(`eval_eq_lateralProcess_add_radOf2`).  The circle average of `h` at `q` is the lateral circle average at `q` plus the
same radial read-out of the radial process of `h`.  Both vectors of circle averages are therefore the same
measurable function `circleVecOf` of a pair (radial pair, lateral vector), and the two pairs have the same law
when the radial pair of the rescaled field has the law of the radial pair of `h`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

open MatedCRT.ConeMeanZeroRestriction

/-- The restriction of a radial pair to rational times. -/
def ratPair (p : RadialPair) : (ℚ≥0 → ℝ) × (ℚ≥0 → ℝ) :=
  (fun q => p.1 (q : ℝ≥0), fun q => p.2 (q : ℝ≥0))

lemma radRat2_eq_ratPair (hcirc : ℝ → ℂ → ℝ) : radRat2 hcirc = ratPair (radialProcess hcirc) := rfl

lemma measurable_ratPair : Measurable ratPair :=
  Measurable.prodMk (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_fst)
    (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_snd)

/-- The circle observable of a nonsingular circle. -/
def circleAt (q : NonsingularCircle) : GFFObservable := GFFObservable.circle (q.1.1 : ℝ) q.1.2

lemma admissible_circleAt (q : NonsingularCircle) : (circleAt q).IsAdmissible := q.1.1.2

/-- The vector of circle averages at the circles `q_j`, as a function of the radial pair and the vector of lateral
circle averages. -/
noncomputable def circleVecOf {k : ℕ} (q : Fin k → NonsingularCircle) (p : RadialPair × (Fin k → ℝ)) :
    Fin k → ℝ :=
  fun j => p.2 j + radOf2 (ratPair p.1) (circleAt (q j))

lemma measurable_circleVecOf {k : ℕ} (q : Fin k → NonsingularCircle) : Measurable (circleVecOf q) := by
  refine Measurable.of_eval fun j => ?_
  have h1 : Measurable fun p : RadialPair × (Fin k → ℝ) => p.2 j :=
    (measurable_pi_apply j).comp measurable_snd
  have h2 : Measurable fun p : RadialPair × (Fin k → ℝ) => radOf2 (ratPair p.1) (circleAt (q j)) :=
    (measurable_radOf2 (admissible_circleAt (q j))).comp (measurable_ratPair.comp measurable_fst)
  exact h1.add h2

/-- The lateral circle average of the rescaled field at a nonsingular circle is the lateral circle average of the
field at the dilated circle. -/
lemma lateralProcess_rescaled_circle {hC hC' : (ℂ → ℝ) → ℝ} {hcirc : ℝ → ℂ → ℝ} {γ b : ℝ}
    (hcont : ContinuousOn (fun s => hcirc s 0) (Ioi 0)) {R : ℝ} (hR : 0 < R) (p : NonsingularCircle) :
    projCircle (lateralProcess hC' (rescaledCircle γ hcirc R b)) p =
      projCircle (lateralProcess hC hcirc) (dilateCircle hR p) := by
  obtain ⟨⟨⟨r, hr⟩, z⟩, hrz⟩ := p
  simp only [projCircle, dilateCircle, lateralProcess, lateralEval, rescaledCircle]
  have hcirc_int : ContinuousOn (fun x : ℂ => hcirc (R * ‖x‖) 0) (Metric.sphere z |r|) := by
    have hne : ∀ x ∈ Metric.sphere z |r|, 0 < ‖x‖ := by
      intro x hx
      rw [mem_sphere_iff_norm, abs_of_pos (show (0 : ℝ) < r from hr)] at hx
      by_contra hle
      have hx0 : x = 0 := norm_le_zero_iff.1 (not_lt.1 hle)
      rw [hx0, zero_sub, norm_neg] at hx
      exact hrz hx.symm
    exact hcont.comp (f := fun x : ℂ => R * ‖x‖) (by fun_prop : Continuous fun x : ℂ => R * ‖x‖).continuousOn
      (fun x hx => mul_pos hR (hne x hx))
  have hint : CircleIntegrable (fun x : ℂ => hcirc (R * ‖x‖) 0) z r :=
    ContinuousOn.circleIntegrable' (by simpa using hcirc_int)
  have hfun : (fun x : ℂ => hcirc (R * ‖x‖) (R * 0) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b) =
      fun x : ℂ => hcirc (R * ‖x‖) 0 + (lqgQ γ * Real.log R - γ⁻¹ * Real.log b) := by
    funext x
    simp only [mul_zero]
    ring
  have hadd : Real.circleAverage (fun x : ℂ => hcirc (R * ‖x‖) 0 + (lqgQ γ * Real.log R - γ⁻¹ * Real.log b)) z r =
      Real.circleAverage (fun x : ℂ => hcirc (R * ‖x‖) 0) z r + (lqgQ γ * Real.log R - γ⁻¹ * Real.log b) := by
    rw [Real.circleAverage_fun_add hint (circleIntegrable_const _ _ _), Real.circleAverage_const]
  have hscale : Real.circleAverage (fun y : ℂ => hcirc ‖y‖ 0) ((R : ℂ) * z) (R * r) =
      Real.circleAverage (fun x : ℂ => hcirc (R * ‖x‖) 0) z r := by
    rw [circleAverage_dilate]
    congr 1
    funext x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  rw [hfun, hadd, hscale]
  ring


/-- Almost surely, the circle averages of the field at finitely many nonsingular circles are `circleVecOf` of the
radial pair and the lateral circle averages at the same circles. -/
lemma circleVec_ae {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) {k : ℕ}
    (q : Fin k → NonsingularCircle) :
    ∀ᵐ ω ∂P, (fun j => hcirc ω (q j).1.1 (q j).1.2) =
      circleVecOf q (radialProcess (hcirc ω), fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)) := by
  filter_upwards [h.ae_continuousOn_circle] with ω hc
  funext j
  have := eval_eq_lateralProcess_add_radOf2 (hC ω) hc ⟨circleAt (q j), admissible_circleAt (q j)⟩
  exact this

/-- Almost surely, the circle averages of the rescaled field at finitely many nonsingular circles are `circleVecOf`
of the radial pair of the rescaled field and the lateral circle averages of the field at the dilated circles. -/
lemma circleVec_rescaled_ae {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) {k : ℕ}
    (q : Fin k → NonsingularCircle) :
    ∀ᵐ ω ∂P, (fun j => rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b (q j).1.1 (q j).1.2) =
      circleVecOf q (radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω)))) := by
  filter_upwards [h.ae_continuousOn_circle, ae_coneScaleRadius_spec hγ0 hγ2 h b] with ω hc hspec
  obtain ⟨hR, -, -⟩ := hspec
  set R := coneScaleRadius γ (hcirc ω) b with hRdef
  have hmap : MapsTo (fun p : ℝ × ℂ => (R * p.1, (R : ℂ) * p.2)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
    fun p hp => ⟨mul_pos hR hp.1, mem_univ _⟩
  have hcomp : ContinuousOn (fun p : ℝ × ℂ => hcirc ω (R * p.1) ((R : ℂ) * p.2)) (Ioi 0 ×ˢ univ) :=
    hc.comp (f := fun p : ℝ × ℂ => (R * p.1, (R : ℂ) * p.2)) (by fun_prop : Continuous _).continuousOn hmap
  have hc' : ContinuousOn (fun p : ℝ × ℂ => rescaledCircle γ (hcirc ω) R b p.1 p.2) (Ioi 0 ×ˢ univ) := by
    unfold rescaledCircle
    exact (hcomp.add continuousOn_const).sub continuousOn_const
  have hcont0 : ContinuousOn (fun s => hcirc ω s 0) (Ioi 0) :=
    hc.comp (f := fun s : ℝ => (s, (0 : ℂ))) (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  funext j
  have := eval_eq_lateralProcess_add_radOf2 (hC ω) hc' ⟨circleAt (q j), admissible_circleAt (q j)⟩
  have hlat := lateralProcess_rescaled_circle (hC := hC ω) (hC' := hC ω) (γ := γ) (b := b) hcont0 hR (q j)
  have hdil : dilVec q R (projCircle (lateralProcess (hC ω) (hcirc ω))) j =
      projCircle (lateralProcess (hC ω) (hcirc ω)) (dilateCircle hR (q j)) := by
    simp only [dilVec, dilateTot_of_pos hR]
  simp only [circleVecOf, hdil, ← hlat]
  exact this

/-- **Circle averages of the rescaled cone at finitely many circles: law, given the radial invariance.**  If the radial
pair of the rescaled cone `h(R_b ·) + Q log R_b - γ⁻¹ log b` has the law of the radial pair of `h`, then the circle
averages of the rescaled cone at finitely many circles avoiding the origin have the law of the circle averages of
`h` at these circles. -/
theorem map_circleVec_rescaled_eq {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) {k : ℕ}
    (q : Fin k → NonsingularCircle)
    (hrad : P.map (fun ω => radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
      P.map (fun ω => radialProcess (hcirc ω))) :
    P.map (fun ω => fun j => rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b
        (q j).1.1 (q j).1.2) =
      P.map (fun ω => fun j => hcirc ω (q j).1.1 (q j).1.2) := by
  have hXm : Measurable fun ω => radialProcess (hcirc ω) :=
    Measurable.prodMk
      (Measurable.of_eval fun t => h.measurable_circle _ _ (Real.exp_pos _))
      (Measurable.of_eval fun s => h.measurable_circle _ _ (Real.exp_pos _))
  have hLae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.ConeMeanZeroRestriction.lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance h
  have hvec : Measurable (fun l : NonsingularCircle → ℝ => fun j => l (q j)) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hYae : AEMeasurable (fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)) P :=
    (hvec.comp measurable_projCircle).comp_aemeasurable hLae
  have hind : IndepFun (fun ω => radialProcess (hcirc ω))
      (fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)) P :=
    h.indep.comp measurable_id (hvec.comp measurable_projCircle)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYae).1 hind
  have hres := radialProcess_rescaled_ae hγ0 hγ2 h b
  have hae' : AEMeasurable (fun ω => (radialProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b),
      dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω))))) P := by
    have h1 : AEMeasurable (fun ω => (radialRescale γ b (radialProcess (hcirc ω)),
        dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω))))) P :=
      ((measurable_radialRescale γ b).comp hXm).aemeasurable.prodMk (aemeasurable_dilVec_cone hγ0 hγ2 h b q)
    refine h1.congr ?_
    filter_upwards [hres] with ω hω
    rw [hω]
  have hae : AEMeasurable (fun ω => (radialProcess (hcirc ω),
      fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j))) P := hXm.aemeasurable.prodMk hYae
  have hmeas := measurable_circleVecOf q
  calc P.map (fun ω => fun j => rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b
          (q j).1.1 (q j).1.2)
      = P.map (fun ω => circleVecOf q (radialProcess (rescaledCircle γ (hcirc ω)
          (coneScaleRadius γ (hcirc ω) b) b),
          dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω))))) :=
        Measure.map_congr (circleVec_rescaled_ae hγ0 hγ2 h b q)
    _ = (P.map (fun ω => (radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
          dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω)))))).map
          (circleVecOf q) := (AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hae').symm
    _ = ((P.map fun ω => radialProcess (hcirc ω)).prod
          (P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j))).map
          (circleVecOf q) := by rw [map_radialRescale_dilatedLateral_vec hγ0 hγ2 h b q hrad]
    _ = (P.map (fun ω => (radialProcess (hcirc ω),
          fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)))).map (circleVecOf q) := by rw [hprod]
    _ = P.map (fun ω => circleVecOf q (radialProcess (hcirc ω),
          fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j))) :=
        AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hae
    _ = P.map (fun ω => fun j => hcirc ω (q j).1.1 (q j).1.2) :=
        (Measure.map_congr (circleVec_ae h q)).symm

end MatedCRT.FirstPass.Derived
