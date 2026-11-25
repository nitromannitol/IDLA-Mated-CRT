import MatedCRT.Proofs.Sec2.ConeFamilyFunctional.LimitMeasure
import MatedCRT.Proofs.Measurability.ConePairing

/-!
# The canonical quantum cone on the values at rational points and the pairings

For a quantum cone field `(P, hC, hcirc, μ)` the map `ω ↦ (values of h_r(z) at the rational points, pairings with
test functions)` pushes `P` to a measure on `CanonSpace = DenseCircle × (TestFn → ℝ)`. With the circle averages
`extend y`, the pairings read off the second coordinate and the measure `limitMeasure γ y`, the push-forward is again a
quantum cone field (`isConeField_canon`):

* the circle averages are measurable, and almost surely continuous: the values at the rational points are almost
  surely locally uniformly continuous (`restrictDense_mem_locUnifCont`);
* almost surely the extended circle averages agree with `h` at positive radii (`extend_restrictDense`), and the radial
  and lateral processes only use positive radii up to null sets (`lateralProcess_congr`), so the radial law, the
  independence of the radial and lateral parts and the lateral law are those of `h`;
* almost surely the values are in `DomR`, so `limitMeasure γ y` is the vague limit of the approximating measures.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open _root_.HarmonicBalls
open scoped ENNReal

namespace ConeFamilyFunctional

/-- The test functions on `ℂ`. -/
abbrev TestFn : Type := {φ : ℂ → ℝ // IsTestFunction univ φ}

/-- The canonical space: values at the rational points and pairings with test functions. -/
abbrev CanonSpace : Type := DenseCircle × (TestFn → ℝ)

open Classical in
/-- The pairings of the canonical field (`0` at functions which are not test functions). -/
noncomputable def canonPairing (x : CanonSpace) (φ : ℂ → ℝ) : ℝ :=
  if h : IsTestFunction univ φ then x.2 ⟨φ, h⟩ else 0

/-- The circle averages of the canonical field. -/
noncomputable def canonCircle (x : CanonSpace) : ℝ → ℂ → ℝ := extend x.1

/-- The LQG measure of the canonical field. -/
noncomputable def canonMeasure (γ : ℝ) (x : CanonSpace) : Measure ℂ := limitMeasure γ x.1

/-- The canonical map of a sample. -/
noncomputable def canonMap {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) : CanonSpace :=
  (restrictDense (circleProcess (hcirc ω)), fun φ => hC ω φ.1)

theorem measurable_canonMap {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmp : ∀ φ, IsTestFunction univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) : Measurable (canonMap hC hcirc) := by
  refine Measurable.prodMk (measurable_restrictDense.comp ?_) (measurable_pi_iff.2 fun φ => hmp φ.1 φ.2)
  exact measurable_pi_iff.2 fun p => hmc p.1 p.2 p.1.2

/-- The lateral process only uses the pairings with test functions and the circle averages at positive radii. -/
theorem lateralProcess_congr {hC hC' : (ℂ → ℝ) → ℝ} {h h' : ℝ → ℂ → ℝ}
    (hpair : ∀ φ, IsTestFunction univ φ → hC φ = hC' φ) (hpos : ∀ r z, 0 < r → h r z = h' r z) :
    lateralProcess hC h = lateralProcess hC' h' := by
  funext ⟨o, ho⟩
  cases o with
  | pairing φ =>
    show hC φ - ∫ x, φ x * h ‖x‖ 0 = hC' φ - ∫ x, φ x * h' ‖x‖ 0
    rw [hpair φ ho]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with x hx
    have hx0 : x ≠ 0 := fun hx' => hx (by rw [hx']; rfl)
    rw [hpos _ _ (norm_pos_iff.2 hx0)]
  | circle r z =>
    show h r z - Real.circleAverage (fun x => h ‖x‖ 0) z r = h' r z - Real.circleAverage (fun x => h' ‖x‖ 0) z r
    have hr : 0 < r := ho
    rw [hpos r z hr, Real.circleAverage_congr_codiscreteWithin
      (CirclePairing.eventuallyEq_codiscreteWithin_of_ne _ 0 fun y hy => hpos _ _ (norm_pos_iff.2 hy)) hr.ne']

/-- The radial process only uses the circle averages at positive radii. -/
theorem radialProcess_congr {h h' : ℝ → ℂ → ℝ} (hpos : ∀ r z, 0 < r → h r z = h' r z) :
    radialProcess h = radialProcess h' := by
  simp only [radialProcess]
  congr 1 <;> funext t <;> exact hpos _ _ (Real.exp_pos _)

theorem measurable_canonCircle (r : ℝ) (z : ℂ) : Measurable fun x : CanonSpace => canonCircle x r z := by
  have h : Measurable fun x : CanonSpace => (x.1, (r, z)) := measurable_fst.prodMk measurable_const
  exact measurable_extend.comp h

theorem measurable_radial_canon : Measurable fun x : CanonSpace => radialProcess (canonCircle x) := by
  have hc : ∀ r : ℝ, Measurable fun x : CanonSpace => canonCircle x r 0 := fun r => measurable_canonCircle r 0
  exact (measurable_pi_iff.2 fun t => hc _).prodMk (measurable_pi_iff.2 fun s => hc _)

/-- **The canonical quantum cone field.** -/
theorem isConeField_canon {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hcone : IsConeField γ P hC hcirc μ) :
    IsConeField γ (P.map (canonMap hC hcirc)) canonPairing canonCircle (canonMeasure γ) := by
  obtain ⟨hP, hQ, hL⟩ := hcone
  have he := measurable_canonMap hQ.measurable_pairing hQ.measurable_circle
  set Q := P.map (canonMap hC hcirc) with hQdef
  have hQP : IsProbabilityMeasure Q := (Measure.isProbabilityMeasure_map_iff he.aemeasurable).2 hP
  -- the good samples
  have hgood : ∀ᵐ ω ∂P, ∀ r z, 0 < r → canonCircle (canonMap hC hcirc ω) r z = hcirc ω r z := by
    filter_upwards [hQ.ae_continuousOn_circle] with ω hω r z hr
    exact extend_restrictDense hω hr z
  have hpairs : ∀ ω, ∀ φ, IsTestFunction univ φ → canonPairing (canonMap hC hcirc ω) φ = hC ω φ := by
    intro ω φ hφ
    simp [canonPairing, canonMap, hφ]
  have hmp : ∀ φ, IsTestFunction univ φ → Measurable fun x : CanonSpace => canonPairing x φ := by
    intro φ hφ
    simp only [canonPairing, hφ, dite_true]
    exact (measurable_pi_apply _).comp measurable_snd
  have hmc : ∀ r z, 0 < r → Measurable fun x : CanonSpace => canonCircle x r z := fun r z _ =>
    measurable_canonCircle r z
  have hcont : ∀ᵐ x ∂Q, ContinuousOn (fun p : ℝ × ℂ => canonCircle x p.1 p.2) (Ioi 0 ×ˢ univ) := by
    have hmeas : MeasurableSet {x : CanonSpace | x.1 ∈ LocUnifCont} := measurable_fst measurableSet_locUnifCont
    have h := (ae_map_iff he.aemeasurable hmeas).2 (by
      filter_upwards [hQ.ae_continuousOn_circle] with ω hω
      exact restrictDense_mem_locUnifCont hω)
    filter_upwards [h] with x hx
    exact continuousOn_extend hx
  -- the radial and lateral maps
  have hrad : Q.map (fun x => radialProcess (canonCircle x)) = P.map fun ω => radialProcess (hcirc ω) := by
    rw [hQdef, Measure.map_map measurable_radial_canon he]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    exact radialProcess_congr hω
  have hlatm : AEMeasurable (fun x => lateralProcess (canonPairing x) (canonCircle x)) Q :=
    CirclePairing.aemeasurable_lateralProcess hmp hmc hcont
  have hlatP : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    CirclePairing.aemeasurable_lateralProcess hQ.measurable_pairing hQ.measurable_circle hQ.ae_continuousOn_circle
  have hlat : Q.map (fun x => lateralProcess (canonPairing x) (canonCircle x)) =
      P.map fun ω => lateralProcess (hC ω) (hcirc ω) := by
    rw [hQdef, AEMeasurable.map_map_of_aemeasurable hlatm he.aemeasurable]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    exact lateralProcess_congr (hpairs ω) hω
  have hjoint : Q.map (fun x => (radialProcess (canonCircle x), lateralProcess (canonPairing x) (canonCircle x))) =
      P.map fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) := by
    rw [hQdef, AEMeasurable.map_map_of_aemeasurable
      (measurable_radial_canon.aemeasurable.prodMk hlatm) he.aemeasurable]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    simp only [Function.comp_apply]
    rw [radialProcess_congr hω, lateralProcess_congr (hpairs ω) hω]
  refine ⟨hQP, ⟨hmp, hmc, hcont, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨ν, hν, hlaw⟩ := hQ.radial_law
    exact ⟨ν, hν, hrad.trans hlaw⟩
  · have hradP : Measurable fun ω => radialProcess (hcirc ω) :=
      (measurable_pi_iff.2 fun t => hQ.measurable_circle _ _ (Real.exp_pos _)).prodMk
        (measurable_pi_iff.2 fun s => hQ.measurable_circle _ _ (Real.exp_pos _))
    rw [indepFun_iff_map_prod_eq_prod_map_map measurable_radial_canon.aemeasurable hlatm, hjoint, hrad, hlat]
    exact (indepFun_iff_map_prod_eq_prod_map_map hradP.aemeasurable hlatP).1 hQ.indep
  · obtain ⟨Ω', mΩ', P', hC', hcirc', hP', hG, hlaw⟩ := hQ.lateral_law
    exact ⟨Ω', mΩ', P', hC', hcirc', hP', hG, hlat.trans hlaw⟩
  · have hmeas : MeasurableSet {x : CanonSpace | x.1 ∈ DomR γ} := measurable_fst (measurableSet_domR γ)
    have h := (ae_map_iff he.aemeasurable hmeas).2 (by
      filter_upwards [hQ.ae_continuousOn_circle, hL] with ω hω hlim
      exact mem_domR_of_isLQGLimit (restrictDense_mem_locUnifCont hω)
        (isLQGLimit_extend_restrictDense hω hlim))
    filter_upwards [h] with x hx
    exact isLQGLimit_limitMeasure (exists_isLQGLimit_of_mem_domR hx)

end ConeFamilyFunctional

end MatedCRT
