import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.FirstPass.LPBridge.GFFRadialBrownian
import MatedCRT.FirstPass.LPBridge.LateralProcessAEMeasurable
import MatedCRT.FirstPass.LPBridge.GFFRadialLateralIndep
import LatticeProb.Gauss.GaussianProcessLawExt
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# The quantum cone in the unit disk (`ConeRestrictionStep`)

For `γ ∈ (0, 2)`, the circle averages `h_r(z)` of the circle average embedding `h` of the `γ`-quantum cone over the
circles with `cl B_r(z) ⊆ B_1` have the law of the circle averages of `h^ℂ - γ log |·|` for a whole-plane GFF `h^ℂ`
(Definition 2.1, lines 427-439, restricted to the unit disk: for `t ≥ 0` the radial part of the cone is `B_t + γ t`
with `B` a standard Brownian motion independent of the lateral part, as for `h^ℂ - γ log |·|`).

A circle average is the lateral circle average plus the average over the circle of the radial function
`x ↦ h_{|x|}(0)`. For a circle not passing through the origin the radial function is continuous on the circle, and
the radial part enters through the countable family of its rational-time values
(`MatedCRT.ConeMeanZeroRestriction.limVal`). The cone and `h^ℂ - γ log |·|` then have the same law of (lateral part,
drift-removed radial path): the lateral laws agree by Definition 2.1, the drift-removed radial paths are Brownian
motions, and the two parts are independent. A circle through the origin is the limit of the circles with the same
centre and smaller radius, along which both circle-average processes converge almost surely (continuity of the circle
averages and of `r ↦ ⨍_{∂B_r(z)} log |x| = log r + log⁺(|z| / r)`); the laws of the limits agree. Two whole-plane GFFs
have the same law of circle averages (a centered Gaussian process is determined in law by its covariance).

## Main statements

* `coneRestrictionStep_holds`: `ConeRestrictionStep`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open MatedCRT.ConeMeanZeroRestriction
open scoped NNReal NNRat

noncomputable section

namespace MatedCRT.ConeRestriction

/-! ### Circles in the unit disk -/

/-- The radius of a circle in the unit disk. -/
abbrev rad (p : UnitBallCircle) : ℝ := p.1.1.1

/-- The centre of a circle in the unit disk. -/
abbrev ctr (p : UnitBallCircle) : ℂ := p.1.2

lemma rad_pos (p : UnitBallCircle) : 0 < rad p := p.1.1.2

/-- A circle in the unit disk that does not pass through the origin. -/
def Avoids (p : UnitBallCircle) : Prop := ‖ctr p‖ ≠ rad p

lemma norm_lt_one_of_mem_sphere (p : UnitBallCircle) {x : ℂ} (hx : x ∈ sphere (ctr p) (rad p)) :
    ‖x‖ < 1 := by
  have h := p.2 (sphere_subset_closedBall hx)
  simpa [mem_ball, dist_zero_right] using h

lemma ne_zero_of_mem_sphere {p : UnitBallCircle} (hp : Avoids p) {x : ℂ}
    (hx : x ∈ sphere (ctr p) (rad p)) : x ≠ 0 := by
  rintro rfl
  apply hp
  rw [mem_sphere, dist_comm, dist_zero_right] at hx
  exact hx

lemma radTime_eq {x : ℂ} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) : radTime x = -Real.log ‖x‖ := by
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg (norm_pos_iff.2 hx0) hx1
  unfold radTime
  exact max_eq_left (by linarith)

lemma exp_neg_radTime {x : ℂ} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) : Real.exp (-radTime x) = ‖x‖ := by
  rw [radTime_eq hx0 hx1, neg_neg, Real.exp_log (norm_pos_iff.2 hx0)]

/-! ### The radial and lateral parts of a circle average -/

/-- The average over the circle of the radial function `x ↦ f (max (-log |x|) 0)` of a rational-time path `f`, read
through `limVal`. -/
def radialCircle (f : ℚ≥0 → ℝ) (p : UnitBallCircle) : ℝ :=
  Real.circleAverage (fun x => limVal f x) (ctr p) (rad p)

/-- The average of `log |·|` over the circle. -/
def logCircle (p : UnitBallCircle) : ℝ :=
  Real.circleAverage (fun x => Real.log ‖x‖) (ctr p) (rad p)

/-- The lateral circle average `h_r(z) - ⨍_{∂B_r(z)} h_{|x|}(0)` of a sample. -/
def latCircle (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (p : UnitBallCircle) : ℝ :=
  lateralProcess hC hcirc ⟨GFFObservable.circle (rad p) (ctr p), rad_pos p⟩

lemma measurable_radialCircle (p : UnitBallCircle) : Measurable (fun f => radialCircle f p) := by
  unfold radialCircle
  simp_rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  have hF : StronglyMeasurable
      (fun q : (ℚ≥0 → ℝ) × ℝ => limVal q.1 (circleMap (ctr p) (rad p) q.2)) :=
    (measurable_limVal_pair.comp (measurable_fst.prodMk
      ((continuous_circleMap _ _).measurable.comp measurable_snd))).stronglyMeasurable
  exact (hF.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).measurable.const_smul
    ((2 * Real.pi)⁻¹ : ℝ)

lemma hcirc_eq_latCircle (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (p : UnitBallCircle) :
    hcirc (rad p) (ctr p) =
      latCircle hC hcirc p + Real.circleAverage (fun x => hcirc ‖x‖ 0) (ctr p) (rad p) := by
  simp only [latCircle, lateralProcess, lateralEval]
  ring

/-- On a circle avoiding the origin, the radial circle average is `radialCircle` of the rational-time radial path. -/
lemma circleAverage_radial_eq {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) {p : UnitBallCircle}
    (hp : Avoids p) :
    Real.circleAverage (fun x => hcirc ‖x‖ 0) (ctr p) (rad p) = radialCircle (radRat hcirc) p := by
  unfold radialCircle
  apply Real.circleAverage_congr_sphere
  intro x hx
  rw [abs_of_pos (rad_pos p)] at hx
  simp only
  rw [limVal_radRat hc x, exp_neg_radTime (ne_zero_of_mem_sphere hp hx) (norm_lt_one_of_mem_sphere p hx)]

/-- On a circle avoiding the origin, the radial circle average is `radialCircle` of the drift-removed rational-time
radial path minus `γ` times the average of `log |·|`. -/
lemma circleAverage_radial_eq_drift {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (γ : ℝ) {p : UnitBallCircle}
    (hp : Avoids p) :
    Real.circleAverage (fun x => hcirc ‖x‖ 0) (ctr p) (rad p) =
      radialCircle (driftRat γ (radRat hcirc)) p - γ * logCircle p := by
  have hR := rad_pos p
  have hsph : ∀ x ∈ sphere (ctr p) (rad p),
      limVal (driftRat γ (radRat hcirc)) x = hcirc ‖x‖ 0 + γ * Real.log ‖x‖ := by
    intro x hx
    have h0 := ne_zero_of_mem_sphere hp hx
    have h1 := norm_lt_one_of_mem_sphere p hx
    rw [limVal_driftRat hc γ x, limVal_radRat hc x, exp_neg_radTime h0 h1, radTime_eq h0 h1]
    ring
  have hlogc : ContinuousOn (fun x : ℂ => Real.log ‖x‖) (sphere (ctr p) (rad p)) := fun x hx =>
    ((Real.continuousAt_log (norm_ne_zero_iff.2 (ne_zero_of_mem_sphere hp hx))).comp
      continuous_norm.continuousAt).continuousWithinAt
  have hradc : ContinuousOn (fun x : ℂ => hcirc ‖x‖ 0) (sphere (ctr p) (rad p)) := by
    have h : ContinuousOn (fun x : ℂ => ((‖x‖, (0 : ℂ)) : ℝ × ℂ)) (sphere (ctr p) (rad p)) := by
      fun_prop
    exact hc.comp h fun x hx => ⟨norm_pos_iff.2 (ne_zero_of_mem_sphere hp hx), mem_univ _⟩
  have hdc : ContinuousOn (fun x => limVal (driftRat γ (radRat hcirc)) x) (sphere (ctr p) (rad p)) :=
    (hradc.add (continuousOn_const.mul hlogc)).congr hsph
  have hI1 : CircleIntegrable (fun x => limVal (driftRat γ (radRat hcirc)) x) (ctr p) (rad p) :=
    hdc.circleIntegrable hR.le
  have hI2 : CircleIntegrable (fun x => γ * Real.log ‖x‖) (ctr p) (rad p) :=
    (continuousOn_const.mul hlogc).circleIntegrable hR.le
  have e1 : Real.circleAverage (fun x => hcirc ‖x‖ 0) (ctr p) (rad p) =
      Real.circleAverage (fun x => limVal (driftRat γ (radRat hcirc)) x - γ * Real.log ‖x‖)
        (ctr p) (rad p) := by
    apply Real.circleAverage_congr_sphere
    intro x hx
    rw [abs_of_pos hR] at hx
    simp only
    rw [hsph x hx]
    ring
  have e2 : Real.circleAverage (fun x => γ * Real.log ‖x‖) (ctr p) (rad p) = γ * logCircle p := by
    unfold logCircle
    simpa only [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := γ) (f := fun x : ℂ => Real.log ‖x‖) (c := ctr p) (R := rad p))
  rw [e1, Real.circleAverage_fun_sub hI1 hI2, e2]
  rfl

/-- Circle averages of a cone sample on a circle avoiding the origin. -/
lemma cone_circle_eq (hC : (ℂ → ℝ) → ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (γ : ℝ) {p : UnitBallCircle}
    (hp : Avoids p) :
    hcirc (rad p) (ctr p) =
      latCircle hC hcirc p + radialCircle (driftRat γ (radRat hcirc)) p - γ * logCircle p := by
  rw [hcirc_eq_latCircle hC hcirc p, circleAverage_radial_eq_drift hc γ hp]
  ring

/-- Circle averages of `h^ℂ - γ log |·|` on a circle avoiding the origin. -/
lemma gff_circle_eq (hC : (ℂ → ℝ) → ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (γ : ℝ) {p : UnitBallCircle}
    (hp : Avoids p) :
    fieldCircleAverage γ hcirc (rad p) (ctr p) =
      latCircle hC hcirc p + radialCircle (radRat hcirc) p - γ * logCircle p := by
  unfold fieldCircleAverage
  rw [hcirc_eq_latCircle hC hcirc p, circleAverage_radial_eq hc hp]
  rfl

/-! ### Laws for families of circles avoiding the origin -/

/-- The read-out of a family of circles from the lateral circle averages and a rational-time radial path. -/
def circReadOut {ι : Type*} (γ : ℝ) (c : ι → UnitBallCircle) : (ι → ℝ) × (ℚ≥0 → ℝ) → (ι → ℝ) :=
  fun q i => q.1 i + radialCircle q.2 (c i) - γ * logCircle (c i)

lemma measurable_circReadOut {ι : Type*} (γ : ℝ) (c : ι → UnitBallCircle) : Measurable (circReadOut γ c) := by
  apply Measurable.of_eval
  intro i
  exact (((measurable_pi_apply i).comp measurable_fst).add
    ((measurable_radialCircle (c i)).comp measurable_snd)).sub measurable_const

lemma law_circReadOut_eq {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] (γ : ℝ)
    (c : ι → UnitBallCircle) {L : Ω → (ι → ℝ)} {B : Ω → (ℚ≥0 → ℝ)} {F : Ω → (ι → ℝ)}
    (hF : ∀ᵐ ω ∂P, F ω = circReadOut γ c (L ω, B ω)) (hL : AEMeasurable L P) (hB : AEMeasurable B P)
    (hind : IndepFun L B P) :
    P.map F = ((P.map L).prod (P.map B)).map (circReadOut γ c) := by
  have hpair : AEMeasurable (fun ω => (L ω, B ω)) P := hL.prodMk hB
  have hiff := indepFun_iff_map_prod_eq_prod_map_map hL hB
  rw [Measure.map_congr hF, ← hiff.1 hind]
  exact (AEMeasurable.map_map_of_aemeasurable (measurable_circReadOut γ c).aemeasurable hpair).symm

/-- The projection of the lateral process to the lateral circle averages of a family of circles. -/
def latProj {ι : Type*} (c : ι → UnitBallCircle) : (GFFObservable.Admissible → ℝ) → (ι → ℝ) :=
  fun g i => g ⟨GFFObservable.circle (rad (c i)) (ctr (c i)), rad_pos (c i)⟩

lemma measurable_latProj {ι : Type*} (c : ι → UnitBallCircle) : Measurable (latProj c) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **The cone and `h^ℂ - γ log |·|` on circles avoiding the origin.** For a quantum cone sample there is a
whole-plane GFF such that, for every family of circles in the unit disk avoiding the origin, the circle averages of
the cone have the law of those of `h^ℂ - γ log |·|`. The GFF is the one of the lateral law in Definition 2.1. -/
theorem exists_gff_law_eq_of_avoids {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) :
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (hC'' : Ω'' → (ℂ → ℝ) → ℝ)
      (hcirc'' : Ω'' → ℝ → ℂ → ℝ), IsProbabilityMeasure P'' ∧ IsWholePlaneGFF P'' hC'' hcirc'' ∧
      ∀ {ι : Type} (c : ι → UnitBallCircle), (∀ i, Avoids (c i)) →
        P.map (fun ω i => hcirc ω (rad (c i)) (ctr (c i))) =
          P''.map (fun ω i => fieldCircleAverage γ (hcirc'' ω) (rad (c i)) (ctr (c i))) := by
  obtain ⟨Ω'', _, P'', hC'', hcirc'', hP'', hgff'', heq⟩ := hcone.lateral_law
  refine ⟨Ω'', inferInstance, P'', hC'', hcirc'', hP'', hgff'', fun {ι} c hc => ?_⟩
  have hproj := measurable_latProj c
  -- the cone: lateral part, drift-removed radial path, independence, read-out
  have hLc : AEMeasurable (fun ω => latProj c (lateralProcess (hC ω) (hcirc ω))) P :=
    hproj.comp_aemeasurable (lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance hcone)
  have hBc : Measurable (fun ω => driftRat γ (radRat (hcirc ω))) := by
    apply Measurable.of_eval
    intro q
    exact (hcone.measurable_circle _ _ (Real.exp_pos _)).sub measurable_const
  have hindC : IndepFun (fun ω => latProj c (lateralProcess (hC ω) (hcirc ω)))
      (fun ω => driftRat γ (radRat (hcirc ω))) P := by
    have hg : Measurable (fun r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
        fun q : ℚ≥0 => r.1 (q : ℝ≥0) - γ * (q : ℝ)) := by
      apply Measurable.of_eval
      intro q
      exact ((measurable_pi_apply _).comp measurable_fst).sub measurable_const
    exact (hcone.indep.comp hg hproj).symm
  have hFc : ∀ᵐ ω ∂P, (fun i => hcirc ω (rad (c i)) (ctr (c i))) =
      circReadOut γ c (latProj c (lateralProcess (hC ω) (hcirc ω)), driftRat γ (radRat (hcirc ω))) := by
    filter_upwards [hcone.ae_continuousOn_circle] with ω hω
    funext i
    exact cone_circle_eq (hC ω) hω γ (hc i)
  -- the whole-plane GFF of the lateral law
  have hLg : AEMeasurable (fun ω => latProj c (lateralProcess (hC'' ω) (hcirc'' ω))) P'' :=
    hproj.comp_aemeasurable (lateralProcessAEMeasurable_holds.2 Ω'' P'' hC'' hcirc'' hP'' hgff'')
  have hRg : Measurable (fun ω (q : ℚ≥0) => radRat (hcirc'' ω) q) :=
    measurable_radRat hgff''.measurable_circle
  have hindG : IndepFun (fun ω => latProj c (lateralProcess (hC'' ω) (hcirc'' ω)))
      (fun ω (q : ℚ≥0) => radRat (hcirc'' ω) q) P'' := by
    have hg : Measurable (fun r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => fun q : ℚ≥0 => r.1 (q : ℝ≥0)) := by
      apply Measurable.of_eval
      intro q
      exact (measurable_pi_apply _).comp measurable_fst
    exact ((gffRadialLateralIndep_holds Ω'' P'' hC'' hcirc'' hP'' hgff'').comp hg hproj).symm
  have hFg : ∀ᵐ ω ∂P'', (fun i => fieldCircleAverage γ (hcirc'' ω) (rad (c i)) (ctr (c i))) =
      circReadOut γ c (latProj c (lateralProcess (hC'' ω) (hcirc'' ω)),
        fun q : ℚ≥0 => radRat (hcirc'' ω) q) := by
    filter_upwards [hgff''.ae_continuousOn_circle] with ω hω
    funext i
    exact gff_circle_eq (hC'' ω) hω γ (hc i)
  -- equal laws of the lateral parts and of the radial paths
  have hlat : P.map (fun ω => latProj c (lateralProcess (hC ω) (hcirc ω))) =
      P''.map (fun ω => latProj c (lateralProcess (hC'' ω) (hcirc'' ω))) := by
    calc P.map (fun ω => latProj c (lateralProcess (hC ω) (hcirc ω)))
        = (P.map (fun ω => lateralProcess (hC ω) (hcirc ω))).map (latProj c) :=
          (AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable
            (lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance hcone)).symm
      _ = (P''.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω))).map (latProj c) := by rw [heq]
      _ = P''.map (fun ω => latProj c (lateralProcess (hC'' ω) (hcirc'' ω))) :=
          AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable
            (lateralProcessAEMeasurable_holds.2 Ω'' P'' hC'' hcirc'' hP'' hgff'')
  rw [law_circReadOut_eq γ c hFc hLc hBc.aemeasurable hindC,
    law_circReadOut_eq γ c hFg hLg hRg.aemeasurable hindG, hlat, cone_radial_BM hcone,
    gffRadialBrownian_holds Ω'' P'' hC'' hcirc'' hP'' hgff'']

/-! ### Two whole-plane GFFs -/

lemma measurable_observables {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    Measurable (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) := by
  apply Measurable.of_eval
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ => exact h.measurable_pairing φ ho
  | circle r z => exact h.measurable_circle r z ho

/-- Two whole-plane GFFs have the same law of the circle averages of `h^ℂ - α log |·|` on every family of circles in
the unit disk. -/
theorem gff_law_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ} {hcirc₁ : Ω₁ → ℝ → ℂ → ℝ} {hC₂ : Ω₂ → (ℂ → ℝ) → ℝ}
    {hcirc₂ : Ω₂ → ℝ → ℂ → ℝ} (h₁ : IsWholePlaneGFF P₁ hC₁ hcirc₁) (h₂ : IsWholePlaneGFF P₂ hC₂ hcirc₂)
    (α : ℝ) {ι : Type*} (c : ι → UnitBallCircle) :
    P₁.map (fun ω i => fieldCircleAverage α (hcirc₁ ω) (rad (c i)) (ctr (c i))) =
      P₂.map (fun ω i => fieldCircleAverage α (hcirc₂ ω) (rad (c i)) (ctr (c i))) := by
  have hP₁ : IsProbabilityMeasure P₁ := gff_isProbabilityMeasure h₁
  have hP₂ : IsProbabilityMeasure P₂ := gff_isProbabilityMeasure h₂
  have hlaw := LatticeProb.gaussianProcess_map_eq_of_mean_cov h₁.isGaussianProcess h₂.isGaussianProcess
    (fun o => by rw [h₁.integral_eq_zero o.1 o.2, h₂.integral_eq_zero o.1 o.2])
    (fun s t => by rw [h₁.covariance_eq s.1 t.1 s.2 t.2, h₂.covariance_eq s.1 t.1 s.2 t.2])
    (measurable_observables h₁).aemeasurable (measurable_observables h₂).aemeasurable
  let G : (GFFObservable.Admissible → ℝ) → (ι → ℝ) :=
    fun g i => g ⟨GFFObservable.circle (rad (c i)) (ctr (c i)), rad_pos (c i)⟩ - α * logCircle (c i)
  have hG : Measurable G := Measurable.of_eval fun _ => (measurable_pi_apply _).sub measurable_const
  have e₁ : (fun ω i => fieldCircleAverage α (hcirc₁ ω) (rad (c i)) (ctr (c i))) =
      G ∘ fun ω (o : GFFObservable.Admissible) => o.1.eval (hC₁ ω) (hcirc₁ ω) := rfl
  have e₂ : (fun ω i => fieldCircleAverage α (hcirc₂ ω) (rad (c i)) (ctr (c i))) =
      G ∘ fun ω (o : GFFObservable.Admissible) => o.1.eval (hC₂ ω) (hcirc₂ ω) := rfl
  rw [e₁, e₂, ← Measure.map_map hG (measurable_observables h₁),
    ← Measure.map_map hG (measurable_observables h₂), hlaw]

/-! ### Circles through the origin -/

/-- The circle with the same centre and the radius multiplied by `(n + 1) / (n + 2)`, when the circle passes through
the origin; the circle itself otherwise. -/
def shrink (n : ℕ) (p : UnitBallCircle) : UnitBallCircle :=
  if ‖ctr p‖ = rad p then
    ⟨(⟨rad p * (((n : ℝ) + 1) / ((n : ℝ) + 2)), mul_pos (rad_pos p) (by positivity)⟩, ctr p),
      (closedBall_subset_closedBall (mul_le_of_le_one_right (rad_pos p).le
        ((div_le_one (by positivity)).2 (by linarith)))).trans p.2⟩
  else p

lemma ctr_shrink (n : ℕ) (p : UnitBallCircle) : ctr (shrink n p) = ctr p := by
  unfold shrink
  split_ifs <;> rfl

lemma avoids_shrink (n : ℕ) (p : UnitBallCircle) : Avoids (shrink n p) := by
  unfold shrink
  split_ifs with h
  · show ‖ctr p‖ ≠ rad p * (((n : ℝ) + 1) / ((n : ℝ) + 2))
    rw [h]
    intro h'
    have hr := rad_pos p
    have hlt : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    nlinarith [mul_lt_mul_of_pos_left hlt hr]
  · exact h

lemma tendsto_rad_shrink (p : UnitBallCircle) :
    Tendsto (fun n => rad (shrink n p)) atTop (𝓝 (rad p)) := by
  by_cases h : ‖ctr p‖ = rad p
  · have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    have hq : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
      have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
      rw [sub_zero] at h1
      refine h1.congr fun n => ?_
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
    have := hq.const_mul (rad p)
    rw [mul_one] at this
    refine this.congr fun n => ?_
    simp [shrink, h]
  · have he : ∀ n, shrink n p = p := fun n => by simp [shrink, h]
    simp only [he]
    exact tendsto_const_nhds

/-- The average of `log |·|` over `∂B_r(z)` is `log r + log⁺(|z| / r)`. -/
lemma logCircle_eq (p : UnitBallCircle) :
    logCircle p = Real.log (rad p) + Real.posLog ((rad p)⁻¹ * ‖ctr p‖) := by
  have h := _root_.circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := ctr p)
    (rad_pos p).ne'
  simp only [sub_zero] at h
  exact h

lemma tendsto_logCircle_shrink (p : UnitBallCircle) :
    Tendsto (fun n => logCircle (shrink n p)) atTop (𝓝 (logCircle p)) := by
  have hr := tendsto_rad_shrink p
  have hcont : ContinuousAt (fun r : ℝ => Real.log r + Real.posLog (r⁻¹ * ‖ctr p‖)) (rad p) := by
    have hne : rad p ≠ 0 := (rad_pos p).ne'
    exact (Real.continuousAt_log hne).add
      (Real.continuous_posLog.continuousAt.comp ((continuousAt_inv₀ hne).mul continuousAt_const))
  have := hcont.tendsto.comp hr
  simp only [Function.comp_def] at this
  rw [logCircle_eq p]
  refine this.congr fun n => ?_
  rw [logCircle_eq, ctr_shrink]

/-- Equal laws pass to almost sure limits. -/
lemma map_eq_of_tendsto {ι : Type} [Fintype ι] {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X : ℕ → Ω₁ → (ι → ℝ)} {X₀ : Ω₁ → (ι → ℝ)} {Y : ℕ → Ω₂ → (ι → ℝ)} {Y₀ : Ω₂ → (ι → ℝ)}
    (hX : ∀ n, Measurable (X n)) (hX₀ : Measurable X₀) (hY : ∀ n, Measurable (Y n)) (hY₀ : Measurable Y₀)
    (hXt : ∀ᵐ ω ∂P₁, Tendsto (fun n => X n ω) atTop (𝓝 (X₀ ω)))
    (hYt : ∀ᵐ ω ∂P₂, Tendsto (fun n => Y n ω) atTop (𝓝 (Y₀ ω)))
    (heq : ∀ n, P₁.map (X n) = P₂.map (Y n)) : P₁.map X₀ = P₂.map Y₀ := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hX₀.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hY₀.aemeasurable f.continuous.aestronglyMeasurable]
  have h₁ : Tendsto (fun n => ∫ ω, f (X n ω) ∂P₁) atTop (𝓝 (∫ ω, f (X₀ ω) ∂P₁)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (hX n)).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
      (hXt.mono fun ω h => (f.continuous.tendsto _).comp h)
  have h₂ : Tendsto (fun n => ∫ ω, f (Y n ω) ∂P₂) atTop (𝓝 (∫ ω, f (Y₀ ω) ∂P₂)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (hY n)).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
      (hYt.mono fun ω h => (f.continuous.tendsto _).comp h)
  have e : (fun n => ∫ ω, f (X n ω) ∂P₁) = fun n => ∫ ω, f (Y n ω) ∂P₂ := by
    funext n
    rw [← integral_map (hX n).aemeasurable f.continuous.aestronglyMeasurable,
      ← integral_map (hY n).aemeasurable f.continuous.aestronglyMeasurable, heq n]
  rw [e] at h₁
  exact tendsto_nhds_unique h₁ h₂

/-- Finite-dimensional marginals determine a probability law on `T → ℝ`. -/
lemma eq_of_finset_marginals' {T : Type*} {μ ν : Measure (T → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ S : Finset T, μ.map (fun g (i : S) => g i) = ν.map (fun g (i : S) => g i)) : μ = ν := by
  have hμ : IsProjectiveLimit μ (fun S : Finset T => μ.map (fun g (i : S) => g i)) := fun S => rfl
  have hν : IsProjectiveLimit ν (fun S : Finset T => μ.map (fun g (i : S) => g i)) :=
    fun S => (h S).symm
  exact IsProjectiveLimit.unique hμ hν

lemma tendsto_circle_shrink {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (p : UnitBallCircle) :
    Tendsto (fun n => hcirc (rad (shrink n p)) (ctr (shrink n p))) atTop (𝓝 (hcirc (rad p) (ctr p))) := by
  have hat : ContinuousAt (fun q : ℝ × ℂ => hcirc q.1 q.2) (rad p, ctr p) :=
    hc.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨rad_pos p, mem_univ _⟩)
  have hq : Tendsto (fun n => ((rad (shrink n p), ctr (shrink n p)) : ℝ × ℂ)) atTop
      (𝓝 (rad p, ctr p)) := by
    simp only [ctr_shrink]
    exact (tendsto_rad_shrink p).prodMk_nhds tendsto_const_nhds
  exact hat.tendsto.comp hq

/-! ### The step -/

/-- **The quantum cone in the unit disk** (`ConeRestrictionStep`): the circle averages of the cone over the circles
in the unit disk have the law of those of `h^ℂ - γ log |·|`. -/
theorem coneRestrictionStep_holds : ConeRestrictionStep := by
  intro γ _ _ Ω _ P hC hcirc hP hcone Ω' _ P' hC' hcirc' hP' hgff
  obtain ⟨Ω'', _, P'', hC'', hcirc'', hP'', hgff'', hlaw⟩ := exists_gff_law_eq_of_avoids hcone
  have hm₁ : Measurable (fun ω => unitBallCircleProcess (hcirc ω)) :=
    Measurable.of_eval fun p => hcone.measurable_circle _ _ (rad_pos p)
  have hm₂ : Measurable (fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc' ω))) :=
    Measurable.of_eval fun p => (hgff.measurable_circle _ _ (rad_pos p)).sub measurable_const
  refine eq_of_finset_marginals' fun S => ?_
  have hres : Measurable (fun g : UnitBallCircle → ℝ => fun (i : S) => g i) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [Measure.map_map hres hm₁, Measure.map_map hres hm₂]
  show P.map (fun ω (i : S) => hcirc ω (rad i) (ctr i)) =
    P'.map (fun ω (i : S) => fieldCircleAverage γ (hcirc' ω) (rad i) (ctr i))
  refine map_eq_of_tendsto
    (X := fun n ω (i : S) => hcirc ω (rad (shrink n i)) (ctr (shrink n i)))
    (Y := fun n ω (i : S) => fieldCircleAverage γ (hcirc' ω) (rad (shrink n i)) (ctr (shrink n i)))
    (fun n => Measurable.of_eval fun i => hcone.measurable_circle _ _ (rad_pos _))
    (Measurable.of_eval fun i => hcone.measurable_circle _ _ (rad_pos _))
    (fun n => Measurable.of_eval fun i => (hgff.measurable_circle _ _ (rad_pos _)).sub measurable_const)
    (Measurable.of_eval fun i => (hgff.measurable_circle _ _ (rad_pos _)).sub measurable_const)
    ?_ ?_ ?_
  · filter_upwards [hcone.ae_continuousOn_circle] with ω hω
    exact tendsto_pi_nhds.2 fun i => tendsto_circle_shrink hω i
  · filter_upwards [hgff.ae_continuousOn_circle] with ω hω
    refine tendsto_pi_nhds.2 fun i => ?_
    exact (tendsto_circle_shrink hω i).sub ((tendsto_logCircle_shrink i).const_mul γ)
  · intro n
    rw [hlaw (fun i : S => shrink n i) (fun i => avoids_shrink n i)]
    exact gff_law_eq hgff'' hgff γ (fun i : S => shrink n i)

end MatedCRT.ConeRestriction
