import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScaleLaw
import MatedCRT.Proofs.Field.WholePlaneAffine
import MatedCRT.Proofs.Field.WholePlaneCircleLaw
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.WholePlaneLQGMeasurable
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Approx
import MatedCRT.Proposed.DuplantierSheffieldCoordinate2011

/-! # Input K of Proposition 4.2: the insertion-`α` LQG scaling law (`InsertionLQGScalingLawStep`)

Task `z5-insertion-lqg-scaling-law`. Target: `InsertionLQGScalingLawStep` (`PlateauScaleLaw.lean:106`).

Statement K: for `γ ∈ (0,2)`, `α < Q`, a whole-plane GFF `h^ℂ` with insertion-`α` LQG measure `μ`, and `a > 0`, there are
a whole-plane GFF `h''` (the affine transform `h^ℂ(a ·) - h^ℂ_a(0)`, i.e. `affHC a 0`, `affHcirc a 0`), its insertion-`α`
LQG measure `μ''`, and a random constant `c > 0` with `μ.map (· / a) = c • μ''` a.s. and `μ'' =_d μ`.

Route (written argument: `notes/prop42-proof/prop42-proof.tex` lines 245-256; `c = e^{γ c_a}`, `c_a = g_a(0) + (Q-α) log a`):
* field law: `MatedCRT.Field.isWholePlaneGFF_affine` (`Proofs/Field/WholePlaneAffine.lean`);
* circle averages: for `s > 0`, `fieldCircleAverage α (affHcirc a 0 h ω) s v = H(a s, a v) - H(a, 0)` with `H = fieldCircleAverage α (h ω)`
  (`insCircleAverage_log_scaled`: `circleAverage (log‖·‖) (a v) (a s) = log a + circleAverage (log‖·‖) v s`);
* LQG limit: the non-dyadic coordinate rule `MatedCRT.Proposed.InsertionCoordinateExtensionStep` (an OPEN INTERNAL
  EXTENSION, WPN-42-insertion-coordinate-extension, staged in `MatedCRT/Proposed/DuplantierSheffieldCoordinate2011.lean`;
  not a DS11 citation; the only open input here), then the constant shift
  `MatedCRT.LQGMeasure.isLQGLimit_addCircleAverage` (`Proofs/Sec2/LQGMeasureProperties/Approx.lean`);
* law: `identDistrib_lqgMeasure_of_circleProcess` (`Proofs/Sec2/ConeFamilyMeasurable/MeasureLaw.lean`, the Borel recovery) with
  `MatedCRT.Field.wholePlane_circle_law` (equality in law of whole-plane circle averages) and a deterministic shift.

The theorem `insertionLQGScalingLawStep_of_coordinateRule` is conditional on the open internal extension
`InsertionCoordinateExtensionStep`, not on a cited theorem; it is not a closure of K. -/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-! ### 1. Continuity and measurability of the insertion circle averages -/

theorem insLogAverage_continuousOn :
    ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage (fun x => Real.log ‖x‖) p.2 p.1) (Ioi 0 ×ˢ univ) := by
  have hlogR : ContinuousOn (fun p : ℝ × ℂ => Real.log p.1 + Real.posLog (p.1⁻¹ * ‖p.2‖)) (Ioi 0 ×ˢ univ) :=
    (ContinuousOn.log continuous_fst.continuousOn (fun p hp => (Set.mem_Ioi.mp hp.1).ne')).add
      (Real.continuous_posLog.comp_continuousOn
        ((ContinuousOn.inv₀ continuous_fst.continuousOn (fun p hp => (Set.mem_Ioi.mp hp.1).ne')).mul
          (continuous_norm.comp continuous_snd).continuousOn))
  refine hlogR.congr fun p hp => ?_
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := p.2) (R := p.1)
    (Set.mem_Ioi.mp hp.1).ne'
  simpa only [sub_zero] using h

theorem insertion_ae_continuousOn {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (α : ℝ) :
    ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => fieldCircleAverage α (hcirc ω) p.1 p.2) (Ioi 0 ×ˢ univ) := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
  simp only [fieldCircleAverage]
  exact hω.sub (continuousOn_const.mul insLogAverage_continuousOn)

theorem insertion_measurable_fieldCircleAverage {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (α : ℝ)
    {r : ℝ} (z : ℂ) (hr : 0 < r) : Measurable fun ω => fieldCircleAverage α (hcirc ω) r z := by
  simp only [fieldCircleAverage]
  exact (hGFF.measurable_circle r z hr).sub measurable_const

/-! ### 2. Circle averages of the affine transform -/

/-- `circleAverage (log‖·‖) (a v) (a s) = log a + circleAverage (log‖·‖) v s` for `a, s > 0`. -/
theorem insCircleAverage_log_scaled {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (v : ℂ) :
    Real.circleAverage (fun x => Real.log ‖x‖) ((a : ℂ) * v) (a * s)
      = Real.log a + Real.circleAverage (fun x => Real.log ‖x‖) v s := by
  have h1 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := (a : ℂ) * v)
    (R := a * s) (mul_pos ha hs).ne'
  have h2 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := v) (R := s) hs.ne'
  have hn : (a * s)⁻¹ * ‖(a : ℂ) * v‖ = s⁻¹ * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    field_simp
  simp only [sub_zero] at h1 h2
  rw [h1, h2, hn, Real.log_mul ha.ne' hs.ne']
  ring

theorem insCircleAverage_log_zero {a : ℝ} (ha : 0 < a) :
    Real.circleAverage (fun x => Real.log ‖x‖) 0 a = Real.log a := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := 0) (R := a) ha.ne'
  simpa only [sub_zero, norm_zero, mul_zero, Real.posLog_zero, add_zero] using h

/-- Insertion-`α` circle averages of the affine transform `h^α(a ·) - h^α_a(0)`, at positive scales:
`fieldCircleAverage α (affHcirc a 0 h ω) s v = H(a s, a v) - H(a, 0)` with `H = fieldCircleAverage α (h ω)`. -/
theorem fieldCircleAverage_affHcirc_pos {Ω : Type} (α : ℝ) {a : ℝ} (ha : 0 < a)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) {s : ℝ} (hs : 0 < s) (v : ℂ) :
    fieldCircleAverage α (MatedCRT.Field.affHcirc a 0 hcirc ω) s v
      = fieldCircleAverage α (hcirc ω) (a * s) ((a : ℂ) * v) - fieldCircleAverage α (hcirc ω) a 0 := by
  simp only [MatedCRT.Field.affHcirc, fieldCircleAverage, add_zero]
  rw [insCircleAverage_log_scaled ha hs v, insCircleAverage_log_zero ha]
  ring

/-! ### 3. LQG limits: congruence at positive scales, constant shift, scaled measure -/

/-- Equal approximations at all positive scales give equal LQG limits (`lqgApprox` reads `hε ε` only for `ε > 0`). -/
theorem isLQGLimit_congr_pos {γ : ℝ} {H H' : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (h : ∀ ε : ℝ, 0 < ε → H ε = H' ε) (hm : IsLQGLimit γ H m) : IsLQGLimit γ H' m := by
  refine ⟨hm.isLocallyFiniteMeasure, fun g hg hgc => ?_⟩
  have hk : ∀ k : ℕ, lqgApprox γ H' (dyadicScale k) = lqgApprox γ H (dyadicScale k) := fun k => by
    unfold lqgApprox
    rw [← h _ (dyadicScale_pos k)]
  simpa only [hk] using hm.tendsto_integral g hg hgc

/-- The insertion constant `c_a = g_a(0) + (Q - α) log a = H_a(0) + Q log a` (draft line 252), for `H = h^α` circle averages. -/
noncomputable def insertionScaleConst (γ α a : ℝ) (hc : ℝ → ℂ → ℝ) : ℝ :=
  fieldCircleAverage α hc a 0 + lqgQ γ * Real.log a

/-- The LQG measure of the scaled insertion field, `μ_{h_a} = e^{-γ c} · m` with `m = μ.map (· / a)` (draft line 252). -/
noncomputable def insertionScaledMeasure (γ c : ℝ) (m : Measure ℂ) : Measure ℂ :=
  m.withDensity fun _ => ENNReal.ofReal (Real.exp (γ * -c))

theorem ofReal_exp_smul_insertionScaledMeasure (γ c : ℝ) (m : Measure ℂ) :
    ENNReal.ofReal (Real.exp (γ * c)) • insertionScaledMeasure γ c m = m := by
  unfold insertionScaledMeasure
  rw [← withDensity_smul _ measurable_const]
  have h1 : (ENNReal.ofReal (Real.exp (γ * c)) • fun _ : ℂ => ENNReal.ofReal (Real.exp (γ * -c)))
      = (1 : ℂ → ℝ≥0∞) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, Pi.one_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  rw [h1, withDensity_one]

/-- Deterministic core of K: the insertion-`α` LQG limit of `H(a·, a·) - H_a(0)`, from that of `H(a·, a·) + Q log a`
(the constant shift `isLQGLimit_addCircleAverage` with `f ≡ -c_a`). -/
theorem isLQGLimit_insertion_shift {γ α a : ℝ} {hc : ℝ → ℂ → ℝ} {m : Measure ℂ} (ha : 0 < a)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => fieldCircleAverage α hc p.1 p.2) (Ioi 0 ×ˢ univ))
    (hm : IsLQGLimit γ (fun ε z => fieldCircleAverage α hc (a * ε) ((a : ℂ) * z) + lqgQ γ * Real.log a) m) :
    IsLQGLimit γ (fun ε z => fieldCircleAverage α hc (a * ε) ((a : ℂ) * z) - fieldCircleAverage α hc a 0)
      (insertionScaledMeasure γ (insertionScaleConst γ α a hc) m) := by
  have hH : ∀ ε : ℝ, 0 < ε → Continuous (fun z : ℂ =>
      fieldCircleAverage α hc (a * ε) ((a : ℂ) * z) + lqgQ γ * Real.log a) := by
    intro ε hε
    have hcomp : Continuous fun z : ℂ => fieldCircleAverage α hc (a * ε) ((a : ℂ) * z) :=
      hcont.comp_continuous (f := fun z : ℂ => (a * ε, (a : ℂ) * z)) (by fun_prop)
        fun z => ⟨mul_pos ha hε, mem_univ _⟩
    exact hcomp.add continuous_const
  have key := MatedCRT.LQGMeasure.isLQGLimit_addCircleAverage hm hH
    (f := fun _ : ℂ => -insertionScaleConst γ α a hc) continuous_const
  have hfun : addCircleAverage (fun ε z => fieldCircleAverage α hc (a * ε) ((a : ℂ) * z) + lqgQ γ * Real.log a)
      (fun _ : ℂ => -insertionScaleConst γ α a hc)
      = fun ε z => fieldCircleAverage α hc (a * ε) ((a : ℂ) * z) - fieldCircleAverage α hc a 0 := by
    funext ε z
    simp only [addCircleAverage, Real.circleAverage_const, insertionScaleConst]
    ring
  rw [hfun] at key
  exact key

/-! ### 4. Input K from the open insertion-coordinate extension -/

/-- **Input K from the open insertion-coordinate extension.** `InsertionLQGScalingLawStep` (`PlateauScaleLaw.lean:106`)
follows from the fixed-map coordinate rule `InsertionCoordinateExtensionStep` (WPN-42-insertion-coordinate-extension). That
hypothesis is an OPEN INTERNAL EXTENSION and NOT a DS11 citation: DS11 Prop. 2.1 (p. 13) does not print its whole-plane
insertion field or its non-dyadic scales (see `MatedCRT/Proposed/DuplantierSheffieldCoordinate2011.lean`). Together with the
existing whole-plane field law, circle-average measurability and Borel recovery, the field law and the Borel recovery are
proved here (not assumed); the non-dyadic convergence is the single open input. -/
theorem insertionLQGScalingLawStep_of_coordinateRule
    (hDS : MatedCRT.Proposed.InsertionCoordinateExtensionStep) : InsertionLQGScalingLawStep := by
  intro γ α hγ0 hγ2 hα Ω _ P hC hcirc μ hP hGFF hLQG a ha
  have := hP
  have hna : ‖(a : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hGFF'' : IsWholePlaneGFF P (MatedCRT.Field.affHC a 0 hC hcirc) (MatedCRT.Field.affHcirc a 0 hcirc) :=
    MatedCRT.Field.isWholePlaneGFF_affine hGFF ha 0
  have hDSae := hDS γ α hγ0 hγ2 hα Ω P hC hcirc μ hP hGFF hLQG (a : ℂ) (Complex.ofReal_ne_zero.mpr ha.ne') 0
  have hlim : ∀ᵐ ω ∂P, IsLQGLimit γ (fun ε z => fieldCircleAverage α (MatedCRT.Field.affHcirc a 0 hcirc ω) ε z)
      (insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ))) := by
    filter_upwards [hDSae, insertion_ae_continuousOn hGFF α] with ω hω hcω
    simp only [hna, sub_zero, add_zero] at hω
    have hsh := isLQGLimit_insertion_shift (hc := hcirc ω) (m := (μ ω).map fun x => x / (a : ℂ)) ha hcω hω
    refine isLQGLimit_congr_pos ?_ hsh
    intro ε hε
    funext z
    exact (fieldCircleAverage_affHcirc_pos α ha hcirc ω hε z).symm
  have hLQGaff : IsLQGMeasureOfField P γ α (MatedCRT.Field.affHcirc a 0 hcirc)
      (fun ω => insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ))) :=
    hlim
  refine ⟨MatedCRT.Field.affHC a 0 hC hcirc, MatedCRT.Field.affHcirc a 0 hcirc,
    fun ω => insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ)),
    fun ω => Real.exp (γ * insertionScaleConst γ α a (hcirc ω)), hGFF'', hLQGaff, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ω =>
      ⟨Real.exp_pos _, (ofReal_exp_smul_insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) _).symm⟩
  · have hXm : Measurable fun ω (p : Ioi (0 : ℝ) × ℂ) => hcirc ω p.1 p.2 :=
      measurable_pi_iff.mpr fun p => hGFF.measurable_circle (p.1 : ℝ) p.2 p.1.2
    have hX''m : Measurable fun ω (p : Ioi (0 : ℝ) × ℂ) => MatedCRT.Field.affHcirc a 0 hcirc ω p.1 p.2 :=
      measurable_pi_iff.mpr fun p => hGFF''.measurable_circle (p.1 : ℝ) p.2 p.1.2
    have hX : IdentDistrib (fun ω => circleProcess (hcirc ω))
        (fun ω => circleProcess (MatedCRT.Field.affHcirc a 0 hcirc ω)) P P :=
      ⟨hXm.aemeasurable, hX''m.aemeasurable, MatedCRT.Field.wholePlane_circle_law hGFF hGFF''⟩
    have hT : Measurable fun g : Ioi (0 : ℝ) × ℂ → ℝ => fun p : Ioi (0 : ℝ) × ℂ =>
        g p - α * Real.circleAverage (fun x => Real.log ‖x‖) p.2 p.1 :=
      measurable_pi_iff.mpr fun p => (measurable_pi_apply p).sub measurable_const
    have hlaw := hX.comp hT
    have hI := identDistrib_lqgMeasure_of_circleProcess (γ := γ)
      (c := fun ω => fieldCircleAverage α (hcirc ω))
      (d := fun ω => fieldCircleAverage α (MatedCRT.Field.affHcirc a 0 hcirc ω))
      (μ := μ)
      (ν := fun ω => insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ)))
      (insertion_ae_continuousOn hGFF α) (insertion_ae_continuousOn hGFF'' α) hLQG hlim
      (aemeasurable_lqgMeasure_of_circleAverages (γ := γ) (hε := fun ω => fieldCircleAverage α (hcirc ω))
        (fun r z hr => insertion_measurable_fieldCircleAverage hGFF α z hr) (insertion_ae_continuousOn hGFF α) hLQG)
      (aemeasurable_lqgMeasure_of_circleAverages (γ := γ)
        (hε := fun ω => fieldCircleAverage α (MatedCRT.Field.affHcirc a 0 hcirc ω))
        (fun r z hr => insertion_measurable_fieldCircleAverage hGFF'' α z hr) (insertion_ae_continuousOn hGFF'' α) hlim)
      hlaw
    exact hI.symm

end MatedCRT
