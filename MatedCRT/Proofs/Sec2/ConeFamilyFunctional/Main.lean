import MatedCRT.Proofs.Sec2.ConeFamilyFunctional.StrictTest
import MatedCRT.Proofs.Sec2.ConeFamilyFunctional.Canonical
import MatedCRT.Proofs.Sec2.ConeFamilyFunctional.Hull

/-!
# The family of Lemma 2.4 is a measurable functional of the field

Proof of `ConeHalfBallFamilyFunctionalStep` (Lemma 2.5, lines 553, 562, 584). Write `y = (c_r(z))` for the values of a
circle average process at the rational points and `ν(y)` for the vague limit of the approximating measures of the
extended process (`limitMeasure`).

* `G` is the set of processes whose `ν(y)` has a strictly growing family of Lemma 2.4, and `Φ` decodes the family
  from the Borel local code `codeOf γ 1 y` of `ν(y)` on `B̄_1` (`codeFamilyProcess`). For a continuous process `c`
  with LQG measure `ν` the vague limit of the extended process is `ν` and the local code is `ν|_{B̄_1}`; a strict
  family is unique and decoded from `ν|_{B̄_1}` (`familyProcess_eq_codeFamilyProcess`), so both properties hold for
  every such `c`.
* `Φ` is Borel. `G` agrees with the Borel set `{StrictTest 1 (codeOf γ 1 y)}` off the set `S` of values where they
  differ. On the canonical quantum cone `(y, pairings)` (`isConeField_canon`) the existence of a strict family is a.s.
  the strict-growth test (`ae_exists_strict_iff_strictTest`, from Lemma 2.4), so a.s. `y ∉ S`; the null sets of the
  first projection from `DenseCircle × (TestFn → ℝ)` (`map_fst_apply_eq_zero`) make `S` null for the law of `y`, and
  hence `G` null-measurable for the law of the circle average process.
-/

namespace MatedCRT

open MeasureTheory Filter Set Metric
open _root_.HarmonicBalls

namespace ConeFamilyFunctional

/-- The values at the rational points whose vague limit measure has a strictly growing family of Lemma 2.4. -/
def StrictSet (γ : ℝ) : Set DenseCircle :=
  {y | ∃ (T : ℝ) (Λ : ℝ → Set ℂ), IsStrictHalfBallFamily (limitMeasure γ y) Λ T}

/-- The values at the rational points whose local code passes the strict-growth test. -/
def StrictCode (γ : ℝ) : Set DenseCircle := {y | StrictTest 1 (codeOf γ 1 y)}

theorem measurableSet_strictCode (γ : ℝ) : MeasurableSet (StrictCode γ) :=
  measurable_codeOf γ 1 (measurableSet_strictTest one_pos)

/-- On the canonical quantum cone the two sets a.s. agree. -/
theorem ae_canon_strictSet_iff {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hcone : IsConeField γ P hC hcirc μ) :
    ∀ᵐ x ∂(P.map (canonMap hC hcirc)), (x.1 ∈ StrictSet γ ↔ x.1 ∈ StrictCode γ) := by
  have hc := isConeField_canon hcone
  filter_upwards [ae_exists_strict_iff_strictTest hγ hγ2 hc (ρ := 1) (by norm_num), hc.2.2] with x hx hlim
  have he : codeOf γ 1 x.1 = diskMeasOf 1 (limitMeasure γ x.1) := codeOf_eq (y := x.1) le_rfl hlim
  show _ ↔ StrictTest 1 (codeOf γ 1 x.1)
  rw [he]
  exact hx

/-- **The family of Lemma 2.4 is a measurable functional of the field.** -/
theorem coneHalfBallFamilyFunctionalStep_holds : ConeHalfBallFamilyFunctionalStep := by
  intro γ hγ hγ2
  refine ⟨restrictDense ⁻¹' StrictSet γ, fun x => codeFamilyProcess 1 (codeOf γ 1 (restrictDense x)), ?_, ?_⟩
  · intro Ω _ P hC hcirc μ hcone
    have hQ := hcone.2.1
    have hP : IsProbabilityMeasure P := hcone.1
    have hcm : Measurable fun ω => circleProcess (hcirc ω) :=
      measurable_pi_iff.2 fun p => hQ.measurable_circle p.1 p.2 p.1.2
    set m := P.map fun ω => circleProcess (hcirc ω) with hm
    refine ⟨?_, ((measurable_codeFamilyProcess one_pos).comp
      ((measurable_codeOf γ 1).comp measurable_restrictDense)).aemeasurable⟩
    have he := measurable_canonMap hQ.measurable_pairing hQ.measurable_circle
    have : IsProbabilityMeasure (P.map (canonMap hC hcirc)) :=
      (Measure.isProbabilityMeasure_map_iff he.aemeasurable).2 hP
    -- the values where the two sets differ are null for the law of `y`
    set S : Set DenseCircle := {y | ¬(y ∈ StrictSet γ ↔ y ∈ StrictCode γ)} with hSdef
    have hS : (P.map (canonMap hC hcirc)).map Prod.fst S = 0 := by
      refine map_fst_apply_eq_zero ?_
      filter_upwards [ae_canon_strictSet_iff hγ hγ2 hcone] with x hx
      exact fun h => h hx
    have hmap : (P.map (canonMap hC hcirc)).map Prod.fst = m.map restrictDense := by
      rw [Measure.map_map measurable_fst he, hm, Measure.map_map measurable_restrictDense hcm]
      rfl
    rw [hmap] at hS
    set T := toMeasurable (m.map restrictDense) S with hTdef
    have hT : m (restrictDense ⁻¹' T) = 0 := by
      rw [← Measure.map_apply measurable_restrictDense (measurableSet_toMeasurable _ _), measure_toMeasurable]
      exact hS
    have hae : ∀ᵐ x ∂m, restrictDense x ∉ T := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => not_not.1 hx) hT
    refine (measurable_restrictDense (measurableSet_strictCode γ)).nullMeasurableSet.congr
      (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hae] with x hx
    have hxS : restrictDense x ∉ S := fun h => hx (subset_toMeasurable _ _ h)
    rw [hSdef, mem_setOf_eq, not_not] at hxS
    exact hxS.symm
  · intro c hc ν hν
    have hy : IsLQGLimit γ (extend (restrictDense (circleProcess c))) ν := isLQGLimit_extend_restrictDense hc hν
    have hlim : limitMeasure γ (restrictDense (circleProcess c)) = ν := limitMeasure_eq hy
    have : IsLocallyFiniteMeasure ν := hν.isLocallyFiniteMeasure
    refine ⟨?_, fun T Λ h => ?_⟩
    · show (∃ (T : ℝ) (Λ : ℝ → Set ℂ), IsStrictHalfBallFamily (limitMeasure γ _) Λ T) ↔ _
      rw [hlim]
    · show familyProcess Λ T = codeFamilyProcess 1 (codeOf γ 1 (restrictDense (circleProcess c)))
      rw [codeOf_eq le_rfl hy]
      exact familyProcess_eq_codeFamilyProcess (by norm_num) h.2.1 h.2.2.1 (strict_closure_subset h)

end ConeFamilyFunctional

end MatedCRT
