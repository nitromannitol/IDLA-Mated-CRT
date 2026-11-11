import MatedCRT.FirstPass.S4d.GlobalMeasurable
import MatedCRT.FirstPass.S4d.RescaleGap
import MatedCRT.FirstPass.S4d.RegDecode
import MatedCRT.Proofs.Measurability.ConeRescaledCircle

/-!
# Measurability of the rescaled whole process (FIRST PASS, S4d)

The rescaled pair of Lemma 2.6, `(circleProcess (rescaledCircle … R_b …), globalFamilyProcess (rescaledFamily (Λ ω) R_b b))`,
is a.e. measurable. The rescaled family is decoded from a measurable version of the global family at the random point
`R̃ ω * p.2` (`mem_iff_proxy_of_regular`, `measurableSet_exists_proxy`), using that `x ∈ R⁻¹ Λ_{bt}` iff `R x ∈ Λ_{bt}`.
The circle part is `coneRescaledCircleAEMeasurableStep_of_pos`. Uses B2 (`coneGlobalFamilyAEMeasurable_of_stopped`).
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- The decoded rescaled family: `p ∈ R⁻¹ Λ_{b p.1}` tested by countable balls at the point `R ω * p.2`. -/
def rescaledProc {Ω : Type*} (D : Set ℂ) (Gm : Ω → ℝ × ℂ → Prop) (Rm : Ω → ℝ) (b : ℝ) (ω : Ω)
    (p : ℝ × ℂ) : Prop :=
  0 < p.1 ∧ ∃ q ∈ D, ∃ r : ℚ, 0 < r ∧ (Rm ω : ℂ) * p.2 ∈ closedBall q (r : ℝ) ∧
    ProxySub D (famOf (Gm ω) (b * p.1)) q (r : ℝ)

/-- **B2R: the rescaled pair is a.e. measurable** (for each deterministic `b > 0`), in the existence form
`ConeStoppedBaseExistsFP4` of Lemma 2.4 (FirstPass/S4d/GlobalMeasurable.lean), which the provider
`ConeHarmonicBallsProviderFP4` gives by `coneStoppedBaseExists_of_provider`. The Draft wrapper is at the end of the file. -/
theorem coneRescaledGlobalFamilyAEMeasurable_of_exists {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hF : IsConeField γ P hC hcirc μ)
    (hexist : ConeStoppedBaseExistsFP4) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (hpos : ConeScaleRadiusPosStep)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) {b : ℝ} (hb : 0 < b) :
    AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
      globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hQC : IsQuantumCone γ P hC hcirc := hF.2.1
  have hG : AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P :=
    coneGlobalFamilyAEMeasurable_of_exists hγ hγ2 hF hexist h25 hfam hpos Λ hΛ
  have hgs : AEMeasurable (fun ω => globalFamilyProcess (Λ ω)) P := hG.snd
  have hcirc' : AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b)) P :=
    coneRescaledCircleAEMeasurableStep_of_pos hpos γ hγ hγ2 Ω P hC hcirc μ hF b hb
  -- measurable versions of the global family process and of the scale radius
  obtain ⟨Gm, hGm, hGae⟩ : ∃ G : Ω → ℝ × ℂ → Prop, Measurable G ∧
      (fun ω => globalFamilyProcess (Λ ω)) =ᵐ[P] G :=
    ⟨hgs.mk _, hgs.measurable_mk, hgs.ae_eq_mk⟩
  have hRae0 := aemeasurable_coneScaleRadius hQC b
  obtain ⟨Rm, hRm, hRae⟩ : ∃ R : Ω → ℝ, Measurable R ∧
      (fun ω => coneScaleRadius γ (hcirc ω) b) =ᵐ[P] R :=
    ⟨hRae0.mk _, hRae0.measurable_mk, hRae0.ae_eq_mk⟩
  have hcoordG : ∀ (s : ℝ) (d : ℂ), MeasurableSet {ω | d ∈ famOf (Gm ω) s} := fun s d =>
    measurableSet_setOfPred.2 ((measurable_pi_apply (s, d)).comp hGm)
  -- the decoded rescaled process is measurable
  have hset : ∀ p : ℝ × ℂ, MeasurableSet {ω | rescaledProc D Gm Rm b ω p} := by
    intro p
    by_cases hp : 0 < p.1
    · have hset' : {ω | rescaledProc D Gm Rm b ω p} = {ω | ∃ q ∈ D, ∃ r : ℚ, 0 < r ∧
          (Rm ω : ℂ) * p.2 ∈ closedBall q (r : ℝ) ∧ ProxySub D (famOf (Gm ω) (b * p.1)) q (r : ℝ)} := by
        ext ω
        simp only [rescaledProc, hp, true_and, mem_ofPred_eq]
      rw [hset']
      have hw : Measurable (fun ω => (Rm ω : ℂ) * p.2) :=
        (Complex.measurable_ofReal.comp hRm).mul_const _
      exact measurableSet_exists_proxy hDc (U := fun ω => famOf (Gm ω) (b * p.1))
        (fun d _ => hcoordG (b * p.1) d) hw
    · have hset' : {ω | rescaledProc D Gm Rm b ω p} = ∅ := by
        ext ω
        simp [rescaledProc, hp]
      rw [hset']
      exact MeasurableSet.empty
  have hRPm : Measurable (rescaledProc D Gm Rm b) :=
    measurable_pi_iff.2 fun p => measurableSet_setOfPred.1 (hset p)
  -- the a.e. identity with the rescaled global family process
  have hconf : ∀ᵐ ω ∂P, ∀ p : ℝ × ℂ, rescaledProc D Gm Rm b ω p ↔
      globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) p := by
    filter_upwards [hΛ, hGae, hRae] with ω hΛω hGω hRω
    intro p
    have hRω' : coneScaleRadius γ (hcirc ω) b = Rm ω := hRω
    have hGω' : globalFamilyProcess (Λ ω) = Gm ω := hGω
    by_cases hp : 0 < p.1
    · have hs : 0 < b * p.1 := mul_pos hb hp
      obtain ⟨-, hopen, hreg⟩ := goodFamily_of_isConeHarmonicBallFamily hΛω
      have hfam_eq : famOf (Gm ω) (b * p.1) = Λ ω (b * p.1) := by
        rw [← hGω', famOf_globalFamilyProcess hs]
      have key : (∃ q ∈ D, ∃ r : ℚ, 0 < r ∧ (Rm ω : ℂ) * p.2 ∈ closedBall q (r : ℝ) ∧
          ProxySub D (Λ ω (b * p.1)) q (r : ℝ)) ↔ (Rm ω : ℂ) * p.2 ∈ Λ ω (b * p.1) :=
        (mem_iff_proxy_of_regular hDd (hopen _ hs) (hreg _ hs) _).symm
      show (0 < p.1 ∧ ∃ q ∈ D, ∃ r : ℚ, 0 < r ∧ (Rm ω : ℂ) * p.2 ∈ closedBall q (r : ℝ) ∧
          ProxySub D (famOf (Gm ω) (b * p.1)) q (r : ℝ)) ↔
        (0 < p.1 ∧ (coneScaleRadius γ (hcirc ω) b : ℂ) * p.2 ∈ Λ ω (b * p.1))
      rw [hfam_eq, hRω']
      exact and_congr_right fun _ => key
    · exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 hp⟩
  have hfamAE : AEMeasurable (fun ω => globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b)) P := by
    refine (hRPm.aemeasurable).congr ?_
    filter_upwards [hconf] with ω hω
    funext p
    exact propext (hω p)
  exact hcirc'.prodMk hfamAE

/-- **B2R with the Draft Lemma 2.4 (`coneRescaledGlobalFamilyAEMeasurable_of_stopped`, signature unchanged for
FixedTimeFinal.lean:30 and S2z.lean:73).** The Draft is used only through `coneStoppedBaseExists_of_draft`. -/
theorem coneRescaledGlobalFamilyAEMeasurable_of_stopped {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hF : IsConeField γ P hC hcirc μ)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (hpos : ConeScaleRadiusPosStep)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) {b : ℝ} (hb : 0 < b) :
    AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
      globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))) P :=
  coneRescaledGlobalFamilyAEMeasurable_of_exists hγ hγ2 hF (coneStoppedBaseExists_of_draft h24) h25 hfam hpos Λ hΛ hb

end MatedCRT
