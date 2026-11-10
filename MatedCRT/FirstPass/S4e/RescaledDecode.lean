import MatedCRT.FirstPass.S4d.RescaledMeasurable

/-!
# B2R from B2: the decoded rescaled global family is a.e. measurable (FIRST PASS, S4e)

Operator task fp-S4e-4-2-rescaled-pair-measurable (ChatGPT answer `CHATGPT-q4-hnj-B1-B2.md` §5).
This is the argument of `coneRescaledGlobalFamilyAEMeasurable_of_stopped` (S4d/RescaledMeasurable.lean), with its
input "the global family process is a.e. measurable" (B2) taken as the hypothesis `hgs`, instead of being derived from
the stopped inputs `h24 h25 hfam hpos`. The decoding uses `rescaledProc` (S4d/RescaledMeasurable),
`measurableSet_exists_proxy` and `mem_iff_proxy_of_regular` (S4d/RegDecode), `famOf_globalFamilyProcess` and
`goodFamily_of_isConeHarmonicBallFamily` (S4d/RescaleGap), `aemeasurable_coneScaleRadius` (Proofs/Measurability).
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT.FirstPass.S4e

/-- **Rescaled global family process is a.e. measurable.** For `b > 0`, if `ω ↦ globalFamilyProcess (Λ ω)` is a.e.
measurable (B2), then so is `ω ↦ globalFamilyProcess (rescaledFamily (Λ ω) R_b b)`, where `R_b = coneScaleRadius γ (hcirc ω) b`.
The random spatial scaling is decoded at the point `R_b ω * p.2`, using a countable dense set of centres and radii. -/
theorem aemeasurable_rescaledGlobalFamilyProcess {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQC : IsQuantumCone γ P hC hcirc)
    {μ : Ω → Measure ℂ} (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hgs : AEMeasurable (fun ω => globalFamilyProcess (Λ ω)) P) {b : ℝ} (hb : 0 < b) :
    AEMeasurable (fun ω => globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b)) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
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
  refine (hRPm.aemeasurable).congr ?_
  filter_upwards [hconf] with ω hω
  funext p
  exact propext (hω p)

end MatedCRT.FirstPass.S4e
