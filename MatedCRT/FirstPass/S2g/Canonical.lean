import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.ScaleInvariance
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Measurability.ConeRescaledCircle

/-! # Corrected Lemmas 2.4 and 2.5 from the canonical factorization

The canonical statements `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` (2.4) and
`ConeScaleInvarianceUpToFixedTimeCanonicalStmt` (2.5) of `FirstPass/S2g.lean` are proved here from one hypothesis,
`ConeCanonicalFactorStep`: on a measurable set `G` of circle average processes of full cone law, the canonical half-ball
time, its stopped family and the space-time process of every stopped family are measurable functionals of the circle
process (the stopped analogue of `ConeGlobalFamilyFactorStep`, `FirstPass/S2g/ScaleInvariance.lean`).

Argument for the step (Theorem 1, formulas (4), (7), (8)), with the
good local support: Theorem 1 identifies the stopping time of an
arbitrary stopped family with the closure-based first time `τ(c)`; equality with the open-containment `halfBallTime` needs
the no-plateau property at `1/2` (the closure route, `ConeHalfBallClosureInsideStep`). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- **Named hypothesis (see docs/campaign/COUNTED.md): canonical factorization on the cone-law support.** There are
measurable maps `ΨT` (canonical time) and `Ψ` (space-time process) of circle average processes and a measurable set `G` of
full cone law such that, for every continuous `c` with `circleProcess c ∈ G` and every LQG limit `ν` of `c`:
(i) `halfBallTime ν = ΨT (circleProcess c)`; (ii) there is a canonical stopped family for `ν`, with positive time;
(iii) every stopped family `(T, Λ)` for `ν` has `familyProcess Λ T = Ψ (circleProcess c)`. For a cone field, `ΨT` and `Ψ`
are a.e. measurable for the law of the circle process and the circle process lies in `G` almost surely. -/
def ConeCanonicalFactorStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ (ΨT : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (Ψ : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop) (G : Set (Ioi (0 : ℝ) × ℂ → ℝ)),
    MeasurableSet G ∧
    (∀ c : ℝ → ℂ → ℝ, circleProcess c ∈ G → ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ) →
      ∀ ν : Measure ℂ, IsLQGLimit γ c ν →
        halfBallTime ν = ΨT (circleProcess c) ∧
        (∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn ν Λ (halfBallTime ν) ∧ IsStoppedAtHalfBall Λ (halfBallTime ν)) ∧
        0 < halfBallTime ν ∧
        ∀ (T : ℝ) (Λ : ℝ → Set ℂ), 0 < T → IsConeHarmonicBallFamilyOn ν Λ T → IsStoppedAtHalfBall Λ T →
          familyProcess Λ T = Ψ (circleProcess c)) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      AEMeasurable ΨT (P.map fun ω => circleProcess (hcirc ω)) ∧
      AEMeasurable Ψ (P.map fun ω => circleProcess (hcirc ω)) ∧ ∀ᵐ ω ∂P, circleProcess (hcirc ω) ∈ G

/-- Rescaling a stopped family for `rescaledMeasure μ R b` gives a family for `μ` on `(0, bT)`. -/
theorem rescaledFamily_transfer_fp {μ : Measure ℂ} {R b T : ℝ} {Λ : ℝ → Set ℂ} (hR : 0 < R) (hb : 0 < b)
    (h : IsConeHarmonicBallFamilyOn (rescaledMeasure μ R b) Λ T) (hst : IsStoppedAtHalfBall Λ T) :
    IsConeHarmonicBallFamilyOn μ (rescaledFamily Λ R⁻¹ b⁻¹) (b * T) ∧
      IsStoppedAtHalfBall (rescaledFamily (rescaledFamily Λ R⁻¹ b⁻¹) R b) T ∧
      ∀ Λ'' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn μ Λ'' (b * T) →
        EqOn Λ'' (rescaledFamily Λ R⁻¹ b⁻¹) (Ioo 0 (b * T)) := by
  have h1 : IsConeHarmonicBallFamilyOn (rescaledMeasure μ R b) Λ (b⁻¹ * (b * T)) := by
    rwa [inv_mul_cancel_left₀ hb.ne']
  have h2 := coneHarmonicBallFamilyOnScalingStep (rescaledMeasure μ R b) Λ R⁻¹ b⁻¹ (b * T)
    (inv_pos.2 hR) (inv_pos.2 hb) h1
  rw [rescaledMeasure_rescaledMeasure_inv μ hR.ne' hb] at h2
  refine ⟨h2, ?_, fun Λ'' hΛ'' => ?_⟩
  · rw [rescaledFamily_rescaledFamily_inv Λ hR.ne' hb.ne']
    exact hst
  · have := h2.eqOn hΛ''
    rwa [min_self] at this

/-- **Corrected Lemma 2.4 from the canonical factorization.** The canonical time is `ΨT` of the circle process
and the canonical family's process is `Ψ` of it, almost surely: this gives both measurability claims with no closure step. -/
theorem firstPass_2_4_canonical_of_factor (hfac : ConeCanonicalFactorStep) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨ΨT, Ψ, G, hGm, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨hΨT, hΨ, hGc⟩ := hfull Ω P hC hcirc μ hcone
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  have hkey : ∀ᵐ ω ∂P, halfBallTime (μ ω) = ΨT (circleProcess (hcirc ω)) ∧
      (∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (μ ω) Λ (halfBallTime (μ ω)) ∧
        IsStoppedAtHalfBall Λ (halfBallTime (μ ω))) ∧ 0 < halfBallTime (μ ω) ∧
      ∀ (T : ℝ) (Λ : ℝ → Set ℂ), 0 < T → IsConeHarmonicBallFamilyOn (μ ω) Λ T → IsStoppedAtHalfBall Λ T →
        familyProcess Λ T = Ψ (circleProcess (hcirc ω)) := by
    filter_upwards [hGc, hcone.2.1.ae_continuousOn_circle, hcone.2.2] with ω hg hc hl
    exact hchar (hcirc ω) hg hc (μ ω) hl
  let x : Ω → ℝ → Set ℂ := fun ω => Classical.epsilon fun Λ : ℝ → Set ℂ =>
    IsConeHarmonicBallFamilyOn (μ ω) Λ (halfBallTime (μ ω)) ∧ IsStoppedAtHalfBall Λ (halfBallTime (μ ω))
  have hx : ∀ᵐ ω ∂P, 0 < halfBallTime (μ ω) ∧ IsConeHarmonicBallFamilyOn (μ ω) (x ω) (halfBallTime (μ ω)) ∧
      IsStoppedAtHalfBall (x ω) (halfBallTime (μ ω)) := by
    filter_upwards [hkey] with ω hω
    obtain ⟨-, ⟨Λ, hΛ⟩, hp, -⟩ := hω
    exact ⟨hp, Classical.epsilon_spec (p := fun Λ : ℝ → Set ℂ => IsConeHarmonicBallFamilyOn (μ ω) Λ
      (halfBallTime (μ ω)) ∧ IsStoppedAtHalfBall Λ (halfBallTime (μ ω))) ⟨Λ, hΛ⟩⟩
  have hT : AEMeasurable (fun ω => halfBallTime (μ ω)) P := by
    refine (hΨT.comp_aemeasurable hmeasc).congr ?_
    filter_upwards [hkey] with ω hω
    exact hω.1.symm
  have hJ : AEMeasurable (fun ω => familyProcess (x ω) (halfBallTime (μ ω))) P := by
    refine (hΨ.comp_aemeasurable hmeasc).congr ?_
    filter_upwards [hkey, hx] with ω hω hx'
    exact (hω.2.2.2 _ _ hx'.1 hx'.2.1 hx'.2.2).symm
  refine ⟨hT, x, hmeasc.prodMk hJ, ?_⟩
  filter_upwards [hx] with ω hω
  exact ⟨hω.1, uniqueConeFamilyOn_of_family hω.2.1, hω.2.2⟩

/-- **Corrected Lemma 2.5 from the canonical factorization.** The rescaled canonical time `Tb = halfBallTime ν`
is `ΨT` of the rescaled circle process, the family `Λb` is the inverse rescaling of the canonical family of `ν`
(`rescaledFamily_transfer_fp`), and the joint laws agree since both processes are `Ψ` of the circle process, which has the
same law before and after rescaling (`QuantumConeScalingInput`). -/
theorem firstPass_2_5_canonical_of_factor (hfac : ConeCanonicalFactorStep) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) : ConeScaleInvarianceUpToFixedTimeCanonicalStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ b hb
  have hP : IsProbabilityMeasure P := hcone.1
  have hpos := coneScaleRadiusPosStep_of_input hscale
  obtain ⟨ΨT, Ψ, G, hGm, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨hΨT, hΨ, hGc⟩ := hfull Ω P hC hcirc μ hcone
  have hcont := hcone.2.1.ae_continuousOn_circle
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  have hmeasb := coneRescaledCircleAEMeasurableStep_of_pos hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hlaw := hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb
  have hlqg := coneLQGScalingStep_of_steps h22 hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hGb : ∀ᵐ ω ∂P, circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) ∈ G :=
    ae_mem_of_law_eq_measurable hGm hmeasc hmeasb hlaw hGc
  have hkeyA : ∀ᵐ ω ∂P, halfBallTime (μ ω) = ΨT (circleProcess (hcirc ω)) ∧
      (∃ Λ' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (μ ω) Λ' (halfBallTime (μ ω)) ∧
        IsStoppedAtHalfBall Λ' (halfBallTime (μ ω))) ∧ 0 < halfBallTime (μ ω) ∧
      ∀ (T : ℝ) (Λ' : ℝ → Set ℂ), 0 < T → IsConeHarmonicBallFamilyOn (μ ω) Λ' T → IsStoppedAtHalfBall Λ' T →
        familyProcess Λ' T = Ψ (circleProcess (hcirc ω)) := by
    filter_upwards [hGc, hcont, hcone.2.2] with ω hg hc hl
    exact hchar (hcirc ω) hg hc (μ ω) hl
  have hkeyB : ∀ᵐ ω ∂P, halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) =
      ΨT (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) ∧
      (∃ Λ' : ℝ → Set ℂ,
        IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) Λ'
          (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)) ∧
        IsStoppedAtHalfBall Λ' (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b))) ∧
      0 < halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
      ∀ (T : ℝ) (Λ' : ℝ → Set ℂ), 0 < T →
        IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) Λ' T →
        IsStoppedAtHalfBall Λ' T →
        familyProcess Λ' T = Ψ (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
    filter_upwards [hGb, hcont, hlqg] with ω hg hc hs
    exact hchar _ hg (continuousOn_rescaledCircle hc hs.1) _ hs.2
  intro R ν Tb
  have hνω : ∀ ω, ν ω = rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b := fun ω => by
    simp only [ν, R, rescaledMeasure, div_eq_inv_mul]
  have hTω : ∀ ω, Tb ω = halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) := fun ω => by
    simp only [Tb, hνω]
  refine ⟨?_, ?_⟩
  · have h1 : AEMeasurable ΨT (P.map fun ω =>
        circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
      rw [hlaw]
      exact hΨT
    refine (h1.comp_aemeasurable hmeasb).congr ?_
    filter_upwards [hkeyB] with ω hω
    rw [hTω ω]
    exact hω.1.symm
  · let x2 : Ω → ℝ → Set ℂ := fun ω => Classical.epsilon fun Λ' : ℝ → Set ℂ =>
      IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) Λ'
        (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)) ∧
      IsStoppedAtHalfBall Λ' (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b))
    have hx2 : ∀ᵐ ω ∂P, 0 < halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
        IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (x2 ω)
          (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)) ∧
        IsStoppedAtHalfBall (x2 ω)
          (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
      filter_upwards [hkeyB] with ω hω
      obtain ⟨-, ⟨Λ', hΛ'⟩, hp, -⟩ := hω
      exact ⟨hp, Classical.epsilon_spec (p := fun Λ'' : ℝ → Set ℂ =>
        IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) Λ''
          (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)) ∧
        IsStoppedAtHalfBall Λ'' (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)))
        ⟨Λ', hΛ'⟩⟩
    have hback : ∀ᵐ ω ∂P, 0 < Tb ω ∧
        UniqueConeFamilyOn (μ ω) (rescaledFamily (x2 ω) (coneScaleRadius γ (hcirc ω) b)⁻¹ b⁻¹) (b * Tb ω) ∧
        IsStoppedAtHalfBall (rescaledFamily (rescaledFamily (x2 ω) (coneScaleRadius γ (hcirc ω) b)⁻¹ b⁻¹)
          (coneScaleRadius γ (hcirc ω) b) b) (Tb ω) := by
      filter_upwards [hx2, hlqg] with ω hω hs
      obtain ⟨c1, c2, c3⟩ := rescaledFamily_transfer_fp hs.1 hb hω.2.1 hω.2.2
      rw [hTω ω]
      exact ⟨hω.1, ⟨c1, c3⟩, c2⟩
    refine ⟨fun ω => rescaledFamily (x2 ω) (coneScaleRadius γ (hcirc ω) b)⁻¹ b⁻¹, hback, ?_⟩
    intro J Jb
    have hF : ∀ᵐ ω ∂P, familyProcess (Λ ω) (halfBallTime (μ ω)) = Ψ (circleProcess (hcirc ω)) := by
      filter_upwards [hkeyA, hΛ] with ω hA hΛω
      exact hA.2.2.2 _ _ hΛω.1 hΛω.2.1 hΛω.2.2
    have hG : ∀ᵐ ω ∂P, familyProcess (rescaledFamily (rescaledFamily (x2 ω) (coneScaleRadius γ (hcirc ω) b)⁻¹ b⁻¹)
          (coneScaleRadius γ (hcirc ω) b) b) (Tb ω) =
        Ψ (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
      filter_upwards [hkeyB, hback, hlqg] with ω hB hbk hs
      have hT := hTω ω
      have hcoh := coneHarmonicBallFamilyOnScalingStep (μ ω) (rescaledFamily (x2 ω)
        (coneScaleRadius γ (hcirc ω) b)⁻¹ b⁻¹) (coneScaleRadius γ (hcirc ω) b) b (Tb ω) hs.1 hb hbk.2.1.1
      have hst := hbk.2.2
      rw [hT] at hcoh hst
      rw [hT]
      exact hB.2.2.2 _ _ hB.2.2.1 hcoh hst
    have hFm : AEMeasurable (fun ω => familyProcess (Λ ω) (halfBallTime (μ ω))) P :=
      (hΨ.comp_aemeasurable hmeasc).congr (by filter_upwards [hF] with ω h; exact h.symm)
    have hΨb : AEMeasurable Ψ (P.map fun ω =>
        circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
      rw [hlaw]
      exact hΨ
    have hGm' : AEMeasurable (fun ω => familyProcess (rescaledFamily (rescaledFamily (x2 ω)
        (coneScaleRadius γ (hcirc ω) b)⁻¹ b⁻¹) (coneScaleRadius γ (hcirc ω) b) b) (Tb ω)) P :=
      (hΨb.comp_aemeasurable hmeasb).congr (by filter_upwards [hG] with ω h; exact h.symm)
    refine ⟨hmeasc.prodMk hFm, hmeasb.prodMk hGm', ?_⟩
    exact map_prod_eq_of_ae_eq hmeasc hmeasb hlaw hΨ hF hG
