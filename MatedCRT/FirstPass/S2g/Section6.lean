import MatedCRT.FirstPass.S2g.Canonical
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfConeFamily

/-! # Lemma 2.4 (Draft form), measurability step and Proposition 6.1 from the canonical factorization

The Section 6 chain (`Proofs/Sec6/IDLAUpperBound/OfConeFamily.lean:16`) takes two hypotheses: the Draft statement
`ConeHarmonicBallsUpToFixedTimeStmt` (with the clause `T' = T`, `Draft/Section2.lean:66-72`) and the measurability step
`ConeFamilyAEMeasurableStep` (`Steps/Sec2/ConeHarmonicBalls.lean:31`). Both follow from the canonical factorization
`ConeCanonicalFactorStep` (`FirstPass/S2g/Canonical.lean`) with no closure step:

* the clause `T' = T` and `EqOn` come from the equality of the space-time processes, since the centre `0` lies in every
  `Λ_t`, `0 < t < T`, so `(t, 0) ∈ familyProcess Λ T` iff `t < T`;
* the measurability step is the a.e. measurability of `ω ↦ (circle, Ψ ∘ circle)`, using that the rescaled circle process
  has the same law (`QuantumConeScalingInput`). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

/-- Two stopped cone families whose space-time processes agree have the same stopping time and agree on the common
interval (deterministic). The centre `0` lies in every `Λ_t`, `0 < t < T`, so `(t, 0) ∈ familyProcess Λ T` iff `t < T`. -/
theorem stopped_eq_of_familyProcess_eq {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {T T' : ℝ}
    (hΛ : IsConeHarmonicBallFamilyOn μ Λ T) (hΛ' : IsConeHarmonicBallFamilyOn μ Λ' T')
    (hT : 0 < T) (hT' : 0 < T') (hF : familyProcess Λ T = familyProcess Λ' T') :
    T' = T ∧ EqOn Λ' Λ (Ioo 0 T) := by
  have hTT : T' = T := by
    rcases lt_trichotomy T T' with h | h | h
    · exfalso
      have h2 : familyProcess Λ' T' (T, 0) :=
        ⟨⟨hT, h⟩, hΛ'.2.1.mem T ⟨hT, h⟩⟩
      have h3 : familyProcess Λ T (T, 0) := by
        rw [hF]
        exact h2
      exact lt_irrefl T h3.1.2
    · exact h.symm
    · exfalso
      have h2 : familyProcess Λ T (T', 0) :=
        ⟨⟨hT', h⟩, hΛ.2.1.mem T' ⟨hT', h⟩⟩
      have h3 : familyProcess Λ' T' (T', 0) := by
        rw [← hF]
        exact h2
      exact lt_irrefl T' h3.1.2
  refine ⟨hTT, ?_⟩
  intro t ht
  ext x
  have hiff := (congrFun hF (t, x)).to_iff
  rw [hTT] at hiff
  constructor
  · intro hx
    exact (hiff.mpr ⟨ht, hx⟩).2
  · intro hx
    exact (hiff.mp ⟨ht, hx⟩).2

/-- **Draft Lemma 2.4 from the canonical factorization.** The stopping time is `halfBallTime`, the canonical
family is `x ω`, and any stopped family has the same stopping time and agrees with it on `(0, T)`, by the process equality of
`ConeCanonicalFactorStep` (iii) and `stopped_eq_of_familyProcess_eq`. -/
theorem coneHarmonicBallsUpToFixedTimeStmt_of_factor (hfac : ConeCanonicalFactorStep) :
    ConeHarmonicBallsUpToFixedTimeStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨ΨT, Ψ, G, hGm, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨-, -, hGc⟩ := hfull Ω P hC hcirc μ hcone
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
    exact ⟨hp, (Classical.epsilon_spec (p := fun Λ : ℝ → Set ℂ =>
      IsConeHarmonicBallFamilyOn (μ ω) Λ (halfBallTime (μ ω)) ∧
        IsStoppedAtHalfBall Λ (halfBallTime (μ ω))) ⟨Λ, hΛ⟩).1,
      (Classical.epsilon_spec (p := fun Λ : ℝ → Set ℂ =>
      IsConeHarmonicBallFamilyOn (μ ω) Λ (halfBallTime (μ ω)) ∧
        IsStoppedAtHalfBall Λ (halfBallTime (μ ω))) ⟨Λ, hΛ⟩).2⟩
  filter_upwards [hkey, hx] with ω hω hx'
  refine ⟨halfBallTime (μ ω), hx'.1, x ω, hx'.2.1, hx'.2.2, fun T' Λ' hT' hΛ' hst' => ?_⟩
  have hF : familyProcess (x ω) (halfBallTime (μ ω)) = familyProcess Λ' T' :=
    (hω.2.2.2 _ _ hx'.1 hx'.2.1 hx'.2.2).trans (hω.2.2.2 T' Λ' hT' hΛ' hst').symm
  exact stopped_eq_of_familyProcess_eq hx'.2.1 hΛ' hx'.1 hT' hF

/-- **Measurability step `ConeFamilyAEMeasurableStep` from the canonical factorization.** Both conjuncts
(unscaled and rescaled families) are a.e. measurable: the space-time process of every stopped family is `Ψ` of the circle
process, almost surely, and `Ψ` is measurable for the law of the circle process; the rescaled family has the rescaled circle
process, whose law is the same (`QuantumConeScalingInput`). The rescaled stopped pair is a stopped pair for the rescaled
measure by `coneHarmonicBallFamilyOnScalingStep`. Needs the LQG limit property `LQGMeasurePropertiesStmt`. -/
theorem coneFamilyAEMeasurableStep_of_factor (hfac : ConeCanonicalFactorStep) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) : ConeFamilyAEMeasurableStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  have hP : IsProbabilityMeasure P := hcone.1
  have hpos := coneScaleRadiusPosStep_of_input hscale
  obtain ⟨ΨT, Ψ, G, hGm, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨-, hΨ, hGc⟩ := hfull Ω P hC hcirc μ hcone
  have hcont := hcone.2.1.ae_continuousOn_circle
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  constructor
  · intro T Λ hf
    have hkey : ∀ᵐ ω ∂P, familyProcess (Λ ω) (T ω) = Ψ (circleProcess (hcirc ω)) := by
      filter_upwards [hGc, hcont, hcone.2.2, hf] with ω hg hc hl hω
      exact (hchar (hcirc ω) hg hc (μ ω) hl).2.2.2 (T ω) (Λ ω) hω.1 hω.2.1 hω.2.2
    have hF : AEMeasurable (fun ω => familyProcess (Λ ω) (T ω)) P :=
      (hΨ.comp_aemeasurable hmeasc).congr (by filter_upwards [hkey] with ω h; exact h.symm)
    exact hmeasc.prodMk hF
  · intro b hb Tb Λb hf
    have hmeasb := coneRescaledCircleAEMeasurableStep_of_pos hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
    have hlaw := hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb
    have hlqg := coneLQGScalingStep_of_steps h22 hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
    have hGb : ∀ᵐ ω ∂P, circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) ∈ G :=
      ae_mem_of_law_eq_measurable hGm hmeasc hmeasb hlaw hGc
    have hkey : ∀ᵐ ω ∂P, familyProcess (rescaledFamily (Λb ω) (coneScaleRadius γ (hcirc ω) b) b) (Tb ω) =
        Ψ (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
      filter_upwards [hGb, hcone.2.1.ae_continuousOn_circle, hlqg, hf] with ω hg hc hs hω
      have hcoh := coneHarmonicBallFamilyOnScalingStep (μ ω) (Λb ω) (coneScaleRadius γ (hcirc ω) b) b (Tb ω)
        hs.1 hb hω.2.1
      exact (hchar _ hg (continuousOn_rescaledCircle hc hs.1) _ hs.2).2.2.2 (Tb ω) _ hω.1 hcoh hω.2.2
    have hΨb : AEMeasurable Ψ (P.map fun ω =>
        circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
      rw [hlaw]
      exact hΨ
    have hF : AEMeasurable (fun ω => familyProcess (rescaledFamily (Λb ω) (coneScaleRadius γ (hcirc ω) b) b)
        (Tb ω)) P :=
      (hΨb.comp_aemeasurable hmeasb).congr (by filter_upwards [hkey] with ω h; exact h.symm)
    exact hmeasb.prodMk hF

/-- **Proposition 6.1 from the canonical factorization.** The composition `iDLAUpperBound_of_coneFamilyAEMeasurable`
(`Proofs/Sec6/IDLAUpperBound/OfConeFamily.lean:16`) with the Draft Lemma 2.4 and the measurability step both derived from the
canonical factorization. Hypotheses: Lemma 6.10 (`IterativeBoundStmt`), Proposition 5.1 (`IDLALowerBoundStmt`), the quantum
cone scaling law, the LQG measure property, and `ConeCanonicalFactorStep` (NEW, OPEN). -/
theorem firstPass_6_1_of_factor (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hfac : ConeCanonicalFactorStep) : IDLAUpperBoundStmt 𝒮 :=
  iDLAUpperBound_of_coneFamilyAEMeasurable 𝒮 h610 h51 (coneFamilyAEMeasurableStep_of_factor hfac hscale h22)
    (coneHarmonicBallsUpToFixedTimeStmt_of_factor hfac)

end MatedCRT
