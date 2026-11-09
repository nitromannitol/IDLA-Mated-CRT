import MatedCRT.FirstPass.S2i.ProcessCode
import MatedCRT.FirstPass.S2i.GraphFactor
import MatedCRT.FirstPass.S2i.StoppedHorizon
import MatedCRT.FirstPass.S2i.CircleCode
import MatedCRT.FirstPass.S2i.FamilyCode
import MatedCRT.FirstPass.Frozen.S2i
import MatedCRT.FirstPass.S2g.Canonical
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.StoppedClosure

/-! # Canonical factorization on the cone-law support (FirstPass S2i, z2)

Proof of `ConeCanonicalFactorStep` (`FirstPass/S2g/Canonical.lean`) from the canonical Lemma 2.4 and the closure
containment of stopped families, with two EXTERNAL inputs (`FirstPass/Frozen/S2i.lean`): the cone circle law is unique in
law (`ConeCircleLawUniqueStep`) and a standard Borel reference cone exists (`ConeReferenceExistsStep`).

Route (notes/fp-gaps/CHATGPT-q1-open-steps.md Section 7, F1-F6): on a reference cone, the joint code
`J ω = (circleCode D (circleProcess (hcirc ω)), processCode (halfBallTime (μ ω)) (familyProcess (Λ ω) (halfBallTime (μ ω))))`
is measurable up to a null set; its values on a measurable full set form a graph over the circle code
(`processCode_eq_of_circleCode_eq`: equal circle codes give equal LQG measures, canonical times and processes); the Borel
factor `exists_canonical_factor` gives `B, F`; the witnesses are `G = circleCode D ⁻¹' B`, `ΨT p = (F (circleCode D p)).1`,
`Ψ p = decodeFamily (F (circleCode D p))`. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The deterministic fibre lemma: two cone samples with the same dense circle code have the same LQG measure, the same
canonical time and the same space-time process at their canonical horizon (`IsLQGLimit.unique`, `familyProcess_eq_of_family`).
Positive-radius agreement of continuous circle processes is `eq_of_circleCode_eq`. -/
theorem processCode_eq_of_circleCode_eq {γ : ℝ} {D : ℕ → CirclePt} (hD : DenseRange D)
    {μ μ' : Measure ℂ} {hc hc' : ℝ → ℂ → ℝ} {Λ Λ' : ℝ → Set ℂ}
    (hc_cont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ))
    (hc'_cont : ContinuousOn (fun p : ℝ × ℂ => hc' p.1 p.2) (Ioi 0 ×ˢ univ))
    (hL : IsLQGLimit γ hc μ) (hL' : IsLQGLimit γ hc' μ')
    (hf : IsConeHarmonicBallFamilyOn μ Λ (halfBallTime μ))
    (hf' : IsConeHarmonicBallFamilyOn μ' Λ' (halfBallTime μ'))
    (hcode : circleCode D (circleProcess hc) = circleCode D (circleProcess hc')) :
    processCode (halfBallTime μ) (familyProcess Λ (halfBallTime μ)) =
      processCode (halfBallTime μ') (familyProcess Λ' (halfBallTime μ')) := by
  have hcirc_eq : circleProcess hc = circleProcess hc' :=
    eq_of_circleCode_eq hD (continuous_circleProcess_of_continuousOn hc_cont)
      (continuous_circleProcess_of_continuousOn hc'_cont) hcode
  have hpt : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, hc' ε z = hc ε z := fun ε hε z =>
    (congrFun hcirc_eq (⟨ε, hε⟩, z)).symm
  have hμ : μ = μ' := hL.unique (isLQGLimit_congr hpt hL')
  subst hμ
  rw [familyProcess_eq_of_family hf hf']

/-- The good set of a reference cone sample: the closure containment of all stopped families (Section 5 closure step),
the canonical time is positive with a unique stopped family, and the circle average process is an LQG limit
and continuous on `(0,∞) × ℂ`. -/
def ConeRefGood {Ω : Type} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (Λ : Ω → ℝ → Set ℂ) (ω : Ω) :
    Prop :=
  (∀ (T : ℝ) (Λ' : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn (μ ω) Λ' T → IsStoppedAtHalfBall Λ' T →
      ∀ t ∈ Ioo 0 T, closure (Λ' t) ⊆ ball (0 : ℂ) (1 / 2)) ∧
    (0 < halfBallTime (μ ω) ∧ UniqueConeFamilyOn (μ ω) (Λ ω) (halfBallTime (μ ω)) ∧
      IsStoppedAtHalfBall (Λ ω) (halfBallTime (μ ω))) ∧
    IsLQGLimit γ (hcirc ω) (μ ω) ∧
    ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)

/-- The clauses of `ConeCanonicalFactorStep` for given witnesses `ΨT`, `Ψ`, `G` (the body of the step). -/
abbrev CanonicalFactorClauses (γ : ℝ) (ΨT : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (Ψ : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop) (G : Set (Ioi (0 : ℝ) × ℂ → ℝ)) : Prop :=
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

/-- **Code form of the canonical factor (FirstPass S2i, z2).** The witnesses of `ConeCanonicalFactorStep` can be taken
of the form `ΨT p = (F (circleCode D p)).1`, `Ψ p = decodeFamily (F (circleCode D p))`, `G = circleCode D ⁻¹' B` with
`F` measurable (the joint code of the Borel factor). Used by the global family step. -/
theorem coneCanonicalFactor_code_of (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ)
    (extra : Ω → Prop) (hextra : ∀ᵐ ω ∂P, extra ω) :
    ∃ (D : ℕ → CirclePt) (B : Set (ℕ → ℝ)) (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)),
      DenseRange D ∧ MeasurableSet B ∧ Measurable F ∧
      CanonicalFactorClauses γ (fun p => (F (circleCode D p)).1)
        (fun p => decodeFamily (F (circleCode D p))) ((circleCode D) ⁻¹' B) ∧
      ∀ x ∈ B, ∃ ω, extra ω ∧ circleCode D (circleProcess (hcirc ω)) = x := by
  have : IsProbabilityMeasure P := hcone.1
  obtain ⟨D, hD⟩ := exists_dense_circlePt
  obtain ⟨hTm, Λf, hQ, hgood2⟩ :=
    (firstPass_2_4_canonical_of_steps hcan hcl h27) γ hγ0 hγ2 Ω P hC hcirc μ hcone
  have hcl' := (hcl γ hγ0 hγ2 Ω P hC hcirc μ hcone)
  have hQc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P := hQ.fst
  have hJraw : AEMeasurable (fun ω => ((circleCode D (circleProcess (hcirc ω))),
      processCode (halfBallTime (μ ω)) (familyProcess (Λf ω) (halfBallTime (μ ω))))) P := by
    refine AEMeasurable.prodMk ((measurable_circleCode D).comp_aemeasurable hQc) ?_
    exact measurable_processCode.comp_aemeasurable (hTm.prodMk hQ.snd)
  obtain ⟨Jm, hJm, hJmae⟩ : ∃ Jm : Ω → (ℕ → ℝ) × (ℝ × (ℕ → ℕ → Bool)), Measurable Jm ∧
      (fun ω => ((circleCode D (circleProcess (hcirc ω))),
        processCode (halfBallTime (μ ω)) (familyProcess (Λf ω) (halfBallTime (μ ω))))) =ᵐ[P] Jm :=
    ⟨hJraw.mk _, hJraw.measurable_mk, hJraw.ae_eq_mk⟩
  have hgood : ∀ᵐ ω ∂P, ConeRefGood γ hcirc μ Λf ω ∧
      Jm ω = ((circleCode D (circleProcess (hcirc ω))),
        processCode (halfBallTime (μ ω)) (familyProcess (Λf ω) (halfBallTime (μ ω)))) ∧ extra ω := by
    have hL : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
    have hK : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) :=
      hcone.2.1.ae_continuousOn_circle
    filter_upwards [hcl', hgood2, hL, hK, hJmae, hextra] with ω h1 h2 h3 h4 h5 h6
    exact ⟨⟨h1, h2, h3, h4⟩, h5.symm, h6⟩
  obtain ⟨t, hNt, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hE0 : MeasurableSet tᶜ := htm.compl
  have hfull : P tᶜᶜ = 0 := by rw [compl_compl]; exact ht0
  have hgoodE0 : ∀ ω ∈ tᶜ, ConeRefGood γ hcirc μ Λf ω ∧
      Jm ω = ((circleCode D (circleProcess (hcirc ω))),
        processCode (halfBallTime (μ ω)) (familyProcess (Λf ω) (halfBallTime (μ ω)))) ∧ extra ω := by
    intro ω hω
    by_contra hn
    exact hω (hNt hn)
  have hgraph : ∀ ω ∈ tᶜ, ∀ ω' ∈ tᶜ, (Jm ω).1 = (Jm ω').1 → Jm ω = Jm ω' := by
    intro ω hω ω' hω' hfst
    obtain ⟨⟨-, ⟨hT0, huniq, hstop⟩, hL, hK⟩, hJe, -⟩ := hgoodE0 ω hω
    obtain ⟨⟨-, ⟨-, huniq', -⟩, hL', hK'⟩, hJe', -⟩ := hgoodE0 ω' hω'
    rw [hJe, hJe'] at hfst ⊢
    have hcode : circleCode D (circleProcess (hcirc ω)) = circleCode D (circleProcess (hcirc ω')) := hfst
    exact Prod.ext hcode (processCode_eq_of_circleCode_eq hD hK hK' hL hL' huniq.1 huniq'.1 hcode)
  obtain ⟨B, F, hB, hF, hBw, hBae⟩ := exists_canonical_factor P Jm hJm tᶜ hE0 hfull hgraph
  have hGm : MeasurableSet ((circleCode D) ⁻¹' B) := measurable_circleCode D hB
  refine ⟨D, B, F, hD, hB, hF, ⟨?_, ?_⟩, ?_⟩
  · intro c hcG hcc ν hν
    obtain ⟨ω, hωE0, hJω⟩ := hBw (circleCode D (circleProcess c)) hcG
    obtain ⟨⟨hclω, ⟨hT0, huniq, hstop⟩, hLω, hKω⟩, hJe, -⟩ := hgoodE0 ω hωE0
    have hpair := hJe.symm.trans hJω
    have hcode : circleCode D (circleProcess (hcirc ω)) = circleCode D (circleProcess c) :=
      congrArg Prod.fst hpair
    have hY : processCode (halfBallTime (μ ω)) (familyProcess (Λf ω) (halfBallTime (μ ω))) =
        F (circleCode D (circleProcess c)) := congrArg Prod.snd hpair
    have hcpeq : circleProcess c = circleProcess (hcirc ω) :=
      eq_of_circleCode_eq hD (continuous_circleProcess_of_continuousOn hcc)
        (continuous_circleProcess_of_continuousOn hKω) hcode.symm
    have hceq : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, c ε z = hcirc ω ε z := fun ε hε z =>
      congrFun hcpeq (⟨ε, hε⟩, z)
    have hLν : IsLQGLimit γ (hcirc ω) ν := isLQGLimit_congr hceq hν
    have hνμ : μ ω = ν := hLω.unique hLν
    subst hνμ
    have hT1 : halfBallTime (μ ω) = (F (circleCode D (circleProcess c))).1 := by
      rw [← hY]
      rfl
    have hΨ : decodeFamily (F (circleCode D (circleProcess c))) =
        familyProcess (Λf ω) (halfBallTime (μ ω)) := by
      rw [← hY, ← codeFamily_eq_processCode, decodeFamily_codeFamily_eq huniq.1.2.1]
    refine ⟨hT1, ⟨Λf ω, huniq.1, hstop⟩, hT0, ?_⟩
    intro T Λ _ hΛ hΛs
    have hTeq : T = halfBallTime (μ ω) :=
      stopped_horizon_unique hΛ hΛs huniq.1 hstop (hclω T Λ hΛ hΛs) (hclω _ _ huniq.1 hstop)
    subst hTeq
    show familyProcess Λ (halfBallTime (μ ω)) = decodeFamily (F (circleCode D (circleProcess c)))
    rw [hΨ]
    exact familyProcess_eq_of_family hΛ huniq.1
  · intro Ω' _ P' hC' hcirc' μ' hcone'
    obtain ⟨hTm', Λ', hQ', -⟩ :=
      (firstPass_2_4_canonical_of_steps hcan hcl h27) γ hγ0 hγ2 Ω' P' hC' hcirc' μ' hcone'
    have hQ'c : AEMeasurable (fun ω => circleProcess (hcirc' ω)) P' := hQ'.fst
    have hΨTm : Measurable fun p : Ioi (0 : ℝ) × ℂ → ℝ => (F (circleCode D p)).1 :=
      measurable_fst.comp (hF.comp (measurable_circleCode D))
    have hΨm : Measurable fun p : Ioi (0 : ℝ) × ℂ → ℝ => decodeFamily (F (circleCode D p)) :=
      measurable_decodeFamily.comp (hF.comp (measurable_circleCode D))
    refine ⟨hΨTm.aemeasurable, hΨm.aemeasurable, ?_⟩
    have hGref : ∀ᵐ ω ∂P, circleProcess (hcirc ω) ∈ (circleCode D) ⁻¹' B := by
      filter_upwards [hBae, hJmae] with ω h1 h2
      rw [← h2] at h1
      exact h1
    have h1 : ∀ᵐ y ∂(P.map (fun ω => circleProcess (hcirc ω))), y ∈ (circleCode D) ⁻¹' B :=
      (ae_map_iff hQc hGm).2 hGref
    have hlaw := hE1 γ hγ0 hγ2 Ω P hC hcirc μ hcone Ω' P' hC' hcirc' μ' hcone'
    rw [hlaw] at h1
    exact (ae_map_iff hQ'c hGm).1 h1
  · intro x hx
    obtain ⟨ω, hω, hJω⟩ := hBw x hx
    exact ⟨ω, (hgoodE0 ω hω).2.2, congrArg Prod.fst ((hgoodE0 ω hω).2.1.symm.trans hJω)⟩

/-- Code form of the canonical factor (FirstPass S2i, z2): the witnesses of `ConeCanonicalFactorStep` in code form,
for the reference cone of `ConeReferenceExistsStep`. -/
theorem coneCanonicalFactor_code (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ (D : ℕ → CirclePt) (B : Set (ℕ → ℝ)) (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)),
      DenseRange D ∧ MeasurableSet B ∧ Measurable F ∧
      CanonicalFactorClauses γ (fun p => (F (circleCode D p)).1)
        (fun p => decodeFamily (F (circleCode D p))) ((circleCode D) ⁻¹' B) := by
  obtain ⟨Ω, _, hSB, P, hC, hcirc, μ, hcone⟩ := hE2 γ hγ0 hγ2
  obtain ⟨D, B, F, h1, h2, h3, h4, -⟩ := coneCanonicalFactor_code_of hcan hcl h27 hE1 γ hγ0 hγ2 Ω P hC
    hcirc μ hcone (fun _ => True) (ae_of_all P fun _ => trivial)
  exact ⟨D, B, F, h1, h2, h3, h4⟩

/-- **`ConeCanonicalFactorStep` (FirstPass S2i, z2).** From the canonical Lemma 2.4 (`firstPass_2_4_canonical_of_steps`),
the closure step `ConeHalfBallClosureInsideStep`, the volume growth statement, and the two frozen cone externals. -/
theorem coneCanonicalFactor_proved (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) :
    ConeCanonicalFactorStep := by
  intro γ hγ0 hγ2
  obtain ⟨D, B, F, -, hB, -, hcls⟩ := coneCanonicalFactor_code hcan hcl h27 hE1 hE2 γ hγ0 hγ2
  exact ⟨fun p => (F (circleCode D p)).1, fun p => decodeFamily (F (circleCode D p)),
    (circleCode D) ⁻¹' B, measurable_circleCode D hB, hcls⟩

end MatedCRT
