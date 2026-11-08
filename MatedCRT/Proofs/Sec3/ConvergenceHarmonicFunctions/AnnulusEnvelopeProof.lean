import MatedCRT.Steps.Sec3.PointwiseAnnulusEnvelope
import MatedCRT.Steps.Sec3.UniformCellSize
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.UniformCellSizeMeasurable

/-! # Components of the almost-everywhere annulus envelope

The sandwich is taken under the state law, not a completion of the original
environment sigma-algebra. The estimates below retain their own exponents.
The environment uses Leonardo Bonanno's coupling from
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- A state-law measurable sandwich pulls back to an exactly measurable event
with the same exceptional outer measure as an almost surely equal raw event. -/
theorem stateLaw_measurable_envelope {Ω X : Type} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] (P : Measure Ω) (m : MeasurableSpace Ω)
    (f : Ω → X) (hf : @Measurable Ω X mΩ _ f) (hfm : @Measurable Ω X m _ f)
    (A : Set X) (hA : NullMeasurableSet A (@Measure.map Ω X mΩ _ f P)) (B : Set Ω)
    (hB : ∀ᵐ ω ∂P, (f ω ∈ A ↔ ω ∈ B)) :
    ∃ E : Set Ω, MeasurableSet[m] E ∧
      (∀ᵐ ω ∂P, ω ∈ E → ω ∈ B) ∧ P Eᶜ = P Bᶜ := by
  obtain ⟨T, hTA, hTm, hTeq⟩ := hA.exists_measurable_subset_ae_eq
  refine ⟨f ⁻¹' T, hTm.preimage hfm, ?_, ?_⟩
  · filter_upwards [hB] with ω hω hT
    exact hω.mp (hTA hT)
  · apply measure_congr
    have hpre := ae_of_ae_map hf.aemeasurable hTeq
    filter_upwards [hpre, hB] with ω hω hBω
    exact propext (not_congr ((Iff.of_eq hω).trans hBω))

/-- Polynomial exceptional bounds combine with the smaller of their actual
exponents, uniformly at every mesh in `(0, 1)`. -/
theorem intersection_poly_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Set Ω) {C D α κ ε : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : P Aᶜ ≤ ENNReal.ofReal (C * ε ^ α))
    (hB : P Bᶜ ≤ ENNReal.ofReal (D * ε ^ κ)) :
    P (A ∩ B)ᶜ ≤ ENNReal.ofReal ((C + D) * ε ^ min α κ) := by
  have hα : ε ^ α ≤ ε ^ min α κ :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
  have hκ : ε ^ κ ≤ ε ^ min α κ :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
  calc
    P (A ∩ B)ᶜ = P (Aᶜ ∪ Bᶜ) := by rw [compl_inter]
    _ ≤ P Aᶜ + P Bᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * ε ^ α) + ENNReal.ofReal (D * ε ^ κ) :=
      add_le_add hA hB
    _ = ENNReal.ofReal (C * ε ^ α + D * ε ^ κ) := by
      rw [ENNReal.ofReal_add (mul_nonneg hC (Real.rpow_nonneg hε.le _))
        (mul_nonneg hD (Real.rpow_nonneg hε.le _))]
    _ ≤ ENNReal.ofReal ((C + D) * ε ^ min α κ) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left hα hC, mul_le_mul_of_nonneg_left hκ hD]

/-- The annulus condition whose state-law measurability remains to be coded. -/
def AnnulusGoodEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ β p ε : ℝ) : Set Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) ρ, ∀ r : ℝ,
    ε ^ β ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball 0 ρ →
    ∀ x ∈ cellVertices ε (S.η ω) (ball z r),
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) x
        {w | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (r / 2)),
          walkDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (sphere z (2 * r))) y w}}

/-- Remaining implementation step from the state coding and universal
measurability argument in steps2.tex, lines 395–426. The version is chosen
separately at each mesh and is not assumed to be pointwise equal. -/
def AnnulusGoodMeasurableVersionStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ β p : ℝ) : Prop :=
  ∀ ε : ℝ, ∃ E : Set Ω, MeasurableSet[S.envSigma] E ∧
    ∀ᵐ ω ∂S.P, (ω ∈ E ↔ ω ∈ AnnulusGoodEvent S ρ β p ε)

/-- Measurable versions of the separate good events combine to give the
repaired envelope at the smaller of the two exceptional exponents. -/
theorem pointwiseCellAnnulusEnvelope_of_event_versions
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {ρ a β p α κ : ℝ}
    (A B : ℝ → Set Ω)
    (hAm : ∀ ε, MeasurableSet[S.envSigma] (A ε))
    (hBm : ∀ ε, MeasurableSet[S.envSigma] (B ε))
    (hAgood : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ A ε →
      ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a)
    (hBgood : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ B ε →
      ω ∈ AnnulusGoodEvent S ρ β p ε)
    (hA : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (A ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ α))
    (hB : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (B ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) :
    PointwiseCellAnnulusEnvelopeStep S ρ a β p (min α κ) := by
  obtain ⟨C, δ, hC, hδ, hA⟩ := hA
  obtain ⟨D, δ', hD, hδ', hB⟩ := hB
  refine ⟨fun ε => A ε ∩ B ε, fun ε => (hAm ε).inter (hBm ε),
    C + D, min δ (min δ' 1), add_nonneg hC hD,
    lt_min hδ (lt_min hδ' zero_lt_one), ?_⟩
  intro ε hε hεsmall
  have hεδ : ε < δ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεδ' : ε < δ' := lt_of_lt_of_le hεsmall
    ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hεsmall
    ((min_le_right _ _).trans (min_le_right _ _))).le
  refine ⟨intersection_poly_tail S.P (A ε) (B ε) hC hD hε hε1
    (hA ε hε hεδ) (hB ε hε hεδ'), ?_⟩
  filter_upwards [hAgood ε hε, hBgood ε hε] with ω hAω hBω hω
  exact ⟨hAω hω.1, hBω hω.2⟩

/-- The actual cell and annulus estimates select positive mesh exponents and
a walk probability strictly below one, before selecting a representation. -/
theorem cellAnnulus_parameters_of_estimates (𝒮 : SpaceFillingSLEModel)
    (hcell : UniformCellSizeUpperStep 𝒮) (hgms : GMSAnnulusDisconnectionStmt 𝒮)
    {γ ρ a : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 0 < a) (ha' : a < 2 / (2 + γ) ^ 2) :
    ∃ α β p κ : ℝ, 0 < α ∧ 0 < β ∧ 0 < p ∧ p < 1 ∧ 0 < κ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        S.P {ω | ¬ ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a} ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
      (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ε < 1 →
        S.P {ω | ¬ ∀ z ∈ ball (0 : ℂ) ρ, ∀ r : ℝ,
          ε ^ β ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball 0 ρ →
          ∀ x ∈ cellVertices ε (S.η ω) (ball z r),
            ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) x
              {w | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (r / 2)),
                walkDisconnectsBeforeHit (S.mult ε ω)
                  (cellVertices ε (S.η ω) (sphere z (2 * r))) y w}} ≤
          ENNReal.ofReal (C * ε ^ α)) := by
  obtain ⟨κ, hκ, hcell⟩ := hcell γ hγ hγ2 ρ hρ hρ1 a ha ha'
  obtain ⟨α, β, hα, hβ, hgms⟩ := hgms γ hγ hγ2
  obtain ⟨p₀, hp₀, hgms⟩ := hgms ρ hρ hρ1
  refine ⟨α, β, min p₀ (1 / 2), κ, hα, hβ, lt_min hp₀ (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), hκ, ?_⟩
  intro Ω _ S hS
  refine ⟨hcell Ω S hS, ?_⟩
  obtain ⟨C, δ, hC, hδ, hbound⟩ := hgms Ω S hS
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ε hε hεδ hε1
  refine (measure_mono ?_).trans (hbound ε hε hεδ hε1)
  intro ω hbad hgood
  apply hbad
  intro z hz r hlow hupp hball x hx
  exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
    (hgood z hz r hlow hupp hball x hx)

/-- Conditional assembly of the repaired envelope. The sole additional
implementation hypothesis is the separately stated annulus state-code
measurable-version step; the powers and probability come from the estimates. -/
theorem cellAnnulusEnvelope_of_estimates_of_measurable_version
    (𝒮 : SpaceFillingSLEModel) (hcell : UniformCellSizeUpperStep 𝒮)
    (hgms : GMSAnnulusDisconnectionStmt 𝒮) {γ ρ a : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 0 < a) (ha' : a < 2 / (2 + γ) ^ 2)
    (hcode : ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ β p : ℝ, AnnulusGoodMeasurableVersionStep S ρ β p) :
    ∃ β p κ : ℝ, 0 < β ∧ 0 < p ∧ p < 1 ∧ 0 < κ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        PointwiseCellAnnulusEnvelopeStep S ρ a β p κ := by
  obtain ⟨κ, hκ, hcellEvents⟩ :=
    uniform_envSigma_cellSize_of_step 𝒮 hcell hγ hγ2 hρ hρ1 ha ha'
  obtain ⟨α, β, p, κ', hα, hβ, hp, hp1, hκ', hbounds⟩ :=
    cellAnnulus_parameters_of_estimates 𝒮 hcell hgms hγ hγ2 hρ hρ1 ha ha'
  refine ⟨β, p, min κ α, hβ, hp, hp1, lt_min hκ hα, ?_⟩
  intro Ω _ S hS
  obtain ⟨A, hAm, hAtail, hAgood⟩ := hcellEvents Ω S hS
  obtain ⟨_, C, δ, hC, hδ, htail⟩ := hbounds Ω S hS
  classical
  choose B hBm hBeq using hcode Ω S hS β p
  have hBtail : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (B ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
    refine ⟨C, min δ 1, hC, lt_min hδ zero_lt_one, ?_⟩
    intro ε hε hεsmall
    have heq : S.P (B ε)ᶜ = S.P (AnnulusGoodEvent S ρ β p ε)ᶜ := by
      apply measure_congr
      filter_upwards [hBeq ε] with ω hω
      exact propext (not_congr hω)
    rw [heq]
    exact htail ε hε (lt_of_lt_of_le hεsmall (min_le_left _ _))
      (lt_of_lt_of_le hεsmall (min_le_right _ _))
  apply pointwiseCellAnnulusEnvelope_of_event_versions S A B hAm hBm
      ?_ ?_ hAtail hBtail
  · intro ε hε
    filter_upwards [hAgood ε hε] with ω hω hmem
    exact hω.mp hmem
  · intro ε hε
    filter_upwards [hBeq ε] with ω hω hmem
    exact hω.mp hmem

end MatedCRT

#print axioms MatedCRT.stateLaw_measurable_envelope
#print axioms MatedCRT.intersection_poly_tail
#print axioms MatedCRT.pointwiseCellAnnulusEnvelope_of_event_versions
#print axioms MatedCRT.cellAnnulus_parameters_of_estimates
#print axioms MatedCRT.cellAnnulusEnvelope_of_estimates_of_measurable_version
