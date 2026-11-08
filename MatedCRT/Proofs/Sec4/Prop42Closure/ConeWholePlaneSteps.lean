import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ContactEvent

/-! # Named Step Props for the transfer of the premature-contact event (closure of Proposition 4.2, z5)

Written argument: `notes/prop42-proof/prop42-proof.tex`, draft lines 275-289 ("equality of local cone and `h^γ` laws
excludes the same event for the cone"). Operator ruling (2026-11-08): the volume-growth inputs (B1) and the whole-plane
model (B2) are named Step Props, and fact (2) is stated for the fields exactly as IDLA eq. (2.4) states it
(`eq:gff`, paper line 443: `h|_{B_1} =_d (h^ℂ - γ log|·|)|_{B_1}`).

This file states the Step Props, each with its source, and proves the a.s. local finiteness of a cone LQG measure
(part of `IsConeField`). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace ProbabilityTheory

/-- Test functions supported in `B_1`: the pairings of the restricted field `h|_{B_1}`. -/
abbrev TestB1 : Type := {φ : ℂ → ℝ // IsTestFunction (ball (0 : ℂ) 1) φ}

/-- Region circles in `B_1`: `(r, z)` with `r > 0` and `closedBall z r ⊆ B_1`. Their circle averages determine the LQG
measure on `B_1` (`IsLQGLimit` uses only circles with centre in a compact subset of `B_1` for small radii). -/
abbrev CircleB1 : Type := {p : ℝ × ℂ // 0 < p.1 ∧ closedBall p.2 p.1 ⊆ ball (0 : ℂ) 1}

/-- The restriction `h|_{B_1}` of the field with pairings `hC` and circle averages `hcirc` (the quantum cone `h`). -/
def coneFieldOnB1 {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) :
    (TestB1 → ℝ) × (CircleB1 → ℝ) :=
  (fun φ => hC ω φ.1, fun p => hcirc ω p.1.1 p.1.2)

/-- The restriction to `B_1` of `h^ℂ - γ log|·|` (right-hand side of eq:gff): pairings `fieldPairing γ` and circle
averages `fieldCircleAverage γ` of the whole-plane GFF `h^ℂ`. -/
noncomputable def wholePlaneFieldOnB1 {Ω : Type} (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (ω : Ω) : (TestB1 → ℝ) × (CircleB1 → ℝ) :=
  (fun φ => fieldPairing γ (hC ω) φ.1, fun p => fieldCircleAverage γ (hcirc ω) p.1.1 p.1.2)

/-- **B1, cone side: almost surely the cone LQG measure has volume growth at radius `3/4`.**
Source: IDLA Lemma 2.7 (`VolumeGrowthStmt`, `MatedCRT/Draft/Section2.lean:121`; [BG20] Lemma A.1), which bounds
`μ(B_δ(z))` for all `z ∈ B_{1-δ}` with polynomially high probability. The a.s. local finiteness and the a.s.
measurability of the cone measure are not part of this Step: they are `ae_isLocallyFiniteMeasure_of_isConeField`
and `IsConeField.aemeasurable_lqgMeasure`. -/
def ConeVolumeGrowthAeStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ᵐ ω ∂P, ∃ βm βp : ℝ, VolumeGrowth (μ ω) (3 / 4) βm βp

/-- **B1, whole-plane side: almost surely the whole-plane LQG measure `μ_{h^ℂ - γ log|·|}` has volume growth at radius
`3/4`.** Stated as its own Step (operator ruling (a)); no statement of the repository proves it. -/
def WholePlaneVolumeGrowthAeStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
    ∀ᵐ ω ∂P, ∃ βm βp : ℝ, VolumeGrowth (μ ω) (3 / 4) βm βp

/-- **B2: a whole-plane model with its `γ`-LQG measure, for each `γ ∈ (0, 2)`.**
The whole-plane GFF is `wholePlaneGFF_exists` (`MatedCRT/Proofs/Field/WholePlaneExistence.lean:46`). Its LQG measure
of insertion `γ` is the existence statement `LQGMeasureExistence` (Harmonic-Balls `HarmonicBalls/Proposed/LQG.lean:66`),
which is not proved. Sources: that file and `MatedCRT/Proposed/Berestycki2017.lean`. -/
def WholePlaneLQGModelStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsProbabilityMeasure P ∧ IsWholePlaneGFF P hC hcirc ∧ IsLQGMeasureOfField P γ γ hcirc μ

/-- **Fact (2), for the fields: equality in law of the cone and the whole-plane field on `B_1`.**
IDLA eq. (2.4) (`eq:gff`, paper line 443): `h|_{B_1} =_d (h^ℂ - γ log|·|)|_{B_1}`, where `h` is the quantum cone of
`IsConeField` and `h^ℂ` a whole-plane GFF (`IsWholePlaneGFF`). The compared objects are `coneFieldOnB1` and
`wholePlaneFieldOnB1`, with the product σ-algebra on the function spaces. -/
def ConeWholePlaneFieldLawStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ),
    IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' →
    IdentDistrib (coneFieldOnB1 hC hcirc) (wholePlaneFieldOnB1 γ hC' hcirc') P P'

/-- **Fact (2), for the restricted LQG measures** (the form used by the transfer of the premature-contact event).
NOT DERIVED in this repository: `ConeWholePlaneFieldLawStep` yields it only once `μ|_{B_1}` is a measurable function of
the restricted circle averages (gap G1, `reports/z5.md`). Used only as an explicit hypothesis. -/
def ConeWholePlaneRestrictedLQGLawStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
    IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ γ hcirc' μ' →
    IdentDistrib (fun ω => (μ ω).restrict (ball (0 : ℂ) 1)) (fun ω' => (μ' ω').restrict (ball (0 : ℂ) 1)) P P'

/-- The a.s. local finiteness of the cone LQG measure, from `IsConeField` (the LQG limit is a Radon measure). -/
theorem ae_isLocallyFiniteMeasure_of_isConeField {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
  obtain ⟨-, -, hL⟩ := hcone
  have hL' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hL
  filter_upwards [hL'] with ω hω
  exact hω.isLocallyFiniteMeasure

end MatedCRT
