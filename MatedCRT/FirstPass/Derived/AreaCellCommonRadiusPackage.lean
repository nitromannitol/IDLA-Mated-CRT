import MatedCRT.FirstPass.Derived.AreaCellCommonRadiusTransfer
import MatedCRT.FirstPass.Derived.AreaCellParameterChoice

/-! # Parameters of the common-radius transfer

For every positive error budget `r`, the tolerances `η, τ`, a finite family of covering balls of a
common radius `ρ` for the thickened domain, the collar data of these balls, and the scales
`a, e, δ, mesh, K` and the compact set `C` of the parameter hypothesis of
`MatedCRTEnv.exists_covered_shifted_areaCell_actual_transfer_common_radius` exist, with the
explicit collar constant `MatedCRTEnv.collarConstant`. -/
set_option autoImplicit false
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory Filter ProbabilityTheory _root_.HarmonicBalls BouRabeeGwynne
open MatedCRTHarmonic
open scoped unitInterval ENNReal NNReal Topology
universe u

/-- The collar constant of the uniform transfer is positive. -/
theorem MatedCRTEnv.collarConstant_pos {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (α : ℝ≥0) {m₀ : ℝ≥0} (hm₀ : 0 < m₀) (Uc : Set ℂ) (d : ℝ)
    {U : Set (LatticeProb.Euc 2)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ]
    (hμ : LatticeProb.IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    0 < MatedCRTEnv.collarConstant.{u} S ω h α hm₀ Uc d hL hU hUb μ hμ hη hτ :=
  (Classical.choose_spec
    (MatedCRTEnv.uniform_areaCell_stopped_collar_transfer_of_cell_selectors.{u} S ω h α hm₀ Uc d
      hL hU hUb μ hμ hη hτ)).1

/-- Parameters for the common-radius transfer: the tolerances, a finite covering family of balls
of common radius `ρ` with collar data, and the scales compatible with the collar constant. -/
theorem MatedCRTEnv.exists_common_radius_package {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (α : ℝ≥0) {m₀ : ℝ≥0} (hm₀ : 0 < m₀) (Uc : Set ℂ) (d : ℝ)
    {U : Set (LatticeProb.Euc 2)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ]
    (hμ : LatticeProb.IsStandardBrownianLaw μ) (r : ℝ≥0) (hr : 0 < r) :
    ∃ (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) (J : Type u) (_ : Fintype J)
      (center : J → LatticeProb.Euc 2) (margin ρ K : ℝ)
      (Us Is Ks : J → Set (LatticeProb.Euc 2)) (radius : J → ℝ),
      0 < margin ∧ margin ≤ ρ ∧ 0 < K ∧ 0 < ρ ∧
      (∀ j, Us j = ball (center j) ρ) ∧ (∀ j, ball (center j) (margin / 2) ⊆ Is j) ∧
      (∀ j, Is j ⊆ ball (center j) ρ) ∧
      (∀ j, IsOpen (Us j)) ∧ (∀ j, Bornology.IsBounded (Us j)) ∧
      (∀ j, IsCompact (Is j)) ∧ (∀ j, Is j ⊆ Us j) ∧
      (∀ j, IsCompact (Ks j)) ∧ (∀ j, Ks j ⊆ Us j) ∧ (∀ j, 0 < radius j) ∧
      (∀ j x, x ∈ Is j → ∀ y, dist y x < radius j → y ∈ Ks j) ∧
      ∃ (a e δ mesh : ℝ) (C : Set (LatticeProb.Euc 2)),
        0 < a ∧ 0 < e ∧ 0 < δ ∧ 0 < mesh ∧
        a + e ≤ MatedCRTEnv.collarConstant.{u} S ω h α hm₀ Uc d hL hU hUb μ hμ hη hτ ∧
        δ ≤ MatedCRTEnv.collarConstant.{u} S ω h α hm₀ Uc d hL hU hUb μ hμ hη hτ ∧
        a + e + mesh < δ ∧ ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧
        4 * ρ + 3 * a + 2 * K ≤ e ∧ IsCompact C ∧ thickening δ U ⊆ C ∧
        thickening δ U ⊆ ⋃ j, ball (center j) (margin / 4) ∧
        (∀ j, closure (ball (center j) ρ) ⊆ C) ∧
        ∀ L : ℕ, ∃ b : ℝ, 0 < b ∧
          ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
            (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
            (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞) := by
  obtain ⟨η, τ, hη, hτ, hbud, hex⟩ := exists_common_radius_parameters.{u} hUb r hr
  obtain ⟨J, hJ, center, margin, ρ, K, a, e, δ, mesh, C, hm, hmρ, hK, ha, he, hδ, hmesh, hae,
    hδc, hbuffer, hsmall, hpoint, hC, hUC, hcover, hballC⟩ :=
    hex _ (MatedCRTEnv.collarConstant_pos.{u} S ω h α hm₀ Uc d hL hU hUb μ hμ hη hτ)
  obtain ⟨Us, Is, Ks, radius, hUball, hinner, hIball, hUs, hUsb, hIs, hIUs, hKs, hKUs, hrad,
    hcollar⟩ := exists_ball_collar_data center hm hmρ
  exact ⟨η, τ, hη, hτ, J, hJ, center, margin, ρ, K, Us, Is, Ks, radius, hm, hmρ, hK,
    lt_of_lt_of_le hm hmρ, hUball, hinner, hIball, hUs, hUsb, hIs, hIUs, hKs, hKUs, hrad, hcollar,
    a, e, δ, mesh, C, ha, he, hδ, hmesh, hae, hδc, hbuffer, hsmall, hpoint, hC, hUC, hcover,
    hballC, hbud⟩

end MatedCRT
