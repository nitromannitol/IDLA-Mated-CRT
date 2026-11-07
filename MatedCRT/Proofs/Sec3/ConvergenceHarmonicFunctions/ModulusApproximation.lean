import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CorrectedFromInputs

/-! # Reduction of the closed-disk modulus to Hölder boundary data -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The closed-disk modulus for Hölder boundary data. This is the regular-data
part of `LEMMA36-REPLACEMENT.md`, lines 491–574. -/
def CorrectedHarmonicHolderModulusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, IsHolderContinuousOn ψ (closedBall z r) →
  ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
      dist x y < δ ∧ |projectedDiscreteHarmonicExtension S r z ψ ε ω x -
        projectedDiscreteHarmonicExtension S r z ψ ε ω y| > t} ≤ e

/-- Continuous data on a closed disk admit uniform Lipschitz approximations. -/
theorem exists_holder_approximation_closedBall {r : ℝ} {z : ℂ} {ψ : ℂ → ℝ}
    (hψ : ContinuousOn ψ (closedBall z r)) {η : ℝ} (hη : 0 < η) :
    ∃ φ : ℂ → ℝ, IsHolderContinuousOn φ (closedBall z r) ∧
      ∀ x ∈ closedBall z r, |ψ x - φ x| ≤ η := by
  classical
  let _ : CompactSpace (closedBall z r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall z r)
  let f : C(closedBall z r, ℝ) := ⟨fun x => ψ x, continuousOn_iff_continuous_domRestrict.mp hψ⟩
  obtain ⟨g, C, hC, hg⟩ := exists_lipschitz_approximation f hη
  let φ : ℂ → ℝ := fun x => if hx : x ∈ closedBall z r then g ⟨x, hx⟩ else 0
  have hφ : ∀ x (hx : x ∈ closedBall z r), φ x = g ⟨x, hx⟩ := by
    intro x hx
    dsimp only [φ]
    rw [dite_eq_left hx]
  have hlip : LipschitzOnWith C φ (closedBall z r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [hφ x hx, hφ y hy]
    exact hC.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨φ, ⟨C, 1, by norm_num, le_rfl, hlip.holderOnWith⟩, ?_⟩
  intro x hx
  rw [hφ x hx, abs_sub_comm]
  exact (hg ⟨x, hx⟩).le

/-- The Hölder-data modulus implies the modulus for all continuous data. -/
theorem correctedHarmonicModulus_of_holder (𝒮 : SpaceFillingSLEModel)
    (hmod : CorrectedHarmonicHolderModulusStep 𝒮) : CorrectedHarmonicModulusStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ t ht e he
  obtain ⟨φ, hφ, hclose⟩ := exists_holder_approximation_closedBall hψ (by linarith : 0 < t / 8)
  obtain ⟨K, hK⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hψ
  have hK' : ∀ x ∈ closedBall z r, |ψ x| ≤ K := fun x hx => by
    simpa only [Real.norm_eq_abs] using hK x hx
  obtain ⟨L, hL⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
    (by obtain ⟨C, χ, hχ, _, hhol⟩ := hφ; exact hhol.continuousOn hχ)
  have hL' : ∀ x ∈ closedBall z r, |φ x| ≤ L := fun x hx => by
    simpa only [Real.norm_eq_abs] using hL x hx
  obtain ⟨δ, hδ, hgood⟩ := hmod γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball
    φ hφ (t / 2) (by linarith) e he
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hgood] with ε hε
  refine (measure_mono ?_).trans hε
  rintro ω ⟨x, hx, y, hy, hxy, hbad⟩
  have hx' := (projectedExit_expectations_stable S (y := x) hr ε ω hK' hL' hclose).1
  have hy' := (projectedExit_expectations_stable S (y := y) hr ε ω hK' hL' hclose).1
  refine ⟨x, hx, y, hy, hxy, ?_⟩
  have h1 := abs_add_le
    (projectedDiscreteHarmonicExtension S r z ψ ε ω x -
      projectedDiscreteHarmonicExtension S r z φ ε ω x)
    (projectedDiscreteHarmonicExtension S r z φ ε ω x -
      projectedDiscreteHarmonicExtension S r z φ ε ω y)
  have h2 := abs_add_le
    ((projectedDiscreteHarmonicExtension S r z ψ ε ω x -
      projectedDiscreteHarmonicExtension S r z φ ε ω x) +
      (projectedDiscreteHarmonicExtension S r z φ ε ω x -
        projectedDiscreteHarmonicExtension S r z φ ε ω y))
    (projectedDiscreteHarmonicExtension S r z φ ε ω y -
      projectedDiscreteHarmonicExtension S r z ψ ε ω y)
  have heq : (projectedDiscreteHarmonicExtension S r z ψ ε ω x -
      projectedDiscreteHarmonicExtension S r z φ ε ω x) +
      (projectedDiscreteHarmonicExtension S r z φ ε ω x -
        projectedDiscreteHarmonicExtension S r z φ ε ω y) +
      (projectedDiscreteHarmonicExtension S r z φ ε ω y -
        projectedDiscreteHarmonicExtension S r z ψ ε ω y) =
      projectedDiscreteHarmonicExtension S r z ψ ε ω x -
        projectedDiscreteHarmonicExtension S r z ψ ε ω y := by ring
  rw [heq, abs_sub_comm (projectedDiscreteHarmonicExtension S r z φ ε ω y)] at h2
  linarith

/-- Corrected harmonic convergence follows from the Hölder-data modulus. -/
theorem correctedHarmonicConvergence_of_holder_modulus (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hmod : CorrectedHarmonicHolderModulusStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_modulus 𝒮 h211 hmeps hexc hX h28
    (correctedHarmonicModulus_of_holder 𝒮 hmod)

end MatedCRT
