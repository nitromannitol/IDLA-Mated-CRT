import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AeTightnessCompactness
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ScaledSolutionBound
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! Ordinary expected exit-time bounds along summable mesh scales. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- Lemmas 2.17 and 2.18 give an almost-sure eventual scaled bound for
the ordinary expected exit time on every cell meeting a fixed domain. -/
theorem ae_eventual_expectedExit_size_of_statements
    {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {D : Set ℂ} (hD : D ⊆ ball 0 ρ) (e : ℕ → ℝ) (he : IsPolySummableScales e)
    (he0 : Tendsto e atTop (𝓝 0)) :
    ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (e n) (S.η ω) D,
        expectedExitTime (S.mult (e n) ω) (interiorCellVertices (e n) (S.η ω) D) a ≠ ⊤ ∧
        e n * (expectedExitTime (S.mult (e n) ω) (interiorCellVertices (e n) (S.η ω) D) a).toReal ≤ C := by
  obtain ⟨α, hα, h218α⟩ := h218 γ hγ hγ2
  obtain ⟨C₀, hC₀, h218C⟩ := h218α ρ hρ hρ1
  let ρ' : ℝ := (1 + ρ) / 2
  have hρρ' : ρ < ρ' := by dsimp [ρ']; linarith
  have hρ'1 : ρ' < 1 := by dsimp [ρ']; linarith
  have hρ'0 : 0 < ρ' := by linarith
  obtain ⟨q, -, h217q⟩ := h217 γ hγ hγ2
  have hfin := (h217q ρ' hρ'0 hρ'1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).1
  have hεα : Tendsto (fun ε : ℝ => ε ^ α) (𝓝 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    rwa [Real.zero_rpow hα.ne'] at h
  filter_upwards [Tightness.ae_eventually_mem_of_polyHighProb (h218C Ω S hS) he, hfin] with ω hω hfinω
  refine ⟨C₀ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal, ?_⟩
  have hsmall : ∀ᶠ n in atTop, e n ^ α < ρ' - ρ :=
    (hεα.comp he0).eventually (gt_mem_nhds (by linarith))
  have hMle : largestExitTimeRV (S.μ ω) (ball 0 ρ') ≤
      ⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D :=
    le_iSup₂_of_le (ball 0 ρ') Subset.rfl le_rfl
  have hM : largestExitTimeRV (S.μ ω) (ball 0 ρ') < ⊤ := hMle.trans_lt hfinω
  filter_upwards [hω, hsmall] with n hn hsm
  intro a ha
  have hε := he.1 n
  have hqa := hn.2 D hD a ha
  have hsub : thickening (e n ^ α) D ⊆ ball 0 ρ' := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have hy' := hD hy
    rw [mem_ball] at hy' ⊢
    linarith [dist_triangle x y 0]
  have hCε : 0 ≤ C₀ * (e n)⁻¹ := mul_nonneg hC₀.le (inv_nonneg.2 hε.le)
  have hq : expectedExitTime (S.mult (e n) ω) (interiorCellVertices (e n) (S.η ω) D) a ≤
      ENNReal.ofReal (C₀ * (e n)⁻¹ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal) := by
    calc
      _ ≤ ENNReal.ofReal (C₀ * (e n)⁻¹) * largestExitTimeRV (S.μ ω) (thickening (e n ^ α) D) := hqa.2
      _ ≤ ENNReal.ofReal (C₀ * (e n)⁻¹) * largestExitTimeRV (S.μ ω) (ball 0 ρ') :=
        mul_le_mul_right (Tightness.largestExitTimeRV_mono hsub) _
      _ = _ := by rw [ENNReal.ofReal_mul hCε, ENNReal.ofReal_toReal hM.ne]
  have hqfin : expectedExitTime (S.mult (e n) ω) (interiorCellVertices (e n) (S.η ω) D) a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq
  refine ⟨hqfin, ?_⟩
  have hreal : 0 ≤ C₀ * (e n)⁻¹ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal :=
    mul_nonneg hCε ENNReal.toReal_nonneg
  have hle := (ENNReal.toReal_le_toReal hqfin ENNReal.ofReal_ne_top).2 hq
  rw [ENNReal.toReal_ofReal hreal] at hle
  calc e n * (expectedExitTime (S.mult (e n) ω) (interiorCellVertices (e n) (S.η ω) D) a).toReal ≤
        e n * (C₀ * (e n)⁻¹ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal) :=
      mul_le_mul_of_nonneg_left hle hε.le
    _ = C₀ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal * (e n * (e n)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hε.ne', mul_one]

/-- The exit-time estimate and the maximum principle give an eventual
pathwise size bound for solutions with bounded Laplacian and boundary data. -/
theorem ae_eventual_dirichlet_size_of_statements
    {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (F : Ω → ℕ → ℤ → ℝ) {C A : ℝ} (hC : 0 ≤ C)
    (hdata : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (F ω n) a| ≤ C) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), e n * |F ω n b| ≤ A)) :
    ∀ᵐ ω ∂S.P, ∃ B : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (e n) (S.η ω) (ball z r), e n * |F ω n a| ≤ B := by
  filter_upwards [ae_eventual_expectedExit_size_of_statements h218 h217 hγ hγ2 hρ hρ1 S hS hD e he he0,
    hdata, hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω ⟨B, hB⟩ hd hη hp hadj
  refine ⟨A + C * B, ?_⟩
  apply eventually_scaled_abs_solution_le_of_exit_bound he.1 hr hη.1 hp
    (fun n => hadj (e n) (he.1 n)) (fun n k => S.mult_succ_ne_zero (he.1 n).le ω k)
    (F ω) hC
  filter_upwards [hd, hB] with n hn hq
  refine ⟨hn.1, hn.2, ?_, ?_⟩
  · intro a ha
    exact (hq a (interiorCellVertices_subset _ _ _ ha)).1
  · intro a ha
    exact (hq a ha).2

end MatedCRT
