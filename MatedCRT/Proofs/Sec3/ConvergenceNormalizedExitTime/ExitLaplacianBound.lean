import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.LocalKernelHarmonic

/-! The normalized exit time has bounded discrete Laplacian. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- On a finite domain, the normalized exit time has Laplacian of absolute
value at most one on a locally finite graph with consecutive edges. -/
theorem abs_matedLaplacian_normExitTime_le_one
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (a : ℤ) (ha : a ∈ A) :
    |matedLaplacian m (normExitTime m A) a| ≤ 1 := by
  have hdeg : 1 ≤ (mdeg m a : ℝ) := by
    exact_mod_cast mdeg_pos_of_ne_zero hlf (hcons a)
  have h := normExitTimeLaplacianStep m A hsymm hlf hcons hA a ha
  change matedLaplacian m (normExitTime m A) a = _ at h
  rw [h, abs_neg, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact inv_le_one_of_one_le₀ hdeg

/-- Almost surely the Laplacian bound holds simultaneously for every
positive mesh and every bounded domain. -/
theorem MatedCRTEnv.IsValid.ae_normExitTime_laplacian_le_one
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ D : Set ℂ, Bornology.IsBounded D →
      ∀ a ∈ interiorCellVertices ε (S.η ω) D,
        |matedLaplacian (S.mult ε ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)) a| ≤ 1 := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hη hp hlf
  intro ε hε D hD a ha
  have hA : (interiorCellVertices ε (S.η ω) D).Finite :=
    (Tightness.cellVertices_finite hη.1 hp hε hD).subset (by
      unfold interiorCellVertices
      exact sdiff_subset)
  exact abs_matedLaplacian_normExitTime_le_one (S.mult ε ω) _ (S.mult_symm ε ω)
    (hlf ε hε) (S.mult_succ_ne_zero hε.le ω) hA a ha

/-- An eventual size bound therefore supplies both bounds needed for
discrete potential tightness when its constant is at least one. -/
theorem MatedCRTEnv.IsValid.ae_exit_bounds_of_eventual_size
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (D : Set ℂ) (hD : Bornology.IsBounded D)
    (E : Ω → ℕ → ℝ) (hE : ∀ ω n, 0 < E ω n) (C : Ω → ℝ) (hC : ∀ ω, 1 ≤ C ω)
    (hsize : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (E ω n) (S.η ω) D,
        |normExitTime (S.mult (E ω n) ω)
          (interiorCellVertices (E ω n) (S.η ω) D) a| ≤ C ω / E ω n) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
        |matedLaplacian (S.mult (E ω n) ω)
          (normExitTime (S.mult (E ω n) ω)
            (interiorCellVertices (E ω n) (S.η ω) D)) a| ≤ C ω) ∧
      (∀ a ∈ cellVertices (E ω n) (S.η ω) D,
        |normExitTime (S.mult (E ω n) ω)
          (interiorCellVertices (E ω n) (S.η ω) D) a| ≤ C ω / E ω n) := by
  filter_upwards [hS.ae_normExitTime_laplacian_le_one hγ hγ2, hsize] with ω hl hs
  filter_upwards [hs] with n hn
  exact ⟨fun a ha => (hl (E ω n) (hE ω n) D hD a ha).trans (hC ω), hn⟩

end MatedCRT
