import MatedCRT.FirstPass.Derived.ValidIntegerWalkCurveSupport

/-! # Finite exits of walks in valid environments -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set HarmonicBalls ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.GMSMain
open scoped ENNReal NNReal

/-- At each positive mesh, almost every valid environment has finite walk exits from
all bounded sets, simultaneously at all positive speeds, for each starting vertex. -/
theorem MatedCRTEnv.IsValid.ae_finite_exit_integerWalk
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ x : ℤ,
      ∀ᵐ ξ ∂srwLaw (S.mult ε ω) x,
        ∀ v : ℝ, 0 < v → ∀ U : Set ℂ, Bornology.IsBounded U →
          pathExitTime U (interpolatedWalk ε (S.η ω) v ξ) ≠ ∞ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ηc, _, hC, hη⟩ := hS.matingOfTrees
  filter_upwards [hS.isAreaParametrized, hη, epsA_ae_exists_cellularEmbedding hC hε]
    with ω harea hηω hemb
  obtain ⟨hlf, H, hH⟩ := hemb
  have hcell : H.cell = cell ε (S.η ω) := by
    funext x
    rw [hH x, cell, ← hηω.1]
  intro x
  exact ae_pathExitTime_ne_top_all_positive_speeds_all_bounded_integerWalk
    harea hε (S.mult ε ω) hlf H hcell
    (MatedCRTHarmonic.GMS3.matedCRT_connected ε (S.bm ω) hlf) x

end MatedCRT
end
