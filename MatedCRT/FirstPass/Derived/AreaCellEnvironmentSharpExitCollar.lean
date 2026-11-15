import MatedCRT.FirstPass.Derived.AreaCellSharpExitCollar
import MatedCRT.FirstPass.Derived.AreaCellEnvironmentConfiguration
import MatedCRT.FirstPass.Derived.SrwReversibleSteps
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected

/-! # Sharp exit errors and collars for area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- Sharp clock, endpoint and stopped-path bounds with collar containment
for area-cell walks, simultaneously for all shifts and admissible domains. -/
theorem MatedCRTEnv.ae_areaCell_sharp_exit_error_and_collar_of_embedding
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent) (x : ℤ) :
    let hc := S.areaCellConfig_isCellConfiguration ω hε h hlf H hH
    let G := areaCellConfig h hε (S.mult ε ω)
    ∀ᵐ ζ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      ∀ k : ℕ, ∀ p : G.cells → Plane,
      (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ a : ℝ≥0, 0 < a →
      ∀ U : Set Plane, Bornology.IsBounded U → IsOpen U → Convex ℝ U →
      ∀ b d : ℝ,
      (∀ C, (a : ℝ) • p C ∈ U → G.holding C ≤ b) →
      (∀ C D, (a : ℝ) • p C ∈ U → G.Adj C D →
        Metric.diam (C.1 : Set Plane) + Metric.diam (D.1 : Set Plane) ≤ d) →
      let ξ := fun n => ζ (k + n)
      let T := hitTime {C : G.cells | (a : ℝ) • p C ∉ U}
      let τ := continuousExitTime U 0 (G.interpolatedWalk p a ξ)
      ((a : ℝ) • p (ξ 0) ∉ U → T ξ = 0 ∧ τ = 0) ∧
      ((a : ℝ) • p (ξ 0) ∈ U → ∃ n : ℕ,
        T ξ = (n + 1 : ℕ) ∧ τ ≠ ∞ ∧
        (a : ℝ) ^ 2 * G.jumpTime ξ n < (τ.toNNReal : ℝ) ∧
        (τ.toNNReal : ℝ) ≤ (a : ℝ) ^ 2 * G.jumpTime ξ (n + 1) ∧
        0 ≤ (a : ℝ) ^ 2 * G.jumpTime ξ (n + 1) - (τ.toNNReal : ℝ) ∧
        (a : ℝ) ^ 2 * G.jumpTime ξ (n + 1) - (τ.toNNReal : ℝ) <
          (a : ℝ) ^ 2 * b ∧
        (G.interpolatedWalk p a ξ) τ.toNNReal ∈ frontier U ∧
        dist ((G.interpolatedWalk p a ξ) τ.toNNReal)
          ((a : ℝ) • p (stopState T ξ)) ≤ (a : ℝ) * d ∧
        (∀ t : ℝ≥0,
          dist ((G.interpolatedWalk p a ξ) (min t τ.toNNReal))
            ((G.interpolatedWalk p a ξ) (min t
              ⟨(a : ℝ) ^ 2 * G.jumpTime ξ (n + 1),
                mul_nonneg (sq_nonneg _) (G.jumpTime_nonneg
                  (LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hc
                    (S.areaCellConfig_exists_adj ω h hε)) (n + 1))⟩)) ≤
            (a : ℝ) * d) ∧
        ∀ t : ℝ≥0,
          G.interpolatedWalk p a ξ (min t
            ⟨(a : ℝ) ^ 2 * G.jumpTime ξ (n + 1),
              mul_nonneg (sq_nonneg _) (G.jumpTime_nonneg
                (LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hc
                    (S.areaCellConfig_exists_adj ω h hε)) (n + 1))⟩)
            ∈ Metric.cthickening ((a : ℝ) * d) U) := by
  exact S.ae_areaCell_sharp_exit_error_and_collar_all_shifts ω h hε hlf
    (FirstPass.Derived.isLocallyFiniteMult_bmEdgeCount hlf hε.le) H hH
    (MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl ε (S.bm ω) hlf)
    (S.areaCellConfig_isCellConfiguration ω hε h hlf H hH) hrec x

end MatedCRT
end
