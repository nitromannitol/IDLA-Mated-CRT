import MatedCRT.FirstPass.Derived.AreaCellEnvironmentExteriorPaths
import MatedCRT.FirstPass.Derived.AreaCellEnvironmentConfiguration
import MatedCRT.FirstPass.Derived.SrwReversibleSteps
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected

/-! # Exterior visits for the mated-CRT cell walk -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- The relabelled walk has adjacent steps and visits the exterior of every
bounded set, simultaneously for all shifts, scales and cell representatives. -/
theorem MatedCRTEnv.ae_areaCell_adjacent_and_exterior_of_embedding
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω)) (x : ℤ) :
    ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      (∀ n, (areaCellConfig h hε (S.mult ε ω)).Adj (ξ n) (ξ (n + 1))) ∧
      (∀ K : ℕ, ∀ p : (areaCellConfig h hε (S.mult ε ω)).cells → Plane,
        (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ a : ℝ≥0, 0 < a →
        ∀ U : Set Plane, Bornology.IsBounded U →
        hitTime {C : (areaCellConfig h hε (S.mult ε ω)).cells | (a : ℝ) • p C ∉ U}
          (fun n => ξ (K + n)) ≠ ⊤) := by
  exact S.ae_areaCell_adjacent_and_exterior_all_shifts ω h hε hlf
    (FirstPass.Derived.isLocallyFiniteMult_bmEdgeCount hlf hε.le) H hH
    (MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl ε (S.bm ω) hlf)
    (S.areaCellConfig_isCellConfiguration ω hε h hlf H hH) x

end MatedCRT
end
