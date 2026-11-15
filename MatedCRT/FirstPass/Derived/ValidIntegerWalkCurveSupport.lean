import MatedCRT.FirstPass.Derived.EuclideanCurveLawSupport
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Theorem14

/-! # Unbounded walk curves in a valid environment -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set MarkovProcess HarmonicBalls ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.GMSMain LatticeProb.ReparamDistanceIsometry
open scoped ENNReal NNReal

/-- At each positive mesh, almost every valid environment gives unbounded Euclidean
walk curves for every starting vertex and positive speed. -/
theorem MatedCRTEnv.IsValid.ae_unbounded_range_map_integerWalk
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (x : ℤ) (v : ℝ) (hv : 0 < v),
      ∀ᵐ (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) ∂((srwLaw (S.mult ε ω) x).map
        (fun ξ => complexToEuclideanPath (interpPathCM (vertexPoint ε (S.η ω)) hv.le ξ))),
        ¬ Bornology.IsBounded (Set.range f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ηc, _, hC, hη⟩ := hS.matingOfTrees
  filter_upwards [hS.isAreaParametrized, hη, epsA_ae_exists_cellularEmbedding hC hε]
    with ω harea hηω hemb
  obtain ⟨hlf, H, hH⟩ := hemb
  have hcell : H.cell = cell ε (S.η ω) := by
    funext x
    rw [hH x, cell, ← hηω.1]
  intro x v hv
  exact MatedCRT.ae_unbounded_range_map_integerWalk harea hε (S.mult ε ω) hlf H hcell
    (MatedCRTHarmonic.GMS3.matedCRT_connected ε (S.bm ω) hlf) x hv

end MatedCRT
end
