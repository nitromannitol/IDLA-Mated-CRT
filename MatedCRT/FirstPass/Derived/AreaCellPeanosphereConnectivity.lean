import MatedCRT.FirstPass.Derived.AreaCellInducedConnectivity
import MatedCRT.FirstPass.Derived.AreaCellEnvironmentConfiguration
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedPoint

/-! # Connectivity of area cells in a Peanosphere embedding -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- The cells meeting a connected set induce a connected graph in Euclidean coordinates. -/
theorem MatedCRTEnv.areaCellConfig_inducedGraph_connected_of_peanosphere
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ε : ℝ} (hε : 0 < ε) (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω)) (η' : C(ℝ, ℂ)) (hη : ⇑η' = S.η ω)
    (hP : RouteM.Peanosphere (S.bm ω) η') (U : Set ReflectedGMS.Plane)
    (hU : IsConnected U) :
    ((areaCellConfig h hε (S.mult ε ω)).inducedGraph U).Connected := by
  apply areaCellConfig_inducedGraph_connected h hε (S.mult ε ω) (S.mult_symm ε ω) U
  have hH' : H.cell = fun x : ℤ => η' '' Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
    rw [hH, ← hη]
    rfl
  have hc := RouteM.connected_verticesMeeting_of_peanosphere_holds hP H hH'
    ((Complex.orthonormalBasisOneI.repr.toHomeomorph.isConnected_preimage).2 hU)
  rw [graph_adj_eq_srwGraph hlf hε.le] at hc
  rw [hH] at hc
  exact hc

/-- A Peanosphere embedding gives the line-connectivity condition for its area cells. -/
theorem MatedCRTEnv.areaCellConfig_lineConnected_of_peanosphere
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ε : ℝ} (hε : 0 < ε) (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω)) (η' : C(ℝ, ℂ)) (hη : ⇑η' = S.η ω)
    (hP : RouteM.Peanosphere (S.bm ω) η') :
    (areaCellConfig h hε (S.mult ε ω)).LineConnected := by
  apply (CellConfig.lineConnected_iff_forall_singleton
    (S.areaCellConfig_isCellConfiguration ω hε h hlf H hH)).2
  intro z
  exact S.areaCellConfig_inducedGraph_connected_of_peanosphere ω hε h hlf H hH η' hη hP
    {z} isConnected_singleton

end MatedCRT
