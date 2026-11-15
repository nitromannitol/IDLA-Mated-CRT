import MatedCRT.FirstPass.Derived.ShiftedAreaCellInducedGraph
import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfiguration
import MatedCRT.FirstPass.Derived.AreaCellPeanosphereConnectivity

/-! # Connectivity of shifted area cells in a Peanosphere embedding -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- A matching Peanosphere embedding connects the shifted cells meeting a connected set. -/
theorem shiftedAreaCellConfig_inducedGraph_connected_of_peanosphere
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (w : MatedCRTHarmonic.MatedCRT.Path2)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε w)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε w hlf) (0 : ℤ))
    (hH : H.cell = cell ε (fun t => η (t + ε * θ)))
    (hP : RouteM.Peanosphere w (fun t => η (t + ε * θ)))
    (U : Set ReflectedGMS.Plane) (hU : IsConnected U) :
    ((shiftedAreaCellConfig h hε θ
      (bmEdgeCount ε (fun t => (w t).1) (fun t => (w t).2))).inducedGraph U).Connected := by
  apply shiftedAreaCellConfig_inducedGraph_connected h hε θ _ (bmEdgeCount_symm ε _ _) U
  have hH' : H.cell = fun x : ℤ =>
      (fun t => η (t + ε * θ)) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
    exact hH
  have hc := RouteM.connected_verticesMeeting_of_peanosphere_holds hP H hH'
    ((Complex.orthonormalBasisOneI.repr.toHomeomorph.isConnected_preimage).2 hU)
  rw [graph_adj_eq_srwGraph hlf hε.le, hH] at hc
  exact hc

/-- A matching Peanosphere embedding gives line connectivity of the shifted cell configuration. -/
theorem shiftedAreaCellConfig_lineConnected_of_peanosphere
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (w : MatedCRTHarmonic.MatedCRT.Path2)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε w)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε w hlf) (0 : ℤ))
    (hH : H.cell = cell ε (fun t => η (t + ε * θ)))
    (hP : RouteM.Peanosphere w (fun t => η (t + ε * θ))) :
    (shiftedAreaCellConfig h hε θ
      (bmEdgeCount ε (fun t => (w t).1) (fun t => (w t).2))).LineConnected := by
  have hconfig := shiftedAreaCellConfig_isCellConfiguration h hε θ _ H hH
    (bmEdgeCount_symm ε _ _) (bmEdgeCount_self ε _ _) (by
      intro a b hp
      have hne : a ≠ b := by
        intro hab
        subst b
        rw [bmEdgeCount_self] at hp
        exact (lt_irrefl 0) hp
      rw [graph_adj_eq_srwGraph hlf hε.le]
      exact ⟨hne, Or.inl (Nat.ne_of_gt hp)⟩)
  apply (CellConfig.lineConnected_iff_forall_singleton hconfig).2
  intro z
  exact shiftedAreaCellConfig_inducedGraph_connected_of_peanosphere h hε θ w hlf H hH hP
    {z} isConnected_singleton

end MatedCRT
