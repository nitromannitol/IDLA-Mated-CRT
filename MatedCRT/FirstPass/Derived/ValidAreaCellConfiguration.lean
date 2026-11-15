import MatedCRT.FirstPass.Derived.ValidAreaCellConnectivity
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp210

/-! # Area-cell configurations in valid environments -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.GMSMain

/-- At each fixed positive mesh, a valid environment almost surely has a line-connected
area-cell configuration, with connected induced graphs on all connected sets. -/
theorem MatedCRTEnv.IsValid.ae_areaCellConfig_isCellConfiguration
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration ∧
      (∀ U : Set ReflectedGMS.Plane, IsConnected U →
        ((areaCellConfig h hε (S.mult ε ω)).inducedGraph U).Connected) ∧
      (areaCellConfig h hε (S.mult ε ω)).LineConnected := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ηc, _, hC, hη⟩ := hS.matingOfTrees
  filter_upwards [hS.isAreaParametrized, hη, epsA_ae_exists_cellularEmbedding hC hε,
    hS.ae_areaCellConfig_connected S] with ω harea hηω hemb hconn
  obtain ⟨hlf, H, hH⟩ := hemb
  have hcell : H.cell = cell ε (S.η ω) := by
    funext x
    rw [hH x, cell, ← hηω.1]
  exact ⟨harea, S.areaCellConfig_isCellConfiguration ω hε harea hlf H hcell,
    hconn ε hε harea hlf H hcell⟩

/-- A deterministic countable family of positive meshes has the configuration and
connectivity properties on one common almost-sure event. -/
theorem MatedCRTEnv.IsValid.ae_areaCellConfig_isCellConfiguration_countable
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∀ᵐ ω ∂S.P, ∀ i, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (areaCellConfig h (hε i) (S.mult (ε i) ω)).IsCellConfiguration ∧
      (∀ U : Set ReflectedGMS.Plane, IsConnected U →
        ((areaCellConfig h (hε i) (S.mult (ε i) ω)).inducedGraph U).Connected) ∧
      (areaCellConfig h (hε i) (S.mult (ε i) ω)).LineConnected :=
  ae_all_iff.2 fun i => hS.ae_areaCellConfig_isCellConfiguration S (hε i)

end MatedCRT
