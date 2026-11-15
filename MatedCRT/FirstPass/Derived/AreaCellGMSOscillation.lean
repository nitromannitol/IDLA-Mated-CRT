import MatedCRT.FirstPass.Derived.GMSExitOscillation
import MatedCRT.FirstPass.Derived.AreaCellLaw
import MatedCRT.FirstPass.Derived.AreaCellRepresentative

/-! # Neighboring exits for area-cell walks -/

set_option autoImplicit false

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal
open ReflectedGMS ReflectedGMS.GMS
open LatticeProb.UnboundedRayIntervalIntegrand

namespace MatedCRT

/-- A measurable realization of a GMS configuration transfers the fixed-start
neighboring-exit estimate to the corresponding area-cell random walk. -/
theorem MatedCRTEnv.ae_areaCell_tendsto_ballExitOscillation
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (F : Ω → GMSSpace) (hF : AEMeasurable F S.P)
    [IsProbabilityMeasure (S.P.map F)]
    (hmt : MassTransport (S.P.map F)) (herg : ErgodicModuloScaling (S.P.map F))
    (hfin : FiniteExpectation (S.P.map F)) (hconn : ConnectedAlongLines (S.P.map F))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (μ : Measure ℂ) (h : IsAreaParametrized μ (S.η ω)),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω) →
      IsLocallyFiniteMult (S.mult ε ω) → ∀ a : ℤ,
      ∀ (s : ℕ → ℝ≥0), Tendsto s atTop (𝓝[>] 0) →
      ∀ (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) →
      ∀ r η : ℝ, 0 < r → 0 < η →
        Tendsto (fun n => ((srwLaw (S.mult ε ω) a).map
          (fun p k => euclideanCellEquiv h hε (p k)))
          (((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
            (areaCellRepresentative h hε (S.mult ε ω)) (s n)) ⁻¹'
              (ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η)ᶜ))
            atTop (𝓝 0) := by
  have hgood := ae_tendsto_ballExitOscillation (S.P.map F) hmt herg hfin hconn
  filter_upwards [ae_of_ae_map hF hgood] with ω hω
  intro μ h heq hlf a s hs δ hδ r η hr hη
  rw [heq] at hω
  exact hω (euclideanCellEquiv h hε a) _ (S.areaCellConfig_isSRWLaw ω h hε hlf a)
    (areaCellRepresentative h hε (S.mult ε ω))
    (areaCellRepresentative_mem h hε (S.mult ε ω)) s hs δ hδ r η hr hη

/-- The same estimate, expressed directly under the integer walk law. -/
theorem MatedCRTEnv.ae_integerWalk_tendsto_ballExitOscillation
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (F : Ω → GMSSpace) (hF : AEMeasurable F S.P)
    [IsProbabilityMeasure (S.P.map F)]
    (hmt : MassTransport (S.P.map F)) (herg : ErgodicModuloScaling (S.P.map F))
    (hfin : FiniteExpectation (S.P.map F)) (hconn : ConnectedAlongLines (S.P.map F))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (μ : Measure ℂ) (h : IsAreaParametrized μ (S.η ω)),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω) →
      IsLocallyFiniteMult (S.mult ε ω) → ∀ a : ℤ,
      ∀ (s : ℕ → ℝ≥0), Tendsto s atTop (𝓝[>] 0) →
      ∀ (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) →
      ∀ r η : ℝ, 0 < r → 0 < η →
        Tendsto (fun n => (srwLaw (S.mult ε ω) a)
          {p | (areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
            (areaCellRepresentative h hε (S.mult ε ω)) (s n)
            (fun k => euclideanCellEquiv h hε (p k)) ∉
              ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η})
            atTop (𝓝 0) := by
  filter_upwards [S.ae_areaCell_tendsto_ballExitOscillation F hF hmt herg hfin hconn hε]
    with ω hω
  intro μ h heq hlf a s hs δ hδ r η hr hη
  let C := areaCellConfig h hε (S.mult ε ω)
  let e := euclideanCellEquiv h hε
  let : Countable C.cells := Countable.of_equiv ℤ e
  let e' : ℤ ≃ᵐ C.cells :=
    { toEquiv := e
      measurable_toFun := measurable_of_countable _
      measurable_invFun := measurable_of_countable _ }
  let E : (ℕ → ℤ) ≃ᵐ (ℕ → C.cells) := MeasurableEquiv.piCongrRight (fun _ => e')
  have hres := hω μ h heq hlf a s hs δ hδ r η hr hη
  have hequal : ∀ n, ((srwLaw (S.mult ε ω) a).map E)
      ((C.interpolatedWalk (areaCellRepresentative h hε (S.mult ε ω)) (s n)) ⁻¹'
        (ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η)ᶜ) =
      (srwLaw (S.mult ε ω) a)
        {p | C.interpolatedWalk (areaCellRepresentative h hε (S.mult ε ω)) (s n)
          (fun k => e (p k)) ∉
            ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η} := by
    intro n
    exact E.map_apply _
  change Tendsto (fun n => ((srwLaw (S.mult ε ω) a).map E)
    ((C.interpolatedWalk (areaCellRepresentative h hε (S.mult ε ω)) (s n)) ⁻¹'
      (ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η)ᶜ)) atTop (𝓝 0) at hres
  simpa only [hequal] using hres

end MatedCRT
