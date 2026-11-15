import MatedCRT.FirstPass.Derived.AnisotropicTargetExitOscillation
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116
import LatticeProb.Prob.CellConfigWalkMeasurable

/-! # Neighboring exits for walks in random cell configurations -/

set_option autoImplicit false

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal
open ReflectedGMS ReflectedGMS.GMS ReflectedGMS.StatementIngredients
open LatticeProb.UnboundedRayIntervalIntegrand

namespace MatedCRT

/-- Under the hypotheses of the GMS invariance principle, neighboring ball-exit
oscillations vanish in probability for each fixed starting cell and walk law. -/
theorem ae_tendsto_ballExitOscillation
    (μ : Measure GMSSpace) [IsProbabilityMeasure μ]
    (hmt : MassTransport μ) (herg : ErgodicModuloScaling μ)
    (hfin : FiniteExpectation μ) (hconn : ConnectedAlongLines μ) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)),
        H.1.IsSRWLaw K₀ Q → ∀ p : H.1.cells → Plane,
        (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
        ∀ (ε : ℕ → ℝ≥0), Tendsto ε atTop (𝓝[>] 0) →
        ∀ (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) →
        ∀ r η : ℝ, 0 < r → 0 < η →
          Tendsto (fun n => Q ((H.1.interpolatedWalk p (ε n)) ⁻¹'
            (ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η)ᶜ))
              atTop (𝓝 0) := by
  obtain ⟨target, hconv, hrec, _⟩ := theorem1_16 μ hmt herg hfin hconn
  filter_upwards [hconv, LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk hconn hrec]
    with H hW hY K₀ Q hQ p hp ε hε δ hδ r η hr hη
  have : IsProbabilityMeasure Q := hQ.1
  exact tendsto_measure_ballExitOscillationGood_compl_of_convergesWeaklyInC
    Q (H.1.interpolatedWalk p) target (hY K₀ Q hQ p) (hW K₀ Q hQ p hp)
    hε hδ hr hη

end MatedCRT
