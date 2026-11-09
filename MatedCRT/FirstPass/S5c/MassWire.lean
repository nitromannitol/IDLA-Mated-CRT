import MatedCRT.FirstPass.S5c.MassBound
import MatedCRT.FirstPass.S5c.MassCluster
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CellIntegral

/-!
# FIRST PASS, Lemma 5.3: almost-sure mass bound of the filled discrete cluster (`hUmass`)

For a valid environment `S`, almost surely, for every `t > 0` and every mesh `ε > 0`, the quantum mass of the filled
discrete cluster is at most `t`: `μ (fillCells ε η (matedDiscreteCluster (S.mult ε ω) ε (η ω) ρ t)) ≤ ofReal t`
(eq. (7) of the G-5-3 note). Each cell `H^ε_a = η([ε(a-1), εa])` has mass `ε` (area parametrization,
`measure_cell_of_area_parametrized`), and the discrete cluster is finite with at most `t / ε` vertices
(`DiscreteConservationOfMassCorrectedStmt`, Draft Lemma 4.5, proved unconditionally in `discreteConservationOfMass_proved`),
so `measure_fillCells_le_of_card` applies. This is the hypothesis `hUmass` of `surplus_eventually_of_threshold`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set
open scoped ENNReal

/-- **Almost-sure mass bound of the filled discrete cluster** (G-5-3 eq. (7)): see the module docstring. -/
theorem ae_fillCells_mass_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
      S.μ ω (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)) ≤ ENNReal.ofReal t := by
  filter_upwards [discreteConservationOfMass_proved 𝒮 γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS,
    hS.isAreaParametrized] with ω hdc hap
  intro t ε ht hε
  obtain ⟨hfin, hcard, -⟩ := hdc t ε ht hε
  exact measure_fillCells_le_of_card hε hfin
    (fun k => (measure_cell_of_area_parametrized hap hε k).le) hcard

end MatedCRT.S5c
