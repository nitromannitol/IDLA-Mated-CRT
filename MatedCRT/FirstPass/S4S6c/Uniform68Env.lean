import MatedCRT.FirstPass.S4S6c.Uniform68Walk
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.Proofs.Infra.LocallyFinite

/-!
# Environment inputs of the walk-level Lemma 6.8 (q2, task fp-S4S6c-envscaling-6-7-6-8, file `Uniform68Env.lean`)

`Uniform68Walk.config_exit_lower_bound_walk` takes four environment inputs for the embedding `η` and the edge
multiplicity `m` of the map `𝒢^ε`: properness of `η`, local finiteness of `m`, consecutive adjacency
`m k (k+1) ≠ 0`, and adjacency of cells. This file supplies them for a valid environment `S`:

* almost surely `η` is continuous and proper (`TraceInputs68.ae_continuous_eta`, `IsValid.ae_tendsto_cocompact`);
* almost surely, for every `ε > 0`, adjacent vertices of `𝒢^ε` have meeting cells (`TraceInputs68.ae_adjacent`);
* local finiteness of `m` from properness and cell adjacency (`isLocallyFiniteMult_of_cells_meet`,
  Proofs/Infra/LocallyFinite.lean);
* consecutive adjacency `m k (k+1) ≠ 0` for every `ω` and `ε ≥ 0` (`MatedCRTEnv.mult_succ_ne_zero`).

All four are proved in the repository; no literature input is used. Terminology: edge multiplicity of the mated-CRT
map (Duplantier-Sheffield mating of trees), properness and local finiteness (Armitage-Gardiner).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

namespace Uniform68Env

variable {Ω : Type} [MeasurableSpace Ω]

/-- Almost surely, `η` is continuous and proper, and for every `ε > 0` adjacent vertices of `𝒢^ε` have meeting cells. -/
theorem ae_envInputs {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    TraceInputs68.ae_adjacent hγ hγ2 S hS] with ω hc hp hadj
  exact ⟨hc, hp, hadj⟩

/-- The environment inputs of `Uniform68Walk.config_exit_lower_bound_walk` at one `ω` and one `ε > 0`: local
finiteness of `S.mult ε ω`, consecutive adjacency, and adjacency of cells. -/
theorem envAt (S : MatedCRTEnv Ω) {ε : ℝ} (hε : 0 < ε) (ω : Ω)
    (hc : Continuous (S.η ω)) (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) :
    IsLocallyFiniteMult (S.mult ε ω) ∧ (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧
      ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
  ⟨isLocallyFiniteMult_of_cells_meet hc hp hε (hadj ε hε), fun k => S.mult_succ_ne_zero hε.le ω k, hadj ε hε⟩

end Uniform68Env

end MatedCRT
