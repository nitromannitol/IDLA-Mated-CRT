import MatedCRT.FirstPass.S4S6c.Uniform68Env

/-!
# The edge-multiplicity hypothesis of the window route of Lemma 6.8 (z10, fp-S4S6c-window-hmult)

`exitQ_core_ae_window` (ShellOrderWindow68.lean:71) takes the binder `hmult`: almost surely, for the given `ε`, the edge
multiplicity `S.mult ε ω` is locally finite and has consecutive adjacency `m k (k+1) ≠ 0`. This file discharges that
binder for a valid environment:

* `hmult_of_valid68`: the binder, from `Uniform68Env.ae_envInputs` and `Uniform68Env.envAt` (Uniform68Env.lean). Local
  finiteness comes from the properness of `η` and the meeting of adjacent cells (`isLocallyFiniteMult_of_cells_meet`,
  Proofs/Infra/LocallyFinite.lean); consecutive adjacency is `MatedCRTEnv.mult_succ_ne_zero`
  (Proofs/Infra/MatingOfTrees.lean:70), which needs only `0 ≤ ε`.

The explicit `0 < γ < 2` hypotheses are those of the environment inputs (`ae_envInputs`, `ae_adjacent`); they are not
fields of `MatedCRTEnv.IsValid`. Terminology: edge multiplicity of the mated-CRT map (Duplantier-Sheffield mating of
trees), local finiteness (Armitage-Gardiner).

The companion `exitQ_core_ae_window_noMult` (the window route with `hmult` discharged) needs `ShellOrderWindow68`, which
imports the currently uncompilable working-tree `ShellHoneInst68`; it is not in this module yet.
-/

open MeasureTheory Set Filter

namespace MatedCRT
namespace Lemma68WindowMult

/-- **The `hmult` binder of the window route, discharged (fp-S4S6c-window-hmult).** For a valid environment `S` and
`ε > 0`, almost surely the edge multiplicity `S.mult ε ω` is locally finite and has consecutive adjacency. The
conjunct on consecutive adjacency holds for every `ω` (`MatedCRTEnv.mult_succ_ne_zero`); local finiteness uses the
almost-sure properness and cell adjacency of `Uniform68Env.ae_envInputs`. -/
theorem hmult_of_valid68 {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := by
  filter_upwards [Uniform68Env.ae_envInputs hγ0 hγ2 hS] with ω hω
  obtain ⟨hlf, hsucc, -⟩ := Uniform68Env.envAt S hε ω hω.1 hω.2.1 hω.2.2
  exact ⟨hlf, hsucc⟩

end Lemma68WindowMult
end MatedCRT
