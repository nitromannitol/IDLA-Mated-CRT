import MatedCRT.FirstPass.S4S6c.ShellOrderWindow68
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S4S6c.WindowStart68

/-!
# The edge-multiplicity hypothesis of the window route of Lemma 6.8 (z10, fp-S4S6c-window-hmult)

`exitQ_core_ae_window` (ShellOrderWindow68.lean:71) takes the binder `hmult`: almost surely, for the given `ε`, the edge
multiplicity `S.mult ε ω` is locally finite and has consecutive adjacency `m k (k+1) ≠ 0`. This file discharges that
binder for a valid environment:

* `hmult_of_valid68`: the binder, from `Uniform68Env.ae_envInputs` (Uniform68Env.lean) and `Uniform68Env.envAt`. Local
  finiteness comes from the properness of `η` and the meeting of adjacent cells (`isLocallyFiniteMult_of_cells_meet`,
  Proofs/Infra/LocallyFinite.lean); consecutive adjacency is the field `MatedCRTEnv.mult_succ_ne_zero`.
* `exitQ_core_ae_window_noMult`: `exitQ_core_ae_window` with `hmult` removed from the binders.

The explicit `0 < γ < 2` hypotheses are those of the valid environment statements (ae_envInputs, ae_adjacent); they are
not fields of `MatedCRTEnv.IsValid`, see the report. Terminology: edge multiplicity of the mated-CRT map (Duplantier-
Sheffield mating of trees), local finiteness (Armitage-Gardiner).
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68WindowMult

open MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow

/-- **The `hmult` binder of the window route, discharged (fp-S4S6c-window-hmult).** For a valid environment `S` and
`ε > 0`, almost surely the edge multiplicity `S.mult ε ω` is locally finite and has consecutive adjacency. The
conjunct on consecutive adjacency holds for every `ω` (field `mult_succ_ne_zero`); local finiteness uses the
almost-sure properness and cell-adjacency of `Uniform68Env.ae_envInputs`. -/
theorem hmult_of_valid68 {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := by
  filter_upwards [Uniform68Env.ae_envInputs hγ0 hγ2 hS] with ω hω
  obtain ⟨hlf, hsucc, -⟩ := Uniform68Env.envAt S hε ω hω.1 hω.2.1 hω.2.2
  exact ⟨hlf, hsucc⟩

/-- **`exitQ_core_ae_window` without the `hmult` binder (fp-S4S6c-window-hmult).** The binder `hmult` is discharged
by `hmult_of_valid68`; every other binder and the conclusion are those of `exitQ_core_ae_window`
(ShellOrderWindow68.lean:71-94), unchanged. -/
theorem exitQ_core_ae_window_noMult {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (ε ρ s₀ ζ q0 r c₀ C : ℝ) (hε : 0 < ε) (hs₀ : 0 < s₀) (i : Lemma68Config.Config68) (E : Set Ω)
    (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4)
    (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω) k x ≠ ⊤)
    (hone : ∀ᵐ ω ∂S.P, ω ∈ E →
      Lemma68ShellHoneInst.ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε
        (fillCells ε (S.η ω) ↑i.Θ) (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2)) :
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
        Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N :=
  exitQ_core_ae_window hγ0 hγ2 S hS ε ρ s₀ ζ q0 r c₀ C hε hs₀ i E hζ hζ1 hq0 hq1 hr hr1 hrz hrρ hRA
    hmesh hstart htest hone (hmult_of_valid68 hγ0 hγ2 S hS hε)

/-- **`exitQ_core_ae_window_noMult` with the guarded start cell discharged (fp-S4S6c-windowmult-guard).** The binder
`hstart` is discharged by `Lemma68WindowStart.hstart_fullAdm_ae` (WindowStart68.lean:58), the FullAdm-guarded start-cell
fact proved from the continuity of `η` and `cell_meets_frontier_thickening`. Every other binder and the conclusion are
those of `exitQ_core_ae_window_noMult`, unchanged. -/
theorem exitQ_core_ae_window_noMultStart {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (ε ρ s₀ ζ q0 r c₀ C : ℝ) (hε : 0 < ε) (hs₀ : 0 < s₀) (i : Lemma68Config.Config68) (E : Set Ω)
    (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4)
    (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω) k x ≠ ⊤)
    (hone : ∀ᵐ ω ∂S.P, ω ∈ E →
      Lemma68ShellHoneInst.ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε
        (fillCells ε (S.η ω) ↑i.Θ) (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2)) :
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
        Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N :=
  exitQ_core_ae_window hγ0 hγ2 S hS ε ρ s₀ ζ q0 r c₀ C hε hs₀ i E hζ hζ1 hq0 hq1 hr hr1 hrz hrρ hRA
    hmesh (Lemma68WindowStart.hstart_fullAdm_ae S hS hε hs₀ hr i) htest hone
    (hmult_of_valid68 hγ0 hγ2 S hS hε)

#print axioms MatedCRT.Lemma68WindowMult.hmult_of_valid68
#print axioms MatedCRT.Lemma68WindowMult.exitQ_core_ae_window_noMult
#print axioms MatedCRT.Lemma68WindowMult.exitQ_core_ae_window_noMultStart

end Lemma68WindowMult
end MatedCRT
