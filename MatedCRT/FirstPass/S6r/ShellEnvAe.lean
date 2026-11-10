import MatedCRT.FirstPass.S6r.ShellPathAe
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Lemma 6.8 shell order on the environment, almost surely (`ShellEnvAe`)

`Lemma68ShellPathAe.shell_ineqs_ae` gives the four shell-order inequalities for simple random walk on the multigraph
`mm`, for a fixed environment `η`, given the map input `hmap` (adjacent cells of the map meet). Here:

* `map_cells_meet_ae` discharges `hmap` on the environment: `adjacentCellsMeetAeStep` (proved, MatingOfTrees/AdjacentCells)
  gives, `S.P`-almost surely, that every edge `S.mult ε ω j k ≠ 0` joins two intersecting cells, for all `ε > 0`.
  No literature input is used for this step (operator 09:08).
* `shell_order_env_ae` gives `ShellOrderAe` `S.P`-almost surely. Its remaining inputs are a.s. environment conditions
  (continuity of `η`, mesh, start, `F0 ⊇ {dd < r}`), the killed exit `vExitTime (killed ..) x ≠ ⊤` as an explicit
  hypothesis `hkill` (the conclusion of `ae_killed_exit_ne_top`, KilledExitAe, which cannot be imported here: its
  ExitNull68 chain clashes with GoodScale), and the finiteness/eligibility hypothesis `hde` (named, open).

This file does not import WalkBridge68 (GoodAnnulusHF68 clash).
-/

open MeasureTheory Set
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath

namespace MatedCRT
namespace Lemma68ShellEnvAe

/-- The four shell-order inequalities of `Lemma68ShellPathAe.shell_ineqs_ae` for the walk on `mm` from `a`, with
environment `η`: shell spacing `T_j ≤ T_{j+1}`, test end `L_j ≤ T_{j+1}` (both under `T_{j+1} < τ_U`), and the crossing
`T_n < τ_U`, `L_n ≤ τ_U`, all almost surely on the path. -/
def ShellOrderAe (ε : ℝ) (η : ℝ → ℂ) (Θ F0 : Finset ℤ) (r s d : ℝ) (R : ℂ → ℝ) (n : ℕ)
    (mm : ℤ → ℤ → ℕ) (a : ℤ) : Prop :=
  (∀ j < n, ∀ᵐ x ∂(srwLaw mm a),
      shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        shellExit ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
  (∀ j < n, ∀ᵐ x ∂(srwLaw mm a),
      shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        testEnd ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
  (∀ᵐ x ∂(srwLaw mm a), shellExit ε η (fillCells ε η ↑Θ) r s d R n x < vExitTime (killed ε η Θ F0 r) x) ∧
  (∀ᵐ x ∂(srwLaw mm a), testEnd ε η (fillCells ε η ↑Θ) r s d R n x ≤ vExitTime (killed ε η Θ F0 r) x)

/-- The map input of the shell chain, almost surely on the environment: every edge `S.mult ε ω j k ≠ 0` of the
mated-CRT map joins intersecting SLE cells, for all mesh sizes `ε > 0` (`adjacentCellsMeetAeStep`). -/
theorem map_cells_meet_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
  adjacentCellsMeetAeStep 𝒮 γ hγ0 hγ2 Ω S hS

/-- **Shell order on the environment.** For `S.P`-almost every environment `ω`, the four shell-order inequalities
`ShellOrderAe` hold for the walk on `S.mult ε ω` from `a`. The map input comes from `map_cells_meet_ae`; the remaining
inputs are almost-sure environment conditions and the killed exit `hkill` and finiteness/eligibility `hde`. -/
theorem shell_order_env_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop} {n : ℕ} {a : ℤ}
    (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d) (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100)
    (hΘne : Θ.Nonempty) (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hη : ∀ᵐ ω ∂S.P, Continuous (S.η ω))
    (hF0 : ∀ᵐ ω ∂S.P, ∀ v : ℤ, dd ε (S.η ω) Θ v < r → v ∈ F0)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) h Set.univ)
    (hstart : ∀ᵐ ω ∂S.P,
      (cell ε (S.η ω) a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑Θ))).Nonempty)
    (hkill : ∀ᵐ ω ∂S.P, ∀ᵐ x ∂(srwLaw (S.mult ε ω) a),
      vExitTime (killed ε (S.η ω) Θ F0 r) x ≠ ⊤)
    (hde : ∀ᵐ ω ∂S.P, ∀ᵐ x ∂(srwLaw (S.mult ε ω) a),
      (∀ k ≤ n, shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑Θ) r s d R k x ≠ ⊤ ∧
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑Θ) r s d R k x ≠ ⊤) ∧
      (∀ k ≤ n, Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑Θ) r s d k x))) :
    ∀ᵐ ω ∂S.P, ShellOrderAe ε (S.η ω) Θ F0 r s d R n (S.mult ε ω) a := by
  filter_upwards [hη, hF0, hmesh, hstart, hkill, hde, map_cells_meet_ae hγ0 hγ2 S hS]
    with ω hη' hF0' hmesh' hstart' hkill' hde' hmap'
  exact Lemma68ShellPathAe.shell_ineqs_ae hη' hε hr hs hs4 hd hh hds hΘne hR hF0' hmesh' hNs hstart'
    (hmap' ε hε) (hkill'.and hde')

end Lemma68ShellEnvAe
end MatedCRT
