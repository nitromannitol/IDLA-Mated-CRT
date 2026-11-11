import MatedCRT.FirstPass.S6r.ShellEnvAe
import MatedCRT.FirstPass.S6r.KilledExitAe
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# Inputs of the shell order on the environment (`ShellEnvAeInputs`)

`shell_order_env_ae` (ShellEnvAe) takes two binders about the walk on `S.mult ε ω` from `a`:

* `hkill` (the killed exit time is finite, almost surely): **proved here** as `hkill_of_valid`, from `S.IsValid 𝒮 γ`
  alone. The multigraph `S.mult ε ω` is locally finite for `S.P`-almost every `ω` (`isLocallyFiniteMult_of_cells_meet`
  from continuity of `η`, properness of `η` and adjacency of meeting cells), and consecutive vertices are always adjacent
  (`MatedCRTEnv.mult_succ_ne_zero`); then `ae_killed_exit_ne_top` (KilledExitAe) gives the claim.
* `hde` (finite shell exits and test ends, and eligibility of the shell centres, for `k ≤ n`): **not derivable** from
  `S.IsValid` and the other binders. The eligibility conjunct `Elig (shellCentre ..)` is about the predicate `Elig`, which
  the theorem leaves free: no binder constrains `Elig` beyond `hR`, which is vacuous for `Elig ≡ False`. The finiteness
  conjunct needs the crossing of the shells `twoSidedShell` by the chain of intersecting cells before the killed exit.
  Kept as the named hypothesis `hde` of `shell_order_env_ae_closed`, with the exact type of `shell_order_env_ae`.
-/

open MeasureTheory Set
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath

namespace MatedCRT
namespace Lemma68ShellEnvAeInputs

/-- **`hkill`, proved.** For the mated-CRT environment `S` with `S.IsValid 𝒮 γ`, almost surely the killed exit time of
simple random walk on `S.mult ε ω` from `a` is finite, almost surely in the walk. This is the binder `hkill` of
`shell_order_env_ae` (ShellEnvAe.lean:50), with the same type. -/
theorem hkill_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) {Θ F0 : Finset ℤ} {r : ℝ} {a : ℤ} :
    ∀ᵐ ω ∂S.P, ∀ᵐ x ∂(srwLaw (S.mult ε ω) a), vExitTime (killed ε (S.η ω) Θ F0 r) x ≠ ⊤ := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    Lemma68ShellEnvAe.map_cells_meet_ae hγ0 hγ2 S hS] with ω hc hp hmeet
  have hlf : IsLocallyFiniteMult (S.mult ε ω) :=
    isLocallyFiniteMult_of_cells_meet hc hp hε (hmeet ε hε)
  exact Lemma68KilledExitAe.ae_killed_exit_ne_top hlf (fun k => S.mult_succ_ne_zero hε.le ω k) a ε (S.η ω) Θ F0 r

/-- **`shell_order_env_ae` without `hkill`.** The killed-exit binder is discharged by `hkill_of_valid`; the remaining named
hypothesis is `hde` (exact type of ShellEnvAe.lean:52, not derivable from `S.IsValid`; see the module docstring).
Same conclusion as `shell_order_env_ae`. -/
theorem shell_order_env_ae_closed {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop} {n : ℕ} {a : ℤ}
    (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d) (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100)
    (hΘne : Θ.Nonempty) (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hη : ∀ᵐ ω ∂S.P, Continuous (S.η ω))
    (hF0 : ∀ᵐ ω ∂S.P, ∀ v : ℤ, dd ε (S.η ω) Θ v < r → v ∈ F0)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) h Set.univ)
    (hstart : ∀ᵐ ω ∂S.P,
      (cell ε (S.η ω) a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑Θ))).Nonempty)
    (hde : ∀ᵐ ω ∂S.P, ∀ᵐ x ∂(srwLaw (S.mult ε ω) a),
      (∀ k ≤ n, shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑Θ) r s d R k x ≠ ⊤ ∧
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑Θ) r s d R k x ≠ ⊤) ∧
      (∀ k ≤ n, Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑Θ) r s d k x))) :
    ∀ᵐ ω ∂S.P, Lemma68ShellOrder.ShellOrderAe ε (S.η ω) Θ F0 r s d R n (S.mult ε ω) a :=
  Lemma68ShellEnvAe.shell_order_env_ae hγ0 hγ2 S hS hε hr hs hs4 hd hh hds hΘne hR hNs hη hF0 hmesh hstart
    (hkill_of_valid hγ0 hγ2 S hS hε) hde

end Lemma68ShellEnvAeInputs
end MatedCRT
