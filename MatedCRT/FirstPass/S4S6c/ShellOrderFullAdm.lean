import MatedCRT.FirstPass.S4S6c.ShellWire68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S6r.ShellEnvAeInputs
import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S6e.GeometryId
import MatedCRT.FirstPass.S6e.Relation
import MatedCRT.FirstPass.S6r.Count
import MatedCRT.FirstPass.S6r.Window

/-!
# The shell order `hShell` of `exitQ_core_step` from the full admissibility guard (fp-S4S6c-shell-order-fulladm)

`exitQ_core_step` (S4S6c/ShellChainGlue68.lean) takes the shell order `hShell : ShellOrderAe ..` as a binder, for the
parameters `s = dyadicD r ^ shortExp ζ`, `d = dyadicD r`, `R = Rf`, `n = shellCount r s - 1`. This file proves it almost
surely, for every configuration satisfying the full guard `FullAdm` (S6h/Core.lean), from the path lemma
`shellOrderAe_of_path` (S4S6c/ShellWire68.lean).

Pointwise, the inputs of `shellOrderAe_of_path` are:
* continuity of `η` (`TraceInputs68.ae_continuous_eta`, almost surely);
* the meeting of adjacent cells (`Lemma68ShellEnvAe.map_cells_meet_ae`, almost surely);
* the killed exit is finite (`Lemma68ShellEnvAeInputs.hkill_of_valid`, almost surely);
* `Θ ≠ ∅`, and `hF0 : dd ε η Θ v < r → v ∈ F0`: both come from `FullAdm` alone. `FullAdm` gives `F0 = cellVertices ε η (ball 0 ρ)`
  and `closure (fillCells Θ) ⊆ ball 0 (ρ/2)`; with `r ≤ ρ/4` the thickening `thickening r (fillCells Θ)` lies in `ball 0 ρ`,
  and `dd < r` puts the vertex in `cellVertices (thickening r (fillCells Θ))` (`cellVertices_thickening_eq`, with
  `cellDist_ne_top` for the finiteness of the cell distance);
* the shell parameters: `s ≤ r/4000` (`shell_size_le`), `d ≤ s` (`d ≤ 1`, `shortExp ζ ≤ 1`), `20 (n+1) s ≤ r/20`
  (`shellCount` is `⌊r/(400 s)⌋₊`), `h := d/100`;
* NOT derivable from `FullAdm`, kept as named a.s. binders with their exact types: `hmesh` (the global mesh bound
  `CellDiamLe ε η h univ`), `hstart` (the start cell meets the frontier of the `r/2`-thickening), `hde` (finiteness of the
  shell exits and test ends, and the eligibility `Elig` of the shell centres; `hde` of ShellEnvAe.lean:52), and the range
  `hR` of `Rf` on `Elig` (a property of the instantiation of `Elig` by the caller).

The conclusion is pointwise in the environment `ω`: `FullAdm` is a pointwise guard, and `hF0` needs it at the same `ω`.
Not using `shell_order_env_ae_closed` (S6r/ShellEnvAeInputs.lean:45), whose `hF0` is almost sure and would need
`FullAdm` almost surely.
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellOrderFullAdm

/-- **The vertices at cell distance below `r` from the filled set lie in its `r`-thickening.** For a continuous `η`, a
nonempty filled set `K = fillCells Θ` and `r > 0`: `dd ε η Θ v < r` (the cell distance `d_v` of Duplantier-Sheffield's
cell-distance notation, finite by `cellDist_ne_top`) gives `v ∈ cellVertices ε η (thickening r K)`. -/
theorem dd_lt_mem_cellVertices_thickening {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {Θ : Finset ℤ}
    (hK : (fillCells ε η ↑Θ).Nonempty) {r : ℝ} (hr : 0 < r) {v : ℤ} (hv : dd ε η Θ v < r) :
    v ∈ cellVertices ε η (Metric.thickening r (fillCells ε η ↑Θ)) := by
  rw [cellVertices_thickening_eq hη hε Θ r]
  show cellDist ε η Θ v < ENNReal.ofReal r
  have hne := Lemma68Relation.cellDist_ne_top hη hε hK v
  rw [← ENNReal.ofReal_toReal hne]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hv

/-- **The shell order from the full guard, almost surely (fp-S4S6c-shell-order-fulladm).** For the configuration
`i : Config68` at radius `r`, with the shell parameters `s = dyadicD r ^ shortExp ζ`, `d = dyadicD r`, `n = shellCount r s - 1`
and the eligibility predicate `Elig` of the caller: for `S.P`-almost every environment `ω`, if the full guard
`FullAdm S ρ s₀ γ ε ω r i` holds, then `ShellOrderAe` holds for the walk on `S.mult ε ω` from `i.a`, with the exact
parameters of the binder `hShell` of `exitQ_core_step`. The almost-sure binders are `hmesh`, `hstart`, `hde`; `hR` is the
range of `Rf` on `Elig`. -/
theorem shellOrder_fullAdm_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P,
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hde : ∀ᵐ ω ∂S.P, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ ∧
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
      (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  -- deterministic parameter facts
  have hr1 : r ≤ 1 := hrz.trans (countThreshold_le_one hζ)
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hd2 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ hr hrz hd hd2
  have hds : dyadicD r / 100 ≤ dyadicD r ^ shortExp ζ / 100 := by
    have h1 : dyadicD r ^ (1 : ℝ) ≤ dyadicD r ^ shortExp ζ :=
      Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    rw [Real.rpow_one] at h1
    linarith
  have h400 : 400 * dyadicD r ^ shortExp ζ ≤ r := by linarith
  have hc1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ (by linarith)]
    linarith
  have hfl : (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) * (400 * dyadicD r ^ shortExp ζ) ≤ r := by
    have h := Nat.floor_le (show 0 ≤ r / (400 * dyadicD r ^ shortExp ζ) by positivity)
    exact (le_div_iff₀ (by linarith)).1 h
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ ≤ r / 20 := by
    rw [Nat.sub_add_cancel hc1]
    nlinarith [hfl]
  -- almost sure environment facts
  filter_upwards [TraceInputs68.ae_continuous_eta hS, Lemma68ShellEnvAe.map_cells_meet_ae hγ0 hγ2 S hS,
    Lemma68ShellEnvAeInputs.hkill_of_valid hγ0 hγ2 S hS hε (Θ := i.Θ) (F0 := i.F0) (r := r) (a := i.a),
    hmesh, hstart, hde] with ω hη hmap hkill hm hst hdeω
  intro hadm
  unfold Lemma68Config.FullAdm Lemma68Config.ConfigOK at hadm
  obtain ⟨⟨hF0eq, hcl, hball⟩, -⟩ := hadm
  have hK : (fillCells ε (S.η ω) ↑i.Θ).Nonempty := ⟨0, hball (Metric.mem_ball_self hs₀)⟩
  have hΘ : i.Θ.Nonempty := by
    rcases i.Θ.eq_empty_or_nonempty with h0 | h0
    · exfalso
      have h1 := hball (Metric.mem_ball_self hs₀)
      rw [h0] at h1
      simp [fillCells] at h1
    · exact h0
  -- the thickening of the filled set lies in B_ρ, so the vertices at cell distance < r lie in F0
  have hsub : Metric.thickening r (fillCells ε (S.η ω) ↑i.Θ) ⊆ Metric.ball (0 : ℂ) ρ := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.1 hx
    have hz' : z ∈ Metric.ball (0 : ℂ) (ρ / 2) := hcl (subset_closure hz)
    rw [Metric.mem_ball] at hz' ⊢
    have htri := dist_triangle x z (0 : ℂ)
    linarith
  have hF0 : ∀ v : ℤ, dd ε (S.η ω) i.Θ v < r → v ∈ i.F0 := by
    intro v hv
    have hmono : cellVertices ε (S.η ω) (Metric.thickening r (fillCells ε (S.η ω) ↑i.Θ)) ⊆
        cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) ρ) := by
      intro k hk
      obtain ⟨y, hy1, hy2⟩ := hk
      exact ⟨y, hy1, hsub hy2⟩
    have hmem := hmono (dd_lt_mem_cellVertices_thickening hη hε hK hr hv)
    rw [← hF0eq] at hmem
    exact Finset.mem_coe.1 hmem
  exact Lemma68ShellWire.shellOrderAe_of_path hη hε hr hs hs4 hd le_rfl hds hΘ hR hF0 hm hNs hst (hmap ε hε)
    (hkill.and hdeω)

end Lemma68ShellOrderFullAdm
end MatedCRT
