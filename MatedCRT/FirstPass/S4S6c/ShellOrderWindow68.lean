import MatedCRT.FirstPass.S4S6c.ShellOrderOmega68
import MatedCRT.FirstPass.S4S6c.ShellHdeOmega68
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.FirstPass.S4S6c.ShellHoneInst68

/-!
# The shell order and the core step at the window radius (q2, fp-S4S6c-hU-wiring)

* `shellOrderAe_window`: the almost-sure shell order `ShellOrderAe` (ShellWire68) with the total window radius
  `windowRfT` (ShellWindowRf68.lean). It is `shellOrder_fullAdm_ae_omega` (ShellOrderOmega68.lean) with `Rf = windowRfT`
  and the constant eligibility `shortEligible ρ d a`, `d = dyadicD r`, `a = shortExp ζ`. The range `hR` holds for every
  environment (`windowRfT_bounds`). The guarded shell hypothesis `hde` is `shellHde68_full_omega` (ShellHdeOmega68.lean),
  whose only named input is the testEnd conjunct `htest`. No window prevalence is used.
* `exitQ_core_ae_window`: `exitQ_core_step` (ShellChainGlue68.lean) at the window radius, almost surely. Its `hShell` is
  supplied by `shellOrderAe_window` (no `hShell` binder); its one-test binder `hone` is the named input `ShellOneTestAt`
  (ShellHoneInst68.lean:39), assumed almost surely on the window event `E`.

Named inputs kept (routed, not discharged here): `hmesh`, `hstart`, `htest` (the q3 testEnd finite-domain lemma), the
one-test bound `hone`, and the mult facts `hmult`. Terminology: good annuli (Armstrong-Kuusi-Mourrat), shells and cell
distance (Duplantier-Sheffield).
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellOrderWindow

open MatedCRT.Lemma68WindowRf

/-- **The shell order at the total window radius, almost surely.** The guarded `hde` is discharged by
`shellHde68_full_omega` from `hmesh`, `hstart`, `htest` and the range `windowRfT_bounds`. -/
theorem shellOrderAe_window {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r c₀ C : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω) k x ≠ ⊤) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  have hRw : ∀ᵐ ω ∂S.P, ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) →
      dyadicD r ≤ windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω w ∧
        windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω w ≤ dyadicD r ^ shortExp ζ :=
    Filter.Eventually.of_forall fun ω w hw =>
      windowRfT_bounds S.μ ρ (shortExp ζ) c₀ C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r)
        (by unfold shortExp; linarith) ω hw
  have hElig : ∀ᵐ ω ∂S.P, ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) →
      w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) :=
    Filter.Eventually.of_forall fun _ _ hw => hw
  have hde := Lemma68ShellHdeOmega.shellHde68_full_omega hγ0 hγ2 S hS hε hs₀ hζ hζ1 hr hrz hrρ i
    (Rf := fun ω => windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
    (Elig := fun _ w => w ∈ shortEligible ρ (dyadicD r) (shortExp ζ))
    hRw hElig hmesh hstart htest
  exact Lemma68ShellOrderOmega.shellOrder_fullAdm_ae_omega hγ0 hγ2 S hS hε hs₀ hζ hζ1 hr hrz hrρ i
    (Rf := fun ω => windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
    (Elig := fun _ w => w ∈ shortEligible ρ (dyadicD r) (shortExp ζ))
    hRw hmesh hstart hde

/-- **The shell step of `exitQ_core_step` at the total window radius, almost surely.** `hShell` is supplied by
`shellOrderAe_window` (from `hmesh`, `hstart`, `htest`); the one-test binder `hone` (`ShellOneTestAt`,
ShellHoneInst68.lean:39) is a named a.s. input on the event `E`. -/
theorem exitQ_core_ae_window {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (ε ρ s₀ ζ q0 r c₀ C : ℝ) (hε : 0 < ε) (hs₀ : 0 < s₀) (i : Lemma68Config.Config68) (E : Set Ω)
    (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4)
    (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω) k x ≠ ⊤)
    (hone : ∀ᵐ ω ∂S.P, ω ∈ E →
      Lemma68ShellHoneInst.ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε
        (fillCells ε (S.η ω) ↑i.Θ) (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2))
    (hmult : ∀ᵐ ω ∂S.P, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
        Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
  have hShell := shellOrderAe_window (c₀ := c₀) (C := C) hγ0 hγ2 S hS hε hs₀ hζ hζ1 hr hrz hrρ i
    hmesh hstart htest
  filter_upwards [hone, hShell, hmult] with ω hone' hShell' hmult' hE hadm
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r
    (fun z => windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω z) i hζ hζ1 hq0 hq1 hr hr1 hRA
    (hone' hE) (hShell' hadm) hmult'.1 hmult'.2

end Lemma68ShellOrderWindow
end MatedCRT

#print axioms MatedCRT.Lemma68ShellOrderOmega.shellOrder_fullAdm_ae_omega
#print axioms MatedCRT.Lemma68ShellOrderWindow.shellOrderAe_window
#print axioms MatedCRT.Lemma68ShellOrderWindow.exitQ_core_ae_window
