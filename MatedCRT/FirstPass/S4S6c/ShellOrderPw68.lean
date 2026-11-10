import MatedCRT.FirstPass.S4S6c.ShellOrderOmega68
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68

/-!
# The pointwise shell order at one environment (q4, fp-S4S6c-shell-pointwise)

The pointwise cores (fixed environment `ω`) of two almost-sure shell-order lemmas.

* `Lemma68ShellOrderPw.shellOrder_fullAdm_pw`: the core of `shellOrder_fullAdm_ae_omega` (ShellOrderOmega68.lean:28).
  The almost-sure proof filters over five environment facts. Here each one is a hypothesis at `ω`, in the same form as
  the a.s. statement at `ω`: the continuity of `η ω` (`TraceInputs68.ae_continuous_eta`), the cell adjacency at the scale
  `ε` (`Lemma68ShellEnvAe.map_cells_meet_ae`), the killed exit `hkill` (`Lemma68ShellEnvAeInputs.hkill_of_valid`), the
  range `hR`, the mesh `hmesh` and the start `hstart` (both guarded as in the a.s. statement), and the shell-hde `hde`.
* `Lemma68ShellOrderPw.shellOrderAe_window_pw`: the core of `shellOrderAe_window` (ShellOrderWindow68.lean:34) at the
  total window radius `windowRfT` (ShellWindowRf68.lean:56). The range is `windowRfT_bounds`, valid for every `ω`. The
  shell-hde input `hde` is supplied by the caller (the pointwise `shellHde68_full_pw`, ShellHdePw68.lean).

The mesh is the univ form `CellDiamLe ε η (dyadicD r / 100) Set.univ`, because `shellOrderAe_of_path`
(ShellWire68.lean:56, forwarded to `shell_ineqs_ae` at ShellWire68.lean:65) takes it on the whole line.

Terminology: cell distance and cell diameter (Duplantier-Sheffield); shells and good annuli (Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry
open MatedCRT.Lemma68WindowRf

namespace MatedCRT
namespace Lemma68ShellOrderPw

/-- **The shell order from the full guard at one environment (pointwise core of `shellOrder_fullAdm_ae_omega`).**
Every environment fact of the almost-sure proof is taken at `ω`. The conclusion is the guarded `ShellOrderAe` of
ShellOrderOmega68.lean:28 at `ω`. -/
theorem shellOrder_fullAdm_pw {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hη : Continuous (S.η ω))
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hde : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  -- deterministic parameter facts (as in shellOrder_fullAdm_ae_omega)
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
  intro hadm
  have hstA := hstart hadm
  have hdeA := hde hadm
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm
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
    have hmem := hmono (Lemma68ShellOrderFullAdm.dd_lt_mem_cellVertices_thickening hη hε hK hr hv)
    rw [← hF0eq] at hmem
    exact Finset.mem_coe.1 hmem
  exact Lemma68ShellWire.shellOrderAe_of_path hη hε hr hs hs4 hd le_rfl hds hΘ hR hF0 hmesh hNs hstA hmap
    (hkill.and hdeA)

/-- **The shell order at the total window radius at one environment (pointwise core of `shellOrderAe_window`).**
The range `hR` is `windowRfT_bounds` on the short-eligible set, for every environment. The shell-hde input `hde` is the
pointwise `shellHde68_full_pw` (ShellHdePw68.lean), supplied by the caller. -/
theorem shellOrderAe_window_pw {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ε ρ s₀ ζ c₀ C r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    (hη : Continuous (S.η ω))
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hde : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω) k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a :=
  shellOrder_fullAdm_pw (γ := γ) S ω hε hs₀ hζ hζ1 hr hrz hrρ i
    (Rf := windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
    (Elig := fun w => w ∈ shortEligible ρ (dyadicD r) (shortExp ζ)) hη hmap hkill
    (fun w hw => windowRfT_bounds S.μ ρ (shortExp ζ) c₀ C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r)
      (by unfold shortExp; linarith) ω hw) hmesh hstart hde

end Lemma68ShellOrderPw
end MatedCRT

#print axioms MatedCRT.Lemma68ShellOrderPw.shellOrder_fullAdm_pw
#print axioms MatedCRT.Lemma68ShellOrderPw.shellOrderAe_window_pw
