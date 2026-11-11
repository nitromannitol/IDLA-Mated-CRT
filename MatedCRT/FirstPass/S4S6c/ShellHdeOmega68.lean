import MatedCRT.FirstPass.S4S6c.ShellHde68

/-!
# The shell hypothesis `hde` with an environment-dependent radius, almost surely

`shellHde_ae68` and `shellHde68_full` (S4S6c/ShellHde68.lean:304, :367) take the radius `Rf : ℂ → ℝ` and the eligibility
predicate `Elig : ℂ → Prop` as FIXED parameters. The window radius `windowRfT S.μ ρ a c₀ C d ω` (S4S6c/ShellWindowRf68.lean:56)
depends on the environment `ω`, so those two lemmas cannot be applied to it. This file states the same two results with
`Rf ω` and `Elig ω` evaluated at the environment `ω`. They give the guarded binder `hde` of `shellOrder_fullAdm_ae_omega`
(S4S6c/ShellOrderOmega68.lean). The proofs are the pointwise proofs of ShellHde68.lean (lines 305-362 and 364-374), with
`Rf`, `Elig`, `hR`, `hElig` taken at `ω`; the environment facts used are the same almost-sure facts. ShellHde68.lean is not
edited. The testEnd conjunct stays the named almost-sure input `htest` (not yet committed).

Terminology: shells and cell distance (Duplantier-Sheffield); good annuli and the shell chain (Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellHdeOmega

open MatedCRT.Lemma68ShellHde68

/-- **The shell hypothesis `hde`, almost surely, guarded by `FullAdm`, with an environment-dependent radius.**
`shellHde_ae68` (ShellHde68.lean:304) with `Rf ω` and `Elig ω`; `hR` and `hElig` are almost sure. -/
theorem shellHde_ae68_omega {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : Ω → ℂ → ℝ} {Elig : Ω → ℂ → Prop}
    (hR : ∀ᵐ ω ∂S.P, ∀ w, Elig ω w → dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ᵐ ω ∂S.P, ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig ω w)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) := by
  -- deterministic parameter facts (as in shellHde_ae68)
  have hr1 : r ≤ 1 := hrz.trans (countThreshold_le_one hζ)
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hd2 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ hr hrz hd hd2
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h1 : dyadicD r ^ (1 : ℝ) ≤ dyadicD r ^ shortExp ζ :=
      Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    rw [Real.rpow_one] at h1
    exact h1
  have h400 : 400 * dyadicD r ^ shortExp ζ ≤ r := by
    have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
    linarith
  have hc1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ (by linarith)]
    linarith
  have hfl : (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) * (400 * dyadicD r ^ shortExp ζ) ≤ r := by
    have h := Nat.floor_le (show 0 ≤ r / (400 * dyadicD r ^ shortExp ζ) by
      have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
      positivity)
    exact (le_div_iff₀ (by linarith)).1 h
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hc1]
    nlinarith [hfl]
  -- almost sure environment facts; the radius facts `hR` and `hElig` are taken at the same `ω`
  filter_upwards [TraceInputs68.ae_continuous_eta hS, Lemma68ShellEnvAe.map_cells_meet_ae hγ0 hγ2 S hS,
    Lemma68ShellEnvAeInputs.hkill_of_valid hγ0 hγ2 S hS hε (Θ := i.Θ) (F0 := i.F0) (r := r) (a := i.a),
    hmesh, hstart, hR, hElig] with ω hη hmap _hkill hm hst hRω hEω
  intro hadm
  have hstA := hst hadm
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm
  obtain ⟨⟨hF0eq, hcl, hball⟩, -⟩ := hadm
  have h0K : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hball (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := fun y hy => hcl (subset_closure hy)
  have hRS : ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ := fun w hw => hRω w (hEω w hw)
  filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
    Lemma68ShellPathAe.ae_cell_adjacent (S.mult ε ω) i.a hε (hmap ε hε), _hkill] with x hx0 hadj hτ
  have hpath := shell_fin_of_path (ε := ε) (R := Rf ω) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hη hε hr hrρ hd hds hs4 hNs hm hF0eq h0K hKb hRS hadj (by rw [hx0]; exact hstA) hτ
  exact ⟨fun k hk => (hpath k hk).1, fun k hk => hEω _ (hpath k hk).2⟩

/-- **The full shell hypothesis `hde`, almost surely, with an environment-dependent radius.** The testEnd conjunct is the
named almost-sure input `htest` (the finite-domain exit statement for the test ends, guarded by `FullAdm`). The conclusion
is the conjunction of `shellHde_ae68_omega` with `htest`: the form of `shellHde68_full` (ShellHde68.lean:367) at `Rf ω`,
`Elig ω`. -/
theorem shellHde68_full_omega {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : Ω → ℂ → ℝ} {Elig : Ω → ℂ → Prop}
    (hR : ∀ᵐ ω ∂S.P, ∀ w, Elig ω w → dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ᵐ ω ∂S.P, ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig ω w)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) := by
  filter_upwards [shellHde_ae68_omega hγ0 hγ2 S hS hε hs₀ hζ hζ1 hr hrz hrρ i hR hElig hmesh hstart, htest]
    with ω h1 h2 hadm
  filter_upwards [h1 hadm, h2 hadm] with x ha hb
  exact ⟨fun k hk => ⟨ha.1 k hk, hb k hk⟩, ha.2⟩

end Lemma68ShellHdeOmega
end MatedCRT

#print axioms MatedCRT.Lemma68ShellHdeOmega.shellHde_ae68_omega
#print axioms MatedCRT.Lemma68ShellHdeOmega.shellHde68_full_omega
