import MatedCRT.FirstPass.S4S6c.ShellOrderOmega68

/-!
# The shell order with the mesh localized to a ball (fp-S4S6c-shellorder-loc, z1)

`shellOrder_fullAdm_ae_omega` (S4S6c/ShellOrderOmega68.lean:28) uses the global mesh bound `CellDiamLe ε (S.η ω) (dyadicD r / 100)
Set.univ`. Here the same statement is given with the mesh localized to the ball `B(0, ρmesh)`, with the gap
`dyadicD r / 100 ≤ ρmesh - ρ` (chat 252, notes/fp-gaps/CHATGPT-252-idla-z12-mesh-radius-PRO.md §3 and §6).

The global bound is consumed in the path chain only through the walk cells `x m` for `m ≤ vExitTime` (`hdiam`) and the
shell balls (`hmeshShell`). Until the path-level producers land, the three inputs are NAMED binders with the printed
types:
* `hWalk` (q4, PathMesh68, chat 252 §3): the walk up to the exit index stays in the cells meeting `B(0, ρmesh)`;
* `hShellBall` (z12, chat 252 §4 and §2): the shell-centre balls `B(zc k, 2 R(zc k))` carry the cell-diameter bound;
* `hWire` (z8, ShellPathLoc68, chat 252 §6): the localized `shellOrderAe_of_path` (ShellWire68.lean:51) with the univ
  hypothesis `hmesh` replaced by the two printed hypotheses `hdiam` and `hmeshShell`.
The walk diameter bound `hdiam` is derived here from `hmesh` (ball form) and `hWalk`, with no further input.
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellOrderLoc

/-- **The shell order from the full guard, almost surely, with the mesh localized to `B(0, ρmesh)`.** The statement of
`shellOrder_fullAdm_ae_omega` (ShellOrderOmega68.lean:28) with the global mesh `Set.univ` replaced by the ball `B(0, ρmesh)`
and the gap `dyadicD r / 100 ≤ ρmesh - ρ`. All other binders and the conclusion are as there. -/
theorem shellOrder_fullAdm_ae_omega_loc {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : Ω → ℂ → ℝ} {Elig : Ω → ℂ → Prop}
    (ρmesh : ℝ) (hgap : dyadicD r / 100 ≤ ρmesh - ρ)
    (hR : ∀ᵐ ω ∂S.P, ∀ w, Elig ω w → dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    -- q4 (PathMesh68, chat 252 §3): the walk up to the exit index meets only the cells meeting `B(0, ρmesh)`
    (hWalk : ∀ ω : Ω, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh) →
      dyadicD r / 100 ≤ ρmesh - ρ → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ m ≤ (vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x).toNat,
        x m ∈ cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) ρmesh))
    -- z12 (chat 252 §4, §2): the shell-centre balls carry the cell-diameter bound `dyadicD r / 100`
    (hShellBall : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        CellDiamLe ε (S.η ω) (dyadicD r / 100)
          (Metric.ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
            (2 * Rf ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))))
    -- z8 (ShellPathLoc68, chat 252 §6): `shellOrderAe_of_path` (ShellWire68.lean:51) with `hmesh` replaced by `hdiam`, `hmeshShell`
    (hWire : ∀ {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {s d h : ℝ} {R : ℂ → ℝ} {Elig' : ℂ → Prop} {n : ℕ}
      {mm : ℤ → ℤ → ℕ} {a : ℤ},
      Continuous η → 0 < s → s ≤ r / 4000 → 0 < d → h ≤ d / 100 → d / 100 ≤ s / 100 → Θ.Nonempty →
      (∀ w, Elig' w → d ≤ R w ∧ R w ≤ s) → (∀ v : ℤ, dd ε η Θ v < r → v ∈ F0) →
      (∀ᵐ x ∂(srwLaw mm a), ∀ m ≤ (vExitTime (killed ε η Θ F0 r) x).toNat,
        ∀ p ∈ cell ε η (x m), ∀ q ∈ cell ε η (x m), dist p q ≤ h) →
      (∀ᵐ x ∂(srwLaw mm a), ∀ k ≤ n,
        CellDiamLe ε η h
          (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)
            (2 * R (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)))) →
      20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20 →
      (cell ε η a ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty →
      (∀ j k : ℤ, mm j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) →
      (∀ᵐ x ∂(srwLaw mm a), vExitTime (killed ε η Θ F0 r) x ≠ ⊤ ∧
        (∀ k ≤ n, shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤ ∧
          testEnd ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤) ∧
        (∀ k ≤ n, Elig' (shellCentre ε η (fillCells ε η ↑Θ) r s d k x))) →
      Lemma68ShellOrder.ShellOrderAe ε η Θ F0 r s d R n mm a)
    -- guarded by `FullAdm` (the start cell meets the frontier only for a full admissible configuration)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    -- guarded by `FullAdm` (the z11 deviation: the unguarded form is not provable, reports/z11.md l.25-32)
    (hde : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω)
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
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hc1]
    nlinarith [hfl]
  -- almost sure environment facts; the radius facts `hR`, `hShellBall` and `hde` are taken at the same `ω`
  filter_upwards [TraceInputs68.ae_continuous_eta hS, Lemma68ShellEnvAe.map_cells_meet_ae hγ0 hγ2 S hS,
    Lemma68ShellEnvAeInputs.hkill_of_valid hγ0 hγ2 S hS hε (Θ := i.Θ) (F0 := i.F0) (r := r) (a := i.a),
    hmesh, hstart, hR, hde, hShellBall] with ω hη hmap hkill hm hst hRω hdeω hSω
  intro hadm
  have hstA := hst hadm
  have hdeA := hdeω hadm
  have hShellA := hSω hadm
  have hWalkA := hWalk ω hm hgap hadm
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
  -- the walk diameter bound, from the ball mesh at `ω` and the walk-visit lemma `hWalk`
  have hdiamA : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ m ≤ (vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x).toNat,
      ∀ p ∈ cell ε (S.η ω) (x m), ∀ q ∈ cell ε (S.η ω) (x m), dist p q ≤ dyadicD r / 100 :=
    hWalkA.mono fun x hx m hmle p hp q hq => hm (x m) (hx m hmle) p hp q hq
  exact hWire hη hs hs4 hd le_rfl hds hΘ hRω hF0 hdiamA hShellA hNs hstA (hmap ε hε) (hkill.and hdeA)

end Lemma68ShellOrderLoc
end MatedCRT

#print axioms MatedCRT.Lemma68ShellOrderLoc.shellOrder_fullAdm_ae_omega_loc
