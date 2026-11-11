import MatedCRT.FirstPass.S4S6c.ShellOrderOmega68
import MatedCRT.FirstPass.S4S6c.PathMesh68
import MatedCRT.FirstPass.S4S6c.ShellPathLoc68
import MatedCRT.FirstPass.S4S6c.HoneExitGeom68
import MatedCRT.FirstPass.S4S6c.ShellBallLoc68

/-!
# The shell order with the mesh localized to a ball

`shellOrder_fullAdm_ae_omega` (S4S6c/ShellOrderOmega68.lean:28) uses the global mesh bound `CellDiamLe ε (S.η ω) (dyadicD r / 100)
Set.univ`. Here the same statement is given with the mesh localized to the ball `B(0, ρmesh)`, with the gap
`dyadicD r / 100 ≤ ρmesh - ρ` .

The path-level inputs are discharged here:
* the walk diameter bound is `PathMesh68.diam_upto_vExitTime`, applied at each `ω` with the walk
  adjacency `srwLaw_step_ae_adjacent`, the start `srwLaw_ae_start`, and the start cell from `hstart`;
* the shell chain is `ShellPathLoc68.shell_ineqs_ae_meshBall`.
The one remaining named input is `hShellBall`: the shell-centre balls `B(zc k, 2 R(zc k))`
carry the cell-diameter bound `dyadicD r / 100`. It is not obtained from the ball mesh by inclusion under `hgap` alone

-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellOrderLoc

/-- A walk index `m ≤ τ.toNat` is `≤ τ` in `ℕ∞`: a finite exit time is its own `toNat`, and `⊤.toNat = 0`. -/
theorem natCast_le_of_le_toNat {τ : ℕ∞} {m : ℕ} (hm : m ≤ τ.toNat) : (m : ℕ∞) ≤ τ := by
  rcases eq_or_ne τ ⊤ with ht | ht
  · simp [ht]
  · rw [← ENat.natCast_toNat ht]
    exact_mod_cast hm

/-- **The shell order from the full guard, almost surely, with the mesh localized to `B(0, ρmesh)`.** The statement of
`shellOrder_fullAdm_ae_omega` (ShellOrderOmega68.lean:28) with the global mesh `Set.univ` replaced by the ball `B(0, ρmesh)`
and the gap `dyadicD r / 100 ≤ ρmesh - ρ`. All other binders and the conclusion are as there. The walk and shell path
inputs are discharged from PathMesh68 and ShellPathLoc68; the shell-centre bound is the named input `hShellBall`. -/
theorem shellOrder_fullAdm_ae_omega_loc {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : Ω → ℂ → ℝ} {Elig : Ω → ℂ → Prop}
    (ρmesh : ℝ) (hgap : dyadicD r / 100 ≤ ρmesh - ρ)
    (hR : ∀ᵐ ω ∂S.P, ∀ w, Elig ω w → dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    -- The shell-centre balls carry the cell-diameter bound `dyadicD r / 100`; the centre is
    -- the hitting-time centre `gridRound (vertexPoint (x (hitTime …)))` consumed by `shell_ineqs_ae_meshBall`
    (hShellBall : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        CellDiamLe ε (S.η ω) (dyadicD r / 100)
          (Metric.ball (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) x k))))
            (2 * Rf ω (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) x k)))))))
    -- guarded by `FullAdm` (the start cell meets the frontier only for a full admissible configuration)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    -- guarded by `FullAdm` (l.25-32)
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
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    hmesh, hstart, hR, hde, hShellBall] with ω hη hmap hkill hdg hm hst hRω hdeω hSω
  intro hadm
  have hstA := hst hadm
  have hdeA := hdeω hadm
  have hShellA := hSω hadm
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
  -- the start cell meets `B_ρ`: the frontier of `thickening (r / 2)` lies in `thickening r`, which lies in `B_ρ`
  have hfr : frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ)) ⊆
      Metric.thickening r (fillCells ε (S.η ω) ↑i.Θ) := fun p hp =>
    Metric.cthickening_subset_thickening' hr (by linarith) _
      (Metric.closure_thickening_subset_cthickening _ _ (frontier_subset_closure hp))
  have hst0 : (cell ε (S.η ω) i.a ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hstA
    exact ⟨p, hp1, hsub (hfr hp2)⟩
  -- the walk diameter bound up to the exit time (PathMesh68.diam_upto_vExitTime), a.s. in the walk
  have hdiam : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ m ≤ (vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x).toNat,
      ∀ p ∈ cell ε (S.η ω) (x m), ∀ q ∈ cell ε (S.η ω) (x m), dist p q ≤ dyadicD r / 100 := by
    filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
      MatedCRT.Lemma68HoneExitGeom.srwLaw_step_ae_adjacent (S.mult ε ω) hdg i.a] with x hx0 hxadj
    have hadjx : ∀ n : ℕ, (n : ℕ∞) < vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x →
        (cell ε (S.η ω) (x n) ∩ cell ε (S.η ω) (x (n + 1))).Nonempty :=
      fun n _ => hmap ε hε (x n) (x (n + 1)) (hxadj n)
    have hst1 : (cell ε (S.η ω) (x 0) ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
      rw [hx0]
      exact hst0
    have hh : 0 ≤ dyadicD r / 100 := div_nonneg hd.le (by norm_num)
    intro m hmτ
    exact MatedCRT.Lemma68PathMesh.diam_upto_vExitTime hh hF0eq.subset hgap (hm) hadjx hst1 m
      (natCast_le_of_le_toNat hmτ)
  -- the shell chain (ShellPathLoc68.shell_ineqs_ae_meshBall, the localized `shell_ineqs_ae`)
  exact MatedCRT.Lemma68ShellPathLoc68.shell_ineqs_ae_meshBall hη hε hr hs hs4 hd le_rfl hds hΘ hRω hF0 hdiam
    hShellA hNs hstA (hmap ε hε) (hkill.and hdeA)

/-- **The sparsity-parameter form of `shellOrder_fullAdm_ae_omega_loc`.** The guard `FullAdmAt` is taken
at the exponent `s1` in place of `sparsityS1 γ`; the proof uses `s1` only through `FullAdmAt` (it unfolds `FullAdmAt` and keeps
`ConfigOK`), so no property of `s1` is assumed. The shell-centre bound `hShellBall` is produced in ShellBallLoc68, given
under the deterministic gap `hgapShell` (a named binder). -/
theorem shellOrder_fullAdm_ae_omega_loc_s1 {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (s1 : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : Ω → ℂ → ℝ} {Elig : Ω → ℂ → Prop}
    (ρmesh : ℝ) (hgap : dyadicD r / 100 ≤ ρmesh - ρ)
    (hgapShell : 2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ ρmesh - ρ)
    (hR : ∀ᵐ ω ∂S.P, ∀ w, Elig ω w → dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    -- The shell-centre balls carry the cell-diameter bound `dyadicD r / 100`; the centre is
    -- the hitting-time centre `gridRound (vertexPoint (x (hitTime …)))` consumed by `shell_ineqs_ae_meshBall`
    (hShellBall : 2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ ρmesh - ρ → ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        CellDiamLe ε (S.η ω) (dyadicD r / 100)
          (Metric.ball (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) x k))))
            (2 * Rf ω (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) x k)))))))
    -- guarded by `FullAdm` (the start cell meets the frontier only for a full admissible configuration)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    -- guarded by `FullAdm` (l.25-32)
    (hde : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
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
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    hmesh, hstart, hR, hde, (hShellBall hgapShell)] with ω hη hmap hkill hdg hm hst hRω hdeω hSω
  intro hadm
  have hstA := hst hadm
  have hdeA := hdeω hadm
  have hShellA := hSω hadm
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
  -- the start cell meets `B_ρ`: the frontier of `thickening (r / 2)` lies in `thickening r`, which lies in `B_ρ`
  have hfr : frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ)) ⊆
      Metric.thickening r (fillCells ε (S.η ω) ↑i.Θ) := fun p hp =>
    Metric.cthickening_subset_thickening' hr (by linarith) _
      (Metric.closure_thickening_subset_cthickening _ _ (frontier_subset_closure hp))
  have hst0 : (cell ε (S.η ω) i.a ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hstA
    exact ⟨p, hp1, hsub (hfr hp2)⟩
  -- the walk diameter bound up to the exit time (PathMesh68.diam_upto_vExitTime), a.s. in the walk
  have hdiam : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ m ≤ (vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x).toNat,
      ∀ p ∈ cell ε (S.η ω) (x m), ∀ q ∈ cell ε (S.η ω) (x m), dist p q ≤ dyadicD r / 100 := by
    filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
      MatedCRT.Lemma68HoneExitGeom.srwLaw_step_ae_adjacent (S.mult ε ω) hdg i.a] with x hx0 hxadj
    have hadjx : ∀ n : ℕ, (n : ℕ∞) < vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x →
        (cell ε (S.η ω) (x n) ∩ cell ε (S.η ω) (x (n + 1))).Nonempty :=
      fun n _ => hmap ε hε (x n) (x (n + 1)) (hxadj n)
    have hst1 : (cell ε (S.η ω) (x 0) ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
      rw [hx0]
      exact hst0
    have hh : 0 ≤ dyadicD r / 100 := div_nonneg hd.le (by norm_num)
    intro m hmτ
    exact MatedCRT.Lemma68PathMesh.diam_upto_vExitTime hh hF0eq.subset hgap (hm) hadjx hst1 m
      (natCast_le_of_le_toNat hmτ)
  -- the shell chain (ShellPathLoc68.shell_ineqs_ae_meshBall, the localized `shell_ineqs_ae`)
  exact MatedCRT.Lemma68ShellPathLoc68.shell_ineqs_ae_meshBall hη hε hr hs hs4 hd le_rfl hds hΘ hRω hF0 hdiam
    hShellA hNs hstA (hmap ε hε) (hkill.and hdeA)

#print axioms MatedCRT.Lemma68ShellOrderLoc.shellOrder_fullAdm_ae_omega_loc_s1
/-- **The shell-centre ball bound at a free sparsity `s1`.** The `s1`-generic form of
`Lemma68ShellBallLoc.hShellBall_loc` (ShellBallLoc68.lean, which fixes `s1 := sparsityS1 γ`). Its proof uses
`FullAdmAt` only as a hypothesis, never the value of `s1`, so the copy below differs only in the parameter.
Chat 252 §2, §4: the hitting-time centre lies in `shortEligible`, so `B(c, 2R) ⊆ B(0, ρ) ⊆ B(0, ρmesh)`
and the mesh bound `CellDiamLe … (Metric.ball 0 ρmesh)` restricts to it; only `ρ ≤ ρmesh` is needed. -/
theorem hShellBall_loc_s1 {γ ζ ρ s₀ ε r ρmesh : ℝ} (s1 : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (i : Lemma68Config.Config68) {Rf : Ω → ℂ → ℝ}
    (hρ : ρ ≤ ρmesh)
    (hR : ∀ᵐ ω ∂S.P, ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    (hEl : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
          ∈ shortEligible ρ (dyadicD r) (shortExp ζ)) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        CellDiamLe ε (S.η ω) (dyadicD r / 100)
          (Metric.ball (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) x k))))
            (2 * Rf ω (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) x k)))))) := by
  filter_upwards [hmesh, hR, hEl] with ω hm hRω hElω
  intro hFA
  filter_upwards [hElω hFA] with x hx
  intro k hk
  have hkey : CellDiamLe ε (S.η ω) (dyadicD r / 100)
      (Metric.ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
        (2 * Rf ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) := by
    have hc := hx k hk
    have hRc := hRω _ hc
    have hd0 : 0 < dyadicD r := by unfold dyadicD; positivity
    have hd0a : 0 ≤ dyadicD r ^ shortExp ζ := Real.rpow_nonneg hd0.le _
    have hsub := MatedCRT.Lemma68ShellBallLoc.ball_two_mul_R_subset_of_shortEligible hc hRc.2 hd0a
    exact MatedCRT.Lemma68HoneRrLocal.cellDiamLe_mono_set (hsub.trans (Metric.ball_subset_ball hρ)) hm
  rw [MatedCRT.Lemma68ShellBallLoc.hitTime_eq_toNat_shellHit]
  exact hkey

/-- **The shell order with the mesh localized to a ball and the shell-centre bound discharged, at a free `s1`.**
`shellOrder_fullAdm_ae_omega_loc_s1` with the named input `hShellBall` replaced by
`hShellBall_loc_s1`. Two changes against `_s1`, both forced by `hShellBall_loc_s1`:
* `Elig` is specialised to `shortEligible ρ (dyadicD r) (shortExp ζ)`, the set that contains the hitting-time
  centres; the `Elig` clause of `hde` becomes the centre clause, and `hR` is stated on `shortEligible`;
* the gap `hgapShell` is dropped: `ρ ≤ ρmesh` follows from `hgap` (`dyadicD r / 100 ≥ 0`). -/
theorem shellOrder_fullAdm_ae_omega_loc_hb_s1 {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (s1 : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : Ω → ℂ → ℝ}
    (ρmesh : ℝ) (hgap : dyadicD r / 100 ≤ ρmesh - ρ)
    (hR : ∀ᵐ ω ∂S.P, ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    -- guarded by `FullAdm` (the start cell meets the frontier only for a full admissible configuration)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    -- guarded by `FullAdm` (l.25-32)
    (hde : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
            ∈ shortEligible ρ (dyadicD r) (shortExp ζ))) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  -- deterministic parameter facts (as in shellOrder_fullAdm_ae_omega)
  have hr1 : r ≤ 1 := hrz.trans (countThreshold_le_one hζ)
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hd2 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
  have hρm : ρ ≤ ρmesh := by
    have h0 : 0 ≤ dyadicD r / 100 := div_nonneg hd.le (by norm_num)
    linarith
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
  -- the shell-centre bound, from the centre clause of `hde` (the `Elig` clause with `Elig := shortEligible`)
  have hEl := hde.mono fun ω hω hadm => (hω hadm).mono fun x hx => hx.2
  have hShell := hShellBall_loc_s1 s1 S i hρm hR hmesh hEl
  -- almost sure environment facts; the radius facts `hR`, `hShell` and `hde` are taken at the same `ω`
  filter_upwards [TraceInputs68.ae_continuous_eta hS, Lemma68ShellEnvAe.map_cells_meet_ae hγ0 hγ2 S hS,
    Lemma68ShellEnvAeInputs.hkill_of_valid hγ0 hγ2 S hS hε (Θ := i.Θ) (F0 := i.F0) (r := r) (a := i.a),
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    hmesh, hstart, hR, hde, hShell] with ω hη hmap hkill hdg hm hst hRω hdeω hSω
  intro hadm
  have hstA := hst hadm
  have hdeA := hdeω hadm
  have hShellA := hSω hadm
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
  -- the start cell meets `B_ρ`: the frontier of `thickening (r / 2)` lies in `thickening r`, which lies in `B_ρ`
  have hfr : frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ)) ⊆
      Metric.thickening r (fillCells ε (S.η ω) ↑i.Θ) := fun p hp =>
    Metric.cthickening_subset_thickening' hr (by linarith) _
      (Metric.closure_thickening_subset_cthickening _ _ (frontier_subset_closure hp))
  have hst0 : (cell ε (S.η ω) i.a ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hstA
    exact ⟨p, hp1, hsub (hfr hp2)⟩
  -- the walk diameter bound up to the exit time (PathMesh68.diam_upto_vExitTime), a.s. in the walk
  have hdiam : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ m ≤ (vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x).toNat,
      ∀ p ∈ cell ε (S.η ω) (x m), ∀ q ∈ cell ε (S.η ω) (x m), dist p q ≤ dyadicD r / 100 := by
    filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
      MatedCRT.Lemma68HoneExitGeom.srwLaw_step_ae_adjacent (S.mult ε ω) hdg i.a] with x hx0 hxadj
    have hadjx : ∀ n : ℕ, (n : ℕ∞) < vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x →
        (cell ε (S.η ω) (x n) ∩ cell ε (S.η ω) (x (n + 1))).Nonempty :=
      fun n _ => hmap ε hε (x n) (x (n + 1)) (hxadj n)
    have hst1 : (cell ε (S.η ω) (x 0) ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
      rw [hx0]
      exact hst0
    have hh : 0 ≤ dyadicD r / 100 := div_nonneg hd.le (by norm_num)
    intro m hmτ
    exact MatedCRT.Lemma68PathMesh.diam_upto_vExitTime hh hF0eq.subset hgap (hm) hadjx hst1 m
      (natCast_le_of_le_toNat hmτ)
  -- the shell chain (ShellPathLoc68.shell_ineqs_ae_meshBall, the localized `shell_ineqs_ae`)
  exact MatedCRT.Lemma68ShellPathLoc68.shell_ineqs_ae_meshBall hη hε hr hs hs4 hd le_rfl hds hΘ hRω hF0 hdiam
    hShellA hNs hstA (hmap ε hε) (hkill.and hdeA)

/-- **`shellOrder_fullAdm_ae_omega_loc_hb_s1` at the sparsity `sparsityS1 γ`**: the statement of
`shellOrder_fullAdm_ae_omega_loc` with `hShellBall` discharged by `hShellBall_loc_s1` (see its docstring). -/
theorem shellOrder_fullAdm_ae_omega_loc_hb {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    {Rf : Ω → ℂ → ℝ}
    (ρmesh : ℝ) (hgap : dyadicD r / 100 ≤ ρmesh - ρ)
    (hR : ∀ᵐ ω ∂S.P, ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hde : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
            ∈ shortEligible ρ (dyadicD r) (shortExp ζ))) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) (Rf ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a :=
  shellOrder_fullAdm_ae_omega_loc_hb_s1 (Lemma68Config.sparsityS1 γ) hγ0 hγ2 S hS hε hs₀ hζ hζ1 hr hrz hrρ i ρmesh
    hgap hR hmesh hstart hde

#print axioms MatedCRT.Lemma68ShellOrderLoc.hShellBall_loc_s1
#print axioms MatedCRT.Lemma68ShellOrderLoc.shellOrder_fullAdm_ae_omega_loc_hb_s1
#print axioms MatedCRT.Lemma68ShellOrderLoc.shellOrder_fullAdm_ae_omega_loc_hb

end Lemma68ShellOrderLoc
end MatedCRT

#print axioms MatedCRT.Lemma68ShellOrderLoc.shellOrder_fullAdm_ae_omega_loc
