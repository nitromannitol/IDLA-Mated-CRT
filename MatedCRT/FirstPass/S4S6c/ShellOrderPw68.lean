import MatedCRT.FirstPass.S4S6c.ShellOrderOmega68
import MatedCRT.FirstPass.S4S6c.ShellPathLoc68
import MatedCRT.FirstPass.S4S6c.PathMesh68
import MatedCRT.FirstPass.S4S6c.HoneExitGeom68
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.FirstPass.S4S6c.HoneRadii68
import MatedCRT.FirstPass.S4S6c.HoneCellGood68

/-!
# The pointwise shell order with the window radius

The pointwise form, at a fixed environment `ω`, of the localized shell order `shellOrder_fullAdm_ae_omega_loc_hb_s1`
(ShellOrderLoc68.lean), with the radius `windowRfT` (ShellWindowRf68.lean) and a free sparsity `s1`. Its conclusion
is the input `hShellLoc` of `shellOne_at_of_goodEnv_loc_g`-type consumers (B1Assembly68.lean, goodEnv_loc_g),
namely `hShellLoc_pw_g`. Chat 252 §2–§6, as in ShellOrderLoc68.

Against the a.s. `_hb` form every `∀ᵐ ω` input is taken at the fixed `ω`:
* the environment facts `Continuous (S.η ω)`, the cell meeting `hmap`, the degree bound `hdg` and the walk exit
  finiteness `hkill` are the a.s. lemmas `TraceInputs68.ae_continuous_eta`, `Lemma68ShellEnvAe.map_cells_meet_ae`,
  `MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid`, `Lemma68ShellEnvAeInputs.hkill_of_valid`, taken pointwise;
* the start-cell and exit/centre clauses `hstart`, `hde` stay guarded by `FullAdmAt` (as in `_hb`);
* the radius bound `hR` is not a hypothesis: `Lemma68HoneRadii.windowRfT_rangeShortEligible` holds at every `ω`;
* the deterministic gap `hgap : dyadicD r / 100 ≤ rhoCell68 ρ - ρ` is a named binder.
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellOrderPw

/-!
### Local copies of four helpers (import-cycle guard)

`ShellBallLoc68` and `ShellOrderLoc68` import `HoneRrLocal68`, which imports `B1Assembly68`; at HEAD `B1Assembly68`
imports this file (B1Assembly68.lean:12). Importing them here would close a cycle, so the four helpers are copied
verbatim from their homes: `HoneRrLocal68.cellDiamLe_mono_set` (HoneRrLocal68.lean:113),
`ShellBallLoc68.hitTime_eq_toNat_shellHit` (ShellBallLoc68.lean:36), `ShellBallLoc68.ball_two_mul_R_subset_of_shortEligible`
(ShellBallLoc68.lean:50), `ShellOrderLoc68.natCast_le_of_le_toNat` (ShellOrderLoc68.lean:31). Dedupe once the cycle is
broken at its root (HoneRrLocal68's import of B1Assembly68).
-/

/-- Copy of `HoneRrLocal68.cellDiamLe_mono_set`: a cell-diameter bound on a larger set holds on a subset. -/
theorem cellDiamLe_mono_set {ε : ℝ} {η : ℝ → ℂ} {h : ℝ} {E F : Set ℂ} (hEF : E ⊆ F)
    (hF : CellDiamLe ε η h F) : CellDiamLe ε η h E :=
  fun k hk => hF k (by obtain ⟨p, hp1, hp2⟩ := hk; exact ⟨p, hp1, hEF hp2⟩)

/-- Copy of `ShellBallLoc68.hitTime_eq_toNat_shellHit`: the hitting time is the `toNat` of the shell hit. -/
theorem hitTime_eq_toNat_shellHit {ε : ℝ} {η : ℝ → ℂ} (K : Set ℂ) (r s : ℝ) (x : ℕ → ℤ) (k : ℕ) :
    hitTime ε η K r s x k = (shellHit ε η K r s k x).toNat := by
  unfold hitTime firstShellHit shellHit firstTime
  split_ifs with h
  · rw [ENat.toNat_natCast]
    exact Nat.sInf_def (s := {n : ℕ | (cell ε η (x n) ∩ twoSidedShell K r (shellOffset s (k + 1))).Nonempty}) h
  · rw [ENat.toNat_top]
    have hempty : {n : ℕ | (cell ε η (x n) ∩ twoSidedShell K r (shellOffset s (k + 1))).Nonempty} = ∅ := by
      ext n
      exact ⟨fun hn => absurd ⟨n, hn⟩ h, fun hn => hn.elim⟩
    rw [hempty, Nat.sInf_empty]

/-- Copy of `ShellBallLoc68.ball_two_mul_R_subset_of_shortEligible`: `B(c, 2R) ⊆ B(0, ρ)` for `c` shortly eligible. -/
theorem ball_two_mul_R_subset_of_shortEligible {ρ d a R : ℝ} {c : ℂ} (hc : c ∈ shortEligible ρ d a)
    (hRa : R ≤ d ^ a) (hd0 : 0 ≤ d ^ a) :
    Metric.ball c (2 * R) ⊆ Metric.ball (0 : ℂ) ρ := by
  intro z hz
  obtain ⟨⟨hball, -⟩, -⟩ := hc
  have h1 : dist c 0 < ρ - 3 * d ^ a := Metric.mem_ball.1 hball
  have h2 : dist z c < 2 * R := Metric.mem_ball.1 hz
  rw [Metric.mem_ball]
  have htri := dist_triangle z c 0
  linarith

/-- Copy of `ShellOrderLoc68.natCast_le_of_le_toNat`: a walk index `m ≤ τ.toNat` is `≤ τ` in `ℕ∞`. -/
theorem natCast_le_of_le_toNat {τ : ℕ∞} {m : ℕ} (hm : m ≤ τ.toNat) : (m : ℕ∞) ≤ τ := by
  rcases eq_or_ne τ ⊤ with ht | ht
  · simp [ht]
  · rw [← ENat.natCast_toNat ht]
    exact_mod_cast hm

/-- **The shell-centre ball bound at a fixed environment.** At `ω`, with the mesh bound on the ball `B(0, ρmesh)`
and the radius bound on `shortEligible`, the shell-centre balls `B(c, 2R(c))` of the hitting-time centres carry the
cell-diameter bound (the pointwise form of `Lemma68ShellBallLoc.hShellBall_loc`, centre clause `hEl`). -/
theorem shellBall_pt {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) (i : Lemma68Config.Config68)
    {ε ζ ρ r ρmesh : ℝ} {Rf : ℂ → ℝ} (hρ : ρ ≤ ρmesh)
    (hR : ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ), dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hm : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    (hEl : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
      shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
        ∈ shortEligible ρ (dyadicD r) (shortExp ζ)) :
    ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
      CellDiamLe ε (S.η ω) (dyadicD r / 100)
        (Metric.ball (gridRound (dyadicD r / 100)
            (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) x k))))
          (2 * Rf (gridRound (dyadicD r / 100)
            (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) x k)))))) := by
  filter_upwards [hEl] with x hx
  intro k hk
  have hkey : CellDiamLe ε (S.η ω) (dyadicD r / 100)
      (Metric.ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
        (2 * Rf (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) := by
    have hc := hx k hk
    have hRc := hR _ hc
    have hd0 : 0 < dyadicD r := by unfold dyadicD; positivity
    have hd0a : 0 ≤ dyadicD r ^ shortExp ζ := Real.rpow_nonneg hd0.le _
    have hsub := ball_two_mul_R_subset_of_shortEligible hc hRc.2 hd0a
    exact cellDiamLe_mono_set (hsub.trans (Metric.ball_subset_ball hρ)) hm
  rw [hitTime_eq_toNat_shellHit]
  exact hkey

/-- **The pointwise shell order, for a general radius `Rf` and a free sparsity `s1`.** At a fixed environment `ω`:
if the mesh `CellDiamLe` holds on `B(0, ρmesh)` and the full admissibility `FullAdmAt s1` holds at `ω`, then the
four shell-order inequalities `ShellOrderAe` hold for the walk on `S.mult ε ω` from `i.a`. The walk diameter bound
is `PathMesh68.diam_upto_vExitTime`; the shell chain is `ShellPathLoc68.shell_ineqs_ae_meshBall`
; the shell-centre balls are `shellBall_pt`. -/
theorem shellOrder_pw {γ : ℝ} (s1 : ℝ) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {Rf : ℂ → ℝ}
    (ρmesh : ℝ) (hgap : dyadicD r / 100 ≤ ρmesh - ρ)
    (hη : Continuous (S.η ω))
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hdg : ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hR : ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ), dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    -- guarded by `FullAdm` (the start cell meets the frontier only for a full admissible configuration)
    (hstart : Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    -- guarded by `FullAdm` (l.25-32)
    (hde : Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
            ∈ shortEligible ρ (dyadicD r) (shortExp ζ))) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh) →
      Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  intro hmesh hadm
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
  -- the facts at `ω`, taken before `hadm` is unfolded
  have hdeA := hde hadm
  have hstA := hstart hadm
  have hShellA := shellBall_pt S ω i hρm hR hmesh (hdeA.mono fun x hx => hx.2)
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
      fun n _ => hmap (x n) (x (n + 1)) (hxadj n)
    have hst1 : (cell ε (S.η ω) (x 0) ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
      rw [hx0]
      exact hst0
    have hh : 0 ≤ dyadicD r / 100 := div_nonneg hd.le (by norm_num)
    intro m hmτ
    exact MatedCRT.Lemma68PathMesh.diam_upto_vExitTime hh hF0eq.subset hgap hmesh hadjx hst1 m
      (natCast_le_of_le_toNat hmτ)
  -- the shell chain (ShellPathLoc68.shell_ineqs_ae_meshBall)
  exact MatedCRT.Lemma68ShellPathLoc68.shell_ineqs_ae_meshBall hη hε hr hs hs4 hd le_rfl hds hΘ hR hF0 hdiam
    hShellA hNs hstA hmap (hkill.and hdeA)

/-- **The pointwise shell order with the window radius: the input `hShellLoc` of `goodEnv_loc_g`** (
B1Assembly68.lean). At a fixed environment `ω`, with the radius `windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω`
and a free sparsity `s1`: if `CellDiamLe` holds on `B(0, rhoCell68 ρ)` and
`FullAdmAt s1` holds at `ω`, then `ShellOrderAe` holds. The radius bound on `shortEligible` is
`Lemma68HoneRadii.windowRfT_rangeShortEligible`; the deterministic gap is the named binder `hgap`. -/
theorem hShellLoc_pw_g {γ : ℝ} (s1 : ℝ) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (c0W C : ℝ) {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    (hgap : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hη : Continuous (S.η ω))
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hdg : ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hstart : Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hde : Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
            ∈ shortEligible ρ (dyadicD r) (shortExp ζ))) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) →
      Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a :=
  shellOrder_pw s1 S ω hε hs₀ hζ hζ1 hr hrz hrρ i (Lemma68HoneCellGood.rhoCell68 ρ) hgap hη hmap hdg hkill
    (Lemma68HoneRadii.windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) c0W C (dyadicD r) (dyadicD_pos r)
      (dyadicD_le_one r) (by unfold shortExp; linarith) ω) hstart hde

#print axioms MatedCRT.Lemma68ShellOrderPw.shellBall_pt
#print axioms MatedCRT.Lemma68ShellOrderPw.shellOrder_pw
#print axioms MatedCRT.Lemma68ShellOrderPw.hShellLoc_pw_g

open MatedCRT.Lemma68WindowRf

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
