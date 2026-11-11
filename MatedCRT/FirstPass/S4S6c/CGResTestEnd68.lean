import MatedCRT.FirstPass.S4S6c.CGResLoc68
import MatedCRT.FirstPass.S4S6c.CGResRr68
import MatedCRT.FirstPass.S4S6c.WalkLoc68
import MatedCRT.FirstPass.S4S6c.ShellHde68
import MatedCRT.FirstPass.S6r.ShellWiring

/-!
# The test-end finiteness `ShellCGTestEndLoc`

`ShellCGTestEndLoc 𝒮` (CGResLoc68.lean) asks that, on the shell chain of `ShellPtPremCG`, the test ends `L_k` of the
shells are almost surely finite. The route is the localized one (
lines 199-256), with no global mesh and no new probability event:

1. `testEnd ≤ τ` deterministically, where `τ = vExitTime (killed …) x` is the killed exit time (`testEnd_le_vExit_of_path_loc`).
   The shell exit `shellExit ≤ τ` is proved by the copy of `shell_fin_of_path_loc` (ShellHdePw68.lean:49) with the exit bound
   exported (its `hexit`, ShellHdePw68.lean:126-136, is the same argument).
2. The test ball `D = B_{R/4}(η(X_T))` of the exit cell lies in `B_{2R}(z)` (`Lemma68Window.test_ball_of_exit`, ShellWiring.lean:61),
   with the ball mesh on `B_{2R}(z) ⊆ B_ρ(0)` (`ball_two_mul_R_subset_of_shortEligible`).
3. `cellVertices (B_{2R}(z)) ⊆ killed` (`cell_meets_ball2_mem_killed`, the 2R-version of `cell_meets_ball_mem_killed`,
   ShellHde68.lean:162). Hence `X_τ ∉ I(D)`, and `testEnd ≤ τ`.
4. Almost surely `τ ≠ ⊤` (`ae_killed_exit_ne_top`), so `testEnd ≠ ⊤`.

Terminology: shells, shell chain and cell distance (Duplantier-Sheffield; Armstrong-Kuusi-Mourrat); the killed walk and
its exit time (Armitage-Gardiner, potential theory on `ℤ²`-cells).
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry
open MatedCRT.Lemma68ShellHde68

namespace MatedCRT
namespace Lemma68CGResTestEnd

/-- The 2R-version of `cell_meets_ball_mem_killed` (ShellHde68.lean:162): a cell meeting `B_{2R'}(z)` is killed. The
proof is that lemma with `4 R'/3` replaced by `2 R'` and `4 s/3` by `2 s`; the bounds are `dist y z < 2 R' ≤ 2 s`,
`dist y y0 ≤ 2 d/100 + 2 s`, and the shell band `9/20 r ≤ infDist y0 ≤ 11/20 r`. -/
theorem cell_meets_ball2_mem_killed {η : ℝ → ℂ} {ε : ℝ} (hη : Continuous η) (hε : 0 < ε) {ρ r d s lam R' : ℝ}
    {Θ F0 : Finset ℤ} (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) {z y0 : ℂ} (hy0 : y0 ∈ twoSidedShell (fillCells ε η ↑Θ) r lam)
    (hlam : lam ≤ r / 20) (hzy : dist z y0 ≤ 2 * (d / 100)) (hzρ : ‖z‖ < ρ - 3 * s)
    (hR0 : 0 < R') (hRs : R' ≤ s) (hds : d ≤ s) (hs4 : s ≤ r / 4000) (_hd : 0 < d) (_hr : 0 < r)
    (_hrρ : r ≤ ρ / 4) {v : ℤ} (hv : (cell ε η v ∩ Metric.ball z (2 * R')).Nonempty) :
    v ∈ killed ε η Θ F0 r := by
  obtain ⟨y, hyc, hyB⟩ := hv
  have hdy : dist y z < 2 * R' := Metric.mem_ball.1 hyB
  have hdy0 : dist y y0 ≤ 2 * (d / 100) + 2 * s := by
    have := dist_triangle y z y0
    linarith
  obtain ⟨hlo, hhi⟩ := shell_band hlam hy0
  have hKne : (fillCells ε η ↑Θ).Nonempty := ⟨0, h0⟩
  have hinf_lo : 9 / 20 * r - 2 * (d / 100) - 2 * s ≤ Metric.infDist y (fillCells ε η ↑Θ) := by
    have := Metric.infDist_le_infDist_add_dist (x := y0) (y := y) (s := fillCells ε η ↑Θ)
    rw [dist_comm] at this
    linarith
  have hinf_hi : Metric.infDist y (fillCells ε η ↑Θ) ≤ 11 / 20 * r + 2 * (d / 100) + 2 * s := by
    have := Metric.infDist_le_infDist_add_dist (x := y) (y := y0) (s := fillCells ε η ↑Θ)
    linarith
  show v ∈ F0 ∧ dd ε η Θ v < r ∧ v ∉ Θ
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.mem_coe, hF0]
    refine ⟨y, hyc, mem_ball_zero_iff.2 ?_⟩
    have := dist_triangle y z 0
    rw [dist_zero_right, dist_zero_right] at this
    linarith
  · obtain ⟨w, hw, hdw⟩ :=
      (Metric.infDist_lt_iff hKne).1 (show Metric.infDist y (fillCells ε η ↑Θ) < r by linarith)
    have hmem : v ∈ cellVertices ε η (Metric.thickening r (fillCells ε η ↑Θ)) :=
      ⟨y, hyc, Metric.mem_thickening_iff.2 ⟨w, hw, hdw⟩⟩
    rw [cellVertices_thickening_eq hη hε Θ r] at hmem
    exact ENNReal.toReal_lt_of_lt_ofReal hmem
  · intro hΘv
    have hy0' : Metric.infDist y (fillCells ε η ↑Θ) = 0 :=
      Metric.infDist_zero_of_mem ((cell_subset_fillCells (ε := ε) (η := η) hΘv) hyc)
    linarith

/-- **Localized test ends (steps 1-4).** Copy of `shell_fin_of_path_loc` (ShellHdePw68.lean:49) with the
exit bound exported and the test end added. Deterministically, on one walk `x` from the start cell, with the killed
exit time `τ = vExitTime (killed ε η Θ F0 r) x` finite: for every shell `k ≤ n` the centre is eligible and the test end
`testEnd k x` is at most `τ`. The mesh bound is used only on `B_ρ(0)`. -/
theorem testEnd_le_vExit_of_path_loc {η : ℝ → ℂ} {ε : ℝ} (hη : Continuous η) (hε : 0 < ε)
    {Θ F0 : Finset ℤ} {ρ r d a : ℝ} {R : ℂ → ℝ} {n : ℕ} (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρ))
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRS : ∀ w ∈ shortEligible ρ d a, d ≤ R w ∧ R w ≤ d ^ a)
    {x : ℕ → ℤ} (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : vExitTime (killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, testEnd ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x
        ≤ ((vExitTime (killed ε η Θ F0 r) x).toNat : ℕ∞) ∧
      shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x ∈ shortEligible ρ d a := by
  intro k hk
  have hKne : (fillCells ε η ↑Θ).Nonempty := ⟨0, h0⟩
  have hs : 0 < d ^ a := Real.rpow_pos_of_pos hd a
  have hlam0 : 0 < shellOffset (d ^ a) (k + 1) := by
    unfold shellOffset
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.2 (Nat.succ_pos k))) hs
  have hlam1 : shellOffset (d ^ a) (k + 1) ≤ r / 20 := by
    unfold shellOffset
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
    have hm := mul_le_mul_of_nonneg_right hk' (show (0 : ℝ) ≤ 20 * d ^ a by positivity)
    linarith
  -- the start level 0 and the exit level at least r/2
  obtain ⟨p, hp, hpf⟩ := hst
  have hpinf : Metric.infDist p (fillCells ε η ↑Θ) = r / 2 := infDist_eq_of_mem_frontier hKne hpf
  have hτn : x (vExitTime (killed ε η Θ F0 r) x).toNat ∉ killed ε η Θ F0 r :=
    vExitTime_toNat_not_mem hτ
  obtain ⟨q, hq, hqf⟩ := level_ge_of_not_killed hε hη hr hrρ hF0 hKne hKb hτn
  have hf : Continuous (fun y : ℂ => |Metric.infDist y (fillCells ε η ↑Θ) - r / 2|) :=
    continuous_abs.comp ((Metric.continuous_infDist_pt _).sub continuous_const)
  obtain ⟨i, hi, y, hyc, hy⟩ := exists_index_level hη hε hadj hf hp hq
    (c := shellOffset (d ^ a) (k + 1))
    (by
      show |Metric.infDist p (fillCells ε η ↑Θ) - r / 2| ≤ shellOffset (d ^ a) (k + 1)
      rw [hpinf, sub_self, abs_zero]
      exact hlam0.le)
    (by
      show shellOffset (d ^ a) (k + 1) ≤ |Metric.infDist q (fillCells ε η ↑Θ) - r / 2|
      linarith)
  have hyshell : y ∈ twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1)) := hy
  -- the first hit is at most the killed exit time
  set τ : ℕ := (vExitTime (killed ε η Θ F0 r) x).toNat with hτ_def
  have hitle : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≤ (τ : ℕ∞) := by
    unfold shellHit
    exact (firstTime_le_iff _ τ).2 ⟨i, hi, y, hyc, hyshell⟩
  have hCfin : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top τ) hitle
  set C : ℕ := (shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x).toNat with hC_def
  have hCspec : (cell ε η (x C) ∩
      twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty :=
    firstTime_toNat_spec (P := fun m => (cell ε η (x m) ∩
      twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty) hCfin
  obtain ⟨y0, hy0c, hy0⟩ := hCspec
  -- the centre is within 2d/100 of the shell
  have hw : vertexPoint ε η (x C) ∈ cell ε η (x C) := vertexPoint_mem_cell_nonneg hε.le η (x C)
  have hwy : dist (vertexPoint ε η (x C)) y0 ≤ d / 100 :=
    hmesh (x C) ⟨y0, hy0c, Lemma68ShellHdePw68.twoSidedShell_mem_ball hKne hKb hr hrρ hlam1 hy0⟩ _ hw _ hy0c
  have hz_def : shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x
      = Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x C)) := rfl
  have hzy : dist (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) y0 ≤ 2 * (d / 100) := by
    rw [hz_def]
    have h1 := Lemma68Window.dist_gridRound_le (g := d / 100) (div_pos hd (by norm_num))
      (vertexPoint ε η (x C))
    have h2 := dist_triangle (Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x C)))
      (vertexPoint ε η (x C)) y0
    linarith
  have hz_bd := centre_norm_bounds h0 hKb hlam1 hy0 hzy hr hrρ hd hds hs4
  -- the centre lies in the eligible set Z_d
  have hzS : shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x ∈ shortEligible ρ d a := by
    obtain ⟨m, nn, hmn⟩ := gridRound_mem_grid (g := d / 100) (vertexPoint ε η (x C))
    refine ⟨⟨mem_ball_zero_iff.2 hz_bd.2, fun h => ?_⟩, m, nn, ?_⟩
    · have := mem_ball_zero_iff.1 h
      linarith [hz_bd.1]
    · rw [hz_def]
      exact hmn
  obtain ⟨hRlo, hRhi⟩ := hRS _ hzS
  have hR0 : 0 < R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) := lt_of_lt_of_le hd hRlo
  -- the walk at the killed exit time is outside the 4R/3-exit ball (ShellHde68 lemma, unchanged)
  have hxτB : x τ ∉ interiorCellVertices ε η
      (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3)) := by
    intro hmem
    exact hτn (cell_meets_ball_mem_killed hη hε hF0 h0 hy0 hlam1 hzy hz_bd.2 hR0 hRhi hds hs4 hd hr hrρ
      (mem_interiorCellVertices_iff.1 hmem).1)
  have hexit : shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≤ (τ : ℕ∞) := by
    unfold shellExit
    exact (firstTime_le_iff _ τ).2 ⟨τ, le_rfl, hitle, hxτB⟩
  -- Steps 2-4: the test end is at most the killed exit time
  have hExitNe : shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top τ) hexit
  have hshC : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x = (C : ℕ∞) := by
    rw [hC_def]
    exact (ENat.natCast_toNat hCfin).symm
  set T : ℕ := (shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x).toNat with hT_def
  have hTspec : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≤ (T : ℕ∞) ∧
      x T ∉ interiorCellVertices ε η (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3)) :=
    firstTime_toNat_spec (P := fun m : ℕ => shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≤ (m : ℕ∞) ∧
      x m ∉ interiorCellVertices ε η (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3))) hExitNe
  have hCT : C ≤ T := toNat_le_of_le_nat hTspec.1
  -- the first hit cell is in the interior of the 4R/3-ball (mesh on B_ρ(0), walk localized)
  have hCint : x C ∈ interiorCellVertices ε η
      (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3)) :=
    Lemma68WalkLoc.shellHit_interior_of_mesh_loc hε (fillCells ε η ↑Θ) hd hKne hKb hr hrρ le_rfl hmesh k x
      hlam1 hRlo C hshC
  -- between the hit and the exit, the walk stays in the interior (firstTime minimality)
  have hmin : ∀ m : ℕ, C ≤ m → m < T →
      x m ∈ interiorCellVertices ε η (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3)) := by
    intro m hCm hmT
    by_contra hnot
    have hPm : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≤ (m : ℕ∞) := by
      rw [hshC]
      exact_mod_cast hCm
    have hle : shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≤ (m : ℕ∞) := by
      unfold shellExit
      exact (firstTime_le_iff _ m).2 ⟨m, le_rfl, hPm, hnot⟩
    have hTm : T ≤ m := toNat_le_of_le_nat hle
    omega
  have hCTlt : C < T := by
    rcases lt_or_eq_of_le hCT with h | h
    · exact h
    · rw [h] at hCint
      exact absurd hCint hTspec.2
  -- the test ball lies in B_{2R}(z), and its mesh is the restricted ball mesh
  have hball2 : Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
      (2 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)) ⊆ Metric.ball (0 : ℂ) ρ :=
    Lemma68ShellOrderPw.ball_two_mul_R_subset_of_shortEligible hzS hRhi hs.le
  have hmesh2 : CellDiamLe ε η (d / 100)
      (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (2 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x))) :=
    Lemma68ShellOrderPw.cellDiamLe_mono_set hball2 hmesh
  have hhR : d / 100 < R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 4 := by
    linarith
  have hTb := Lemma68Window.test_ball_of_exit hη hε.le x hadj hR0 hhR hmesh2 hCTlt hmin hTspec.2
  -- the walk at the killed exit time is outside the interior of the test ball
  have hτball : x τ ∉ interiorCellVertices ε η
      (Metric.ball (vertexPoint ε η (x T))
        (R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 4)) := by
    intro hmem
    apply hτn
    have hcv : (cell ε η (x τ) ∩ Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (2 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x))).Nonempty := by
      obtain ⟨y1, hy1, hy2⟩ := (mem_interiorCellVertices_iff.1 hmem).1
      exact ⟨y1, hy1, hTb.2 hy2⟩
    exact cell_meets_ball2_mem_killed hη hε hF0 h0 hy0 hlam1 hzy hz_bd.2 hR0 hRhi hds hs4 hd hr hrρ hcv
  have htest : testEnd ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≤ (τ : ℕ∞) := by
    unfold Lemma68Omega.testEnd
    exact (firstTime_le_iff _ τ).2 ⟨τ, le_rfl, hexit, hτball⟩
  exact ⟨htest, hzS⟩

/-- **The residual `ShellCGTestEndLoc 𝒮` holds for every `𝒮`.** Destructures the 43
clauses of `ShellPtPremCG` (current form, ShellCoreCG68.lean), derives the mesh on `B_{ρ_cell}(0)` from the counting event,
the killed exit a.s. finite, the start and the adjacency almost surely, and applies `testEnd_le_vExit_of_path_loc`. -/
theorem shellCGTestEndLoc_holds (𝒮 : SpaceFillingSLEModel) : Lemma68CGResLoc.ShellCGTestEndLoc 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hP hFA
  obtain ⟨hγ0, hγ2, hω₀, -, -, -, -, hκ2, hCG, -, -, hζ0, hζ1, hρ0, hρ1, -, hq0, hq0C, -, -, hRρ, hRA, -,
    hs₀, -, -, hε, hεe, hr10, hrR, -, hmeshC, hgapCl, -, hfin, hη, -, -, hdg, -, hcell, -, -⟩ := hP
  have hεω : 0 < ε ^ ω₀ := Real.rpow_pos_of_pos hε ω₀
  have hr : 0 < r := by linarith
  have hsc : 1 ≤ Lemma68ConstOrder.shellChone68 CE C := Lemma68ConstOrder.one_le_shellChone68 CE C
  have hq1 : q0 ≤ 1 := by
    have hpos : 0 < 4 * Lemma68ConstOrder.shellChone68 CE C := by linarith
    have h1 : (1 / 4 : ℝ) ^ 2 / (4 * Lemma68ConstOrder.shellChone68 CE C) ≤ 1 := by
      rw [div_le_one hpos]
      nlinarith
    exact hq0C.trans h1
  have hrz : r ≤ countThreshold ζ :=
    hrR.trans (hRA.trans (Lemma68ChainGlue.rAmp_le_countThreshold hq0 hq1 hζ0 hζ1))
  have hrρ : r ≤ ρ / 4 := hrR.trans hRρ
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hgap : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
    have := Real.rpow_nonneg hd.le (shortExp ζ)
    linarith
  have hR := Lemma68HoneRadii.windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) (Lemma68ConstOrder.shellC0 CG) C
    (dyadicD r) hd (dyadicD_le_one r) (by unfold shortExp; linarith) ω
  -- the mesh on B_{ρ_cell}(0) from the counting event, then on B_ρ(0)
  have hr0 : 0 < r := hr
  have hεcell := Lemma68ShellCoreCG.shellKCG_eps_cell
    (Lemma68ShellConstants.shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hκ2 hε hεe hr10
  have hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100)
      (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) :=
    Lemma68ShellCoreCG.cellDiamLe_rhoCell_of_meshEventR (c0 := Lemma68ConstOrder.shellC0 CG) S ω
      (Lemma68Guard10.countingMeshEventR_meshR hmeshC) hε hρ1 hr0 hrρ
      (Lemma68ShellCoreCG.shellC0_le_one_cg hCG) hεcell
  have hmesh_ball : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    Lemma68ShellOrderPw.cellDiamLe_mono_set
      (Metric.ball_subset_ball (by unfold Lemma68HoneCellGood.rhoCell68; linarith)) hmesh
  -- the almost sure inputs: killed exit finite, adjacency, start
  have hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ :=
    Lemma68KilledExitAe.ae_killed_exit_ne_top (hfin ε hε).1 (hfin ε hε).2 i.a ε (S.η ω) i.Θ i.F0 r
  have hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k hjk => hcell ε hε j k hjk
  have hstA := Lemma68HoneElAe.hstart_of_fullAdmAt_s1 S hε hs₀ ω hη r hr i hFA
  have hadm := hFA
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm
  obtain ⟨⟨hF0eq, hcl, hball⟩, -⟩ := hadm
  have h0K : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hball (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := fun y hy => hcl (subset_closure hy)
  -- the parameter facts of the shell chain (as in shellHde_pw68_s1)
  have hr1 : r ≤ 1 := hrz.trans (countThreshold_le_one hζ0)
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hd2 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr hrz hd hd2
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
    exact (le_div_iff₀ (by
      have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
      linarith)).1 h
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hc1]
    nlinarith [hfl]
  filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
    Lemma68ShellPathAe.ae_cell_adjacent (S.mult ε ω) i.a hε hmap, hkill] with x hx0 hadj hτ
  intro k hk
  have hst : (cell ε (S.η ω) (x 0) ∩
      frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty := by
    rw [hx0]
    exact hstA
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _)
    ((testEnd_le_vExit_of_path_loc hη hε hr hrρ hd hds hs4 hNs hmesh_ball hF0eq h0K hKb hR hadj hst hτ k hk).1)

end Lemma68CGResTestEnd
end MatedCRT

#print axioms MatedCRT.Lemma68CGResTestEnd.cell_meets_ball2_mem_killed
#print axioms MatedCRT.Lemma68CGResTestEnd.testEnd_le_vExit_of_path_loc
#print axioms MatedCRT.Lemma68CGResTestEnd.shellCGTestEndLoc_holds
