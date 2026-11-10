import MatedCRT.FirstPass.S4S6c.ShellHdeOmega68

/-!
# The pointwise shell hypothesis `hde` with a localized mesh bound (fp-S4S6c-hde-pointwise, z1)

The pointwise form of `shellHde68_full_omega` (S4S6c/ShellHdeOmega68.lean:94): the same conclusion at ONE environment
point `ω`, with each environment fact that the almost-sure proof filters over given as a hypothesis at `ω`:
continuity of `η` (`TraceInputs68.ae_continuous_eta`), the cell-adjacency of the multiplicities
(`Lemma68ShellEnvAe.map_cells_meet_ae`), the killed exit `hkill` (`Lemma68ShellEnvAeInputs.hkill_of_valid`), the mesh bound
`hmesh`, the start input `hstart` and the test input `htest`. The radius facts `hR`, `hElig` are the ones of `Rf`, `Elig`
at `ω`, so `Rf` and `Elig` are plain functions here.

Localized mesh. `shell_fin_of_path` (S4S6c/ShellHde68.lean:209) uses its mesh hypothesis once (ShellHde68.lean:265), on the
cell `x C` of the shell hit. That cell meets the two-sided shell `twoSidedShell (fillCells …) r λ` with `λ ≤ r/20`
(`hlam1`). The shell lies in `Metric.ball 0 ρ` when `fillCells ⊆ ball 0 (ρ/2)` and `r ≤ ρ/4`
(`twoSidedShell_mem_ball`). So the mesh bound is needed only on the cells meeting `Metric.ball 0 ρ`, the localized form of
chat 239 (`notes/fp-gaps/CHATGPT-239-idla-hU-named-inputs-PRO.md` l.269-291). `shell_fin_of_path_loc` is a copy of
`shell_fin_of_path` that differs only in that hypothesis and in that one application (ShellHde68.lean is not edited).

Terminology: shells and cell distance (Duplantier-Sheffield); good annuli and the shell chain (Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry
open MatedCRT.Lemma68ShellHde68

namespace MatedCRT
namespace Lemma68ShellHdePw68

/-- A point of the two-sided shell `{x | |infDist x K - r/2| = λ}` (`twoSidedShell`, S6r/Shells/Parameters.lean:28) with
`λ ≤ r/20` lies in `B(0, ρ)`, when `K` is nonempty, `K ⊆ B(0, ρ/2)` and `0 < r ≤ ρ/4`. -/
theorem twoSidedShell_mem_ball {K : Set ℂ} (hK : K.Nonempty) {ρ r lam : ℝ}
    (hKb : K ⊆ Metric.ball (0 : ℂ) (ρ / 2)) (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hlam : lam ≤ r / 20) {y : ℂ}
    (hy : y ∈ twoSidedShell K r lam) : y ∈ Metric.ball (0 : ℂ) ρ := by
  have hy' : |Metric.infDist y K - r / 2| = lam := hy
  have hle : Metric.infDist y K - r / 2 ≤ lam := (le_abs_self _).trans hy'.le
  have hlt : Metric.infDist y K < ρ / 4 := by linarith
  obtain ⟨z, hzK, hyz⟩ := (Metric.infDist_lt_iff hK).1 hlt
  have hz : dist z 0 < ρ / 2 := hKb hzK
  have htri : dist y 0 ≤ dist y z + dist z 0 := dist_triangle y z 0
  rw [Metric.mem_ball]
  linarith

/-- **The shell path lemma with the localized mesh bound** (copy of `shell_fin_of_path`, ShellHde68.lean:209). On a
walk from `i.a` whose killed exit is finite and whose consecutive cells are adjacent, the shell exits are finite and the
shell centres are eligible. The mesh bound `hmesh` is needed only on the cells meeting `Metric.ball 0 ρ`: the one use
(the cell `x C` of the shell hit) meets the shell, which lies in that ball (`twoSidedShell_mem_ball`). -/
theorem shell_fin_of_path_loc {η : ℝ → ℂ} {ε : ℝ} (hη : Continuous η) (hε : 0 < ε)
    {Θ F0 : Finset ℤ} {ρ r d a : ℝ} {R : ℂ → ℝ} {n : ℕ} (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρ))
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRS : ∀ w ∈ shortEligible ρ d a, d ≤ R w ∧ R w ≤ d ^ a)
    {x : ℕ → ℤ} (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : vExitTime (killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≠ ⊤ ∧
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
  have hCspec : (cell ε η (x C) ∩ twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty :=
    firstTime_toNat_spec (P := fun m => (cell ε η (x m) ∩
      twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty) hCfin
  obtain ⟨y0, hy0c, hy0⟩ := hCspec
  -- the centre is within 2d/100 of the shell
  have hw : vertexPoint ε η (x C) ∈ cell ε η (x C) := vertexPoint_mem_cell_nonneg hε.le η (x C)
  have hwy : dist (vertexPoint ε η (x C)) y0 ≤ d / 100 :=
    hmesh (x C) ⟨y0, hy0c, twoSidedShell_mem_ball hKne hKb hr hrρ hlam1 hy0⟩ _ hw _ hy0c
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
  -- the walk at the killed exit time is outside the exit ball
  have hxτB : x τ ∉ interiorCellVertices ε η
      (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3)) := by
    intro hmem
    exact hτn (cell_meets_ball_mem_killed hη hε hF0 h0 hy0 hlam1 hzy hz_bd.2 hR0 hRhi hds hs4 hd hr hrρ
      (mem_interiorCellVertices_iff.1 hmem).1)
  have hexit : shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≤ (τ : ℕ∞) := by
    unfold shellExit
    exact (firstTime_le_iff _ τ).2 ⟨τ, le_rfl, hitle, hxτB⟩
  exact ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top τ) hexit, hzS⟩

/-- **The pointwise shell hypothesis `hde` (the ω-level form of `shellHde_ae68_omega`, ShellHdeOmega68.lean:28).**
At one environment point `ω`, with each almost-sure environment fact of the proof given as a hypothesis at `ω`:
on the guard `FullAdmAt` at `ω`, for almost every walk from `i.a` on `S.mult ε ω`, every shell exit `shellExit k`
(`k ≤ shellCount - 1`) is finite and every shell centre `shellCentre k` is eligible. The mesh bound `hmesh` is localized to
the cells meeting `Metric.ball 0 ρ`. -/
theorem shellHde_pw68 {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {ω : Ω}
    {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hη : Continuous (S.η ω))
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig w)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ))
    (hstart : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) := by
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
  intro hadm
  have hstA := hstart hadm
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm
  obtain ⟨⟨hF0eq, hcl, hball⟩, -⟩ := hadm
  have h0K : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hball (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := fun y hy => hcl (subset_closure hy)
  have hRS : ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ := fun w hw => hR w (hElig w hw)
  filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
    Lemma68ShellPathAe.ae_cell_adjacent (S.mult ε ω) i.a hε hmap, hkill] with x hx0 hadj hτ
  have hpath := shell_fin_of_path_loc (ε := ε) (R := Rf) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hη hε hr hrρ hd hds hs4 hNs hmesh hF0eq h0K hKb hRS hadj (by rw [hx0]; exact hstA) hτ
  exact ⟨fun k hk => (hpath k hk).1, fun k hk => hElig _ (hpath k hk).2⟩

/-- **The pointwise full shell hypothesis `hde` (the ω-level form of `shellHde68_full_omega`,
ShellHdeOmega68.lean:94).** The testEnd conjunct is the named pointwise input `htest` (the finite-domain exit statement
for the test ends, guarded by `FullAdmAt`, as the a.s. input `htest` of `shellHde68_full_omega`). The conclusion is the
conjunction of `shellHde_pw68` with `htest`, at the same environment point `ω`. -/
theorem shellHde68_full_pw {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {ω : Ω}
    {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hη : Continuous (S.η ω))
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig w)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ))
    (hstart : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) := by
  intro hadm
  have h1 := shellHde_pw68 S hε hs₀ hζ hζ1 hr hrz hrρ i hη hmap hkill hR hElig hmesh hstart hadm
  filter_upwards [h1, htest hadm] with x ha hb
  exact ⟨fun k hk => ⟨ha.1 k hk, hb k hk⟩, ha.2⟩

/-- **The sparsity-parameter form of `shellHde_pw68` (fp-S4S6c-s1, z1).** The guard `FullAdmAt` is taken at the
exponent `s1` in place of `sparsityS1 γ`; the proof is that of `shellHde_pw68`, which uses `s1` only through `FullAdmAt`. -/
theorem shellHde_pw68_s1 {γ : ℝ} (s1 : ℝ) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {ω : Ω}
    {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hη : Continuous (S.η ω))
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig w)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ))
    (hstart : Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) := by
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
  intro hadm
  have hstA := hstart hadm
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm
  obtain ⟨⟨hF0eq, hcl, hball⟩, -⟩ := hadm
  have h0K : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hball (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := fun y hy => hcl (subset_closure hy)
  have hRS : ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ := fun w hw => hR w (hElig w hw)
  filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
    Lemma68ShellPathAe.ae_cell_adjacent (S.mult ε ω) i.a hε hmap, hkill] with x hx0 hadj hτ
  have hpath := shell_fin_of_path_loc (ε := ε) (R := Rf) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hη hε hr hrρ hd hds hs4 hNs hmesh hF0eq h0K hKb hRS hadj (by rw [hx0]; exact hstA) hτ
  exact ⟨fun k hk => (hpath k hk).1, fun k hk => hElig _ (hpath k hk).2⟩

end Lemma68ShellHdePw68
end MatedCRT

#print axioms MatedCRT.Lemma68ShellHdePw68.twoSidedShell_mem_ball
#print axioms MatedCRT.Lemma68ShellHdePw68.shell_fin_of_path_loc
#print axioms MatedCRT.Lemma68ShellHdePw68.shellHde_pw68
#print axioms MatedCRT.Lemma68ShellHdePw68.shellHde68_full_pw
#print axioms MatedCRT.Lemma68ShellHdePw68.shellHde_pw68_s1
