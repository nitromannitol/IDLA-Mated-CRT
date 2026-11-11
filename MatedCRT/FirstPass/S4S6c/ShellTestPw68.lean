import MatedCRT.FirstPass.S4S6c.ShellHdePw68
import MatedCRT.FirstPass.S4S6c.FiniteExitTestEnd68
import MatedCRT.FirstPass.S4S6c.FiniteExitMomentHone68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S6r.ShellOmegaStop
import MatedCRT.FirstPass.S6r.ShellPathAe

/-!
# The test-end event at one environment point (htest of `shellOneTest_at_of_goodEnv'`)

The pointwise form of the named input `htest` of `shellHde68_full_omega` (S4S6c/ShellHdeOmega68.lean:104) and of
`shellOneTest_at_of_goodEnv'` (S4S6c/B1Assembly68.lean:823). At ONE environment point `ω` the test ends
`L_k = testEnd k` of the shell chain are almost surely finite, from `FullAdmAt` and the environment facts at `ω`
(continuity and properness of `η`, locally finite multiplicities with `m(k, k+1) ≠ 0`, cell adjacency, the cell diameter
bound `CellDiamLe`, the killed exit `hkill`). No almost-sure quantifier over `ω` is used.

Route (finite test domain, `FiniteExitTestEnd68.testEnd_ne_top_of_finite`):
1. The shell exit `T_k = shellExit k` is a walk random time (`isStoppingTime_of_prefixLocal`, `shellExit_prefixLocal`).
2. On `{T_k < ∞}` the test interior `B_{R/4}(η(X_{T_k}))` meets only the vertices of the finite set `V^ε(B(0, ρ+3))`:
   the exit point satisfies `|η(εX_{T_k})| ≤ ρ + 2`. Either `T_k` is the hit `C_{k+1}`, whose cell meets the two-sided
   shell (inside `B(0, ρ)`, `twoSidedShell_mem_ball`), or the walk steps from the interior of the shell ball
   `B(c, 4R/3)` (minimality of the first exit, Armstrong-Kuusi-Mourrat shell chain) to `X_{T_k}`; the cells have diameter
   `≤ r/100` (Duplantier-Sheffield cell distance).
3. `cellVertices` of a bounded set is finite for a proper `η` (`TraceInputs68.cellVertices_finite_of_tendsto`).
4. `T_k < ∞` almost surely (`shellHde_pw68`, which does not use `htest`), so the test end is finite almost surely.
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry
open MatedCRT.Lemma68ShellHde68
open scoped Classical

namespace MatedCRT
namespace Lemma68ShellTestPw68

/-- The vertex point `η(εk)` lies in the cell `η([ε(k-1), εk])` of the vertex `εk`. -/
lemma vertexPoint_mem_cell_pw68 {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩

/-- A first-time value `firstTime P = m` (a `Nat.find`) gives `P m` and `¬ P j` for every `j < m`. -/
lemma firstTime_eq_coe_spec_pw68 {P : ℕ → Prop} {m : ℕ} (h : Lemma68Omega.firstTime P = (m : ℕ∞)) :
    P m ∧ ∀ j < m, ¬ P j := by
  unfold Lemma68Omega.firstTime at h
  split at h
  · rename_i hex
    have hm : Nat.find hex = m := by exact_mod_cast h
    rw [← hm]
    exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  · exact absurd h (by simp)

/-- **The test interior of a finite shell exit lies in a bounded set of vertices (pointwise).** Let `k` be a shell index
with `λ_{k+1} ≤ r/20`, let the shell centre have radius `R ≤ 1`, and let the path be cell-adjacent. If the shell exit
`T_k` is finite, the vertices of the test interior `I(B_{R/4}(η(X_{T_k})))` have cells meeting `B(0, ρ+3)`. -/
lemma testInterior_sub_pw68 {ε : ℝ} {η : ℝ → ℂ} {K : Set ℂ} {r s d ρ : ℝ} {R : ℂ → ℝ}
    {k : ℕ} {x : ℕ → ℤ} (hε : 0 < ε) (hd : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) (hrρ : r ≤ ρ / 4)
    (hmesh : CellDiamLe ε η (d / 100) Set.univ)
    (hK : K.Nonempty) (hKb : K ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hlam : shellOffset s (k + 1) ≤ r / 20)
    (hRc : R (shellCentre ε η K r s d k x) ≤ 1)
    (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    (hT : shellExit ε η K r s d R k x ≠ ⊤) :
    interiorCellVertices ε η (Metric.ball (vertexPoint ε η (x (shellExit ε η K r s d R k x).toNat))
        (R (shellCentre ε η K r s d k x) / 4)) ⊆ cellVertices ε η (Metric.ball (0 : ℂ) (ρ + 3)) := by
  have hg : 0 < d / 100 := by positivity
  have hdiam : ∀ n : ℕ, ∀ p ∈ cell ε η (x n), ∀ q ∈ cell ε η (x n), dist p q ≤ d / 100 :=
    fun n p hp q hq => hmesh (x n) ⟨p, hp, Set.mem_univ _⟩ p hp q hq
  have hvm : ∀ n : ℕ, vertexPoint ε η (x n) ∈ cell ε η (x n) :=
    fun n => vertexPoint_mem_cell_pw68 hε η (x n)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
  have htn : (shellExit ε η K r s d R k x).toNat = m := by rw [← hm, ENat.toNat_natCast]
  rw [htn]
  obtain ⟨hPm, hmin⟩ := firstTime_eq_coe_spec_pw68 (P := fun n : ℕ => shellHit ε η K r s k x ≤ (n : ℕ∞) ∧
      x n ∉ interiorCellVertices ε η (Metric.ball (shellCentre ε η K r s d k x)
        (4 * R (shellCentre ε η K r s d k x) / 3))) hm.symm
  have hhit_le : shellHit ε η K r s k x ≤ (m : ℕ∞) := hPm.1
  have hhit_ne : shellHit ε η K r s k x ≠ ⊤ :=
    (lt_of_le_of_lt hhit_le (ENat.natCast_lt_top m)).ne
  obtain ⟨h, hh⟩ : ∃ h : ℕ, shellHit ε η K r s k x = (h : ℕ∞) :=
    ⟨_, (ENat.natCast_toNat hhit_ne).symm⟩
  have hhm : h ≤ m := by
    have h1 : (h : ℕ∞) ≤ (m : ℕ∞) := hh ▸ hhit_le
    exact_mod_cast h1
  have hcen : shellCentre ε η K r s d k x = gridRound (d / 100) (vertexPoint ε η (x h)) := by
    unfold shellCentre
    rw [hh, ENat.toNat_natCast]
  -- the hit cell meets the two-sided shell, which lies in B(0, ρ)
  obtain ⟨z, hzc, hzS⟩ := (firstTime_eq_coe_spec_pw68 (P := fun n : ℕ =>
      (cell ε η (x n) ∩ twoSidedShell K r (shellOffset s (k + 1))).Nonempty) hh).1
  have hzB : dist z 0 < ρ :=
    Metric.mem_ball.1 (Lemma68ShellHdePw68.twoSidedShell_mem_ball hK hKb hr hrρ hlam hzS)
  have hvh : dist (vertexPoint ε η (x h)) 0 ≤ ρ + d / 100 := by
    have h1 := hdiam h _ (hvm h) z hzc
    linarith [dist_triangle (vertexPoint ε η (x h)) z 0]
  have hcd : dist (shellCentre ε η K r s d k x) (vertexPoint ε η (x h)) ≤ d / 100 := by
    rw [hcen]
    exact dist_gridRound_le hg _
  have hcz : dist (shellCentre ε η K r s d k x) 0 ≤ ρ + 2 * (d / 100) := by
    linarith [dist_triangle (shellCentre ε η K r s d k x) (vertexPoint ε η (x h)) 0]
  -- the exit point is within ρ + 2 of the origin
  have hp : dist (vertexPoint ε η (x m)) 0 ≤ ρ + 2 := by
    rcases eq_or_lt_of_le hhm with hmh | hlt
    · rw [← hmh]
      linarith
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hxj : x j ∈ interiorCellVertices ε η (Metric.ball (shellCentre ε η K r s d k x)
          (4 * R (shellCentre ε η K r s d k x) / 3)) := by
        by_contra hnot
        exact hmin j (Nat.lt_succ_self j) ⟨by rw [hh]; exact_mod_cast (by omega : h ≤ j), hnot⟩
      have hyne : (cell ε η (x j) ∩ Metric.ball (shellCentre ε η K r s d k x)
          (4 * R (shellCentre ε η K r s d k x) / 3)).Nonempty := hxj.1
      obtain ⟨y, hyc, hyB⟩ := hyne
      obtain ⟨w, hwj, hwj1⟩ := hadj j
      have hyc' := Metric.mem_ball.1 hyB
      have h1 := hdiam j y hyc w hwj
      rw [dist_comm y w] at h1
      have h2 := hdiam (j + 1) (vertexPoint ε η (x (j + 1))) (hvm (j + 1)) w hwj1
      have hRc' : 4 * R (shellCentre ε η K r s d k x) / 3 ≤ 4 / 3 := by linarith
      have t1 := dist_triangle (vertexPoint ε η (x (j + 1))) w y
      have t2 := dist_triangle (vertexPoint ε η (x (j + 1))) y (shellCentre ε η K r s d k x)
      have t3 := dist_triangle (vertexPoint ε η (x (j + 1))) (shellCentre ε η K r s d k x) 0
      linarith
  -- the test interior lies in the vertices whose cells meet B(0, ρ + 3)
  intro v hv
  have hv1 : (cell ε η v ∩ Metric.ball (vertexPoint ε η (x m))
      (R (shellCentre ε η K r s d k x) / 4)).Nonempty := hv.1
  obtain ⟨y', hy'c, hy'B⟩ := hv1
  have hy'0 := Metric.mem_ball.1 hy'B
  have hRc4 : R (shellCentre ε η K r s d k x) / 4 ≤ 1 / 4 := by linarith
  show (cell ε η v ∩ Metric.ball (0 : ℂ) (ρ + 3)).Nonempty
  refine ⟨y', hy'c, Metric.mem_ball.2 ?_⟩
  linarith [dist_triangle y' (vertexPoint ε η (x m)) 0]

/-- **The test-end event at one environment point (the pointwise `htest`).** At ONE environment point `ω`, from
`FullAdmAt` and the environment facts at `ω`, the test ends `testEnd k` of the shell chain are almost surely finite,
for every shell index `k ≤ N = shellCount r s - 1`, with `s = dyadicD r ^ shortExp ζ`. The finite domain is
`V^ε(B(0, ρ+3))`; the shell exit `shellExit k` is finite almost surely by `shellHde_pw68`, which does not use `htest`. -/
theorem shellTest_pw68 {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {ω : Ω}
    {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hη : Continuous (S.η ω))
    (hcurve : Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig w)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ := by
  -- properness of η at ω (the cocompact form of the curve escaping both ends, S6e/Geometry.lean:94)
  have hprop : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  -- deterministic parameter facts (as in shellHde_pw68)
  have hr1 : r ≤ 1 := hrz.trans (countThreshold_le_one hζ)
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hd2 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
  have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
  have hs1 : dyadicD r ^ shortExp ζ ≤ 1 :=
    Real.rpow_le_one hd.le hd1 (by unfold shortExp; linarith)
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ hr hrz hd hd2
  have h400 : 400 * dyadicD r ^ shortExp ζ ≤ r := by linarith
  have hc1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ (by linarith)]
    linarith
  have hfl : (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) * (400 * dyadicD r ^ shortExp ζ) ≤ r := by
    have h := Nat.floor_le (show 0 ≤ r / (400 * dyadicD r ^ shortExp ζ) by positivity)
    exact (le_div_iff₀ (by linarith)).1 h
  have hmesh_ball : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    fun k hk => hmesh k (by obtain ⟨y, hy⟩ := hk; exact ⟨y, hy.1, Set.mem_univ _⟩)
  intro hadm
  have hadm' := hadm
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm'
  obtain ⟨⟨-, hcl, hball⟩, -⟩ := hadm'
  have hK : (fillCells ε (S.η ω) ↑i.Θ).Nonempty := ⟨0, hball (Metric.mem_ball_self hs₀)⟩
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) :=
    fun y hy => hcl (subset_closure hy)
  -- the shell exit is finite almost surely (shellHde_pw68, without htest)
  have hA : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
      (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) :=
    Lemma68ShellHdePw68.shellHde_pw68 S hε hs₀ hζ hζ1 hr hrz hrρ i hη hmap hkill hR hElig hmesh_ball hstart hadm
  have hadjA := Lemma68ShellPathAe.ae_cell_adjacent (S.mult ε ω) i.a hε hmap
  have hfin : (cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) (ρ + 3))).Finite :=
    TraceInputs68.cellVertices_finite_of_tendsto hε hprop Metric.isBounded_ball
  have hk : ∀ k : ℕ, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1 →
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ := by
    intro k
    by_cases hkN : k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1
    · have hTw : S6j.IsWalkRandomTime
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k) :=
        FiniteExitMomentHone68.isWalkRandomTime_of_isStoppingTime
          (Lemma68OmegaStop.isStoppingTime_of_prefixLocal
            (Lemma68Omega.shellExit_prefixLocal ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k))
      have hlam : shellOffset (dyadicD r ^ shortExp ζ) (k + 1) ≤ r / 20 := by
        have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) := by
          exact_mod_cast (by omega : k + 1 ≤ shellCount r (dyadicD r ^ shortExp ζ))
        unfold shellOffset
        nlinarith [mul_le_mul_of_nonneg_right hk1 hs.le]
      have hIG : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x < ⊤ →
            interiorCellVertices ε (S.η ω) (Metric.ball (vertexPoint ε (S.η ω)
              (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
                Rf k x).toNat))
              (Rf (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
                / 4))
            ⊆ cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) (ρ + 3)) := by
        filter_upwards [hadjA, hA] with x hadjx hx hT
        exact testInterior_sub_pw68 hε hd hd1 hr hrρ hmesh hK hKb hlam
          ((hR _ (hx.2 k hkN)).2.trans hs1) hadjx hT.ne
      have hfinite := FiniteExitTestEnd68.testEnd_ne_top_of_finite (m := S.mult ε ω) hlf hcons hTw hfin i.a
        (I := fun x => interiorCellVertices ε (S.η ω) (Metric.ball (vertexPoint ε (S.η ω)
          (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            Rf k x).toNat))
          (Rf (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
            / 4)))
        hIG (testE := fun x => testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
          (dyadicD r) Rf k x) (fun _ => rfl)
      filter_upwards [hfinite, hA] with x h1 hx _
      exact h1 (lt_top_iff_ne_top.2 (hx.1 k hkN))
    · exact Filter.Eventually.of_forall fun x hx => absurd hx hkN
  filter_upwards [ae_all_iff.2 hk] with x hx
  exact hx

/-- **The sparsity-parameter form of `shellTest_pw68`.** The guard `FullAdmAt` is taken at the
exponent `s1` in place of `sparsityS1 γ`; the shell finiteness is `shellHde_pw68_s1` at the same `s1`. -/
theorem shellTest_pw68_s1 {γ : ℝ} (s1 : ℝ) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {ω : Ω}
    {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hη : Continuous (S.η ω))
    (hcurve : Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤)
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig w)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ := by
  -- properness of η at ω (the cocompact form of the curve escaping both ends, S6e/Geometry.lean:94)
  have hprop : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  -- deterministic parameter facts (as in shellHde_pw68)
  have hr1 : r ≤ 1 := hrz.trans (countThreshold_le_one hζ)
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hd2 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
  have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
  have hs1 : dyadicD r ^ shortExp ζ ≤ 1 :=
    Real.rpow_le_one hd.le hd1 (by unfold shortExp; linarith)
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ hr hrz hd hd2
  have h400 : 400 * dyadicD r ^ shortExp ζ ≤ r := by linarith
  have hc1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ (by linarith)]
    linarith
  have hfl : (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) * (400 * dyadicD r ^ shortExp ζ) ≤ r := by
    have h := Nat.floor_le (show 0 ≤ r / (400 * dyadicD r ^ shortExp ζ) by positivity)
    exact (le_div_iff₀ (by linarith)).1 h
  have hmesh_ball : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    fun k hk => hmesh k (by obtain ⟨y, hy⟩ := hk; exact ⟨y, hy.1, Set.mem_univ _⟩)
  intro hadm
  have hadm' := hadm
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm'
  obtain ⟨⟨-, hcl, hball⟩, -⟩ := hadm'
  have hK : (fillCells ε (S.η ω) ↑i.Θ).Nonempty := ⟨0, hball (Metric.mem_ball_self hs₀)⟩
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) :=
    fun y hy => hcl (subset_closure hy)
  -- the shell exit is finite almost surely (shellHde_pw68, without htest)
  have hA : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
      (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) :=
    Lemma68ShellHdePw68.shellHde_pw68_s1 s1 S hε hs₀ hζ hζ1 hr hrz hrρ i hη hmap hkill hR hElig hmesh_ball hstart hadm
  have hadjA := Lemma68ShellPathAe.ae_cell_adjacent (S.mult ε ω) i.a hε hmap
  have hfin : (cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) (ρ + 3))).Finite :=
    TraceInputs68.cellVertices_finite_of_tendsto hε hprop Metric.isBounded_ball
  have hk : ∀ k : ℕ, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1 →
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ := by
    intro k
    by_cases hkN : k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1
    · have hTw : S6j.IsWalkRandomTime
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k) :=
        FiniteExitMomentHone68.isWalkRandomTime_of_isStoppingTime
          (Lemma68OmegaStop.isStoppingTime_of_prefixLocal
            (Lemma68Omega.shellExit_prefixLocal ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k))
      have hlam : shellOffset (dyadicD r ^ shortExp ζ) (k + 1) ≤ r / 20 := by
        have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) := by
          exact_mod_cast (by omega : k + 1 ≤ shellCount r (dyadicD r ^ shortExp ζ))
        unfold shellOffset
        nlinarith [mul_le_mul_of_nonneg_right hk1 hs.le]
      have hIG : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x < ⊤ →
            interiorCellVertices ε (S.η ω) (Metric.ball (vertexPoint ε (S.η ω)
              (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
                Rf k x).toNat))
              (Rf (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
                / 4))
            ⊆ cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) (ρ + 3)) := by
        filter_upwards [hadjA, hA] with x hadjx hx hT
        exact testInterior_sub_pw68 hε hd hd1 hr hrρ hmesh hK hKb hlam
          ((hR _ (hx.2 k hkN)).2.trans hs1) hadjx hT.ne
      have hfinite := FiniteExitTestEnd68.testEnd_ne_top_of_finite (m := S.mult ε ω) hlf hcons hTw hfin i.a
        (I := fun x => interiorCellVertices ε (S.η ω) (Metric.ball (vertexPoint ε (S.η ω)
          (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            Rf k x).toNat))
          (Rf (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
            / 4)))
        hIG (testE := fun x => testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
          (dyadicD r) Rf k x) (fun _ => rfl)
      filter_upwards [hfinite, hA] with x h1 hx _
      exact h1 (lt_top_iff_ne_top.2 (hx.1 k hkN))
    · exact Filter.Eventually.of_forall fun x hx => absurd hx hkN
  filter_upwards [ae_all_iff.2 hk] with x hx
  exact hx

end Lemma68ShellTestPw68
end MatedCRT

#print axioms MatedCRT.Lemma68ShellTestPw68.testInterior_sub_pw68
#print axioms MatedCRT.Lemma68ShellTestPw68.shellTest_pw68
#print axioms MatedCRT.Lemma68ShellTestPw68.shellTest_pw68_s1
