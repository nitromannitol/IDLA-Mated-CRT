import MatedCRT.FirstPass.S4S6c.HoneMomSPw68
import MatedCRT.FirstPass.S4S6c.HoneRrLocal68
import MatedCRT.FirstPass.S4S6c.PathMesh68
import MatedCRT.FirstPass.S4S6c.HoneExitGeom68

/-!
# The margin binder `hx1` with the ball mesh

`hx1_fixedOmega` (HoneMomSPw68.lean:138) takes the global mesh `CellDiamLe ε (η ω) (dyadicD r / 100) univ`. Here the mesh
is the ball form `CellDiamLe ε (η ω) (dyadicD r / 100) (ball 0 ρmesh)` with `dyadicD r / 100 ≤ ρmesh - ρ`. The instance
`ρmesh := ρ + dyadicD r / 100` is the exit-cell radius of `Lemma68PathMesh.diam_upto_vExitTime_exit`. The conclusion is
the conclusion of `hx1_fixedOmega`; the original theorem is kept unchanged.

Where the univ form was used, and its ball replacement:
* shell centres (`hEl` of the walk): `Lemma68HoneRrLocal.shellCentre_mem_of_walk_loc` needs the mesh on `ball 0 ρ`,
  which is `ball 0 ρmesh` restricted (`cellDiamLe_mono_set`);
* hit cell (`hhit`): a hit time `t` is at most the shell exit time, which is below the exit time of the killed walk
  (`prefixSet`); the walk vertex `x t` then meets `ball 0 ρmesh` (`walk_mem_meshBall_upto_vExitTime`), which gives
  the cell diameter bound of `shellHit_interior_of_cellDiam` (HoneExitGeom68);
* exit vertex (`exitVertex_mem_ball_of_sphere`): its mesh input concerns cells meeting `ball 0 ρ ⊆ ball 0 ρmesh`;
* walk start: `cell_meets_ball_of_frontier` turns the frontier start input into `cell (x 0) ∩ ball 0 ρ ≠ ∅`.

Terminology: Armstrong-Kuusi-Mourrat (cells, mesh), Armitage-Gardiner (balls), Duplantier-Sheffield (boundary-length
parametrisation of the walk).
-/

namespace MatedCRT
namespace HoneX1Loc68

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68Window Lemma68Omega Lemma68OmegaStop Lemma68ShellParam Lemma68B1Assembly
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68ShellIdent MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible MatedCRT.Lemma68ConstOrder

/-- The start cell meets `ball 0 ρ` when it meets the frontier of `thickening (r / 2) K`, for `K ⊆ ball 0 (ρ / 2)`:
the frontier lies in `closedBall 0 (ρ / 2 + r / 2) ⊆ ball 0 ρ` (`r ≤ ρ / 4`). -/
theorem cell_meets_ball_of_frontier {ε : ℝ} {η : ℝ → ℂ} {a : ℤ} {K : Set ℂ} {ρ r : ℝ}
    (hK : K ⊆ Metric.ball (0 : ℂ) (ρ / 2)) (hr : 0 < r) (hrρ : r ≤ ρ / 4)
    (h : (cell ε η a ∩ frontier (Metric.thickening (r / 2) K)).Nonempty) :
    (cell ε η a ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
  obtain ⟨p, hpc, hpf⟩ := h
  have hT : Metric.thickening (r / 2) K ⊆ Metric.ball (0 : ℂ) (ρ / 2 + r / 2) :=
    (Metric.thickening_subset_of_subset (r / 2) hK).trans
      ((Metric.thickening_ball (0 : ℂ) (r / 2) (ρ / 2)).trans (Metric.ball_subset_ball (by linarith)))
  have hcl : closure (Metric.thickening (r / 2) K) ⊆ Metric.closedBall (0 : ℂ) (ρ / 2 + r / 2) :=
    closure_minimal (hT.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  exact ⟨p, hpc, Metric.closedBall_subset_ball (by linarith) (hcl (frontier_subset_closure hpf))⟩

/-- **`hx1_fixedOmega_loc_s1`: `hx1_fixedOmega_loc` with a general sparsity coefficient `s1` (variant).**
The guard `FullAdmAt s1` replaces `FullAdmAt (sparsityS1 γ)`. The proof uses only `ConfigOK` (of `hadm.1`) and
`hstart_of_fullAdmAt`, which are generic in `s1`; no hypothesis on `s1` is needed. The original `hx1_fixedOmega_loc` is
the specialisation `s1 := sparsityS1 γ` with the same statement. Mesh: the ball form
`CellDiamLe ε (η ω) (dyadicD r / 100) (ball 0 ρmesh)` of `hx1_fixedOmega`. Same conclusion
and same hypotheses as `hx1_fixedOmega`, except that the global mesh `univ` is replaced by the ball `ball 0 ρmesh`
and the mesh gap `dyadicD r / 100 ≤ ρmesh - ρ` is added (named `hgapMesh`, since `hgap : ρ ≤ ρmom` is kept). -/
theorem hx1_fixedOmega_loc_s1 {γ ω₀ ρ CG ζ α CE C ε s₀ r ρmom ρmesh s1 : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r)
    (hrρ : r ≤ ρ / 4) (hrle : r ≤ countThreshold ζ) (hgap : ρ ≤ ρmom)
    (hgapMesh : dyadicD r / 100 ≤ ρmesh - ρ)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh)) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < ρmom - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4 := by
  intro hadm
  obtain ⟨-, hcurve, hmult, hη, -, -, hdeg, hadjC, hadjε⟩ := hreg
  obtain ⟨hlf, hcons⟩ := hmult ε hε
  have hedge := hadjε ε hε
  have hp := Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  have hF0 : (↑i.F0 : Set ℤ) = cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) ρ) := hadm.1.1
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) :=
    subset_closure.trans hadm.1.2.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hadm.1.2.2 (Metric.mem_ball_self hs₀)
  have hst := Lemma68ShellCorePw.hstart_of_fullAdmAt S ω i hη hε hr0 hs₀ hadm
  have hr1 : r ≤ 1 := by linarith
  have hd := dyadicD_pos r
  have hd1 := dyadicD_le_one r
  have hdr : r ^ 2 ≤ dyadicD r := (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd2 : dyadicD r < 2 * r ^ 2 := (Lemma68ChainGlue.dyadicD_mem hr0 hr1).2
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    simpa using h
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrle hd hd2
  have hcb := Lemma68ChainGlue.countBound_zeta hζ0 hr0 hrle hd hdr hd2
  have hζr : r ^ ζ ≤ (2 : ℝ) ^ (-shortExp ζ) / 4000 := by
    have h := Real.rpow_le_rpow hr0.le hrle hζ0.le
    unfold countThreshold at h
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hζ0.ne', Real.rpow_one] at h
  have hrpos : 0 < r ^ ζ := Real.rpow_pos_of_pos hr0 ζ
  have hkey : 1 ≤ countConst ζ * r ^ (-ζ) := by
    unfold countConst
    rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, one_le_div hrpos]
    have hX : (0 : ℝ) < (2 : ℝ) ^ (-shortExp ζ) := by positivity
    linarith
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h := hkey.trans hcb
    exact_mod_cast h
  have hn : shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 = shellCount r (dyadicD r ^ shortExp ζ) :=
    Nat.sub_add_cancel hN1
  have hNs : 20 * (((shellCount r (dyadicD r ^ shortExp ζ) - 1) + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [hn]
    have h1 : ((shellCount r (dyadicD r ^ shortExp ζ) : ℕ) : ℝ) ≤ r / (400 * dyadicD r ^ shortExp ζ) := by
      unfold shellCount
      exact Nat.floor_le (by positivity)
    have hpos : 0 < 400 * dyadicD r ^ shortExp ζ := by positivity
    have h2 := (le_div_iff₀ hpos).mp h1
    nlinarith [h2]
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ winRf S ρ ζ C r ω z ∧ winRf S ρ ζ C r ω z ≤ dyadicD r ^ shortExp ζ :=
    Lemma68HoneRadii.windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd hd1 ha1 ω
  have hPath := Lemma68HoneGoodEventAe.walk_inputs_ae hη hε hp hedge hlf hcons i.a hF0 hst
  have hρle : ρ ≤ ρmesh := by linarith
  have hmeshB : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    Lemma68HoneRrLocal.cellDiamLe_mono_set (Metric.ball_subset_ball hρle) hmω
  -- the shell centres of a walk are eligible (ball mesh on `ball 0 ρ`)
  have hzW : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ x : ℕ → ℤ,
      (∀ j : ℕ, (cell ε (S.η ω) (x j) ∩ cell ε (S.η ω) (x (j + 1))).Nonempty) →
      (cell ε (S.η ω) (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty →
      vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
      shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
        ∈ shortEligible ρ (dyadicD r) (shortExp ζ) :=
    fun k hk x hadj hst' hτ =>
      Lemma68HoneRrLocal.shellCentre_mem_of_walk_loc hη hε hr0 hrρ hd hds hs4 hNs hmeshB hF0 h0 hKb hRf hadj hst'
        hτ k hk
  have hhit : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) (↑i.A : Set ℤ)
        (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
      ∀ t : ℕ, shellHit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) k x = (t : ℕ∞) →
        x t ∈ interiorCellVertices ε (S.η ω) (ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) (4 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω)
            (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 3)) := by
    intro k hk
    filter_upwards [hPath] with x hx hxm t ht
    obtain ⟨hadj, hst', hτ⟩ := hx
    have hz := hzW k hk x hadj hst' hτ
    -- the hit time is at most the shell exit time, which is below the exit time of the killed walk
    have h1 := MatedCRT.Lemma68ShellParam.shellHit_le_shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
      (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x
    rw [ht] at h1
    have hlt := hxm.1
    have hτt : (t : ℕ∞) ≤ vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x := h1.trans hlt.le
    have hstB := cell_meets_ball_of_frontier hKb hr0 hrρ hst'
    have hxt := MatedCRT.Lemma68PathMesh.walk_mem_meshBall_upto_vExitTime (Θ := i.Θ) (F0 := i.F0) (x := x)
      (div_nonneg hd.le (by norm_num)) hF0.subset hgapMesh hmω (fun n _ => hadj n) hstB t hτt
    have hcell : ∀ p ∈ cell ε (S.η ω) (x t), ∀ q ∈ cell ε (S.η ω) (x t), dist p q ≤ dyadicD r / 100 :=
      fun p hp q hq => hmω (x t) hxt p hp q hq
    exact MatedCRT.Lemma68HoneExitGeom.shellHit_interior_of_cellDiam hε (fillCells ε (S.η ω) ↑i.Θ) hd k x
      (hRf _ hz).1 t ht hcell
  have hb := MatedCRT.Lemma68HoneExitGeom.hb_ae_of_walk hη (fillCells ε (S.η ω) ↑i.Θ)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (S.mult ε ω) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1) hdeg hadjC (fun _ _ => rfl) hhit
  have hmeshLoc : ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ p ∈ cell ε (S.η ω) k', ∀ q ∈ cell ε (S.η ω) k', dist p q ≤ dyadicD r / 100 :=
    fun k' hk' => hmω k' (Set.Nonempty.mono (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hρle)) hk')
  intro k hk
  filter_upwards [hb k hk, hPath] with x hbx hx hpre
  obtain ⟨hadj, hst', hτ⟩ := hx
  have hbx' := hbx hpre
  have hz := hzW k hk x hadj hst' hτ
  have hRz := hRf _ hz
  have hv := MatedCRT.Lemma68HoneWalkAe.exitVertex_mem_ball_of_sphere hε
    (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
      (winRf S ρ ζ C r ω) k x).toNat)
    hd hds hRz.2 hgap hz hmeshLoc hbx'
  exact mem_ball_zero_iff.mp hv

/-- **`hx1_fixedOmega_loc_s1` with a free window constant `c0W` (`_g`).** The window radius
`winRf S ρ ζ C r ω` (= `windowRfT S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω`, B1Assembly68.lean:63-65) is written
inline as `windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω` (`Lemma68WindowRf.windowRfT`, no new definition), in the
statement and in the proof. The proof is that of `hx1_fixedOmega_loc_s1` with `shellC068` replaced by `c0W` in the
range lemma `Lemma68HoneRadii.windowRfT_rangeShortEligible`, which takes an arbitrary window constant `c₀` (no
hypothesis on it). The proof reads no property of `c0W` and never reads the value of `shellC068`. The conclusion is the
binder `hx1` of `shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean:1216) with `ρmom := rhoCell68 ρ`. No hypothesis
on `s1` or `c0W` is used. -/
theorem hx1_fixedOmega_loc_s1_g {γ ω₀ ρ CG ζ α CE C ε s₀ r ρmom ρmesh s1 c0W : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r)
    (hrρ : r ≤ ρ / 4) (hrle : r ≤ countThreshold ζ) (hgap : ρ ≤ ρmom)
    (hgapMesh : dyadicD r / 100 ≤ ρmesh - ρ)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh)) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat)‖
            < ρmom - Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω)
              (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4 := by
  intro hadm
  obtain ⟨-, hcurve, hmult, hη, -, -, hdeg, hadjC, hadjε⟩ := hreg
  obtain ⟨hlf, hcons⟩ := hmult ε hε
  have hedge := hadjε ε hε
  have hp := Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  have hF0 : (↑i.F0 : Set ℤ) = cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) ρ) := hadm.1.1
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) :=
    subset_closure.trans hadm.1.2.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hadm.1.2.2 (Metric.mem_ball_self hs₀)
  have hst := Lemma68ShellCorePw.hstart_of_fullAdmAt S ω i hη hε hr0 hs₀ hadm
  have hr1 : r ≤ 1 := by linarith
  have hd := dyadicD_pos r
  have hd1 := dyadicD_le_one r
  have hdr : r ^ 2 ≤ dyadicD r := (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd2 : dyadicD r < 2 * r ^ 2 := (Lemma68ChainGlue.dyadicD_mem hr0 hr1).2
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    simpa using h
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrle hd hd2
  have hcb := Lemma68ChainGlue.countBound_zeta hζ0 hr0 hrle hd hdr hd2
  have hζr : r ^ ζ ≤ (2 : ℝ) ^ (-shortExp ζ) / 4000 := by
    have h := Real.rpow_le_rpow hr0.le hrle hζ0.le
    unfold countThreshold at h
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hζ0.ne', Real.rpow_one] at h
  have hrpos : 0 < r ^ ζ := Real.rpow_pos_of_pos hr0 ζ
  have hkey : 1 ≤ countConst ζ * r ^ (-ζ) := by
    unfold countConst
    rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, one_le_div hrpos]
    have hX : (0 : ℝ) < (2 : ℝ) ^ (-shortExp ζ) := by positivity
    linarith
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h := hkey.trans hcb
    exact_mod_cast h
  have hn : shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 = shellCount r (dyadicD r ^ shortExp ζ) :=
    Nat.sub_add_cancel hN1
  have hNs : 20 * (((shellCount r (dyadicD r ^ shortExp ζ) - 1) + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [hn]
    have h1 : ((shellCount r (dyadicD r ^ shortExp ζ) : ℕ) : ℝ) ≤ r / (400 * dyadicD r ^ shortExp ζ) := by
      unfold shellCount
      exact Nat.floor_le (by positivity)
    have hpos : 0 < 400 * dyadicD r ^ shortExp ζ := by positivity
    have h2 := (le_div_iff₀ hpos).mp h1
    nlinarith [h2]
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) z ∧
        (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) z ≤ dyadicD r ^ shortExp ζ :=
    Lemma68HoneRadii.windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd hd1 ha1 ω
  have hPath := Lemma68HoneGoodEventAe.walk_inputs_ae hη hε hp hedge hlf hcons i.a hF0 hst
  have hρle : ρ ≤ ρmesh := by linarith
  have hmeshB : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    Lemma68HoneRrLocal.cellDiamLe_mono_set (Metric.ball_subset_ball hρle) hmω
  -- the shell centres of a walk are eligible (ball mesh on `ball 0 ρ`)
  have hzW : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ x : ℕ → ℤ,
      (∀ j : ℕ, (cell ε (S.η ω) (x j) ∩ cell ε (S.η ω) (x (j + 1))).Nonempty) →
      (cell ε (S.η ω) (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty →
      vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
      shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
        ∈ shortEligible ρ (dyadicD r) (shortExp ζ) :=
    fun k hk x hadj hst' hτ =>
      Lemma68HoneRrLocal.shellCentre_mem_of_walk_loc hη hε hr0 hrρ hd hds hs4 hNs hmeshB hF0 h0 hKb hRf hadj hst'
        hτ k hk
  have hhit : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) (↑i.A : Set ℤ)
        (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
      ∀ t : ℕ, shellHit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) k x = (t : ℕ∞) →
        x t ∈ interiorCellVertices ε (S.η ω) (ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) (4 * (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C
            (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            k x) / 3)) := by
    intro k hk
    filter_upwards [hPath] with x hx hxm t ht
    obtain ⟨hadj, hst', hτ⟩ := hx
    have hz := hzW k hk x hadj hst' hτ
    -- the hit time is at most the shell exit time, which is below the exit time of the killed walk
    have h1 := MatedCRT.Lemma68ShellParam.shellHit_le_shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
      (dyadicD r ^ shortExp ζ) (dyadicD r) (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x
    rw [ht] at h1
    have hlt := hxm.1
    have hτt : (t : ℕ∞) ≤ vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x := h1.trans hlt.le
    have hstB := cell_meets_ball_of_frontier hKb hr0 hrρ hst'
    have hxt := MatedCRT.Lemma68PathMesh.walk_mem_meshBall_upto_vExitTime (Θ := i.Θ) (F0 := i.F0) (x := x)
      (div_nonneg hd.le (by norm_num)) hF0.subset hgapMesh hmω (fun n _ => hadj n) hstB t hτt
    have hcell : ∀ p ∈ cell ε (S.η ω) (x t), ∀ q ∈ cell ε (S.η ω) (x t), dist p q ≤ dyadicD r / 100 :=
      fun p hp q hq => hmω (x t) hxt p hp q hq
    exact MatedCRT.Lemma68HoneExitGeom.shellHit_interior_of_cellDiam hε (fillCells ε (S.η ω) ↑i.Θ) hd k x
      (hRf _ hz).1 t ht hcell
  have hb := MatedCRT.Lemma68HoneExitGeom.hb_ae_of_walk hη (fillCells ε (S.η ω) ↑i.Θ)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (S.mult ε ω) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1) hdeg hadjC (fun _ _ => rfl) hhit
  have hmeshLoc : ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ p ∈ cell ε (S.η ω) k', ∀ q ∈ cell ε (S.η ω) k', dist p q ≤ dyadicD r / 100 :=
    fun k' hk' => hmω k' (Set.Nonempty.mono (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hρle)) hk')
  intro k hk
  filter_upwards [hb k hk, hPath] with x hbx hx hpre
  obtain ⟨hadj, hst', hτ⟩ := hx
  have hbx' := hbx hpre
  have hz := hzW k hk x hadj hst' hτ
  have hRz := hRf _ hz
  have hv := MatedCRT.Lemma68HoneWalkAe.exitVertex_mem_ball_of_sphere hε
    (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
      (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat)
    hd hds hRz.2 hgap hz hmeshLoc hbx'
  exact mem_ball_zero_iff.mp hv

/-- **`hx1_fixedOmega_loc` (the original statement, `FullAdmAt (sparsityS1 γ)`).** The proof is `hx1_fixedOmega_loc_s1`
at `s1 := sparsityS1 γ`; the statement and the conclusion are those of the committed declaration (0b56690). -/
theorem hx1_fixedOmega_loc {γ ω₀ ρ CG ζ α CE C ε s₀ r ρmom ρmesh : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r)
    (hrρ : r ≤ ρ / 4) (hrle : r ≤ countThreshold ζ) (hgap : ρ ≤ ρmom)
    (hgapMesh : dyadicD r / 100 ≤ ρmesh - ρ)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh)) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < ρmom - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4 :=
  hx1_fixedOmega_loc_s1 (s1 := Lemma68Config.sparsityS1 γ) S hreg hρ1 hζ0 hζ1 hε hs₀ hr0 hrρ hrle hgap hgapMesh hmω i

end HoneX1Loc68
end MatedCRT
